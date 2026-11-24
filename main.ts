// main.ts is mend, the CLI SPEC.md specifies, and this is the kit's starting point for it (MIT). It does sections 1 to 4, 9 and 10 of SPEC.md: the command line, the output and
// exit codes, safe paths, format detection, JSON edits and the all-or-nothing write. The other three formats are
// detected and then read as holding no edit, so they answer `error: parse 1`: reading unified diffs (section 6),
// SEARCH/REPLACE blocks (section 7) and V4A patches (section 8), and matching lines at three tiers (section 5), are
// yours to write. Node 22, the standard library alone; run it as `node main.ts [options] [PATCH]`.
//
// In a trial the grader runs `node /bot/main.ts` with MAKEFUN_ENV_URL set, and then this file hands over to runner.ts
// (the last lines below): keep that hand-over and runner.ts as they are, and write the CLI.

import { mkdirSync, readFileSync, rmSync, statSync, writeFileSync, writeSync } from 'node:fs';
import { dirname } from 'node:path';

const FORMATS = ['auto', 'unified', 'search-replace', 'v4a', 'json'];

class Exit2 {
  readonly line: string;
  constructor(line: string) {
    this.line = line;
  }
}
class Fail {
  readonly code: string;
  readonly path: string;
  constructor(code: string, path: string) {
    this.code = code;
    this.path = path;
  }
}

const blank = (s: string): boolean => s.trim() === '';

function patchLines(text: string): string[] {
  if (text === '') return [];
  const lines = text.split('\n');
  if (text.endsWith('\n')) lines.pop();
  return lines.map((l) => (l.endsWith('\r') ? l.slice(0, -1) : l));
}

function safe(p: string): boolean {
  return p !== '' && !p.startsWith('/') && !p.includes('\\') && p.split('/').every((s) => s !== '' && s !== '.' && s !== '..');
}

/**
 * The tree as the edits leave it: changed paths in `now` (null: deleted), the rest read from disk. A file a line edit
 * changed may be held as its lines (a Doc) and is turned into text only when it is read as text, so many edits of one
 * large file do not split and join it each time.
 */
class Tree {
  private readonly orig = new Map<string, string | null>();
  readonly now = new Map<string, string | null | Doc>();
  /** Move edits that succeeded, in order: [old path, new path]. */
  readonly moves: [string, string][] = [];
  original(p: string): string | null {
    if (!this.orig.has(p)) {
      let v: string | null = null;
      try {
        if (statSync(p).isFile()) v = readFileSync(p, 'utf8');
      } catch {
        v = null;
      }
      this.orig.set(p, v);
    }
    return this.orig.get(p)!;
  }
  private value(p: string): string | null | Doc {
    return this.now.has(p) ? this.now.get(p)! : this.original(p);
  }
  /** The file's text now, or null when it does not exist. */
  get(p: string): string | null {
    const v = this.value(p);
    if (v === null || typeof v === 'string') return v;
    const text = fromDoc(v);
    this.now.set(p, text);
    return text;
  }
  exists(p: string): boolean {
    return this.value(p) !== null;
  }
  /** The file's lines now, as a copy the caller may change, or null when it does not exist. */
  doc(p: string): Doc | null {
    const v = this.value(p);
    if (v === null) return null;
    if (typeof v === 'string') return toDoc(v);
    return { br: v.br, lines: v.lines.slice(), final: v.final };
  }
}

type Edit = (tree: Tree) => void;

/** A file's text as lines (SPEC.md section 3): its break, its lines, and whether it ends with the break. */
interface Doc {
  br: string;
  lines: string[];
  final: boolean;
}

function toDoc(text: string): Doc {
  const nl = text.indexOf('\n');
  const br = nl > 0 && text[nl - 1] === '\r' ? '\r\n' : '\n';
  if (text === '') return { br, lines: [], final: false };
  const lines = text.split(br);
  const final = text.endsWith(br);
  if (final) lines.pop();
  return { br, lines, final };
}

function fromDoc(d: Doc): string {
  return d.lines.length === 0 ? '' : d.lines.join(d.br) + (d.final ? d.br : '');
}

/** A file an edit creates: LF breaks, a final break unless `final` is false. */
function created(lines: string[], final = true): string {
  return lines.length === 0 ? '' : lines.join('\n') + (final ? '\n' : '');
}

// The three tiers of SPEC.md section 5: exact, trailing spaces and tabs removed, both ends' spaces and tabs removed.
const TIERS: ((s: string) => string)[] = [(s) => s, (s) => s.replace(/[ \t]+$/, ''), (s) => s.replace(/^[ \t]+|[ \t]+$/g, '')];

/** An order of the positions O can start at: it calls `each` on them in turn until `each` answers true. */
type Order = (each: (i: number) => boolean) => void;

/** Every position O can start at in `lines` (0 to lines - k), in ascending order from `from`. */
const ascending =
  (lines: string[], k: number, from = 0): Order =>
  (each) => {
    for (let i = Math.max(from, 0); i + k <= lines.length; i++) if (each(i)) return;
  };

/** Every position O can start at, nearest to `target` first; of two equally near, the earlier first. */
const nearest =
  (lines: string[], k: number, target: number): Order =>
  (each) => {
    const last = lines.length - k;
    // A target past either end: the nearest positions are that end's, in order.
    if (target > last) {
      for (let i = last; i >= 0; i--) if (each(i)) return;
      return;
    }
    if (target < 0) {
      for (let i = 0; i <= last; i++) if (each(i)) return;
      return;
    }
    for (let d = 0; target - d >= 0 || target + d <= last; d++) {
      if (target - d >= 0 && each(target - d)) return;
      if (d > 0 && target + d <= last && each(target + d)) return;
    }
  };

/**
 * Occurrences of `old` in `lines` at the first tier that has one (SPEC.md section 5): the positions `order` gives, in
 * its order, up to `limit` of them; null when O occurs at no tier among those positions. A tier-1 or tier-2 match of a
 * line holds the normalised text as a substring of the file's line, so each position is first screened on O's longest
 * line before the lines are normalised and compared.
 */
function occurrences(lines: string[], old: string[], strict: boolean, order: Order, limit = Infinity): { tier: number; at: number[] } | null {
  const tiers = strict ? 1 : 3;
  for (let t = 0; t < tiers; t++) {
    const f = TIERS[t]!;
    const want = old.map(f);
    let key = 0;
    for (let j = 1; j < want.length; j++) if (want[j]!.length > want[key]!.length) key = j;
    const probe = want[key]!;
    const at: number[] = [];
    order((i) => {
      const line = lines[i + key]!;
      if (t === 0 ? line !== probe : !line.includes(probe)) return false;
      let j = 0;
      while (j < want.length && f(lines[i + j]!) === want[j]) j++;
      if (j < want.length) return false;
      at.push(i);
      return at.length >= limit;
    });
    if (at.length > 0) return { tier: t, at };
  }
  return null;
}

/** A line of N: its text, and for a context line the index in O of the line it shares. */
interface NewLine {
  text: string;
  ctx: number;
}

const lead = (s: string): string => /^[ \t]*/.exec(s)![0];

/** The lines that replace O's k lines matched at `at` (SPEC.md section 5). */
function replacement(lines: string[], at: number, old: string[], neu: NewLine[], tier: number): string[] {
  const F = lines[at] === undefined ? '' : lead(lines[at]!);
  const P = old.length === 0 ? '' : lead(old[0]!);
  return neu.map((n) => {
    if (n.ctx >= 0) return lines[at + n.ctx]!;
    if (tier === 2 && !blank(n.text) && n.text.startsWith(P)) return F + n.text.slice(P.length);
    return n.text;
  });
}

const unsafeCheck = (...paths: string[]): void => {
  for (const p of paths) if (!safe(p)) throw new Fail('unsafe', p);
};

function detect(lines: string[]): string | null {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) return null;
  if (lines[first]!.trim() === '*** Begin Patch') return 'v4a';
  const c = lines[first]!.trimStart()[0];
  if (c === '[' || c === '{') return 'json';
  if (lines.some((l) => l.trimEnd() === '<<<<<<< SEARCH')) return 'search-replace';
  if (lines.some((l, i) => l.startsWith('diff --git ') || (l.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')))) return 'unified';
  return null;
}

/** One JSON edit object (SPEC.md section 9), or null when it is not one. */
function jsonEdit(v: unknown): Edit | null {
  if (v === null || typeof v !== 'object' || Array.isArray(v)) return null;
  const o = v as Record<string, unknown>;
  const p = o.path;
  if (typeof p !== 'string') return null;
  const exists = (tree: Tree): string => {
    if (!safe(p)) throw new Fail('unsafe', p);
    const t = tree.get(p);
    if (t === null) throw new Fail('missing', p);
    return t;
  };
  if (o.command === 'create' && typeof o.file_text === 'string') {
    const text = o.file_text;
    return (tree) => {
      if (!safe(p)) throw new Fail('unsafe', p);
      if (tree.get(p) !== null) throw new Fail('exists', p);
      tree.now.set(p, text);
    };
  }
  if (o.command === 'str_replace' && typeof o.old_str === 'string' && o.old_str !== '' && (o.new_str === undefined || typeof o.new_str === 'string')) {
    const oldStr = o.old_str;
    const newStr = (o.new_str as string | undefined) ?? '';
    return (tree) => {
      const before = exists(tree);
      const nl = before.indexOf('\n');
      const crlf = nl > 0 && before[nl - 1] === '\r';
      const lf = (s: string): string => (crlf ? s.replaceAll('\r\n', '\n') : s);
      const t = lf(before);
      const old = lf(oldStr);
      let count = 0;
      for (let k = t.indexOf(old); k >= 0; k = t.indexOf(old, k + 1)) count += 1;
      if (count === 0) throw new Fail('no-match', p);
      if (count > 1) throw new Fail('ambiguous', p);
      const at = t.indexOf(old);
      const out = t.slice(0, at) + lf(newStr) + t.slice(at + old.length);
      tree.now.set(p, crlf ? out.replaceAll('\n', '\r\n') : out);
    };
  }
  if (o.command === 'insert' && typeof o.insert_line === 'number' && Number.isInteger(o.insert_line) && typeof o.new_str === 'string') {
    const line = o.insert_line;
    const add = patchLines(o.new_str);
    return (tree) => {
      const before = exists(tree);
      const nl = before.indexOf('\n');
      const br = nl > 0 && before[nl - 1] === '\r' ? '\r\n' : '\n';
      const lines = before === '' ? [] : before.split(br);
      const final = before !== '' && before.endsWith(br);
      if (final) lines.pop();
      if (line < 0 || line > lines.length) throw new Fail('no-match', p);
      lines.splice(line, 0, ...add);
      tree.now.set(p, lines.length === 0 ? '' : lines.join(br) + (final ? br : ''));
    };
  }
  return null;
}

function jsonEdits(text: string, lines: string[]): Edit[] {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  const edits: Edit[] = [];
  if (lines[first]!.trimStart().startsWith('[')) {
    let v: unknown;
    try {
      v = JSON.parse(text);
    } catch {
      throw new Exit2(`error: parse ${first + 1}`);
    }
    if (!Array.isArray(v)) throw new Exit2(`error: parse ${first + 1}`);
    for (const x of v) {
      const e = jsonEdit(x);
      if (e === null) throw new Exit2(`error: parse ${first + 1}`);
      edits.push(e);
    }
    return edits;
  }
  lines.forEach((l, i) => {
    if (blank(l)) return;
    let e: Edit | null = null;
    try {
      e = jsonEdit(JSON.parse(l));
    } catch {
      e = null;
    }
    if (e === null) throw new Exit2(`error: parse ${i + 1}`);
    edits.push(e);
  });
  return edits;
}

// ---- Unified diffs (SPEC.md section 6) ----

interface Hunk {
  a: number;
  old: string[];
  neu: NewLine[];
  /** The `+` lines, in order (for a creation). */
  plus: string[];
  /** No `\` line follows the hunk's last context or `+` line. */
  eolEnd: boolean;
  /** A `\` line follows the hunk's last `+` line. */
  plusNoEol: boolean;
}

interface Section {
  git: [string, string] | null;
  pair: boolean;
  old?: string | null;
  neu?: string | null;
  renFrom?: string;
  renTo?: string;
  create: boolean;
  del: boolean;
  hunks: Hunk[];
}

const spaces = (s: string): string => s.replace(/^ +| +$/g, '');

function diffPath(l: string): string | null {
  let p = l.slice(4);
  const tab = p.indexOf('\t');
  if (tab >= 0) p = p.slice(0, tab);
  p = spaces(p);
  if (p === '/dev/null') return null;
  if (p.startsWith('a/') || p.startsWith('b/')) p = p.slice(2);
  return p;
}

/** The two paths of `diff --git a/<X> b/<Y>`: where several splits read, the one with X = Y, else the first. */
function gitPaths(rest: string): [string, string] | null {
  if (!rest.startsWith('a/')) return null;
  const splits: [string, string][] = [];
  for (let k = rest.indexOf(' b/'); k >= 0; k = rest.indexOf(' b/', k + 1)) splits.push([rest.slice(2, k), rest.slice(k + 3)]);
  return splits.find(([x, y]) => x === y) ?? splits[0] ?? null;
}

function hunkOf(body: string[], a: number): Hunk {
  const old: string[] = [];
  const neu: NewLine[] = [];
  const plus: string[] = [];
  const kinds: string[] = [];
  const noEol: boolean[] = [];
  for (const b of body) {
    if (b.startsWith('\\')) {
      if (kinds.length > 0) noEol[kinds.length - 1] = true;
      continue;
    }
    const k = b === '' ? ' ' : b[0]!;
    const t = b.slice(1);
    kinds.push(k);
    noEol.push(false);
    if (k === ' ') {
      neu.push({ text: t, ctx: old.length });
      old.push(t);
    } else if (k === '-') old.push(t);
    else {
      neu.push({ text: t, ctx: -1 });
      plus.push(t);
    }
  }
  const lastNew = kinds.findLastIndex((k) => k !== '-');
  const lastPlus = kinds.findLastIndex((k) => k === '+');
  return { a, old, neu, plus, eolEnd: lastNew < 0 || !noEol[lastNew], plusNoEol: lastPlus >= 0 && noEol[lastPlus]! };
}

function parseUnified(lines: string[]): Section[] {
  const secs: Section[] = [];
  let cur: Section | null = null;
  const pairAt = (i: number): boolean => lines[i]!.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ');
  const open = (git: [string, string] | null): Section => {
    cur = { git, pair: false, create: false, del: false, hunks: [] };
    secs.push(cur);
    return cur;
  };
  let i = 0;
  while (i < lines.length) {
    const l = lines[i]!;
    const header = cur !== null && (cur as Section).hunks.length === 0;
    if (l.startsWith('diff --git ')) {
      const g = gitPaths(l.slice(11));
      if (g === null) throw new Exit2(`error: parse ${i + 1}`);
      open(g);
      i += 1;
    } else if (l.startsWith('--- ') && pairAt(i)) {
      const s: Section = header && !(cur as unknown as Section).pair ? (cur as unknown as Section) : open(null);
      s.pair = true;
      s.old = diffPath(l);
      s.neu = diffPath(lines[i + 1]!);
      i += 2;
    } else if (l.startsWith('--- ') && header) {
      throw new Exit2(`error: parse ${i + 2}`);
    } else if (l.startsWith('@@')) {
      const m = /^@@ -(\d+)(?:,\d+)? \+\d+(?:,\d+)? @@/.exec(l);
      if (m === null || cur === null) throw new Exit2(`error: parse ${i + 1}`);
      let j = i + 1;
      while (j < lines.length) {
        const b = lines[j]!;
        if (b !== '' && !' -+\\'.includes(b[0]!)) break;
        if (pairAt(j)) break;
        j += 1;
      }
      while (j > i + 1 && lines[j - 1] === '') j -= 1;
      (cur as Section).hunks.push(hunkOf(lines.slice(i + 1, j), Number(m[1])));
      i = j;
    } else {
      if (header) {
        const s = cur as unknown as Section;
        if (l.startsWith('rename from ')) s.renFrom = spaces(l.slice(12));
        else if (l.startsWith('rename to ')) s.renTo = spaces(l.slice(10));
        else if (l.startsWith('new file mode')) s.create = true;
        else if (l.startsWith('deleted file mode')) s.del = true;
      }
      i += 1;
    }
  }
  return secs;
}

function applyHunks(doc: Doc, hunks: Hunk[], strict: boolean, path: string): void {
  let d = 0;
  for (const h of hunks) {
    const L = doc.lines;
    const k = h.old.length;
    let at: number;
    let tier = 0;
    if (k > 0) {
      const target = h.a - 1 + d;
      const occ = occurrences(L, h.old, strict, nearest(L, k, target), 1);
      if (occ === null) throw new Fail('no-match', path);
      at = occ.at[0]!;
      tier = occ.tier;
    } else at = Math.min(Math.max(h.a + d, 0), L.length);
    const toEnd = at + k === L.length;
    L.splice(at, k, ...replacement(L, at, h.old, h.neu, tier));
    if (toEnd) doc.final = h.eolEnd;
    d += h.neu.length - k;
  }
}

function unifiedEdits(lines: string[], strict: boolean): Edit[] {
  return parseUnified(lines).map((s): Edit => {
    const oldP = s.pair ? s.old! : (s.renFrom ?? s.git?.[0] ?? null);
    const newP = s.pair ? s.neu! : (s.renTo ?? s.git?.[1] ?? null);
    const creation = s.create || (s.pair && s.old === null);
    const deletion = !creation && (s.del || (s.pair && s.neu === null));
    return (tree) => {
      if (creation) {
        const p = newP ?? oldP ?? '';
        unsafeCheck(p);
        if (tree.get(p) !== null) throw new Fail('exists', p);
        const plus = s.hunks.flatMap((h) => h.plus);
        const last = s.hunks.findLast((h) => h.plus.length > 0);
        tree.now.set(p, created(plus, !(last?.plusNoEol ?? false)));
        return;
      }
      if (deletion) {
        const p = oldP ?? newP ?? '';
        unsafeCheck(p);
        if (tree.get(p) === null) throw new Fail('missing', p);
        tree.now.set(p, null);
        return;
      }
      const from = oldP ?? newP ?? '';
      const to = newP ?? from;
      unsafeCheck(from, to);
      const doc = tree.doc(from);
      if (doc === null) throw new Fail('missing', from);
      const move = from !== to;
      if (move && tree.exists(to)) throw new Fail('exists', to);
      applyHunks(doc, s.hunks, strict, from);
      if (move) {
        tree.now.set(from, null);
        tree.now.set(to, doc);
        tree.moves.push([from, to]);
      } else tree.now.set(from, doc);
    };
  });
}

// ---- SEARCH/REPLACE blocks (SPEC.md section 7) ----

function searchReplaceEdits(lines: string[], strict: boolean): Edit[] {
  const edits: Edit[] = [];
  const marker = (i: number, m: string): boolean => lines[i]!.trimEnd() === m;
  let from = 0;
  let prev: string | null = null;
  for (let s = 0; s < lines.length; s++) {
    if (!marker(s, '<<<<<<< SEARCH')) continue;
    let path: string | null = null;
    for (let j = s - 1; j >= from && path === null; j--) {
      const t = lines[j]!.trim();
      if (t !== '' && !t.startsWith('```')) path = t;
    }
    path ??= prev;
    if (path === null) throw new Exit2(`error: parse ${s + 1}`);
    let eq = s + 1;
    while (eq < lines.length && !marker(eq, '=======')) eq++;
    let rep = eq + 1;
    while (rep < lines.length && !marker(rep, '>>>>>>> REPLACE')) rep++;
    if (rep >= lines.length) throw new Exit2(`error: parse ${s + 1}`);
    const p = path;
    const old = lines.slice(s + 1, eq);
    const neu = lines.slice(eq + 1, rep).map((text) => ({ text, ctx: -1 }));
    edits.push((tree) => {
      unsafeCheck(p);
      if (old.length === 0) {
        if (tree.exists(p)) throw new Fail('exists', p);
        tree.now.set(p, created(neu.map((n) => n.text)));
        return;
      }
      const doc = tree.doc(p);
      if (doc === null) throw new Fail('missing', p);
      const occ = occurrences(doc.lines, old, strict, ascending(doc.lines, old.length), 2);
      if (occ === null) throw new Fail('no-match', p);
      if (occ.at.length > 1) throw new Fail('ambiguous', p);
      const at = occ.at[0]!;
      doc.lines.splice(at, old.length, ...replacement(doc.lines, at, old, neu, occ.tier));
      tree.now.set(p, doc);
    });
    prev = path;
    from = rep + 1;
    s = rep;
  }
  return edits;
}

// ---- V4A patches (SPEC.md section 8) ----

interface Chunk {
  anchor: string | null;
  old: string[];
  neu: NewLine[];
  eof: boolean;
}

/** The first line at or after `from` equal to `anchor` at the first tier where one is, or -1. */
function findAnchor(lines: string[], anchor: string, from: number, strict: boolean): number {
  for (let t = 0; t < (strict ? 1 : 3); t++) {
    const f = TIERS[t]!;
    const want = f(anchor);
    for (let i = from; i < lines.length; i++) if (lines[i]!.includes(want) && f(lines[i]!) === want) return i;
  }
  return -1;
}

function v4aEdits(lines: string[], strict: boolean): Edit[] {
  const parse = (n: number): Exit2 => new Exit2(`error: parse ${n}`);
  const b = lines.findIndex((l) => !blank(l));
  if (b < 0) throw parse(1);
  if (lines[b]!.trim() !== '*** Begin Patch') throw parse(b + 1);
  let e = lines.length - 1;
  while (e >= 0 && blank(lines[e]!)) e--;
  if (e === b || lines[e]!.trim() !== '*** End Patch') throw parse(lines.length + 1);
  const heads = ['*** Add File: ', '*** Delete File: ', '*** Update File: '];
  const secs: { kind: string; path: string; line: number; body: [string, number][] }[] = [];
  for (let i = b + 1; i < e; i++) {
    const l = lines[i]!;
    const h = heads.find((x) => l.startsWith(x));
    if (h !== undefined) secs.push({ kind: h[4]!, path: spaces(l.slice(h.length)), line: i + 1, body: [] });
    else if (secs.length > 0) secs[secs.length - 1]!.body.push([l, i + 1]);
    else if (!blank(l)) throw parse(i + 1);
  }
  const edits: Edit[] = [];
  for (const sec of secs) {
    const body = sec.body;
    while (body.length > 0 && blank(body[body.length - 1]![0])) body.pop();
    const p = sec.path;
    if (sec.kind === 'A') {
      const add = body.map(([l, n]) => {
        if (l === '') return '';
        if (l.startsWith('+')) return l.slice(1);
        throw parse(n);
      });
      edits.push((tree) => {
        unsafeCheck(p);
        if (tree.get(p) !== null) throw new Fail('exists', p);
        tree.now.set(p, created(add));
      });
    } else if (sec.kind === 'D') {
      if (body.length > 0) throw parse(body[0]![1]);
      edits.push((tree) => {
        unsafeCheck(p);
        if (tree.get(p) === null) throw new Fail('missing', p);
        tree.now.set(p, null);
      });
    } else {
      let k = 0;
      let move: string | null = null;
      if (body.length > 0 && body[0]![0].startsWith('*** Move to: ')) {
        move = spaces(body[0]![0].slice(13));
        k = 1;
      }
      const chunks: Chunk[] = [];
      let ch: Chunk | null = null;
      const start = (anchor: string | null): Chunk => {
        ch = { anchor, old: [], neu: [], eof: false };
        chunks.push(ch);
        return ch;
      };
      for (; k < body.length; k++) {
        const [l, n] = body[k]!;
        if (l.startsWith('@@')) start(spaces(l.slice(2)) || null);
        else if (l.trimEnd() === '*** End of File') {
          if (ch === null) throw parse(n);
          (ch as Chunk).eof = true;
          ch = null;
        } else if (l === '' || ' -+'.includes(l[0]!)) {
          if (ch === null && chunks.length > 0) throw parse(n);
          const c: Chunk = ch ?? start(null);
          const t = l.slice(1);
          if (l[0] === '-') c.old.push(t);
          else if (l[0] === '+') c.neu.push({ text: t, ctx: -1 });
          else {
            c.neu.push({ text: t, ctx: c.old.length });
            c.old.push(t);
          }
        } else throw parse(n);
      }
      if (chunks.length === 0 && move === null) throw parse(sec.line);
      const to = move;
      edits.push((tree) => {
        unsafeCheck(p, ...(to === null ? [] : [to]));
        const doc = tree.doc(p);
        if (doc === null) throw new Fail('missing', p);
        if (to !== null && tree.exists(to)) throw new Fail('exists', to);
        const L = doc.lines;
        let cur = 0;
        for (const c of chunks) {
          if (c.anchor !== null) {
            const i = findAnchor(L, c.anchor, cur, strict);
            if (i < 0) throw new Fail('no-match', p);
            cur = i + 1;
          }
          if (c.old.length === 0) {
            const at = c.eof ? L.length : cur;
            L.splice(at, 0, ...c.neu.map((x) => x.text));
            cur = at + c.neu.length;
            continue;
          }
          const k2 = c.old.length;
          // An end-of-file chunk takes only the occurrence ending at the last line: one position to try.
          const order: Order = c.eof
            ? (each) => {
                if (L.length - k2 >= Math.max(cur, 0)) each(L.length - k2);
              }
            : ascending(L, k2, cur);
          const occ = occurrences(L, c.old, strict, order, 1);
          if (occ === null) throw new Fail('no-match', p);
          const at = occ.at[0]!;
          L.splice(at, k2, ...replacement(L, at, c.old, c.neu, occ.tier));
          cur = at + c.neu.length;
        }
        if (to !== null) {
          tree.now.set(p, null);
          tree.now.set(to, doc);
          tree.moves.push([p, to]);
        } else tree.now.set(p, doc);
      });
    }
  }
  return edits;
}

function run(args: string[]): { code: number; out: string[] } {
  let format: string | null = null;
  let check = false;
  let strict = false;
  const pos: string[] = [];
  let ended = false;
  for (const a of args) {
    if (!ended && a === '--') ended = true;
    else if (!ended && a.startsWith('-') && a !== '-') {
      if (a.startsWith('--format=') && format === null && FORMATS.includes(a.slice(9))) format = a.slice(9);
      else if (a === '--check' && !check) check = true;
      else if (a === '--strict' && !strict) strict = true;
      else return { code: 2, out: ['error: usage'] };
    } else pos.push(a);
  }
  if (pos.length > 1) return { code: 2, out: ['error: usage'] };
  const file = pos.length === 0 || pos[0] === '-' ? null : pos[0]!;
  let text = '';
  try {
    text = readFileSync(file ?? 0, 'utf8');
  } catch {
    if (file !== null) return { code: 2, out: ['error: no-patch'] };
  }
  const lines = patchLines(text);
  const kind = format === null || format === 'auto' ? detect(lines) : format;
  if (kind === null) return { code: 2, out: ['error: format'] };
  let edits: Edit[];
  try {
    edits =
      kind === 'json'
        ? jsonEdits(text, lines)
        : kind === 'unified'
          ? unifiedEdits(lines, strict)
          : kind === 'search-replace'
            ? searchReplaceEdits(lines, strict)
            : v4aEdits(lines, strict);
    if (edits.length === 0) throw new Exit2('error: parse 1');
  } catch (e) {
    if (e instanceof Exit2) return { code: 2, out: [e.line] };
    throw e;
  }
  const tree = new Tree();
  const fails: Fail[] = [];
  for (const edit of edits) {
    const before = new Map(tree.now);
    const moved = tree.moves.length;
    try {
      edit(tree);
    } catch (e) {
      if (!(e instanceof Fail)) throw e;
      tree.now.clear();
      for (const [k, v] of before) tree.now.set(k, v);
      tree.moves.length = moved;
      fails.push(e);
    }
  }
  if (fails.length > 0) return { code: 1, out: [...fails.map((f) => `error: ${f.code} ${f.path}`), `failed: ${fails.length} of ${edits.length} edits`] };
  const byteOrder = (a: string, b: string): number => Buffer.compare(Buffer.from(a), Buffer.from(b));
  const changed = [...tree.now.keys()].filter((p) => tree.original(p) !== tree.get(p)).sort(byteOrder);
  // An R line replaces the D and A lines of a move whose old path is gone and whose new path is new.
  const rows: [string, string][] = [];
  const paired = new Set<string>();
  for (const [o, n] of tree.moves) {
    if (paired.has(o) || paired.has(n)) continue;
    if (tree.original(o) !== null && !tree.exists(o) && tree.original(n) === null && tree.exists(n)) {
      rows.push([n, `R ${o} -> ${n}`]);
      paired.add(o);
      paired.add(n);
    }
  }
  for (const p of changed) {
    if (paired.has(p)) continue;
    const was = tree.original(p);
    rows.push([p, `${was === null ? 'A' : tree.get(p) === null ? 'D' : 'M'} ${p}`]);
  }
  rows.sort((x, y) => byteOrder(x[0], y[0]));
  if (!check) {
    for (const p of changed) {
      const now = tree.get(p);
      if (now === null) rmSync(p, { force: true });
      else {
        mkdirSync(dirname(p), { recursive: true });
        writeFileSync(p, now);
      }
    }
  }
  return { code: 0, out: [...rows.map((r) => r[1]), `ok: ${rows.length} ${rows.length === 1 ? 'file' : 'files'}`] };
}


const trialEnv = process.env.MAKEFUN_ENV_URL;
if (trialEnv !== undefined && trialEnv !== '') {
  // A trial: the kit's runner reads the checks from the env and runs this file on each one, without this variable.
  const { runTrial } = await import('./runner.ts');
  await runTrial(trialEnv);
} else {
  const r = run(process.argv.slice(2));
  writeSync(1, r.out.map((l) => `${l}\n`).join(''));
  process.exitCode = r.code;
}
