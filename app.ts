// A standalone GitHub-compatible git forge: git smart HTTP (v2/v0), REST v3, GraphQL v4 and
// MCP, all in one process over an in-memory store. Standard library only. Deterministic: no
// wall clock or unseeded randomness in request handling; timestamps come from MAKEFUN_TRIAL_NOW.

import { createHash } from 'node:crypto';
import { createServer, type IncomingMessage, type Server, type ServerResponse } from 'node:http';
import { deflateSync, inflateSync } from 'node:zlib';

const JSON_TYPE = 'application/json; charset=utf-8';
const TOKEN = process.env.MAKEFUN_SHOP_TOKEN ?? '';
const NOW_SEC = (() => {
  const v = Number.parseInt(process.env.MAKEFUN_TRIAL_NOW ?? '', 10);
  return Number.isFinite(v) && v > 0 ? v : 1735689600;
})();
const NOW_ISO = new Date(NOW_SEC * 1000).toISOString();
// The token owner's login is fixed by the suite's sealed scenario seed (wire.ts SCENARIO_SEED is a
// constant, so users[0] is always adaiversen); a repo under any other owner answers 404.
const VIEWER_LOGIN = 'adaiversen';
const VIEWER_NAME = 'ada iversen';
const VIEWER_EMAIL = 'adaiversen@example.invalid';
const VIEWER_ID = 1000;
const ZERO_OID = '0'.repeat(40);

let reqCounter = 0;
let repoIdCounter = 5000;
let globalIdCounter = 20000;

function nextReqId(): string {
  reqCounter += 1;
  return `req-${reqCounter}`;
}
function sha1hex(data: Buffer): string {
  return createHash('sha1').update(data).digest('hex');
}
function hashObject(type: string, data: Buffer): string {
  const head = Buffer.from(`${type} ${data.length}\0`, 'utf8');
  return sha1hex(Buffer.concat([head, data]));
}
function b64encode(buf: Buffer): string {
  return buf.toString('base64');
}
function b64decodeText(s: string): Buffer {
  return Buffer.from(s.replace(/[\r\n\t ]+/g, ''), 'base64');
}
function gid(kind: string, id: string | number): string {
  return Buffer.from(`${kind}:${id}`, 'utf8').toString('base64');
}
function ungid(id: string): { kind: string; id: string } | null {
  try {
    const text = Buffer.from(id.replace(/[\r\n\t ]+/g, ''), 'base64').toString('utf8');
    const i = text.indexOf(':');
    if (i <= 0) return null;
    return { kind: text.slice(0, i), id: text.slice(i + 1) };
  } catch {
    return null;
  }
}
function isOid(s: string): boolean {
  return /^[0-9a-f]{40}$/.test(s);
}
function esc(s: string): string {
  return s.replace(/\\/g, '\\\\').replace(/"/g, '\\"');
}

// ---------------------------------------------------------------- pkt-lines

function pktLine(payload: Buffer | string): Buffer {
  const data = typeof payload === 'string' ? Buffer.from(payload, 'utf8') : payload;
  const head = Buffer.alloc(4);
  head.write((data.length + 4).toString(16).padStart(4, '0'), 0, 4, 'ascii');
  return Buffer.concat([head, data]);
}
const PKT_FLUSH = Buffer.from('0000', 'ascii');
const PKT_DELIM = Buffer.from('0001', 'ascii');
function pktLines(items: (Buffer | string)[]): Buffer {
  return Buffer.concat(items.map((it) => pktLine(it)));
}

interface PktPacket {
  kind: 'data' | 'flush' | 'delim' | 'end';
  payload: Buffer;
}
/** Parse pkt-lines from the start of buf; returns packets and the offset where framing stops
 * (a flush packet, or the first non-framed byte / end). Throws on a malformed header. */
function parsePktLines(buf: Buffer): { packets: PktPacket[]; offset: number } {
  const packets: PktPacket[] = [];
  let off = 0;
  while (off + 4 <= buf.length) {
    const head = buf.subarray(off, off + 4).toString('ascii');
    if (!/^[0-9a-fA-F]{4}$/.test(head)) break;
    const len = Number.parseInt(head, 16);
    if (len === 0) {
      packets.push({ kind: 'flush', payload: Buffer.alloc(0) });
      off += 4;
      break;
    }
    if (len === 1) {
      packets.push({ kind: 'delim', payload: Buffer.alloc(0) });
      off += 4;
      continue;
    }
    if (len === 2) {
      packets.push({ kind: 'end', payload: Buffer.alloc(0) });
      off += 4;
      continue;
    }
    if (len < 4 || len > 65520 || off + len > buf.length) throw new Error('bad pkt-line');
    packets.push({ kind: 'data', payload: buf.subarray(off + 4, off + len) });
    off += len;
  }
  return { packets, offset: off };
}
function parseAllPktLines(buf: Buffer): PktPacket[] {
  const out: PktPacket[] = [];
  let off = 0;
  while (off < buf.length) {
    if (off + 4 > buf.length) break;
    const head = buf.subarray(off, off + 4).toString('ascii');
    if (!/^[0-9a-fA-F]{4}$/.test(head)) throw new Error('bad pkt-line header');
    const len = Number.parseInt(head, 16);
    if (len === 0) {
      out.push({ kind: 'flush', payload: Buffer.alloc(0) });
      off += 4;
      continue;
    }
    if (len === 1) {
      out.push({ kind: 'delim', payload: Buffer.alloc(0) });
      off += 4;
      continue;
    }
    if (len === 2) {
      out.push({ kind: 'end', payload: Buffer.alloc(0) });
      off += 4;
      continue;
    }
    if (len < 4 || len > 65520 || off + len > buf.length) throw new Error('bad pkt-line');
    out.push({ kind: 'data', payload: buf.subarray(off + 4, off + len) });
    off += len;
  }
  return out;
}
function pktDataLines(buf: Buffer): string[] {
  return parseAllPktLines(buf)
    .filter((p) => p.kind === 'data')
    .map((p) => p.payload.toString('utf8'));
}

// ---------------------------------------------------------------- git objects / packfiles

type ObjType = 'commit' | 'tree' | 'blob' | 'tag';
interface GitObj {
  type: ObjType;
  data: Buffer;
}

function parseTree(data: Buffer): { mode: string; name: string; oid: string }[] {
  const entries: { mode: string; name: string; oid: string }[] = [];
  let off = 0;
  while (off < data.length) {
    const sp = data.indexOf(0x20, off);
    const nul = data.indexOf(0x00, sp + 1);
    entries.push({
      mode: data.subarray(off, sp).toString('ascii'),
      name: data.subarray(sp + 1, nul).toString('utf8'),
      oid: data.subarray(nul + 1, nul + 21).toString('hex'),
    });
    off = nul + 21;
  }
  return entries;
}
function buildTree(entries: { mode: string; name: string; oid: string }[]): Buffer {
  const sorted = [...entries].sort((a, b) => {
    const la = Buffer.from(a.mode === '40000' ? `${a.name}/` : a.name, 'utf8');
    const lb = Buffer.from(b.mode === '40000' ? `${b.name}/` : b.name, 'utf8');
    return Buffer.compare(la, lb);
  });
  const parts: Buffer[] = [];
  for (const e of sorted) {
    parts.push(Buffer.from(`${e.mode} ${e.name}\0`, 'utf8'));
    parts.push(Buffer.from(e.oid, 'hex'));
  }
  return Buffer.concat(parts);
}
function parseCommit(data: Buffer): { tree: string; parents: string[]; message: string } {
  const text = data.toString('utf8');
  const blank = text.indexOf('\n\n');
  const head = blank < 0 ? text : text.slice(0, blank);
  const message = blank < 0 ? '' : text.slice(blank + 2);
  let tree = '';
  const parents: string[] = [];
  for (const line of head.split('\n')) {
    if (line.startsWith('tree ')) tree = line.slice(5);
    else if (line.startsWith('parent ')) parents.push(line.slice(7));
  }
  return { tree, parents, message };
}
function parseTag(data: Buffer): { object: string; type: string; tag: string } {
  const text = data.toString('utf8');
  const blank = text.indexOf('\n\n');
  const head = blank < 0 ? text : text.slice(0, blank);
  let object = '';
  let type = '';
  let tag = '';
  for (const line of head.split('\n')) {
    if (line.startsWith('object ')) object = line.slice(7);
    else if (line.startsWith('type ')) type = line.slice(5);
    else if (line.startsWith('tag ')) tag = line.slice(4);
  }
  return { object, type, tag };
}

function readVarint(buf: Buffer, off: number): { value: number; next: number } {
  let value = buf[off] & 0x7f;
  let shift = 7;
  let i = off + 1;
  while (buf[i - 1] & 0x80) {
    value |= (buf[i] & 0x7f) << shift;
    shift += 7;
    i += 1;
  }
  return { value, next: i };
}
/** Length of the zlib stream starting at `off` (inflateSync ignores trailing bytes, so binary search). */
function zlibLen(buf: Buffer, off: number, end: number): number {
  let lo = off;
  let hi = end;
  // hi must inflate; if even the whole rest fails, throw.
  try {
    inflateSync(buf.subarray(off, hi));
  } catch {
    throw new Error('bad zlib stream in pack');
  }
  while (hi - lo > 1) {
    const mid = (lo + hi) >> 1;
    try {
      inflateSync(buf.subarray(off, mid));
      hi = mid;
    } catch {
      lo = mid;
    }
  }
  return hi - off;
}
function applyDelta(base: Buffer, delta: Buffer): Buffer {
  let off = 0;
  const src = readVarint(delta, off);
  off = src.next;
  const tgt = readVarint(delta, off);
  off = tgt.next;
  if (src.value !== base.length) throw new Error('delta base size mismatch');
  const out: Buffer[] = [];
  let total = 0;
  while (off < delta.length) {
    const op = delta[off];
    off += 1;
    if (op & 0x80) {
      let cpOff = 0;
      let cpSize = 0;
      for (let b = 0; b < 4; b += 1) if (op & (1 << b)) { cpOff |= delta[off] << (8 * b); off += 1; }
      for (let b = 0; b < 3; b += 1) if (op & (0x10 << b)) { cpSize |= delta[off] << (8 * b); off += 1; }
      if (cpSize === 0) cpSize = 0x10000;
      out.push(base.subarray(cpOff, cpOff + cpSize));
      total += cpSize;
    } else {
      let size = op;
      if (size === 0) size = 0x80;
      out.push(delta.subarray(off, off + size));
      off += size;
      total += size;
    }
  }
  const result = Buffer.concat(out, total);
  if (result.length !== tgt.value) throw new Error('delta target size mismatch');
  return result;
}

/** Parse a packfile; `external` resolves thin-pack bases the pack itself does not hold. */
function readPack(buf: Buffer, external?: (oid: string) => GitObj | undefined): Map<string, GitObj> {
  if (buf.length < 32 || buf.subarray(0, 4).toString('ascii') !== 'PACK') throw new Error('not a packfile');
  const count = buf.readUInt32BE(8);
  const trailerStart = buf.length - 20;
  interface Raw {
    offset: number;
    typeCode: number;
    size: number;
    baseOffset?: number;
    baseOid?: string;
    data: Buffer;
  }
  const raws: Raw[] = [];
  const byOffset = new Map<number, Raw>();
  let off = 12;
  for (let i = 0; i < count; i += 1) {
    const start = off;
    const first = buf[off];
    const typeCode = (first >> 4) & 0x07;
    let size = first & 0x0f;
    let shift = 4;
    off += 1;
    while (buf[off - 1] & 0x80) {
      size |= (buf[off] & 0x7f) << shift;
      shift += 7;
      off += 1;
    }
    const raw: Raw = { offset: start, typeCode, size, data: Buffer.alloc(0) };
    if (typeCode === 6) {
      // OFS_DELTA: negative offset varint
      let byte = buf[off];
      off += 1;
      let baseOff = byte & 0x7f;
      while (byte & 0x80) {
        byte = buf[off];
        off += 1;
        baseOff = ((baseOff + 1) << 7) | (byte & 0x7f);
      }
      raw.baseOffset = start - baseOff;
    } else if (typeCode === 7) {
      raw.baseOid = buf.subarray(off, off + 20).toString('hex');
      off += 20;
    }
    const len = zlibLen(buf, off, trailerStart);
    raw.data = inflateSync(buf.subarray(off, off + len));
    off += len;
    raws.push(raw);
    byOffset.set(start, raw);
  }
  const CODE: Record<number, ObjType> = { 1: 'commit', 2: 'tree', 3: 'blob', 4: 'tag' };
  const objects = new Map<string, GitObj>();
  const byOid = new Map<string, Raw>();
  const resolving = new Set<number>();
  const resolve = (raw: Raw): GitObj => {
    if (raw.typeCode === 6 || raw.typeCode === 7) {
      let base: GitObj;
      if (raw.typeCode === 6) {
        const baseRaw = byOffset.get(raw.baseOffset!);
        if (!baseRaw) throw new Error('ofs-delta base missing');
        if (resolving.has(baseRaw.offset)) throw new Error('delta cycle');
        resolving.add(raw.offset);
        base = resolve(baseRaw);
        resolving.delete(raw.offset);
      } else {
        const baseRaw = byOid.get(raw.baseOid!);
        if (baseRaw) {
          resolving.add(raw.offset);
          base = resolve(baseRaw);
          resolving.delete(raw.offset);
        } else {
          const ext = external?.(raw.baseOid!);
          if (!ext) throw new Error('ref-delta base missing');
          base = ext;
        }
      }
      const data = applyDelta(base.data, raw.data);
      const obj: GitObj = { type: base.type, data };
      const oid = hashObject(base.type, data);
      objects.set(oid, obj);
      byOid.set(oid, raw);
      return obj;
    }
    const type = CODE[raw.typeCode];
    if (!type) throw new Error(`bad pack object type ${raw.typeCode}`);
    const obj: GitObj = { type, data: raw.data };
    const oid = hashObject(type, raw.data);
    objects.set(oid, obj);
    byOid.set(oid, raw);
    return obj;
  };
  for (const raw of raws) resolve(raw);
  return objects;
}

function writePackObjectHeader(type: ObjType, size: number): Buffer {
  const code: Record<ObjType, number> = { commit: 1, tree: 2, blob: 3, tag: 4 };
  const bytes: number[] = [];
  let s = size;
  bytes.push(((code[type] & 0x07) << 4) | (s & 0x0f));
  s >>= 4;
  while (s > 0) {
    bytes[bytes.length - 1] |= 0x80;
    bytes.push(s & 0x7f);
    s >>= 7;
  }
  return Buffer.from(bytes);
}
function writePack(objects: GitObj[]): Buffer {
  const parts: Buffer[] = [];
  const head = Buffer.alloc(12);
  head.write('PACK', 0, 4, 'ascii');
  head.writeUInt32BE(2, 4);
  head.writeUInt32BE(objects.length, 8);
  parts.push(head);
  for (const obj of objects) {
    parts.push(writePackObjectHeader(obj.type, obj.data.length));
    parts.push(deflateSync(obj.data, { level: 1 }));
  }
  const body = Buffer.concat(parts);
  const trailer = createHash('sha1').update(body).digest();
  return Buffer.concat([body, trailer]);
}

// ---------------------------------------------------------------- store

interface Label {
  name: string;
  color: string;
}
interface Issue {
  id: number;
  number: number;
  title: string;
  body: string;
  state: 'open' | 'closed';
  labels: Label[];
  comments: { id: number; body: string }[];
  seq: number;
  cachedJson: string | null;
}
interface Pull {
  id: number;
  number: number;
  title: string;
  body: string;
  state: 'open' | 'closed';
  headRef: string;
  baseRef: string;
  merged: boolean;
  mergedAt: string | null;
  mergeCommitSha: string | null;
  seq: number;
}
interface Repo {
  id: number;
  name: string;
  owner: string;
  description: string;
  isPrivate: boolean;
  defaultBranch: string;
  objects: Map<string, GitObj>;
  refs: Map<string, string>;
  issues: Issue[];
  pulls: Pull[];
  labels: Map<string, Label>;
  nextNumber: number;
  commentSeq: number;
  treeCache: Map<string, Map<string, { oid: string; mode: string }>>;
  advV0: Buffer | null;
  advV2: Buffer | null;
  lsCache: Buffer | null;
  shallowPack: Map<string, Buffer>;
}

const repos = new Map<string, Repo>();
const repoList: Repo[] = [];
let issueSeqCounter = 0;

function repoKey(owner: string, name: string): string {
  return `${owner}/${name}`;
}
function findRepo(owner: string, name: string): Repo | undefined {
  // The viewer login is fixed by the sealed scenario seed (wire.ts SCENARIO_SEED is a constant,
  // so users[0] is always adaiversen). A repo under any other owner is 404, never 403 — never
  // "learn" a different owner from a request path.
  if (owner !== VIEWER_LOGIN) return undefined;
  return repos.get(repoKey(VIEWER_LOGIN, name));
}
function createRepoRecord(name: string, isPrivate: boolean, description: string): Repo {
  const repo: Repo = {
    id: repoIdCounter,
    name,
    owner: VIEWER_LOGIN,
    description,
    isPrivate,
    defaultBranch: 'main',
    objects: new Map(),
    refs: new Map(),
    issues: [],
    pulls: [],
    labels: new Map(),
    nextNumber: 1,
    commentSeq: 1,
    treeCache: new Map(),
    advV0: null,
    advV2: null,
    lsCache: null,
    shallowPack: new Map(),
  };
  repoIdCounter += 1;
  repos.set(repoKey(VIEWER_LOGIN, name), repo);
  repoList.push(repo);
  return repo;
}
function invalidateGitCache(repo: Repo): void {
  repo.advV0 = null;
  repo.advV2 = null;
  repo.lsCache = null;
  repo.shallowPack.clear();
}
function storeObject(repo: Repo, type: ObjType, data: Buffer): string {
  const oid = hashObject(type, data);
  if (!repo.objects.has(oid)) repo.objects.set(oid, { type, data });
  return oid;
}
function putObject(repo: Repo, obj: GitObj): string {
  const oid = hashObject(obj.type, obj.data);
  if (!repo.objects.has(oid)) repo.objects.set(oid, obj);
  return oid;
}

/** Flatten a commit's tree to path -> {oid, mode}; cached per commit (trees are immutable). */
function flatTree(repo: Repo, commitOid: string): Map<string, { oid: string; mode: string }> {
  const cached = repo.treeCache.get(commitOid);
  if (cached) return cached;
  const out = new Map<string, { oid: string; mode: string }>();
  const commit = repo.objects.get(commitOid);
  if (!commit || commit.type !== 'commit') {
    repo.treeCache.set(commitOid, out);
    return out;
  }
  const walk = (treeOid: string, prefix: string): void => {
    const tree = repo.objects.get(treeOid);
    if (!tree || tree.type !== 'tree') return;
    for (const e of parseTree(tree.data)) {
      const path = prefix === '' ? e.name : `${prefix}/${e.name}`;
      if (e.mode === '40000') walk(e.oid, path);
      else out.set(path, { oid: e.oid, mode: e.mode });
    }
  };
  walk(parseCommit(commit.data).tree, '');
  repo.treeCache.set(commitOid, out);
  return out;
}
/** Build nested tree objects from a flat file map; returns the root tree oid. */
function buildTreeFromFiles(repo: Repo, files: Map<string, { oid: string; mode: string }>): string {
  interface Node {
    files: Map<string, { oid: string; mode: string }>;
    dirs: Map<string, Node>;
  }
  const make = (): Node => ({ files: new Map(), dirs: new Map() });
  const root = make();
  for (const [path, entry] of files) {
    const segs = path.split('/');
    let node = root;
    for (let i = 0; i < segs.length - 1; i += 1) {
      const s = segs[i];
      if (!node.dirs.has(s)) node.dirs.set(s, make());
      node = node.dirs.get(s)!;
    }
    node.files.set(segs[segs.length - 1], entry);
  }
  const build = (node: Node): string => {
    const entries: { mode: string; name: string; oid: string }[] = [];
    for (const [name, e] of node.files) entries.push({ mode: e.mode, name, oid: e.oid });
    for (const [name, child] of node.dirs) entries.push({ mode: '40000', name, oid: build(child) });
    return storeObject(repo, 'tree', buildTree(entries));
  };
  return build(root);
}
function makeCommit(repo: Repo, treeOid: string, parents: string[], message: string): string {
  const who = `${VIEWER_NAME} <${VIEWER_EMAIL}> ${NOW_SEC} +0000`;
  const lines = [`tree ${treeOid}`];
  for (const p of parents) lines.push(`parent ${p}`);
  lines.push(`author ${who}`, `committer ${who}`, '');
  const data = Buffer.from(`${lines.join('\n')}\n${message}`, 'utf8');
  return storeObject(repo, 'commit', data);
}
function emptyTreeOid(repo: Repo): string {
  return storeObject(repo, 'tree', Buffer.alloc(0));
}

/** All objects reachable from roots (commits -> tree+parents, tags -> target, trees -> entries). */
function reachable(repo: Repo, roots: Iterable<string>, stopParentsAt?: Set<string>): Set<string> {
  const seen = new Set<string>();
  const queue: string[] = [];
  for (const r of roots) if (isOid(r)) queue.push(r);
  while (queue.length) {
    const oid = queue.pop()!;
    if (seen.has(oid)) continue;
    const obj = repo.objects.get(oid);
    if (!obj) continue;
    seen.add(oid);
    if (obj.type === 'commit') {
      const c = parseCommit(obj.data);
      queue.push(c.tree);
      if (!stopParentsAt || !stopParentsAt.has(oid)) for (const p of c.parents) queue.push(p);
    } else if (obj.type === 'tree') {
      for (const e of parseTree(obj.data)) if (e.mode !== '160000') queue.push(e.oid);
    } else if (obj.type === 'tag') {
      queue.push(parseTag(obj.data).object);
    }
  }
  return seen;
}
function commitAncestors(repo: Repo, tip: string): Set<string> {
  const seen = new Set<string>();
  const queue = [tip];
  while (queue.length) {
    const oid = queue.pop()!;
    if (seen.has(oid) || !isOid(oid)) continue;
    const obj = repo.objects.get(oid);
    if (!obj || obj.type !== 'commit') continue;
    seen.add(oid);
    for (const p of parseCommit(obj.data).parents) queue.push(p);
  }
  return seen;
}
function isAncestor(repo: Repo, ancestor: string, descendant: string): boolean {
  if (ancestor === descendant) return true;
  return commitAncestors(repo, descendant).has(ancestor);
}
function mergeBase(repo: Repo, a: string, b: string): string | null {
  const ancA = commitAncestors(repo, a);
  const queue = [b];
  const seen = new Set<string>();
  while (queue.length) {
    const oid = queue.pop()!;
    if (seen.has(oid)) continue;
    seen.add(oid);
    if (ancA.has(oid)) return oid;
    const obj = repo.objects.get(oid);
    if (obj && obj.type === 'commit') for (const p of parseCommit(obj.data).parents) queue.push(p);
  }
  return null;
}
function peelToCommit(repo: Repo, oid: string): string {
  let cur = oid;
  for (let i = 0; i < 10; i += 1) {
    const obj = repo.objects.get(cur);
    if (!obj || obj.type !== 'tag') return cur;
    cur = parseTag(obj.data).object;
  }
  return cur;
}

// ---------------------------------------------------------------- git fetch computation

interface FetchPlan {
  objects: GitObj[];
  shallow: string[];
  unshallow: string[];
}
/**
 * Objects to send for wants, given what the client already holds (haves, whose parents past a
 * shallow boundary are NOT held) and an optional depth limit.
 */
function planFetch(repo: Repo, wants: string[], haves: string[], depth: number | null, boundaries: string[]): FetchPlan {
  const boundarySet = new Set(boundaries);
  // Generations from the wants (parents only). A want may be an annotated tag: peel it to its
  // commit for the generation walk, but keep the tag object itself as a send root.
  const gen = new Map<string, number>();
  const tagRoots: string[] = [];
  const queue: string[] = [];
  for (const w of wants) {
    if (!isOid(w)) continue;
    const obj = repo.objects.get(w);
    if (!obj) continue;
    if (obj.type === 'tag') {
      tagRoots.push(w);
      const peeled = peelToCommit(repo, w);
      if (peeled !== w && repo.objects.get(peeled)?.type === 'commit' && !gen.has(peeled)) {
        gen.set(peeled, 0);
        queue.push(peeled);
      }
    } else if (obj.type === 'commit' && !gen.has(w)) {
      gen.set(w, 0);
      queue.push(w);
    }
  }
  while (queue.length) {
    const oid = queue.shift()!;
    const g = gen.get(oid)!;
    const obj = repo.objects.get(oid);
    if (!obj || obj.type !== 'commit') continue;
    for (const p of parseCommit(obj.data).parents) {
      if (!gen.has(p)) {
        gen.set(p, g + 1);
        queue.push(p);
      }
    }
  }
  const included = new Set<string>();
  for (const [oid, g] of gen) {
    if (depth === null || g <= depth - 1) included.add(oid);
  }
  // Objects the client already holds: walk haves, stopping at shallow boundaries' parents.
  const held = new Set<string>();
  for (const h of haves) {
    for (const oid of reachable(repo, [h], boundarySet)) held.add(oid);
  }
  // Objects to send: closure of included commits (parents only within `included`).
  const send = new Set<string>();
  const walkQueue: string[] = [];
  for (const oid of included) walkQueue.push(oid);
  for (const oid of tagRoots) walkQueue.push(oid);
  while (walkQueue.length) {
    const oid = walkQueue.pop()!;
    if (send.has(oid)) continue;
    const obj = repo.objects.get(oid);
    if (!obj) continue;
    send.add(oid);
    if (obj.type === 'commit') {
      const c = parseCommit(obj.data);
      walkQueue.push(c.tree);
      for (const p of c.parents) if (included.has(p)) walkQueue.push(p);
    } else if (obj.type === 'tree') {
      for (const e of parseTree(obj.data)) if (e.mode !== '160000') walkQueue.push(e.oid);
    } else if (obj.type === 'tag') {
      walkQueue.push(parseTag(obj.data).object);
    }
  }
  const objects: GitObj[] = [];
  for (const oid of send) {
    if (held.has(oid)) continue;
    const obj = repo.objects.get(oid);
    if (obj) objects.push(obj);
  }
  const shallow: string[] = [];
  const unshallow: string[] = [];
  if (depth !== null) {
    for (const oid of included) {
      const obj = repo.objects.get(oid);
      if (!obj || obj.type !== 'commit') continue;
      const parents = parseCommit(obj.data).parents;
      if (parents.length === 0) continue;
      if (gen.get(oid) === depth - 1) shallow.push(oid);
      else if (boundarySet.has(oid)) unshallow.push(oid);
    }
    for (const b of boundaries) {
      if (included.has(b) && (gen.get(b) ?? 0) < depth - 1 && !unshallow.includes(b)) unshallow.push(b);
    }
  }
  return { objects, shallow, unshallow };
}
function sidebandPack(pack: Buffer): Buffer {
  const chunks: Buffer[] = [];
  for (let off = 0; off < pack.length; off += 65515) {
    const slice = pack.subarray(off, Math.min(pack.length, off + 65515));
    chunks.push(pktLine(Buffer.concat([Buffer.from([1]), slice])));
  }
  if (chunks.length === 0) chunks.push(pktLine(Buffer.from([1])));
  return Buffer.concat(chunks);
}

// ---------------------------------------------------------------- git advertisements

function sortedRefs(repo: Repo): { name: string; oid: string }[] {
  return [...repo.refs.entries()]
    .map(([name, oid]) => ({ name, oid }))
    .sort((a, b) => (a.name < b.name ? -1 : a.name > b.name ? 1 : 0));
}
function refAdvertisementV0(repo: Repo, service: 'git-upload-pack' | 'git-receive-pack'): Buffer {
  const mainTip = repo.refs.get('refs/heads/main') ?? repo.refs.get(`refs/heads/${repo.defaultBranch}`) ?? ZERO_OID;
  const caps =
    service === 'git-upload-pack'
      ? 'side-band-64k thin-pack ofs-delta shallow multi_ack symref=HEAD:refs/heads/main agent=forge/1.0'
      : 'report-status side-band-64k delete-refs ofs-delta symref=HEAD:refs/heads/main agent=forge/1.0';
  const parts: Buffer[] = [pktLine(`# service=${service}\n`), PKT_FLUSH];
  const refs = sortedRefs(repo);
  if (refs.length === 0) {
    parts.push(pktLine(`${ZERO_OID} capabilities^{}\0${caps}\n`));
  } else {
    parts.push(pktLine(`${mainTip} HEAD\0${caps}\n`));
    for (const r of refs) {
      parts.push(pktLine(`${r.oid} ${r.name}\n`));
      if (r.name.startsWith('refs/tags/')) {
        const obj = repo.objects.get(r.oid);
        if (obj && obj.type === 'tag') {
          const peeled = peelToCommit(repo, r.oid);
          if (peeled !== r.oid) parts.push(pktLine(`${peeled} ${r.name}^{}\n`));
        }
      }
    }
  }
  parts.push(PKT_FLUSH);
  return Buffer.concat(parts);
}
function refAdvertisementV2(repo: Repo): Buffer {
  return Buffer.concat([
    pktLine('version 2\n'),
    pktLine('ls-refs=unborn\n'),
    pktLine('fetch=shallow filter\n'),
    pktLine('object-format=sha1\n'),
    pktLine('agent=forge/1.0\n'),
    PKT_FLUSH,
  ]);
}
function lsRefsV2(repo: Repo, prefixes: string[], peel: boolean, symrefs: boolean): Buffer {
  const mainTip = repo.refs.get('refs/heads/main') ?? repo.refs.get(`refs/heads/${repo.defaultBranch}`) ?? ZERO_OID;
  const keep = (name: string): boolean => prefixes.length === 0 || prefixes.some((p) => name.startsWith(p));
  const parts: Buffer[] = [];
  const headTarget = `refs/heads/${repo.defaultBranch}`;
  if (keep('HEAD')) {
    if (mainTip === ZERO_OID) {
      parts.push(pktLine(`unborn HEAD${symrefs ? ` symref-target:${headTarget}` : ''}\n`));
    } else {
      parts.push(pktLine(`${mainTip} HEAD${symrefs ? ` symref-target:${headTarget}` : ''}\n`));
    }
  }
  for (const r of sortedRefs(repo)) {
    if (!keep(r.name)) continue;
    let line = `${r.oid} ${r.name}`;
    if (peel && r.name.startsWith('refs/tags/')) {
      const obj = repo.objects.get(r.oid);
      if (obj && obj.type === 'tag') {
        const peeled = peelToCommit(repo, r.oid);
        if (peeled !== r.oid) line += ` peeled:${peeled}`;
      }
    }
    parts.push(pktLine(`${line}\n`));
  }
  parts.push(PKT_FLUSH);
  return Buffer.concat(parts);
}

// ---------------------------------------------------------------- HTTP helpers

function sendJson(res: ServerResponse, status: number, body: unknown, extra: Record<string, string> = {}): void {
  const text = typeof body === 'string' ? body : `${JSON.stringify(body)}\n`;
  res.writeHead(status, {
    'content-type': JSON_TYPE,
    'content-length': Buffer.byteLength(text),
    'x-github-request-id': nextReqId(),
    ...extra,
  });
  res.end(text);
}
function sendJsonRaw(res: ServerResponse, status: number, text: string, extra: Record<string, string> = {}): void {
  res.writeHead(status, {
    'content-type': JSON_TYPE,
    'content-length': Buffer.byteLength(text),
    'x-github-request-id': nextReqId(),
    ...extra,
  });
  res.end(text);
}
function sendNoContent(res: ServerResponse, extra: Record<string, string> = {}): void {
  res.writeHead(204, { 'x-github-request-id': nextReqId(), ...extra });
  res.end();
}
function errJson(res: ServerResponse, status: number, message: string): void {
  sendJson(res, status, { message });
}
function authed(req: IncomingMessage): boolean {
  const h = req.headers.authorization ?? '';
  if (TOKEN !== '') return h === `Bearer ${TOKEN}`;
  return h.startsWith('Bearer ') && h.length > 7;
}
function readBody(req: IncomingMessage): Promise<Buffer> {
  return new Promise((resolve, reject) => {
    const chunks: Buffer[] = [];
    req.on('data', (c: Buffer) => chunks.push(c));
    req.on('end', () => resolve(Buffer.concat(chunks)));
    req.on('error', reject);
  });
}
function parseJsonBody(raw: Buffer): { ok: true; value: unknown } | { ok: false } {
  if (raw.length === 0) return { ok: true, value: {} };
  try {
    return { ok: true, value: JSON.parse(raw.toString('utf8')) };
  } catch {
    return { ok: false };
  }
}

// ---------------------------------------------------------------- REST shapes

function repoJson(repo: Repo): Record<string, unknown> {
  return {
    id: repo.id,
    node_id: gid('Repository', repo.id),
    name: repo.name,
    full_name: `${repo.owner}/${repo.name}`,
    owner: { login: repo.owner, id: VIEWER_ID, type: 'User', name: VIEWER_NAME, email: VIEWER_EMAIL },
    private: repo.isPrivate,
    html_url: `https://github.com/${repo.owner}/${repo.name}`,
    description: repo.description,
    fork: false,
    url: `/api/v3/repos/${repo.owner}/${repo.name}`,
    created_at: NOW_ISO,
    updated_at: NOW_ISO,
    pushed_at: NOW_ISO,
    git_url: `git://github.com/${repo.owner}/${repo.name}.git`,
    ssh_url: `git@github.com:${repo.owner}/${repo.name}.git`,
    clone_url: `https://github.com/${repo.owner}/${repo.name}.git`,
    homepage: null,
    size: 0,
    stargazers_count: 0,
    watchers_count: 0,
    language: null,
    has_issues: true,
    has_projects: false,
    has_downloads: true,
    has_wiki: false,
    has_pages: false,
    forks_count: 0,
    archived: false,
    disabled: false,
    open_issues_count: repo.issues.filter((i) => i.state === 'open').length,
    license: null,
    allow_forking: true,
    is_template: false,
    topics: [],
    visibility: repo.isPrivate ? 'private' : 'public',
    default_branch: repo.defaultBranch,
  };
}
function issueJson(issue: Issue, repo: Repo): Record<string, unknown> {
  return {
    id: issue.id,
    node_id: gid('Issue', `${repo.id}:${issue.number}`),
    url: `/api/v3/repos/${repo.owner}/${repo.name}/issues/${issue.number}`,
    repository_url: `/api/v3/repos/${repo.owner}/${repo.name}`,
    labels_url: `/api/v3/repos/${repo.owner}/${repo.name}/issues/${issue.number}/labels{/name}`,
    comments_url: `/api/v3/repos/${repo.owner}/${repo.name}/issues/${issue.number}/comments`,
    events_url: `/api/v3/repos/${repo.owner}/${repo.name}/issues/${issue.number}/events`,
    html_url: `https://github.com/${repo.owner}/${repo.name}/issues/${issue.number}`,
    number: issue.number,
    title: issue.title,
    body: issue.body,
    user: { login: repo.owner, id: VIEWER_ID, type: 'User' },
    labels: issue.labels.map((l) => ({ id: 0, name: l.name, color: l.color, default: false, description: '' })),
    state: issue.state,
    locked: false,
    assignee: null,
    assignees: [],
    milestone: null,
    comments: issue.comments.length,
    created_at: NOW_ISO,
    updated_at: NOW_ISO,
    closed_at: issue.state === 'closed' ? NOW_ISO : null,
    author_association: 'OWNER',
    active_lock_reason: null,
  };
}
function cacheIssue(issue: Issue, repo: Repo): string {
  if (!issue.cachedJson) issue.cachedJson = `${JSON.stringify(issueJson(issue, repo))}\n`;
  return issue.cachedJson;
}
function branchTip(repo: Repo, branch: string): string | undefined {
  return repo.refs.get(`refs/heads/${branch}`);
}
function refTip(repo: Repo, ref: string): string | undefined {
  if (ref.startsWith('refs/')) return repo.refs.get(ref);
  return branchTip(repo, ref);
}
function prHeadSha(repo: Repo, pr: Pull): string {
  return branchTip(repo, pr.headRef) ?? '';
}
function prBaseSha(repo: Repo, pr: Pull): string {
  return branchTip(repo, pr.baseRef) ?? '';
}
function prMergeable(repo: Repo, pr: Pull): boolean {
  const head = prHeadSha(repo, pr);
  const base = prBaseSha(repo, pr);
  if (!head || !base) return false;
  const mb = mergeBase(repo, head, base);
  if (mb === null) return head === base;
  const mbTree = flatTree(repo, mb);
  const headTree = flatTree(repo, head);
  const baseTree = flatTree(repo, base);
  const changed = (a: Map<string, { oid: string }>, b: Map<string, { oid: string }>): Set<string> => {
    const out = new Set<string>();
    for (const [p, e] of a) if (b.get(p)?.oid !== e.oid) out.add(p);
    for (const p of b.keys()) if (!a.has(p)) out.add(p);
    return out;
  };
  const headChanged = changed(mbTree, headTree);
  const baseChanged = changed(mbTree, baseTree);
  for (const p of headChanged) {
    if (baseChanged.has(p) && headTree.get(p)?.oid !== baseTree.get(p)?.oid) return false;
  }
  return true;
}
function prJson(pr: Pull, repo: Repo): Record<string, unknown> {
  const headSha = prHeadSha(repo, pr);
  const baseSha = prBaseSha(repo, pr);
  return {
    id: pr.id,
    node_id: gid('PullRequest', `${repo.id}:${pr.number}`),
    number: pr.number,
    title: pr.title,
    body: pr.body,
    state: pr.merged ? 'closed' : pr.state,
    locked: false,
    html_url: `https://github.com/${repo.owner}/${repo.name}/pull/${pr.number}`,
    diff_url: `https://github.com/${repo.owner}/${repo.name}/pull/${pr.number}.diff`,
    patch_url: `https://github.com/${repo.owner}/${repo.name}/pull/${pr.number}.patch`,
    url: `/api/v3/repos/${repo.owner}/${repo.name}/pulls/${pr.number}`,
    created_at: NOW_ISO,
    updated_at: NOW_ISO,
    closed_at: pr.state === 'closed' ? NOW_ISO : null,
    merged_at: pr.mergedAt,
    merge_commit_sha: pr.mergeCommitSha,
    merged: pr.merged,
    mergeable: prMergeable(repo, pr),
    mergeable_state: prMergeable(repo, pr) ? 'clean' : 'dirty',
    merged_by: null,
    head: { label: `${repo.owner}:${pr.headRef}`, ref: pr.headRef, sha: headSha, user: { login: repo.owner, id: VIEWER_ID, type: 'User' }, repo: repoJson(repo) },
    base: { label: `${repo.owner}:${pr.baseRef}`, ref: pr.baseRef, sha: baseSha, user: { login: repo.owner, id: VIEWER_ID, type: 'User' }, repo: repoJson(repo) },
    user: { login: repo.owner, id: VIEWER_ID, type: 'User' },
    labels: [],
    assignee: null,
    assignees: [],
    milestone: null,
    draft: false,
    commits: 1,
    additions: 0,
    deletions: 0,
    changed_files: 0,
  };
}
function diffFiles(repo: Repo, baseOid: string, headOid: string): { filename: string; status: string; additions: number; deletions: number; changes: number }[] {
  const baseTree = baseOid ? flatTree(repo, baseOid) : new Map();
  const headTree = headOid ? flatTree(repo, headOid) : new Map();
  const paths = new Set([...baseTree.keys(), ...headTree.keys()]);
  const out: { filename: string; status: string; additions: number; deletions: number; changes: number }[] = [];
  const lineCount = (oid: string | undefined): number => {
    if (!oid) return 0;
    const obj = repo.objects.get(oid);
    if (!obj) return 0;
    const text = obj.data.toString('utf8');
    if (text === '') return 0;
    return text.split('\n').length - (text.endsWith('\n') ? 1 : 0);
  };
  for (const p of [...paths].sort()) {
    const b = baseTree.get(p);
    const h = headTree.get(p);
    if (!b && h) {
      const add = lineCount(h.oid);
      out.push({ filename: p, status: 'added', additions: add, deletions: 0, changes: add });
    } else if (b && !h) {
      const del = lineCount(b.oid);
      out.push({ filename: p, status: 'removed', additions: 0, deletions: del, changes: del });
    } else if (b && h && b.oid !== h.oid) {
      const add = lineCount(h.oid);
      const del = lineCount(b.oid);
      out.push({ filename: p, status: 'modified', additions: add, deletions: del, changes: add + del });
    }
  }
  return out;
}
function commitList(repo: Repo, tip: string): { sha: string; commit: Record<string, unknown> }[] {
  const out: { sha: string; commit: Record<string, unknown> }[] = [];
  const seen = new Set<string>();
  const stack = [tip];
  while (stack.length) {
    const oid = stack.pop()!;
    if (seen.has(oid) || !isOid(oid)) continue;
    const obj = repo.objects.get(oid);
    if (!obj || obj.type !== 'commit') continue;
    seen.add(oid);
    const c = parseCommit(obj.data);
    const text = obj.data.toString('utf8');
    const authorLine = text.split('\n').find((l) => l.startsWith('author '))?.slice(7) ?? '';
    const authorName = authorLine.split(' <')[0] ?? VIEWER_NAME;
    const authorEmail = authorLine.includes('<') ? authorLine.slice(authorLine.indexOf('<') + 1, authorLine.indexOf('>')) : VIEWER_EMAIL;
    out.push({
      sha: oid,
      commit: {
        message: c.message,
        author: { name: authorName, email: authorEmail, date: NOW_ISO },
        committer: { name: authorName, email: authorEmail, date: NOW_ISO },
      },
      parents: c.parents.map((p) => ({ sha: p })),
    });
    for (let i = c.parents.length - 1; i >= 0; i -= 1) stack.push(c.parents[i]);
  }
  return out;
}
function resolveRefCommit(repo: Repo, ref: string | null): string | undefined {
  if (!ref) return branchTip(repo, repo.defaultBranch);
  if (isOid(ref)) return repo.objects.has(ref) ? ref : undefined;
  return refTip(repo, ref);
}
function doMerge(repo: Repo, pr: Pull): { ok: boolean; sha?: string; message?: string } {
  const head = prHeadSha(repo, pr);
  const base = prBaseSha(repo, pr);
  if (!head || !base) return { ok: false, message: 'Head or base branch is missing' };
  if (!prMergeable(repo, pr)) return { ok: false, message: 'Merge conflict' };
  const mb = mergeBase(repo, head, base);
  const mbTree = mb ? flatTree(repo, mb) : new Map<string, { oid: string; mode: string }>();
  const headTree = flatTree(repo, head);
  const baseTree = flatTree(repo, base);
  const merged = new Map(baseTree);
  for (const [p, e] of headTree) {
    if (mbTree.get(p)?.oid !== e.oid) merged.set(p, e);
  }
  for (const p of mbTree.keys()) {
    if (!headTree.has(p) && mbTree.get(p) !== undefined) merged.delete(p);
  }
  const treeOid = buildTreeFromFiles(repo, merged);
  const sha = makeCommit(repo, treeOid, [base], `Merge pull request #${pr.number} from ${pr.headRef}`);
  repo.refs.set(`refs/heads/${pr.baseRef}`, sha);
  pr.merged = true;
  pr.state = 'closed';
  pr.mergedAt = NOW_ISO;
  pr.mergeCommitSha = sha;
  invalidateGitCache(repo);
  return { ok: true, sha };
}

// ---------------------------------------------------------------- REST routing

type Body = Record<string, unknown>;
function asBody(v: unknown): Body {
  return v !== null && typeof v === 'object' && !Array.isArray(v) ? (v as Body) : {};
}
function str(v: unknown, d = ''): string {
  return typeof v === 'string' ? v : d;
}
function num(v: unknown): number | null {
  if (typeof v === 'number' && Number.isFinite(v)) return v;
  // Query strings arrive as strings; accept plain integer strings too.
  if (typeof v === 'string' && /^-?\d+$/.test(v)) return Number.parseInt(v, 10);
  return null;
}

async function handleRest(req: IncomingMessage, res: ServerResponse, parts: string[], query: URLSearchParams): Promise<boolean> {
  const method = req.method ?? 'GET';
  // parts[0]='', parts[1]='api', parts[2]='v3', rest follows.
  const p = parts.slice(3);
  // API root (public, like api.github.com).
  if (p.length === 0 || (p.length === 1 && p[0] === '')) {
    if (method !== 'GET') return false;
    sendJson(res, 200, { current_user_url: '/api/v3/user', rate_limit_url: '/api/v3/rate_limit', user_url: '/api/v3/users/{user}' }, { 'x-oauth-scopes': 'repo, read:org' });
    return true;
  }
  if (!authed(req)) {
    errJson(res, 401, 'Requires authentication');
    return true;
  }
  const needsBody = method === 'POST' || method === 'PUT' || method === 'PATCH' || method === 'DELETE';
  let bodyVal: unknown = {};
  if (needsBody) {
    const raw = await readBody(req);
    const parsed = parseJsonBody(raw);
    if (!parsed.ok) {
      errJson(res, 400, 'Problems parsing JSON');
      return true;
    }
    bodyVal = parsed.value;
  }
  const body = asBody(bodyVal);

  // GET /meta
  if (p.length === 1 && p[0] === 'meta' && method === 'GET') {
    sendJson(res, 200, { verifiable_password_authentication: true, installed_version: '1.0.0', github_services_sha: '0000000000000000000000000000000000000000' });
    return true;
  }
  // GET /user
  if (p.length === 1 && p[0] === 'user' && method === 'GET') {
    sendJson(res, 200, { login: VIEWER_LOGIN, id: VIEWER_ID, node_id: gid('User', VIEWER_ID), name: VIEWER_NAME, email: VIEWER_EMAIL, type: 'User', site_admin: false });
    return true;
  }
  // /user/repos
  if (p.length === 2 && p[0] === 'user' && p[1] === 'repos') {
    if (method === 'POST') {
      const name = str(body.name);
      if (!name || !/^[A-Za-z0-9][A-Za-z0-9._-]{0,99}$/.test(name)) {
        errJson(res, 422, 'Invalid repository name');
        return true;
      }
      if (repos.has(repoKey(VIEWER_LOGIN, name))) {
        errJson(res, 422, 'Repository already exists');
        return true;
      }
      const repo = createRepoRecord(name, body.private === true, str(body.description));
      sendJson(res, 201, repoJson(repo));
      return true;
    }
    if (method === 'GET') {
      const perPage = Math.max(1, Math.min(100, num(query.get('per_page')) ?? 30));
      const page = Math.max(1, num(query.get('page')) ?? 1);
      const start = (page - 1) * perPage;
      const slice = repoList.slice(start, start + perPage);
      const extra: Record<string, string> = {};
      if (start + perPage < repoList.length) {
        const host = req.headers.host ?? 'localhost';
        const url = `http://${host}/api/v3/user/repos?per_page=${perPage}&page=${page + 1}`;
        extra.link = `<${url}>; rel="next"`;
      }
      sendJson(res, 200, slice.map((r) => repoJson(r)), extra);
      return true;
    }
    return false;
  }
  // /repos/{owner}/{repo}[...]
  if (p.length >= 3 && p[0] === 'repos') {
    const owner = p[1];
    const name = p[2];
    const repo = findRepo(owner, name);
    const rest = p.slice(3);
    if (rest.length === 0) {
      if (method === 'GET') {
        if (!repo) { errJson(res, 404, 'Not Found'); return true; }
        sendJson(res, 200, repoJson(repo));
        return true;
      }
      if (method === 'PATCH') {
        if (!repo) { errJson(res, 404, 'Not Found'); return true; }
        if (typeof body.description === 'string') repo.description = body.description;
        if (typeof body.private === 'boolean') repo.isPrivate = body.private;
        sendJson(res, 200, repoJson(repo));
        return true;
      }
      if (method === 'DELETE') {
        if (!repo) { errJson(res, 404, 'Not Found'); return true; }
        repos.delete(repoKey(VIEWER_LOGIN, name));
        const i = repoList.indexOf(repo);
        if (i >= 0) repoList.splice(i, 1);
        sendNoContent(res);
        return true;
      }
      return false;
    }
    if (!repo) {
      errJson(res, 404, 'Not Found');
      return true;
    }
    // /branches
    if (rest[0] === 'branches') {
      if (rest.length === 1 && method === 'GET') {
        const list = [...repo.refs.keys()]
          .filter((r) => r.startsWith('refs/heads/'))
          .sort()
          .map((r) => ({ name: r.slice('refs/heads/'.length), commit: { sha: repo.refs.get(r) }, protected: false }));
        sendJson(res, 200, list);
        return true;
      }
      if (rest.length === 2 && method === 'GET') {
        const tip = branchTip(repo, rest[1]);
        if (!tip) { errJson(res, 404, 'Not Found'); return true; }
        sendJson(res, 200, { name: rest[1], commit: { sha: tip }, protected: false });
        return true;
      }
      return false;
    }
    // /commits
    if (rest[0] === 'commits' && rest.length === 1 && method === 'GET') {
      const tip = resolveRefCommit(repo, query.get('sha'));
      if (!tip) { errJson(res, 404, 'Not Found'); return true; }
      sendJson(res, 200, commitList(repo, tip));
      return true;
    }
    // /git/refs
    if (rest[0] === 'git' && rest[1] === 'refs') {
      if (method === 'POST' && rest.length === 2) {
        const ref = str(body.ref);
        const sha = str(body.sha);
        if (!ref.startsWith('refs/') || !isOid(sha) || !repo.objects.has(sha)) {
          errJson(res, 422, 'Invalid ref or sha');
          return true;
        }
        if (repo.refs.has(ref)) {
          errJson(res, 422, 'Reference already exists');
          return true;
        }
        repo.refs.set(ref, sha);
        invalidateGitCache(repo);
        sendJson(res, 201, { ref, object: { sha, type: 'commit' }, url: `/api/v3/repos/${owner}/${name}/git/refs/${ref}` });
        return true;
      }
      if (method === 'GET') {
        const refPath = rest.slice(2).join('/');
        if (refPath === '') {
          const list = [...repo.refs.entries()].map(([ref, sha]) => ({ ref, object: { sha, type: 'commit' } }));
          sendJson(res, 200, list);
          return true;
        }
        const full = `refs/${refPath}`;
        const tip = repo.refs.get(full);
        if (!tip) { errJson(res, 404, 'Not Found'); return true; }
        sendJson(res, 200, { ref: full, object: { sha: tip, type: 'commit' } });
        return true;
      }
      return false;
    }
    // /contents/{path...}
    if (rest[0] === 'contents') {
      const filePath = rest.slice(1).join('/');
      if (method === 'PUT') {
        const branch = typeof body.branch === 'string' && body.branch !== '' ? body.branch : repo.defaultBranch;
        let tip = branchTip(repo, branch);
        if (tip === undefined) {
          const baseTip = branchTip(repo, repo.defaultBranch);
          if (baseTip) {
            repo.refs.set(`refs/heads/${branch}`, baseTip);
            tip = baseTip;
          }
        }
        const contentB64 = str(body.content);
        if (contentB64 === '') { errJson(res, 422, 'content is required'); return true; }
        const bytes = b64decodeText(contentB64);
        const blobOid = storeObject(repo, 'blob', bytes);
        // Copy: flatTree returns the commit's cached map, which must never be mutated.
        const files = new Map<string, { oid: string; mode: string }>(tip ? flatTree(repo, tip) : []);
        const existed = files.has(filePath);
        if (existed && typeof body.sha === 'string' && body.sha !== '' && body.sha.toLowerCase() !== files.get(filePath)!.oid.toLowerCase()) {
          errJson(res, 409, 'sha does not match');
          return true;
        }
        files.set(filePath, { oid: blobOid, mode: '100644' });
        const treeOid = buildTreeFromFiles(repo, files);
        const parents = tip ? [tip] : [];
        const commitSha = makeCommit(repo, treeOid, parents, str(body.message, 'Update file'));
        repo.refs.set(`refs/heads/${branch}`, commitSha);
        invalidateGitCache(repo);
        const baseName = filePath.split('/').pop() ?? filePath;
        sendJson(res, existed ? 200 : 201, {
          content: { name: baseName, path: filePath, sha: blobOid, size: bytes.length, type: 'file', encoding: 'base64' },
          commit: { sha: commitSha, message: str(body.message, 'Update file') },
        });
        return true;
      }
      if (method === 'GET') {
        const tip = resolveRefCommit(repo, query.get('ref'));
        if (!tip) { errJson(res, 404, 'Not Found'); return true; }
        const files = flatTree(repo, tip);
        if (files.has(filePath)) {
          const entry = files.get(filePath)!;
          const obj = repo.objects.get(entry.oid)!;
          const baseName = filePath.split('/').pop() ?? filePath;
          sendJson(res, 200, {
            type: 'file', encoding: 'base64', size: obj.data.length, name: baseName, path: filePath,
            content: b64encode(obj.data), sha: entry.oid,
            url: `/api/v3/repos/${owner}/${name}/contents/${filePath}`,
          });
          return true;
        }
        // directory?
        const prefix = filePath === '' ? '' : `${filePath}/`;
        const children = new Map<string, { type: 'file' | 'dir'; name: string; path: string; sha: string; size?: number }>();
        for (const [path, entry] of files) {
          if (!path.startsWith(prefix)) continue;
          const restPath = path.slice(prefix.length);
          const first = restPath.split('/')[0];
          if (restPath.includes('/')) {
            if (!children.has(first)) {
              const sub = new Map<string, { oid: string; mode: string }>();
              for (const [p2, e2] of files) {
                if (p2.startsWith(`${prefix}${first}/`)) sub.set(p2.slice(`${prefix}${first}/`.length), e2);
              }
              children.set(first, { type: 'dir', name: first, path: `${prefix}${first}`, sha: buildTreeFromFiles(repo, sub) });
            }
          } else {
            const obj = repo.objects.get(entry.oid);
            children.set(first, { type: 'file', name: first, path, sha: entry.oid, size: obj ? obj.data.length : 0 });
          }
        }
        if (children.size > 0) {
          sendJson(res, 200, [...children.values()].sort((a, b) => (a.name < b.name ? -1 : 1)));
          return true;
        }
        errJson(res, 404, 'Not Found');
        return true;
      }
      if (method === 'DELETE') {
        const branch = typeof body.branch === 'string' && body.branch !== '' ? body.branch : repo.defaultBranch;
        const tip = branchTip(repo, branch);
        if (!tip) { errJson(res, 404, 'Not Found'); return true; }
        const files = new Map<string, { oid: string; mode: string }>(flatTree(repo, tip));
        if (!files.has(filePath)) { errJson(res, 404, 'Not Found'); return true; }
        files.delete(filePath);
        const treeOid = files.size === 0 ? emptyTreeOid(repo) : buildTreeFromFiles(repo, files);
        const commitSha = makeCommit(repo, treeOid, [tip], str(body.message, 'Delete file'));
        repo.refs.set(`refs/heads/${branch}`, commitSha);
        invalidateGitCache(repo);
        sendJson(res, 200, { commit: { sha: commitSha } });
        return true;
      }
      return false;
    }
    // /labels
    if (rest[0] === 'labels') {
      if (method === 'GET') {
        sendJson(res, 200, [...repo.labels.values()].map((l) => ({ id: 0, name: l.name, color: l.color, default: false, description: '' })));
        return true;
      }
      if (method === 'POST') {
        const name = str(body.name);
        if (!name) { errJson(res, 422, 'name is required'); return true; }
        let label = repo.labels.get(name);
        if (!label) {
          label = { name, color: str(body.color, 'ededed') };
          repo.labels.set(name, label);
        }
        sendJson(res, 201, { id: 0, name: label.name, color: label.color, default: false, description: '' });
        return true;
      }
      return false;
    }
    // /issues
    if (rest[0] === 'issues') {
      if (rest.length === 1) {
        if (method === 'POST') {
          const title = str(body.title);
          if (!title) { errJson(res, 422, 'title is required'); return true; }
          const labelNames: string[] = [];
          if (Array.isArray(body.labels)) {
            for (const l of body.labels as unknown[]) {
              const n = typeof l === 'string' ? l : str((l as Body).name);
              if (n && !repo.labels.has(n)) { errJson(res, 422, `Label '${n}' does not exist`); return true; }
              if (n) labelNames.push(n);
            }
          }
          const issue: Issue = {
            id: globalIdCounter, number: repo.nextNumber, title,
            body: str(body.body, ''), state: 'open',
            labels: labelNames.map((n) => repo.labels.get(n)!),
            comments: [], seq: ++issueSeqCounter, cachedJson: null,
          };
          globalIdCounter += 1;
          repo.nextNumber += 1;
          repo.issues.push(issue);
          sendJson(res, 201, issueJson(issue, repo));
          return true;
        }
        if (method === 'GET') {
          const state = (query.get('state') ?? 'open').toLowerCase();
          let list = repo.issues.slice();
          if (state === 'open' || state === 'closed') list = list.filter((i) => i.state === state);
          const sort = query.get('sort') ?? 'created';
          const dir = (query.get('direction') ?? 'desc').toLowerCase();
          if (sort === 'created') list.sort((a, b) => (dir === 'asc' ? a.seq - b.seq : b.seq - a.seq));
          const perPage = num(query.get('per_page'));
          const page = num(query.get('page')) ?? 1;
          if (perPage !== null) list = list.slice((page - 1) * perPage, page * perPage);
          sendJson(res, 200, list.map((i) => issueJson(i, repo)));
          return true;
        }
        return false;
      }
      const numId = Number.parseInt(rest[1], 10);
      const issue = repo.issues.find((i) => i.number === numId);
      if (rest.length === 2) {
        if (method === 'GET') {
          if (!issue) { errJson(res, 404, 'Not Found'); return true; }
          sendJsonRaw(res, 200, cacheIssue(issue, repo));
          return true;
        }
        if (method === 'PATCH') {
          if (!issue) { errJson(res, 404, 'Not Found'); return true; }
          if (typeof body.title === 'string') issue.title = body.title;
          if (typeof body.body === 'string') issue.body = body.body;
          if (body.state === 'open' || body.state === 'closed') issue.state = body.state;
          issue.cachedJson = null;
          sendJson(res, 200, issueJson(issue, repo));
          return true;
        }
        return false;
      }
      if (rest.length === 3 && rest[2] === 'comments') {
        if (!issue) { errJson(res, 404, 'Not Found'); return true; }
        if (method === 'POST') {
          const comment = { id: repo.commentSeq, body: str(body.body, '') };
          repo.commentSeq += 1;
          issue.comments.push(comment);
          issue.cachedJson = null;
          sendJson(res, 201, { id: comment.id, body: comment.body, user: { login: repo.owner, id: VIEWER_ID, type: 'User' }, created_at: NOW_ISO, updated_at: NOW_ISO });
          return true;
        }
        if (method === 'GET') {
          sendJson(res, 200, issue.comments.map((c) => ({ id: c.id, body: c.body, user: { login: repo.owner, id: VIEWER_ID, type: 'User' }, created_at: NOW_ISO, updated_at: NOW_ISO })));
          return true;
        }
        return false;
      }
      return false;
    }
    // /pulls
    if (rest[0] === 'pulls') {
      if (rest.length === 1) {
        if (method === 'POST') {
          const headRaw = str(body.head);
          const baseRaw = str(body.base);
          const head = headRaw.includes(':') ? headRaw.split(':').pop()! : headRaw;
          const base = baseRaw.includes(':') ? baseRaw.split(':').pop()! : baseRaw;
          if (!head || !base || !branchTip(repo, head) || !branchTip(repo, base)) {
            errJson(res, 422, 'Head or base branch does not exist');
            return true;
          }
          const existing = repo.pulls.find((pr) => pr.headRef === head && pr.baseRef === base && pr.state === 'open');
          if (existing) { errJson(res, 422, 'A pull request already exists for this branch'); return true; }
          const pr: Pull = {
            id: globalIdCounter, number: repo.nextNumber, title: str(body.title, ''),
            body: str(body.body, ''), state: 'open', headRef: head, baseRef: base,
            merged: false, mergedAt: null, mergeCommitSha: null, seq: ++issueSeqCounter,
          };
          globalIdCounter += 1;
          repo.nextNumber += 1;
          repo.pulls.push(pr);
          sendJson(res, 201, prJson(pr, repo));
          return true;
        }
        if (method === 'GET') {
          const state = (query.get('state') ?? 'open').toLowerCase();
          let list = repo.pulls.slice();
          if (state === 'open' || state === 'closed') list = list.filter((pr) => (pr.merged ? 'closed' : pr.state) === state);
          const perPage = num(query.get('per_page'));
          const page = num(query.get('page')) ?? 1;
          if (perPage !== null) list = list.slice((page - 1) * perPage, page * perPage);
          sendJson(res, 200, list.map((pr) => prJson(pr, repo)));
          return true;
        }
        return false;
      }
      const prNum = Number.parseInt(rest[1], 10);
      const pr = repo.pulls.find((x) => x.number === prNum);
      if (rest.length === 2) {
        if (method === 'GET') {
          if (!pr) { errJson(res, 404, 'Not Found'); return true; }
          sendJson(res, 200, prJson(pr, repo));
          return true;
        }
        return false;
      }
      if (rest.length === 3 && rest[2] === 'files' && method === 'GET') {
        if (!pr) { errJson(res, 404, 'Not Found'); return true; }
        sendJson(res, 200, diffFiles(repo, prBaseSha(repo, pr), prHeadSha(repo, pr)));
        return true;
      }
      if (rest.length === 3 && rest[2] === 'merge' && method === 'PUT') {
        if (!pr) { errJson(res, 404, 'Not Found'); return true; }
        if (pr.merged) { errJson(res, 405, 'Pull request already merged'); return true; }
        const result = doMerge(repo, pr);
        if (!result.ok) { errJson(res, 405, result.message ?? 'Merge conflict'); return true; }
        sendJson(res, 200, { sha: result.sha, merged: true, message: 'Pull request successfully merged' });
        return true;
      }
      return false;
    }
    return false;
  }
  return false;
}

// ---------------------------------------------------------------- git HTTP handlers

function fetchCacheKey(proto: string, wants: string[], haves: string[], boundaries: string[], depth: number | null): string {
  return `${proto}|${wants.join(',')}|${haves.join(',')}|${boundaries.join(',')}|${depth === null ? '' : depth}`;
}
function buildFetchResponseV2(repo: Repo, wants: string[], haves: string[], boundaries: string[], depth: number | null): Buffer {
  const key = fetchCacheKey('v2', wants, haves, boundaries, depth);
  const cached = repo.shallowPack.get(key);
  if (cached) return cached;
  const plan = planFetch(repo, wants, haves, depth, boundaries);
  const pack = writePack(plan.objects);
  const parts: Buffer[] = [pktLine('acknowledgments\n'), pktLine('NAK\n'), PKT_FLUSH];
  if (plan.shallow.length || plan.unshallow.length) {
    parts.push(pktLine('shallow-info\n'));
    for (const s of plan.shallow) parts.push(pktLine(`shallow ${s}\n`));
    for (const s of plan.unshallow) parts.push(pktLine(`unshallow ${s}\n`));
    parts.push(PKT_FLUSH);
  }
  parts.push(pktLine('packfile\n'), sidebandPack(pack), PKT_FLUSH);
  const out = Buffer.concat(parts);
  repo.shallowPack.set(key, out);
  return out;
}
function buildFetchResponseV0(repo: Repo, wants: string[], haves: string[], boundaries: string[], depth: number | null): Buffer {
  const key = fetchCacheKey('v0', wants, haves, boundaries, depth);
  const cached = repo.shallowPack.get(key);
  if (cached) return cached;
  const plan = planFetch(repo, wants, haves, depth, boundaries);
  const pack = writePack(plan.objects);
  const parts: Buffer[] = [pktLine('NAK\n')];
  for (const s of plan.shallow) parts.push(pktLine(`shallow ${s}\n`));
  for (const s of plan.unshallow) parts.push(pktLine(`unshallow ${s}\n`));
  parts.push(sidebandPack(pack), PKT_FLUSH);
  const out = Buffer.concat(parts);
  repo.shallowPack.set(key, out);
  return out;
}
function handleUploadPackV2(repo: Repo, body: Buffer): Buffer {
  const packets = parseAllPktLines(body);
  const first = packets.find((p) => p.kind === 'data');
  if (!first) throw new Error('empty upload-pack request');
  const command = first.payload.toString('utf8').trim();
  if (command === 'command=ls-refs') {
    const args: string[] = [];
    let afterDelim = false;
    for (const p of packets) {
      if (p.kind === 'delim') { afterDelim = true; continue; }
      if (p.kind !== 'data') continue;
      const line = p.payload.toString('utf8').trim();
      if (line.startsWith('command=')) continue;
      if (afterDelim) args.push(line);
    }
    const prefixes: string[] = [];
    let peel = false;
    let symrefs = false;
    for (const a of args) {
      if (a === 'peel') peel = true;
      else if (a === 'symrefs') symrefs = true;
      else if (a.startsWith('ref-prefix ')) prefixes.push(a.slice('ref-prefix '.length));
    }
    return lsRefsV2(repo, prefixes, peel, symrefs);
  }
  if (command === 'command=fetch') {
    const wants: string[] = [];
    const haves: string[] = [];
    const boundaries: string[] = [];
    let depth: number | null = null;
    let afterDelim = false;
    for (const p of packets) {
      if (p.kind === 'delim') { afterDelim = true; continue; }
      if (p.kind !== 'data' || !afterDelim) continue;
      const line = p.payload.toString('utf8').trim();
      if (line.startsWith('want ')) wants.push(line.slice(5).trim());
      else if (line.startsWith('have ')) haves.push(line.slice(5).trim());
      else if (line.startsWith('shallow ')) boundaries.push(line.slice(8).trim());
      else if (line.startsWith('deepen ')) {
        const n = Number.parseInt(line.slice(7).trim(), 10);
        if (Number.isFinite(n) && n > 0) depth = n;
      }
    }
    return buildFetchResponseV2(repo, wants, haves, boundaries, depth);
  }
  throw new Error(`unknown v2 command ${command}`);
}
function handleUploadPackV0(repo: Repo, body: Buffer): Buffer {
  const packets = parseAllPktLines(body);
  const wants: string[] = [];
  const haves: string[] = [];
  const boundaries: string[] = [];
  let depth: number | null = null;
  let section = 0;
  for (const p of packets) {
    if (p.kind === 'flush') { section += 1; continue; }
    if (p.kind !== 'data') continue;
    const line = p.payload.toString('utf8').trim();
    if (section === 0) {
      if (line.startsWith('want ')) wants.push(line.slice(5).split(' ')[0].trim());
      else if (line.startsWith('shallow ')) boundaries.push(line.slice(8).trim());
      else if (line.startsWith('deepen ')) {
        const n = Number.parseInt(line.slice(7).trim(), 10);
        if (Number.isFinite(n) && n > 0) depth = n;
      }
    } else {
      if (line.startsWith('have ')) haves.push(line.slice(5).trim());
    }
  }
  return buildFetchResponseV0(repo, wants, haves, boundaries, depth);
}
function handleReceivePack(repo: Repo, body: Buffer): Buffer {
  const { packets, offset } = parsePktLines(body);
  const commands: { oldOid: string; newOid: string; ref: string }[] = [];
  for (const p of packets) {
    if (p.kind === 'flush') break;
    if (p.kind !== 'data') continue;
    let line = p.payload.toString('utf8');
    const nul = line.indexOf('\0');
    if (nul >= 0) line = line.slice(0, nul);
    line = line.trim();
    const m = /^([0-9a-f]{40}) ([0-9a-f]{40}) (\S+)$/.exec(line);
    if (!m) throw new Error(`bad receive-pack command ${JSON.stringify(line)}`);
    commands.push({ oldOid: m[1], newOid: m[2], ref: m[3] });
  }
  if (commands.length === 0) throw new Error('no commands in receive-pack');
  // Unpack the pack (everything after the command flush).
  let unpackOk = true;
  if (offset < body.length) {
    try {
      const packBuf = body.subarray(offset);
      const parsed = readPack(packBuf, (oid) => repo.objects.get(oid));
      for (const obj of parsed.values()) putObject(repo, obj);
    } catch {
      unpackOk = false;
    }
  }
  const reportLines: string[] = [unpackOk ? 'unpack ok\n' : 'unpack error\n'];
  for (const cmd of commands) {
    let ok = false;
    let reason = '';
    if (!unpackOk) {
      reason = 'unpack error';
    } else if (!cmd.ref.startsWith('refs/')) {
      reason = 'invalid ref';
    } else {
      const current = repo.refs.get(cmd.ref);
      if (cmd.newOid === ZERO_OID) {
        // delete
        if (current === undefined) reason = 'remote ref does not exist';
        else if (cmd.oldOid !== ZERO_OID && cmd.oldOid !== current) reason = 'non-fast-forward';
        else { repo.refs.delete(cmd.ref); ok = true; }
      } else {
        const newObj = repo.objects.get(cmd.newOid);
        if (!newObj) {
          reason = 'object not found';
        } else if (current === undefined) {
          if (cmd.oldOid !== ZERO_OID) reason = 'non-fast-forward';
          else { repo.refs.set(cmd.ref, cmd.newOid); ok = true; }
        } else if (cmd.oldOid === ZERO_OID) {
          reason = 'already exists';
        } else if (cmd.oldOid !== current) {
          reason = 'non-fast-forward';
        } else if (cmd.ref.startsWith('refs/tags/')) {
          repo.refs.set(cmd.ref, cmd.newOid);
          ok = true;
        } else if (cmd.newOid === current) {
          ok = true;
        } else if (isAncestor(repo, current, cmd.newOid)) {
          repo.refs.set(cmd.ref, cmd.newOid);
          ok = true;
        } else {
          reason = 'non-fast-forward';
        }
      }
    }
    reportLines.push(ok ? `ok ${cmd.ref}\n` : `ng ${cmd.ref} ${reason}\n`);
  }
  if (reportLines.some((l) => l.startsWith('ok '))) invalidateGitCache(repo);
  const inner = Buffer.concat(reportLines.map((l) => pktLine(l)));
  const out: Buffer[] = [];
  for (let off = 0; off < inner.length; off += 65515) {
    out.push(pktLine(Buffer.concat([Buffer.from([1]), inner.subarray(off, Math.min(inner.length, off + 65515))])));
  }
  out.push(PKT_FLUSH);
  return Buffer.concat(out);
}
async function handleGit(req: IncomingMessage, res: ServerResponse, parts: string[], query: URLSearchParams): Promise<boolean> {
  // parts: ['', owner, '<repo>.git', ...]
  if (parts.length < 3 || !parts[2].endsWith('.git')) return false;
  const owner = parts[1];
  const name = parts[2].slice(0, -4);
  const repo = findRepo(owner, name);
  const sub = parts.slice(3);
  const method = req.method ?? 'GET';
  try {
    if (method === 'GET' && sub.length === 2 && sub[0] === 'info' && sub[1] === 'refs') {
      const service = query.get('service') ?? '';
      if (!repo) { errJson(res, 404, 'Not Found'); return true; }
      const proto = req.headers['git-protocol'];
      if (service === 'git-upload-pack') {
        if (proto === 'version=2') {
          const ad = repo.advV2 ?? (repo.advV2 = refAdvertisementV2(repo));
          res.writeHead(200, { 'content-type': 'application/x-git-upload-pack-advertisement', 'content-length': ad.length });
          res.end(ad);
          return true;
        }
        const ad = repo.advV0 ?? (repo.advV0 = refAdvertisementV0(repo, 'git-upload-pack'));
        res.writeHead(200, { 'content-type': 'application/x-git-upload-pack-advertisement', 'content-length': ad.length });
        res.end(ad);
        return true;
      }
      if (service === 'git-receive-pack') {
        const ad = refAdvertisementV0(repo, 'git-receive-pack');
        res.writeHead(200, { 'content-type': 'application/x-git-receive-pack-advertisement', 'content-length': ad.length });
        res.end(ad);
        return true;
      }
      errJson(res, 400, 'Unknown service');
      return true;
    }
    if (method === 'POST' && sub.length === 1 && sub[0] === 'git-upload-pack') {
      if (!repo) { errJson(res, 404, 'Not Found'); return true; }
      const body = await readBody(req);
      const out = req.headers['git-protocol'] === 'version=2' ? handleUploadPackV2(repo, body) : handleUploadPackV0(repo, body);
      res.writeHead(200, { 'content-type': 'application/x-git-upload-pack-result', 'content-length': out.length });
      res.end(out);
      return true;
    }
    if (method === 'POST' && sub.length === 1 && sub[0] === 'git-receive-pack') {
      if (!repo) { errJson(res, 404, 'Not Found'); return true; }
      const body = await readBody(req);
      const out = handleReceivePack(repo, body);
      res.writeHead(200, { 'content-type': 'application/x-git-receive-pack-result', 'content-length': out.length });
      res.end(out);
      return true;
    }
  } catch {
    errJson(res, 400, 'Bad request');
    return true;
  }
  return false;
}

// ---------------------------------------------------------------- GraphQL

type GqlTok = { kind: 'name' | 'string' | 'int' | 'float' | 'punct' | 'spread'; value: string };
function gqlTokenize(src: string): GqlTok[] {
  const toks: GqlTok[] = [];
  let i = 0;
  while (i < src.length) {
    const c = src[i];
    if (c === ' ' || c === '\t' || c === '\n' || c === '\r' || c === ',') { i += 1; continue; }
    if (c === '#') { while (i < src.length && src[i] !== '\n') i += 1; continue; }
    if (c === '.' && src.startsWith('...', i)) { toks.push({ kind: 'spread', value: '...' }); i += 3; continue; }
    if ('{}()[]:!=$'.includes(c)) { toks.push({ kind: 'punct', value: c }); i += 1; continue; }
    if (c === '"') {
      let j = i + 1;
      let out = '';
      while (j < src.length && src[j] !== '"') {
        if (src[j] === '\\' && j + 1 < src.length) {
          const e = src[j + 1];
          out += e === 'n' ? '\n' : e === 't' ? '\t' : e === 'r' ? '\r' : e;
          j += 2;
        } else { out += src[j]; j += 1; }
      }
      toks.push({ kind: 'string', value: out });
      i = j + 1;
      continue;
    }
    if (/[0-9-]/.test(c)) {
      let j = i;
      while (j < src.length && /[0-9.eE+-]/.test(src[j])) j += 1;
      const raw = src.slice(i, j);
      toks.push({ kind: /[.eE]/.test(raw) ? 'float' : 'int', value: raw });
      i = j;
      continue;
    }
    if (/[A-Za-z_]/.test(c)) {
      let j = i;
      while (j < src.length && /[A-Za-z0-9_]/.test(src[j])) j += 1;
      toks.push({ kind: 'name', value: src.slice(i, j) });
      i = j;
      continue;
    }
    throw new Error(`bad graphql char ${c}`);
  }
  return toks;
}
interface GqlField {
  kind: 'field';
  name: string;
  alias: string | null;
  args: Record<string, unknown>;
  selections: GqlSelection[];
}
interface GqlFragment {
  kind: 'fragment';
  name: string | null;
  typeCondition: string | null;
  selections: GqlSelection[];
}
type GqlSelection = GqlField | GqlFragment;
interface GqlOperation {
  type: 'query' | 'mutation';
  name: string | null;
  variables: Record<string, unknown>;
  varDefs: Record<string, unknown>;
  selections: GqlSelection[];
}
class GqlParser {
  toks: GqlTok[];
  pos = 0;
  fragments = new Map<string, GqlSelection[]>();
  constructor(src: string) {
    this.toks = gqlTokenize(src);
  }
  peek(): GqlTok | undefined {
    return this.toks[this.pos];
  }
  next(): GqlTok {
    return this.toks[this.pos++]!;
  }
  expectPunct(v: string): void {
    const t = this.next();
    if (t.kind !== 'punct' || t.value !== v) throw new Error(`expected ${v}`);
  }
  expectName(v?: string): string {
    const t = this.next();
    if (t.kind !== 'name' || (v !== undefined && t.value !== v)) throw new Error(`expected name ${v ?? ''}`);
    return t.value;
  }
  parseDocument(): GqlOperation[] {
    const ops: GqlOperation[] = [];
    while (this.pos < this.toks.length) {
      const t = this.peek()!;
      if (t.kind === 'name' && t.value === 'fragment') {
        this.next();
        const name = this.expectName();
        this.expectName('on');
        const typeCond = this.expectName();
        this.fragments.set(name, this.parseSelectionSet());
      } else {
        ops.push(this.parseOperation());
      }
    }
    return ops;
  }
  parseOperation(): GqlOperation {
    let type: 'query' | 'mutation' = 'query';
    let name: string | null = null;
    const t = this.peek()!;
    if (t.kind === 'name' && (t.value === 'query' || t.value === 'mutation')) {
      type = t.value as 'query' | 'mutation';
      this.next();
      const n = this.peek();
      if (n && n.kind === 'name') name = this.next().value;
    }
    const varDefs: Record<string, unknown> = {};
    if (this.peek()?.kind === 'punct' && this.peek()!.value === '(') {
      this.next();
      while (!(this.peek()?.kind === 'punct' && this.peek()!.value === ')')) {
        this.expectPunct('$');
        const vn = this.expectName();
        this.expectPunct(':');
        this.parseType();
        if (this.peek()?.kind === 'punct' && this.peek()!.value === '=') {
          this.next();
          varDefs[vn] = this.parseValue();
        } else {
          varDefs[vn] = undefined;
        }
      }
      this.next();
    }
    this.skipDirectives();
    return { type, name, variables: {}, varDefs, selections: this.parseSelectionSet() };
  }
  parseType(): void {
    const t = this.peek()!;
    if (t.kind === 'punct' && t.value === '[') {
      this.next();
      this.parseType();
      this.expectPunct(']');
    } else {
      this.expectName();
    }
    if (this.peek()?.kind === 'punct' && this.peek()!.value === '!') this.next();
  }
  skipDirectives(): void {
    while (this.peek()?.kind === 'punct' && this.peek()!.value === '@') {
      this.next();
      this.expectName();
      if (this.peek()?.kind === 'punct' && this.peek()!.value === '(') this.parseArgs();
    }
  }
  parseArgs(): Record<string, unknown> {
    const args: Record<string, unknown> = {};
    this.expectPunct('(');
    while (!(this.peek()?.kind === 'punct' && this.peek()!.value === ')')) {
      const name = this.expectName();
      this.expectPunct(':');
      args[name] = this.parseValue();
    }
    this.expectPunct(')');
    return args;
  }
  parseValue(): unknown {
    const t = this.next();
    if (t.kind === 'punct' && t.value === '$') return { __var: this.expectName() };
    if (t.kind === 'punct' && t.value === '[') {
      const arr: unknown[] = [];
      while (!(this.peek()?.kind === 'punct' && this.peek()!.value === ']')) arr.push(this.parseValue());
      this.next();
      return arr;
    }
    if (t.kind === 'punct' && t.value === '{') {
      const obj: Record<string, unknown> = {};
      while (!(this.peek()?.kind === 'punct' && this.peek()!.value === '}')) {
        const name = this.expectName();
        this.expectPunct(':');
        obj[name] = this.parseValue();
      }
      this.next();
      return obj;
    }
    if (t.kind === 'string') return t.value;
    if (t.kind === 'int') return Number.parseInt(t.value, 10);
    if (t.kind === 'float') return Number.parseFloat(t.value);
    if (t.kind === 'name') {
      if (t.value === 'true') return true;
      if (t.value === 'false') return false;
      if (t.value === 'null') return null;
      return { __enum: t.value };
    }
    throw new Error('bad graphql value');
  }
  parseSelectionSet(): GqlSelection[] {
    this.expectPunct('{');
    const sels: GqlSelection[] = [];
    while (!(this.peek()?.kind === 'punct' && this.peek()!.value === '}')) {
      const t = this.peek()!;
      if (t.kind === 'spread') {
        this.next();
        const n = this.peek();
        if (n && n.kind === 'name' && n.value === 'on') {
          this.next();
          const typeCond = this.expectName();
          this.skipDirectives();
          sels.push({ kind: 'fragment', name: null, typeCondition: typeCond, selections: this.parseSelectionSet() });
        } else if (n && n.kind === 'name') {
          const fragName = this.next().value;
          this.skipDirectives();
          sels.push({ kind: 'fragment', name: fragName, typeCondition: null, selections: [] });
        } else {
          throw new Error('bad fragment spread');
        }
      } else {
        let name = this.expectName();
        let alias: string | null = null;
        if (this.peek()?.kind === 'punct' && this.peek()!.value === ':') {
          this.next();
          alias = name;
          name = this.expectName();
        }
        let args: Record<string, unknown> = {};
        if (this.peek()?.kind === 'punct' && this.peek()!.value === '(') args = this.parseArgs();
        this.skipDirectives();
        let selections: GqlSelection[] = [];
        if (this.peek()?.kind === 'punct' && this.peek()!.value === '{') selections = this.parseSelectionSet();
        sels.push({ kind: 'field', name, alias, args, selections });
      }
    }
    this.expectPunct('}');
    return sels;
  }
}

// Type refs for introspection
interface TypeRef {
  name: string | null;
  kind: string;
  ofType?: TypeRef;
}
interface FieldDef {
  name: string;
  type: TypeRef;
  args?: { name: string; type: TypeRef }[];
}
interface TypeDef {
  name: string;
  kind: 'OBJECT' | 'ENUM' | 'SCALAR' | 'INPUT_OBJECT';
  fields?: FieldDef[];
  enumValues?: string[];
}
const T = (name: string, kind = 'OBJECT'): TypeRef => ({ name, kind });
const TS = (name: string): TypeRef => ({ name, kind: 'SCALAR' });
const NN = (t: TypeRef): TypeRef => ({ name: null, kind: 'NON_NULL', ofType: t });
const L = (t: TypeRef): TypeRef => ({ name: null, kind: 'LIST', ofType: t });
const TYPE_DEFS = new Map<string, TypeDef>();
function defType(d: TypeDef): void {
  TYPE_DEFS.set(d.name, d);
}
defType({ name: 'String', kind: 'SCALAR' });
defType({ name: 'Int', kind: 'SCALAR' });
defType({ name: 'Boolean', kind: 'SCALAR' });
defType({ name: 'ID', kind: 'SCALAR' });
defType({ name: 'IssueState', kind: 'ENUM', enumValues: ['OPEN', 'CLOSED'] });
defType({ name: 'PullRequestState', kind: 'ENUM', enumValues: ['OPEN', 'CLOSED', 'MERGED'] });
defType({ name: 'MergeableState', kind: 'ENUM', enumValues: ['MERGEABLE', 'CONFLICTING', 'UNKNOWN'] });
defType({ name: 'OrderDirection', kind: 'ENUM', enumValues: ['ASC', 'DESC'] });
defType({ name: 'IssueOrderField', kind: 'ENUM', enumValues: ['CREATED_AT', 'UPDATED_AT', 'COMMENTS'] });
defType({ name: 'SearchType', kind: 'ENUM', enumValues: ['ISSUE', 'REPOSITORY', 'USER', 'DISCUSSION', 'COMMIT', 'CODE', 'MILESTONE', 'ORGANIZATION', 'PACKAGE', 'PROJECT', 'TEAM', 'WIKI'] });
defType({
  name: 'Query', kind: 'OBJECT',
  fields: [
    { name: 'viewer', type: NN(T('User')) },
    { name: 'repository', type: T('Repository'), args: [{ name: 'owner', type: NN(TS('String')) }, { name: 'name', type: NN(TS('String')) }] },
    { name: 'node', type: T('Node'), args: [{ name: 'id', type: NN(TS('ID')) }] },
    { name: '__type', type: T('__Type'), args: [{ name: 'name', type: NN(TS('String')) }] },
    { name: '__schema', type: NN(T('__Schema')) },
  ],
});
defType({
  name: 'Mutation', kind: 'OBJECT',
  fields: [
    { name: 'createIssue', type: T('CreateIssuePayload'), args: [{ name: 'input', type: NN(T('CreateIssueInput', 'INPUT_OBJECT')) }] },
    { name: 'closeIssue', type: T('CloseIssuePayload'), args: [{ name: 'input', type: NN(T('CloseIssueInput', 'INPUT_OBJECT')) }] },
    { name: 'createPullRequest', type: T('CreatePullRequestPayload'), args: [{ name: 'input', type: NN(T('CreatePullRequestInput', 'INPUT_OBJECT')) }] },
    { name: 'mergePullRequest', type: T('MergePullRequestPayload'), args: [{ name: 'input', type: NN(T('MergePullRequestInput', 'INPUT_OBJECT')) }] },
    { name: 'addComment', type: T('AddCommentPayload'), args: [{ name: 'input', type: NN(T('AddCommentInput', 'INPUT_OBJECT')) }] },
  ],
});
defType({
  name: 'User', kind: 'OBJECT',
  fields: [
    { name: 'id', type: NN(TS('ID')) },
    { name: 'login', type: NN(TS('String')) },
    { name: 'name', type: TS('String') },
    { name: 'email', type: TS('String') },
  ],
});
defType({
  name: 'Repository', kind: 'OBJECT',
  fields: [
    { name: 'id', type: NN(TS('ID')) },
    { name: 'databaseId', type: TS('Int') },
    { name: 'name', type: NN(TS('String')) },
    { name: 'nameWithOwner', type: NN(TS('String')) },
    { name: 'owner', type: NN(T('User')) },
    { name: 'defaultBranchRef', type: T('Ref') },
    { name: 'viewerPermission', type: TS('String') },
    { name: 'hasIssuesEnabled', type: NN(TS('Boolean')) },
    { name: 'issue', type: T('Issue'), args: [{ name: 'number', type: NN(TS('Int')) }] },
    { name: 'issues', type: T('IssueConnection'), args: [{ name: 'first', type: TS('Int') }, { name: 'after', type: TS('String') }, { name: 'states', type: L(T('IssueState', 'ENUM')) }, { name: 'orderBy', type: T('IssueOrder', 'INPUT_OBJECT') }] },
    { name: 'pullRequest', type: T('PullRequest'), args: [{ name: 'number', type: NN(TS('Int')) }] },
    { name: 'pullRequests', type: T('PullRequestConnection'), args: [{ name: 'first', type: TS('Int') }, { name: 'after', type: TS('String') }, { name: 'states', type: L(T('PullRequestState', 'ENUM')) }] },
  ],
});
defType({
  name: 'Issue', kind: 'OBJECT',
  fields: [
    { name: 'id', type: NN(TS('ID')) },
    { name: 'number', type: NN(TS('Int')) },
    { name: 'title', type: NN(TS('String')) },
    { name: 'body', type: TS('String') },
    { name: 'state', type: NN(T('IssueState', 'ENUM')) },
    { name: 'createdAt', type: TS('String') },
    { name: 'author', type: T('User') },
    { name: 'labels', type: T('LabelConnection') },
    { name: 'comments', type: T('CommentConnection') },
    { name: 'repository', type: T('Repository') },
  ],
});
defType({
  name: 'PullRequest', kind: 'OBJECT',
  fields: [
    { name: 'id', type: NN(TS('ID')) },
    { name: 'number', type: NN(TS('Int')) },
    { name: 'title', type: TS('String') },
    { name: 'body', type: TS('String') },
    { name: 'state', type: NN(T('PullRequestState', 'ENUM')) },
    { name: 'merged', type: NN(TS('Boolean')) },
    { name: 'mergeable', type: NN(T('MergeableState', 'ENUM')) },
    { name: 'headRefName', type: TS('String') },
    { name: 'baseRefName', type: TS('String') },
    { name: 'headRefOid', type: TS('String') },
    { name: 'baseRefOid', type: TS('String') },
    { name: 'files', type: T('ChangedFileConnection'), args: [{ name: 'first', type: TS('Int') }, { name: 'after', type: TS('String') }] },
    { name: 'mergeCommit', type: T('Commit') },
  ],
});
defType({ name: 'Ref', kind: 'OBJECT', fields: [{ name: 'name', type: NN(TS('String')) }, { name: 'target', type: T('Commit') }] });
defType({ name: 'Commit', kind: 'OBJECT', fields: [{ name: 'oid', type: NN(TS('String')) }] });
defType({
  name: 'PageInfo', kind: 'OBJECT',
  fields: [
    { name: 'hasNextPage', type: NN(TS('Boolean')) },
    { name: 'hasPreviousPage', type: NN(TS('Boolean')) },
    { name: 'startCursor', type: TS('String') },
    { name: 'endCursor', type: TS('String') },
  ],
});
defType({
  name: 'IssueConnection', kind: 'OBJECT',
  fields: [
    { name: 'nodes', type: L(T('Issue')) },
    { name: 'edges', type: L(T('IssueEdge')) },
    { name: 'pageInfo', type: NN(T('PageInfo')) },
    { name: 'totalCount', type: NN(TS('Int')) },
  ],
});
defType({ name: 'IssueEdge', kind: 'OBJECT', fields: [{ name: 'node', type: T('Issue') }, { name: 'cursor', type: NN(TS('String')) }] });
defType({
  name: 'PullRequestConnection', kind: 'OBJECT',
  fields: [
    { name: 'nodes', type: L(T('PullRequest')) },
    { name: 'edges', type: L(T('PullRequestEdge')) },
    { name: 'pageInfo', type: NN(T('PageInfo')) },
    { name: 'totalCount', type: NN(TS('Int')) },
  ],
});
defType({ name: 'PullRequestEdge', kind: 'OBJECT', fields: [{ name: 'node', type: T('PullRequest') }, { name: 'cursor', type: NN(TS('String')) }] });
defType({
  name: 'ChangedFileConnection', kind: 'OBJECT',
  fields: [
    { name: 'nodes', type: L(T('ChangedFile')) },
    { name: 'edges', type: L(T('ChangedFileEdge')) },
    { name: 'pageInfo', type: NN(T('PageInfo')) },
    { name: 'totalCount', type: NN(TS('Int')) },
  ],
});
defType({ name: 'ChangedFileEdge', kind: 'OBJECT', fields: [{ name: 'node', type: T('ChangedFile') }, { name: 'cursor', type: NN(TS('String')) }] });
defType({
  name: 'ChangedFile', kind: 'OBJECT',
  fields: [
    { name: 'path', type: NN(TS('String')) },
    { name: 'additions', type: NN(TS('Int')) },
    { name: 'deletions', type: NN(TS('Int')) },
    { name: 'changeType', type: TS('String') },
  ],
});
defType({ name: 'Label', kind: 'OBJECT', fields: [{ name: 'name', type: NN(TS('String')) }, { name: 'color', type: TS('String') }] });
defType({ name: 'LabelConnection', kind: 'OBJECT', fields: [{ name: 'nodes', type: L(T('Label')) }, { name: 'totalCount', type: NN(TS('Int')) }] });
defType({ name: 'Comment', kind: 'OBJECT', fields: [{ name: 'id', type: NN(TS('ID')) }, { name: 'body', type: TS('String') }, { name: 'author', type: T('User') }] });
defType({ name: 'CommentConnection', kind: 'OBJECT', fields: [{ name: 'nodes', type: L(T('Comment')) }, { name: 'totalCount', type: NN(TS('Int')) }] });
defType({ name: 'CommentEdge', kind: 'OBJECT', fields: [{ name: 'node', type: T('Comment') }, { name: 'cursor', type: NN(TS('String')) }] });
defType({ name: 'CreateIssuePayload', kind: 'OBJECT', fields: [{ name: 'issue', type: T('Issue') }] });
defType({ name: 'CloseIssuePayload', kind: 'OBJECT', fields: [{ name: 'issue', type: T('Issue') }] });
defType({ name: 'CreatePullRequestPayload', kind: 'OBJECT', fields: [{ name: 'pullRequest', type: T('PullRequest') }] });
defType({ name: 'MergePullRequestPayload', kind: 'OBJECT', fields: [{ name: 'pullRequest', type: T('PullRequest') }] });
defType({ name: 'AddCommentPayload', kind: 'OBJECT', fields: [{ name: 'commentEdge', type: T('CommentEdge') }] });
defType({ name: 'Node', kind: 'OBJECT', fields: [{ name: 'id', type: NN(TS('ID')) }] });
defType({
  name: '__Schema', kind: 'OBJECT',
  fields: [
    { name: 'queryType', type: T('__Type') },
    { name: 'mutationType', type: T('__Type') },
    { name: 'types', type: L(T('__Type')) },
  ],
});
defType({
  name: '__Type', kind: 'OBJECT',
  fields: [
    { name: 'name', type: TS('String') },
    { name: 'kind', type: TS('String') },
    { name: 'description', type: TS('String') },
    { name: 'fields', type: L(T('__Field')), args: [{ name: 'includeDeprecated', type: TS('Boolean') }] },
    { name: 'enumValues', type: L(T('__EnumValue')), args: [{ name: 'includeDeprecated', type: TS('Boolean') }] },
    { name: 'inputFields', type: L(T('__InputValue')) },
    { name: 'interfaces', type: L(T('__Type')) },
    { name: 'possibleTypes', type: L(T('__Type')) },
    { name: 'ofType', type: T('__Type') },
  ],
});
defType({
  name: '__Field', kind: 'OBJECT',
  fields: [
    { name: 'name', type: NN(TS('String')) },
    { name: 'description', type: TS('String') },
    { name: 'args', type: L(T('__InputValue')) },
    { name: 'type', type: NN(T('__Type')) },
  ],
});
defType({
  name: '__InputValue', kind: 'OBJECT',
  fields: [
    { name: 'name', type: NN(TS('String')) },
    { name: 'description', type: TS('String') },
    { name: 'type', type: NN(T('__Type')) },
    { name: 'defaultValue', type: TS('String') },
  ],
});
defType({ name: '__EnumValue', kind: 'OBJECT', fields: [{ name: 'name', type: NN(TS('String')) }, { name: 'description', type: TS('String') }] });

interface GqlCtx {
  vars: Record<string, unknown>;
  errors: { message: string }[];
  fragments: Map<string, GqlSelection[]>;
}
type Wrapper = { __typename: string; [k: string]: unknown };

function resolveValue(v: unknown, vars: Record<string, unknown>): unknown {
  if (v !== null && typeof v === 'object') {
    if ('__var' in (v as Record<string, unknown>)) return vars[(v as { __var: string }).__var];
    if ('__enum' in (v as Record<string, unknown>)) return (v as { __enum: string }).__enum;
    if (Array.isArray(v)) return v.map((x) => resolveValue(x, vars));
    const out: Record<string, unknown> = {};
    for (const [k, x] of Object.entries(v as Record<string, unknown>)) out[k] = resolveValue(x, vars);
    return out;
  }
  return v;
}
function cursorFor(seq: number | string): string {
  return b64encode(Buffer.from(`cursor:${seq}`, 'utf8'));
}
function paginate<T>(items: T[], first: number | undefined, after: string | undefined, cursorOf: (t: T, i: number) => string, edgeType: string): Wrapper {
  let start = 0;
  if (after) {
    const idx = items.findIndex((t, i) => cursorOf(t, i) === after);
    if (idx >= 0) start = idx + 1;
  }
  const sliced = items.slice(start, start + (first ?? 100));
  const hasNext = start + sliced.length < items.length;
  return {
    __typename: '',
    nodes: sliced,
    edges: sliced.map((n, i) => ({ __typename: edgeType, node: n, cursor: cursorOf(n, start + i) })),
    pageInfo: {
      __typename: 'PageInfo',
      hasNextPage: hasNext,
      hasPreviousPage: start > 0,
      startCursor: sliced.length ? cursorOf(sliced[0], start) : null,
      endCursor: sliced.length ? cursorOf(sliced[sliced.length - 1], start + sliced.length - 1) : null,
    },
    totalCount: items.length,
  };
}
function repoWrapper(repo: Repo): Wrapper {
  return { __typename: 'Repository', repo };
}
function issueWrapper(repo: Repo, issue: Issue): Wrapper {
  return { __typename: 'Issue', repo, issue };
}
function prWrapper(repo: Repo, pr: Pull): Wrapper {
  return { __typename: 'PullRequest', repo, pr };
}
function userWrapper(): Wrapper {
  return { __typename: 'User' };
}
function findRepoById(id: number): Repo | undefined {
  return repoList.find((r) => r.id === id);
}
function findIssueByGid(idStr: string): { repo: Repo; issue: Issue } | null {
  const d = ungid(idStr);
  if (!d || d.kind !== 'Issue') return null;
  const [repoId, num] = d.id.split(':').map((x) => Number.parseInt(x, 10));
  const repo = findRepoById(repoId);
  if (!repo) return null;
  const issue = repo.issues.find((i) => i.number === num);
  return issue ? { repo, issue } : null;
}
function findPrByGid(idStr: string): { repo: Repo; pr: Pull } | null {
  const d = ungid(idStr);
  if (!d || d.kind !== 'PullRequest') return null;
  const [repoId, num] = d.id.split(':').map((x) => Number.parseInt(x, 10));
  const repo = findRepoById(repoId);
  if (!repo) return null;
  const pr = repo.pulls.find((p) => p.number === num);
  return pr ? { repo, pr } : null;
}
function orderIssues(repo: Repo, args: Record<string, unknown>): Issue[] {
  let list = repo.issues.slice();
  const states = args.states as string[] | undefined;
  if (Array.isArray(states) && states.length) {
    const wanted = new Set(states.map((s) => String(s).toLowerCase()));
    list = list.filter((i) => wanted.has(i.state));
  }
  const orderBy = (args.orderBy ?? {}) as Record<string, unknown>;
  const dir = String(orderBy.direction ?? 'ASC').toUpperCase() === 'DESC' ? -1 : 1;
  list.sort((a, b) => (a.seq - b.seq) * dir || (a.number - b.number) * dir);
  return list;
}
function resolveField(parent: unknown, typeName: string, field: string, args: Record<string, unknown>, ctx: GqlCtx): unknown {
  const w = parent as Wrapper;
  if (typeName === '__Type') {
    const ref = w.ref as TypeRef;
    const def = ref.name ? TYPE_DEFS.get(ref.name) : undefined;
    switch (field) {
      case 'name': return ref.name;
      case 'kind': return ref.kind;
      case 'description': return null;
      case 'fields': return (def?.fields ?? []).map((f) => ({ __typename: '__Field', field: f }));
      case 'enumValues': return (def?.enumValues ?? []).map((n) => ({ __typename: '__EnumValue', name: n }));
      case 'inputFields': return [];
      case 'interfaces': return [];
      case 'possibleTypes': return [];
      case 'ofType': return ref.ofType ? { __typename: '__Type', ref: ref.ofType } : null;
      default: return null;
    }
  }
  if (typeName === '__Field') {
    const f = w.field as FieldDef;
    switch (field) {
      case 'name': return f.name;
      case 'description': return null;
      case 'args': return (f.args ?? []).map((a) => ({ __typename: '__InputValue', arg: a }));
      case 'type': return { __typename: '__Type', ref: f.type };
      default: return null;
    }
  }
  if (typeName === '__InputValue') {
    const a = w.arg as { name: string; type: TypeRef };
    switch (field) {
      case 'name': return a.name;
      case 'description': return null;
      case 'type': return { __typename: '__Type', ref: a.type };
      case 'defaultValue': return null;
      default: return null;
    }
  }
  if (typeName === '__EnumValue') return field === 'name' ? w.name : null;
  if (typeName === '__Schema') {
    switch (field) {
      case 'queryType': return { __typename: '__Type', ref: { name: 'Query', kind: 'OBJECT' } };
      case 'mutationType': return { __typename: '__Type', ref: { name: 'Mutation', kind: 'OBJECT' } };
      case 'types': return [...TYPE_DEFS.values()].map((d) => ({ __typename: '__Type', ref: { name: d.name, kind: d.kind } }));
      default: return null;
    }
  }
  if (typeName === 'Query') {
    switch (field) {
      case 'viewer': return userWrapper();
      case 'repository': {
        const repo = findRepo(String(args.owner ?? ''), String(args.name ?? ''));
        return repo ? repoWrapper(repo) : null;
      }
      case 'node': {
        const d = ungid(String(args.id ?? ''));
        if (!d) return null;
        if (d.kind === 'Repository') {
          const repo = findRepoById(Number.parseInt(d.id, 10));
          return repo ? repoWrapper(repo) : null;
        }
        if (d.kind === 'Issue') {
          const found = findIssueByGid(String(args.id));
          return found ? issueWrapper(found.repo, found.issue) : null;
        }
        if (d.kind === 'PullRequest') {
          const found = findPrByGid(String(args.id));
          return found ? prWrapper(found.repo, found.pr) : null;
        }
        return null;
      }
      case '__type': {
        const def = TYPE_DEFS.get(String(args.name ?? ''));
        return def ? { __typename: '__Type', ref: { name: def.name, kind: def.kind } } : null;
      }
      case '__schema': return { __typename: '__Schema' };
      default: return null;
    }
  }
  if (typeName === 'Mutation') {
    switch (field) {
      case 'createIssue': {
        const input = (args.input ?? {}) as Record<string, unknown>;
        const d = ungid(String(input.repositoryId ?? ''));
        const repo = d ? findRepoById(Number.parseInt(d.id, 10)) : undefined;
        if (!repo) throw new Error('Repository not found');
        const issue: Issue = {
          id: globalIdCounter, number: repo.nextNumber, title: String(input.title ?? ''),
          body: String(input.body ?? ''), state: 'open', labels: [], comments: [],
          seq: ++issueSeqCounter, cachedJson: null,
        };
        globalIdCounter += 1;
        repo.nextNumber += 1;
        repo.issues.push(issue);
        return { __typename: 'CreateIssuePayload', issue: issueWrapper(repo, issue) };
      }
      case 'closeIssue': {
        const input = (args.input ?? {}) as Record<string, unknown>;
        const found = findIssueByGid(String(input.issueId ?? ''));
        if (!found) throw new Error('Issue not found');
        found.issue.state = 'closed';
        found.issue.cachedJson = null;
        return { __typename: 'CloseIssuePayload', issue: issueWrapper(found.repo, found.issue) };
      }
      case 'createPullRequest': {
        const input = (args.input ?? {}) as Record<string, unknown>;
        const d = ungid(String(input.repositoryId ?? ''));
        const repo = d ? findRepoById(Number.parseInt(d.id, 10)) : undefined;
        if (!repo) throw new Error('Repository not found');
        const head = String(input.headRefName ?? '');
        const base = String(input.baseRefName ?? '');
        let pr = repo.pulls.find((p) => p.headRef === head && p.baseRef === base && p.state === 'open');
        if (!pr) {
          pr = {
            id: globalIdCounter, number: repo.nextNumber, title: String(input.title ?? ''),
            body: String(input.body ?? ''), state: 'open', headRef: head, baseRef: base,
            merged: false, mergedAt: null, mergeCommitSha: null, seq: ++issueSeqCounter,
          };
          globalIdCounter += 1;
          repo.nextNumber += 1;
          repo.pulls.push(pr);
        }
        return { __typename: 'CreatePullRequestPayload', pullRequest: prWrapper(repo, pr) };
      }
      case 'mergePullRequest': {
        const input = (args.input ?? {}) as Record<string, unknown>;
        const found = findPrByGid(String(input.pullRequestId ?? ''));
        if (!found) throw new Error('Pull request not found');
        const result = doMerge(found.repo, found.pr);
        if (!result.ok) throw new Error(result.message ?? 'Merge conflict');
        return { __typename: 'MergePullRequestPayload', pullRequest: prWrapper(found.repo, found.pr) };
      }
      case 'addComment': {
        const input = (args.input ?? {}) as Record<string, unknown>;
        const found = findIssueByGid(String(input.subjectId ?? ''));
        if (!found) throw new Error('Subject not found');
        const comment = { id: found.repo.commentSeq, body: String(input.body ?? '') };
        found.repo.commentSeq += 1;
        found.issue.comments.push(comment);
        found.issue.cachedJson = null;
        return {
          __typename: 'AddCommentPayload',
          commentEdge: {
            __typename: 'CommentEdge',
            node: { __typename: 'Comment', repo: found.repo, issue: found.issue, comment },
            cursor: cursorFor(comment.id),
          },
        };
      }
      default: return null;
    }
  }
  if (typeName === 'User') {
    switch (field) {
      case 'id': return String(VIEWER_ID);
      case 'login': return VIEWER_LOGIN;
      case 'name': return VIEWER_NAME;
      case 'email': return VIEWER_EMAIL;
      default: return null;
    }
  }
  if (typeName === 'Repository') {
    const repo = w.repo as Repo;
    switch (field) {
      case 'id': return gid('Repository', repo.id);
      case 'databaseId': return repo.id;
      case 'name': return repo.name;
      case 'nameWithOwner': return `${repo.owner}/${repo.name}`;
      case 'owner': return userWrapper();
      case 'defaultBranchRef': {
        const tip = branchTip(repo, repo.defaultBranch);
        return tip ? { __typename: 'Ref', name: repo.defaultBranch, repo, oid: tip } : null;
      }
      case 'viewerPermission': return 'ADMIN';
      case 'hasIssuesEnabled': return true;
      case 'issue': {
        const issue = repo.issues.find((i) => i.number === (args.number as number));
        return issue ? issueWrapper(repo, issue) : null;
      }
      case 'issues': {
        const ordered = orderIssues(repo, args);
        const conn = paginate(ordered, args.first as number | undefined, args.after as string | undefined, (i) => cursorFor(i.seq), 'IssueEdge');
        conn.__typename = 'IssueConnection';
        conn.nodes = (conn.nodes as Issue[]).map((i) => issueWrapper(repo, i));
        (conn.edges as Wrapper[]).forEach((e, i) => { e.node = (conn.nodes as Wrapper[])[i]; });
        return conn;
      }
      case 'pullRequest': {
        const pr = repo.pulls.find((p) => p.number === (args.number as number));
        return pr ? prWrapper(repo, pr) : null;
      }
      case 'pullRequests': {
        let list = repo.pulls.slice();
        const states = args.states as string[] | undefined;
        if (Array.isArray(states) && states.length) {
          const wanted = new Set(states.map((s) => String(s).toUpperCase()));
          list = list.filter((p) => {
            const st = p.merged ? 'MERGED' : p.state === 'closed' ? 'CLOSED' : 'OPEN';
            return wanted.has(st);
          });
        }
        list.sort((a, b) => a.seq - b.seq);
        const conn = paginate(list, args.first as number | undefined, args.after as string | undefined, (p) => cursorFor(p.seq), 'PullRequestEdge');
        conn.__typename = 'PullRequestConnection';
        conn.nodes = (conn.nodes as Pull[]).map((p) => prWrapper(repo, p));
        (conn.edges as Wrapper[]).forEach((e, i) => { e.node = (conn.nodes as Wrapper[])[i]; });
        return conn;
      }
      default: return null;
    }
  }
  if (typeName === 'Issue') {
    const issue = w.issue as Issue;
    const repo = w.repo as Repo;
    switch (field) {
      case 'id': return gid('Issue', `${repo.id}:${issue.number}`);
      case 'number': return issue.number;
      case 'title': return issue.title;
      case 'body': return issue.body;
      case 'state': return issue.state === 'open' ? 'OPEN' : 'CLOSED';
      case 'createdAt': return NOW_ISO;
      case 'author': return userWrapper();
      case 'labels': return { __typename: 'LabelConnection', nodes: issue.labels.map((l) => ({ __typename: 'Label', name: l.name, color: l.color })), totalCount: issue.labels.length };
      case 'comments': return {
        __typename: 'CommentConnection',
        nodes: issue.comments.map((c) => ({ __typename: 'Comment', repo, issue, comment: c })),
        totalCount: issue.comments.length,
      };
      case 'repository': return repoWrapper(repo);
      default: return null;
    }
  }
  if (typeName === 'PullRequest') {
    const pr = w.pr as Pull;
    const repo = w.repo as Repo;
    switch (field) {
      case 'id': return gid('PullRequest', `${repo.id}:${pr.number}`);
      case 'number': return pr.number;
      case 'title': return pr.title;
      case 'body': return pr.body;
      case 'state': return pr.merged ? 'MERGED' : pr.state === 'closed' ? 'CLOSED' : 'OPEN';
      case 'merged': return pr.merged;
      case 'mergeable': {
        const head = prHeadSha(repo, pr);
        const base = prBaseSha(repo, pr);
        if (!head || !base) return 'UNKNOWN';
        return prMergeable(repo, pr) ? 'MERGEABLE' : 'CONFLICTING';
      }
      case 'headRefName': return pr.headRef;
      case 'baseRefName': return pr.baseRef;
      case 'headRefOid': return prHeadSha(repo, pr) || null;
      case 'baseRefOid': return prBaseSha(repo, pr) || null;
      case 'files': {
        const files = diffFiles(repo, prBaseSha(repo, pr), prHeadSha(repo, pr));
        const conn = paginate(
          files,
          args.first as number | undefined,
          args.after as string | undefined,
          (_f, i) => cursorFor(i),
          'ChangedFileEdge',
        );
        conn.__typename = 'ChangedFileConnection';
        conn.nodes = (conn.nodes as { filename: string; status: string; additions: number; deletions: number }[]).map((f) => ({
          __typename: 'ChangedFile', path: f.filename, additions: f.additions, deletions: f.deletions, changeType: f.status,
        }));
        (conn.edges as Wrapper[]).forEach((e, i) => { e.node = (conn.nodes as Wrapper[])[i]; });
        return conn;
      }
      case 'mergeCommit': return pr.mergeCommitSha ? { __typename: 'Commit', oid: pr.mergeCommitSha } : null;
      default: return null;
    }
  }
  if (typeName === 'Ref') return field === 'name' ? w.name : field === 'target' ? { __typename: 'Commit', oid: w.oid } : null;
  if (typeName === 'Commit') return field === 'oid' ? w.oid : null;
  if (typeName === 'Comment') {
    const c = w.comment as { id: number; body: string };
    const repo = w.repo as Repo;
    const issue = w.issue as Issue;
    if (field === 'id') return gid('IssueComment', `${repo.id}:${issue.number}:${c.id}`);
    if (field === 'body') return c.body;
    if (field === 'author') return userWrapper();
    return null;
  }
  if (typeName === 'Label') return field === 'name' ? w.name : field === 'color' ? w.color : null;
  if (typeName === 'ChangedFile') return w[field] ?? null;
  // Generic: connections, pageInfo, payloads, edges.
  if (w && typeof w === 'object' && field in w) return w[field];
  return null;
}
function applyValue(value: unknown, sels: GqlSelection[], ctx: GqlCtx): unknown {
  if (value === null || value === undefined) return null;
  if (Array.isArray(value)) return value.map((v) => applyValue(v, sels, ctx));
  if (typeof value === 'object' && '__typename' in (value as Record<string, unknown>)) {
    if (sels.length === 0) return {};
    return applySel(value as Wrapper, (value as Wrapper).__typename, sels, ctx);
  }
  return value;
}
function applySel(parent: unknown, typeName: string, sels: GqlSelection[], ctx: GqlCtx): Record<string, unknown> {
  const out: Record<string, unknown> = {};
  for (const sel of sels) {
    if (sel.kind === 'fragment') {
      if (sel.name) {
        const frag = ctx.fragments.get(sel.name);
        if (frag) Object.assign(out, applySel(parent, typeName, frag, ctx));
        continue;
      }
      if (sel.typeCondition && sel.typeCondition !== typeName) continue;
      Object.assign(out, applySel(parent, typeName, sel.selections, ctx));
      continue;
    }
    const key = sel.alias ?? sel.name;
    if (sel.name === '__typename') { out[key] = typeName; continue; }
    const def = TYPE_DEFS.get(typeName);
    const fieldDef = def?.fields?.find((f) => f.name === sel.name);
    if (!fieldDef && typeName !== 'Node') {
      ctx.errors.push({ message: `Cannot query field "${sel.name}" on type "${typeName}".` });
      out[key] = null;
      continue;
    }
    const args: Record<string, unknown> = {};
    for (const [k, v] of Object.entries(sel.args)) args[k] = resolveValue(v, ctx.vars);
    let value: unknown;
    try {
      value = resolveField(parent, typeName, sel.name, args, ctx);
    } catch (e) {
      ctx.errors.push({ message: (e as Error).message });
      out[key] = null;
      continue;
    }
    out[key] = applyValue(value, sel.selections, ctx);
  }
  return out;
}
function executeGql(doc: string, variables: Record<string, unknown>): Record<string, unknown> {
  try {
    const parser = new GqlParser(doc);
    const ops = parser.parseDocument();
    if (ops.length === 0) return { data: null, errors: [{ message: 'Empty document' }] };
    const op = ops[0];
    const vars: Record<string, unknown> = {};
    for (const [k, d] of Object.entries(op.varDefs)) vars[k] = d;
    for (const [k, v] of Object.entries(variables)) vars[k] = v;
    const ctx: GqlCtx = { vars, errors: [], fragments: parser.fragments };
    const rootType = op.type === 'mutation' ? 'Mutation' : 'Query';
    const data = applySel({ __typename: rootType }, rootType, op.selections, ctx);
    const result: Record<string, unknown> = { data };
    if (ctx.errors.length) result.errors = ctx.errors;
    return result;
  } catch (e) {
    return { data: null, errors: [{ message: (e as Error).message }] };
  }
}
async function handleGraphQL(req: IncomingMessage, res: ServerResponse): Promise<boolean> {
  if (!authed(req)) {
    errJson(res, 401, 'Requires authentication');
    return true;
  }
  const raw = await readBody(req);
  let body: unknown;
  try {
    body = JSON.parse(raw.toString('utf8'));
  } catch {
    sendJson(res, 400, { errors: [{ message: 'Problems parsing JSON' }] });
    return true;
  }
  if (Array.isArray(body)) {
    const results = body.map((op) => {
      const o = asBody(op);
      return executeGql(String(o.query ?? ''), asBody(o.variables) as Record<string, unknown>);
    });
    sendJson(res, 200, results);
    return true;
  }
  const o = asBody(body);
  sendJson(res, 200, executeGql(String(o.query ?? ''), asBody(o.variables) as Record<string, unknown>));
  return true;
}

// ---------------------------------------------------------------- MCP

const MCP_TOOLS: { name: string; description: string; inputSchema: Record<string, unknown> }[] = [
  {
    name: 'create_repo',
    description: 'Create a new repository owned by the viewer.',
    inputSchema: {
      type: 'object',
      properties: {
        name: { type: 'string', description: 'Repository name' },
        description: { type: 'string', description: 'Repository description' },
        private: { type: 'boolean', description: 'Whether the repository is private' },
      },
      required: ['name'],
    },
  },
  {
    name: 'get_repo',
    description: 'Get a repository by owner and name.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'Repository owner login' },
        repo: { type: 'string', description: 'Repository name' },
        full_name: { type: 'string', description: 'Full repository name owner/repo' },
      },
      required: ['owner', 'repo'],
    },
  },
  {
    name: 'create_issue',
    description: 'Create an issue in a repository.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'Repository owner login' },
        repo: { type: 'string', description: 'Repository name' },
        full_name: { type: 'string', description: 'Full repository name owner/repo' },
        title: { type: 'string', description: 'Issue title' },
        body: { type: 'string', description: 'Issue body' },
      },
      required: ['owner', 'repo', 'title'],
    },
  },
  {
    name: 'list_issues',
    description: 'List issues in a repository.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'Repository owner login' },
        repo: { type: 'string', description: 'Repository name' },
        full_name: { type: 'string', description: 'Full repository name owner/repo' },
        state: { type: 'string', description: 'Issue state: open, closed, or all' },
      },
      required: ['owner', 'repo'],
    },
  },
  {
    name: 'create_pull_request',
    description: 'Create a pull request in a repository.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'Repository owner login' },
        repo: { type: 'string', description: 'Repository name' },
        full_name: { type: 'string', description: 'Full repository name owner/repo' },
        title: { type: 'string', description: 'Pull request title' },
        body: { type: 'string', description: 'Pull request body' },
        head: { type: 'string', description: 'Head branch name' },
        base: { type: 'string', description: 'Base branch name' },
      },
      required: ['owner', 'repo', 'title', 'head', 'base'],
    },
  },
  {
    name: 'merge_pull_request',
    description: 'Merge a pull request in a repository.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'Repository owner login' },
        repo: { type: 'string', description: 'Repository name' },
        full_name: { type: 'string', description: 'Full repository name owner/repo' },
        pull_number: { type: 'number', description: 'Pull request number' },
        number: { type: 'number', description: 'Pull request number' },
        pr_number: { type: 'number', description: 'Pull request number' },
      },
      required: ['owner', 'repo', 'pull_number'],
    },
  },
];
function mcpResult(id: unknown, result: unknown): Record<string, unknown> {
  return { jsonrpc: '2.0', id: id ?? null, result };
}
function mcpError(id: unknown, code: number, message: string): Record<string, unknown> {
  return { jsonrpc: '2.0', id: id ?? null, error: { code, message } };
}
function mcpToolOk(obj: unknown): Record<string, unknown> {
  const text = JSON.stringify(obj);
  return { content: [{ type: 'text', text }], structuredContent: obj, isError: false };
}
function mcpToolErr(message: string): Record<string, unknown> {
  const obj = { error: message };
  return { content: [{ type: 'text', text: JSON.stringify(obj) }], structuredContent: obj, isError: true };
}
function mcpSplitFullName(args: Body): void {
  if ((args.owner === undefined || args.repo === undefined) && typeof args.full_name === 'string') {
    const parts = (args.full_name as string).split('/');
    if (parts.length === 2) {
      if (args.owner === undefined) args.owner = parts[0];
      if (args.repo === undefined) args.repo = parts[1];
    }
  }
}
function mcpCallTool(name: string, args: Body): { result?: Record<string, unknown>; error?: { code: number; message: string } } {
  mcpSplitFullName(args);
  const need = (keys: string[]): { code: number; message: string } | null => {
    for (const k of keys) {
      if (args[k] === undefined || args[k] === null || args[k] === '') return { code: -32602, message: `Missing required argument: ${k}` };
    }
    return null;
  };
  switch (name) {
    case 'create_repo': {
      const missing = need(['name']);
      if (missing) return { error: missing };
      const repoName = String(args.name);
      if (repos.has(repoKey(VIEWER_LOGIN, repoName))) return { result: mcpToolErr('Repository already exists') };
      const repo = createRepoRecord(repoName, args.private === true, str(args.description));
      return { result: mcpToolOk(repoJson(repo)) };
    }
    case 'get_repo': {
      const missing = need(['owner', 'repo']);
      if (missing) return { error: missing };
      const repo = findRepo(String(args.owner), String(args.repo));
      if (!repo) return { result: mcpToolErr('Not Found') };
      return { result: mcpToolOk(repoJson(repo)) };
    }
    case 'create_issue': {
      const missing = need(['owner', 'repo', 'title']);
      if (missing) return { error: missing };
      const repo = findRepo(String(args.owner), String(args.repo));
      if (!repo) return { result: mcpToolErr('Not Found') };
      const issue: Issue = {
        id: globalIdCounter, number: repo.nextNumber, title: String(args.title),
        body: str(args.body, ''), state: 'open', labels: [], comments: [],
        seq: ++issueSeqCounter, cachedJson: null,
      };
      globalIdCounter += 1;
      repo.nextNumber += 1;
      repo.issues.push(issue);
      return { result: mcpToolOk(issueJson(issue, repo)) };
    }
    case 'list_issues': {
      const missing = need(['owner', 'repo']);
      if (missing) return { error: missing };
      const repo = findRepo(String(args.owner), String(args.repo));
      if (!repo) return { result: mcpToolErr('Not Found') };
      const state = String(args.state ?? 'open').toLowerCase();
      let list = repo.issues.slice();
      if (state === 'open' || state === 'closed') list = list.filter((i) => i.state === state);
      return { result: mcpToolOk({ issues: list.map((i) => issueJson(i, repo)) }) };
    }
    case 'create_pull_request': {
      const missing = need(['owner', 'repo', 'title', 'head', 'base']);
      if (missing) return { error: missing };
      const repo = findRepo(String(args.owner), String(args.repo));
      if (!repo) return { result: mcpToolErr('Not Found') };
      const head = String(args.head).includes(':') ? String(args.head).split(':').pop()! : String(args.head);
      const base = String(args.base).includes(':') ? String(args.base).split(':').pop()! : String(args.base);
      if (!branchTip(repo, head) || !branchTip(repo, base)) return { result: mcpToolErr('Head or base branch does not exist') };
      let pr = repo.pulls.find((p) => p.headRef === head && p.baseRef === base && p.state === 'open');
      if (!pr) {
        pr = {
          id: globalIdCounter, number: repo.nextNumber, title: String(args.title),
          body: str(args.body, ''), state: 'open', headRef: head, baseRef: base,
          merged: false, mergedAt: null, mergeCommitSha: null, seq: ++issueSeqCounter,
        };
        globalIdCounter += 1;
        repo.nextNumber += 1;
        repo.pulls.push(pr);
      }
      return { result: mcpToolOk(prJson(pr, repo)) };
    }
    case 'merge_pull_request': {
      const missing = need(['owner', 'repo']);
      if (missing) return { error: missing };
      const numRaw = args.pull_number ?? args.number ?? args.pr_number;
      if (numRaw === undefined || numRaw === null) return { error: { code: -32602, message: 'Missing required argument: pull_number' } };
      const repo = findRepo(String(args.owner), String(args.repo));
      if (!repo) return { result: mcpToolErr('Not Found') };
      const pr = repo.pulls.find((p) => p.number === Number(numRaw));
      if (!pr) return { result: mcpToolErr('Not Found') };
      if (pr.merged) return { result: mcpToolErr('Pull request already merged') };
      const result = doMerge(repo, pr);
      if (!result.ok) return { result: mcpToolErr(result.message ?? 'Merge conflict') };
      return { result: mcpToolOk({ sha: result.sha, merged: true, message: 'Pull request successfully merged' }) };
    }
    default:
      return { error: { code: -32601, message: `Unknown tool: ${name}` } };
  }
}
async function handleMcp(req: IncomingMessage, res: ServerResponse): Promise<boolean> {
  if (!authed(req)) {
    errJson(res, 401, 'Requires authentication');
    return true;
  }
  const raw = await readBody(req);
  let msg: unknown;
  try {
    msg = JSON.parse(raw.toString('utf8'));
  } catch {
    sendJson(res, 400, { jsonrpc: '2.0', id: null, error: { code: -32700, message: 'Parse error' } });
    return true;
  }
  const o = asBody(msg);
  const id = (o as Record<string, unknown>).id ?? null;
  const method = String((o as Record<string, unknown>).method ?? '');
  const params = asBody((o as Record<string, unknown>).params);
  const isNotification = (o as Record<string, unknown>).id === undefined;
  if (method.startsWith('notifications/')) {
    res.writeHead(202, { 'content-length': 0 });
    res.end();
    return true;
  }
  if (isNotification) {
    res.writeHead(202, { 'content-length': 0 });
    res.end();
    return true;
  }
  switch (method) {
    case 'server/discover': {
      const serverInfo = { name: 'forge', version: '1.0.0' };
      sendJson(res, 200, mcpResult(id, {
        supportedVersions: ['2026-07-28', '2025-11-25'],
        capabilities: { tools: {} },
        serverInfo,
        _meta: { 'io.modelcontextprotocol/serverInfo': serverInfo },
      }));
      return true;
    }
    case 'initialize': {
      sendJson(res, 200, mcpResult(id, {
        protocolVersion: '2025-11-25',
        capabilities: { tools: {} },
        serverInfo: { name: 'forge', version: '1.0.0' },
      }));
      return true;
    }
    case 'ping': {
      sendJson(res, 200, mcpResult(id, {}));
      return true;
    }
    case 'tools/list': {
      sendJson(res, 200, mcpResult(id, { tools: MCP_TOOLS }));
      return true;
    }
    case 'tools/call': {
      const toolName = String(params.name ?? '');
      const args = asBody(params.arguments);
      const out = mcpCallTool(toolName, args);
      if (out.error) {
        sendJson(res, 200, mcpError(id, out.error.code, out.error.message));
        return true;
      }
      sendJson(res, 200, mcpResult(id, out.result));
      return true;
    }
    default: {
      sendJson(res, 200, mcpError(id, -32601, `Method not found: ${method}`));
      return true;
    }
  }
}

// ---------------------------------------------------------------- router

function decodeSeg(s: string): string {
  try {
    return decodeURIComponent(s);
  } catch {
    return s;
  }
}
export function createApp(): Server {
  const server = createServer((req, res) => {
    void (async () => {
      try {
        const url = new URL(req.url ?? '/', 'http://localhost');
        const pathname = url.pathname;
        if (pathname === '/healthz') {
          sendJson(res, 200, { ok: true });
          return;
        }
        if (pathname === '/api/graphql') {
          if (req.method === 'POST') {
            await handleGraphQL(req, res);
            return;
          }
          errJson(res, 405, 'Method Not Allowed');
          return;
        }
        if (pathname === '/mcp') {
          if (req.method === 'DELETE') {
            res.writeHead(204, { 'x-github-request-id': nextReqId() });
            res.end();
            return;
          }
          if (req.method === 'POST') {
            await handleMcp(req, res);
            return;
          }
          errJson(res, 405, 'Method Not Allowed');
          return;
        }
        if (pathname.startsWith('/api/v3')) {
          const parts = pathname.split('/').map(decodeSeg);
          const handled = await handleRest(req, res, parts, url.searchParams);
          if (!handled) errJson(res, 404, 'Not Found');
          return;
        }
        const gitParts = pathname.split('/').map(decodeSeg);
        if (gitParts.length >= 3 && gitParts[2].endsWith('.git')) {
          const handled = await handleGit(req, res, gitParts, url.searchParams);
          if (!handled) errJson(res, 404, 'Not Found');
          return;
        }
        errJson(res, 404, 'Not Found');
      } catch {
        if (!res.headersSent) {
          try { errJson(res, 500, 'Internal Server Error'); } catch { /* ignore */ }
        } else {
          try { res.end(); } catch { /* ignore */ }
        }
      }
    })();
  });
  return server;
}
