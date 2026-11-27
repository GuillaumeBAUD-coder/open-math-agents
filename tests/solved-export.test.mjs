import assert from 'node:assert/strict';
import { registerHooks } from 'node:module';
import test from 'node:test';

const rootId = 'Example.theorem';
const stepId = `${rootId}.R1.H2`;
const stubs = {
  'server-only': 'export {};',
  'next/server': 'export const NextResponse = Response;',
  '@/lib/catalog': `export const getFullMany = async () => [];
    export const getProblem = (id) => id === globalThis.solvedFixture.rootId ? { title: 'Example', kind: 'known' } : undefined;`,
  '@/lib/db': `export const getSolvedForExport = async () => {
      if (globalThis.solvedFixture.failed) throw Error('mock database unavailable');
      return globalThis.solvedFixture.rows;
    };
    export const getSolved = () => getSolvedForExport().catch(() => []);
    export const getSteps = async () => [];`,
};
const routeDependencies = new Set(['desk', 'outcome', 'steps']);
const hooks = registerHooks({
  resolve(specifier, context, nextResolve) {
    if (Object.hasOwn(stubs, specifier)) {
      return { shortCircuit: true, url: `data:text/javascript,${encodeURIComponent(stubs[specifier])}` };
    }
    const name = specifier.startsWith('@/lib/') ? specifier.slice('@/lib/'.length) : '';
    if (routeDependencies.has(name)) {
      return nextResolve(new URL(`../lib/${name}.ts`, import.meta.url).href, context);
    }
    return nextResolve(specifier, context);
  },
});
const { GET } = await import('../app/api/solved/route.ts');
hooks.deregister();

test('a failed database read returns an uncached 503 instead of zero proofs', async (t) => {
  t.mock.method(console, 'error', () => {});
  globalThis.solvedFixture = { rootId, failed: true };
  const response = await GET();
  assert.equal(response.status, 503);
  assert.equal(response.headers.get('cache-control'), 'no-store');
  assert.equal((await response.json()).error, 'solved_list_unavailable');
});

test('a genuinely empty list is a successful response', async () => {
  globalThis.solvedFixture = { rootId, rows: [] };
  const response = await GET();
  assert.equal(response.status, 200);
  assert.equal((await response.json()).count, 0);
});

test('accepted steps retain their public metadata without the global step list', async () => {
  const row = (id) => ({ problem_id: id, handle: 'fixture', pr_url: 'https://example.test/pull/1#closed' });
  globalThis.solvedFixture = { rootId, rows: [row(rootId), row(stepId)] };
  const response = await GET();
  assert.equal(response.status, 200);
  const body = await response.json();
  assert.deepEqual(body.byOutcome, { open: 0, known: 1, warmup: 0, step: 1 });
  assert.deepEqual(body.solved.map(({ title, step, outcome }) => ({ title, step, outcome })), [
    { title: 'Example', step: false, outcome: 'known' },
    { title: 'Step H2 of Example', step: true, outcome: 'step' },
  ]);
  assert.equal(body.solved[1].pr_url, 'https://example.test/pull/1');
});
