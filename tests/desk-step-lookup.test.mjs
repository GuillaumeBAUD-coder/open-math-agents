import assert from 'node:assert/strict';
import { registerHooks } from 'node:module';
import test from 'node:test';

const stepId = 'Example.theorem.R1.H2';
const stubs = {
  catalog: `export const PROBLEMS = [];
    export const getProblem = () => undefined;
    export const getFull = undefined, skeleton = undefined, proofPath = undefined, statementSkeleton = undefined;`,
  db: `export const deskOnline = true;
    export const getLiveMap = async () => new Map();
    export const getStats = async () => ({ solved: [] });
    export const getSteps = async (id, fresh) => {
      globalThis.fixture.lookups.push([id, fresh]);
      return id === globalThis.fixture.step.id
        ? [globalThis.fixture.step] : globalThis.fixture.globalSteps;
    };
    export const claim2 = async (id) => {
      globalThis.fixture.claims.push(id);
      return { lease: 'fixture-lease' };
    };
    export const hashIp = (ip) => ip;`,
  desk: `export const json = (body, status) => Response.json(body, {status});
    export const clientIp = () => '192.0.2.1';`,
  points: `export const pointsFor = () => 0;`,
  site: `export const SITE = 'https://example.test'; export const REPO = 'test/test';`,
};

const hooks = registerHooks({
  resolve(specifier, context, nextResolve) {
    if (specifier === '@/lib/steps') {
      return nextResolve(new URL('../lib/steps.ts', import.meta.url).href, context);
    }
    if (specifier.startsWith('@/lib/')) {
      const module = stubs[specifier.slice('@/lib/'.length)];
      assert.ok(module, `Missing test stub for ${specifier}`);
      return { shortCircuit: true, url: `data:text/javascript,${encodeURIComponent(module)}` };
    }
    return nextResolve(specifier, context);
  },
});
const { GET } = await import('../app/api/desk/next/route.ts');
hooks.deregister();

function setup(solved = false) {
  const step = {
    id: stepId,
    parent: 'Example.theorem',
    reduction: 'Example.theorem.R1',
    module: 'OMAReductions.R_Example_theorem_R1',
    statement: 'True',
    solved,
    k: 2,
  };
  const fixture = { step, globalSteps: [], lookups: [], claims: [] };
  globalThis.fixture = fixture;
  return fixture;
}

function request(params) {
  return new Request(`https://example.test/api/desk/next?${new URLSearchParams({ handle: 'fixture', ...params })}`);
}

test('an exact open step is found even if the global listing omits it', async () => {
  const fixture = setup();
  const res = await GET(request({ problem: stepId }));
  assert.equal(res.status, 200);
  assert.equal((await res.json()).problem.id, stepId);
  assert.deepEqual(fixture.lookups, [[stepId, true]]);
  assert.deepEqual(fixture.claims, [stepId]);
});

test('a solved exact step is excluded before claiming', async () => {
  const fixture = setup(true);
  const res = await GET(request({ problem: stepId }));
  assert.equal(res.status, 404);
  assert.deepEqual(fixture.lookups, [[stepId, true]]);
  assert.deepEqual(fixture.claims, []);
});

test('an unqualified step request still uses the global listing', async () => {
  const fixture = setup();
  fixture.globalSteps = [fixture.step];
  const res = await GET(request({ kind: 'step' }));
  assert.equal(res.status, 200);
  assert.deepEqual(fixture.lookups, [[undefined, true]]);
  assert.deepEqual(fixture.claims, [stepId]);
});
