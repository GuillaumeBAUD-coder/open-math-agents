import assert from 'node:assert/strict';
import { registerHooks } from 'node:module';
import test from 'node:test';

const parent = {
  id: 'Example.theorem', decl: 'Example.theorem', title: 'Example', kind: 'known',
  source: 'Example', fields: [], difficulty: 15, lean: 'theorem example : True', file: '',
};
const step = {
  id: `${parent.id}.R1.H2`, parent: parent.id, k: 2, points: 1,
  reduction: `${parent.id}.R1`, module: 'OMAReductions.R_Example_theorem_R1',
  statement: 'True', reduction_by: 'fixture', reduction_pr: 'https://example.test/reduction',
  solved: false,
};

const stubs = {
  'server-only': 'export {};',
  '@/lib/catalog': `export const PROBLEMS = [], META = {};
    export const getFull = async (id) => id === globalThis.briefFixture.parent.id ? globalThis.briefFixture.parent : undefined;
    export const getProblem = getFull;
    export const getFullMany = async () => [];
    export const prizeOf = () => null;
    export const skeleton = () => 'example', statementSkeleton = skeleton;
    export const proofPath = (problem) => 'proofs/' + problem.id + '.lean';
    export const KIND_LABEL = { known: 'Known' };`,
  '@/lib/d1': 'export const upstreamFileFromDb = async () => null;',
  '@/lib/db': `export const getEvents = async () => [], getSolved = getEvents;
    export const getLiveMap = async () => new Map();
    export const getActiveIds = async () => new Set([globalThis.briefFixture.parent.id]);
    export const getSteps = async (id) => {
      const { step, lookups } = globalThis.briefFixture;
      lookups.push(id);
      return id === step.id || id === step.parent ? [step] : [];
    };`,
  '@/lib/points': 'export const pointsFor = () => 1;',
  '@/lib/site': "export const SITE = 'https://example.test', REPO = 'example/example';",
};
const hooks = registerHooks({
  resolve(specifier, context, nextResolve) {
    if (specifier === '@/lib/steps') {
      return nextResolve(new URL('../lib/steps.ts', import.meta.url).href, context);
    }
    if (Object.hasOwn(stubs, specifier)) {
      return { shortCircuit: true, url: `data:text/javascript,${encodeURIComponent(stubs[specifier])}` };
    }
    return nextResolve(specifier, context);
  },
});
const { buildBrief } = await import('../lib/pack.ts');
hooks.deregister();

test('a step brief works when the global step list is unavailable', async () => {
  const fixture = { parent, step, lookups: [] };
  globalThis.briefFixture = fixture;
  const brief = await buildBrief(step.id);
  assert.ok(brief?.includes(`LEFT TO SOLVE · AGENT BRIEF · ${step.id}`));
  assert.ok(brief.includes(`def H2 : Prop :=\n  ${step.statement}`));
  assert.deepEqual(fixture.lookups, [step.id]);
});

test('a parent brief still lists its direct steps', async () => {
  const fixture = { parent, step, lookups: [] };
  globalThis.briefFixture = fixture;
  const brief = await buildBrief(parent.id);
  assert.ok(brief?.includes(`${step.id} (open)`));
  assert.deepEqual(fixture.lookups, [parent.id]);
});
