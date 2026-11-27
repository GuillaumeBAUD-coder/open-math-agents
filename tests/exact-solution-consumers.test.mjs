import assert from 'node:assert/strict';
import { registerHooks } from 'node:module';
import test from 'node:test';

const target = {
  id: 'Fixture.target', decl: 'Fixture.target', title: 'Target', kind: 'known',
  source: 'Fixture', fields: [], difficulty: 15, lean: 'theorem target : True',
  file: 'Fixture.lean',
};
const sibling = { ...target, id: 'Fixture.sibling', decl: 'Fixture.sibling', title: 'Sibling' };
const record = {
  problem_id: target.id, handle: 'first-solver', polarity: 'disproof',
  pr_url: 'https://example.test/pull/1', created_at: '2026-01-01T00:00:00Z',
};
const keyPair = await crypto.subtle.generateKey('Ed25519', true, ['sign', 'verify']);
const publicKey = Buffer.from(await crypto.subtle.exportKey('raw', keyPair.publicKey)).toString('base64url');
process.env.CERT_SIGNING_KEY = Buffer.from(await crypto.subtle.exportKey('pkcs8', keyPair.privateKey)).toString('base64');
globalThis.exactSolutionFixture = { target, sibling, record, lookups: [] };

const stubs = {
  'server-only': 'export {};',
  '@/public/certificate-key.json': `export default ${JSON.stringify({ publicKey, keyId: 'fixture' })};`,
  '@/lib/catalog': `const { target, sibling } = globalThis.exactSolutionFixture;
    export const PROBLEMS = [target, sibling], META = {};
    export const getProblem = (id) => PROBLEMS.find((problem) => problem.id === id);
    export const getFull = async (id) => getProblem(id), getFullMany = async () => [];
    export const prizeOf = () => null;
    export const skeleton = () => 'example', statementSkeleton = skeleton;
    export const proofPath = (p) => 'proofs/' + p.id + '.lean';
    export const KIND_LABEL = { known: 'Known' };`,
  '@/lib/d1': "export const upstreamFileFromDb = async () => 'namespace Fixture\\ntheorem target : True := by trivial\\nend Fixture';",
  '@/lib/db': `const f = globalThis.exactSolutionFixture;
    export const getLiveMap = async () => new Map(), getActiveIds = async () => new Set([f.target.id, f.sibling.id]);
    export const getEvents = async () => [], getSteps = getEvents;
    export const getSolution = async (id) => {
      f.lookups.push(id);
      return id === f.target.id ? f.record : null;
    };
    export const getStats = async () => ({ solved: [{ problem_id: f.target.id }] });
    export const getContributions = async () => [{ handle: f.record.handle, share: 1, roles: [] }];`,
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
const { certificateFor, verifySigned } = await import('../lib/cert.ts');
const { buildBrief } = await import('../lib/pack.ts');
hooks.deregister();

test('certificate uses the exact accepted record without the global solved list', async () => {
  const signed = await certificateFor(target.id, 'FIRST-SOLVER');
  assert.equal(signed?.certificate.solvedAt, record.created_at);
  assert.equal(signed.certificate.result, 'disproof');
  assert.equal(await verifySigned(signed), true);
  assert.equal(await certificateFor(sibling.id, 'first-solver'), null);
  assert.deepEqual(globalThis.exactSolutionFixture.lookups.splice(0), [target.id, sibling.id]);
});

test('brief shows exact credit and retains the related target solved label', async () => {
  const solved = await buildBrief(target.id);
  assert.match(solved, /STATUS: ALREADY SOLVED/);
  assert.ok(solved.includes(`Solved by @${record.handle} (${record.pr_url})`));
  const unsolved = await buildBrief(sibling.id);
  assert.doesNotMatch(unsolved, /STATUS: ALREADY SOLVED/);
  assert.ok(unsolved.includes(`${target.id}  · Known · difficulty 15 · SOLVED HERE`));
  assert.deepEqual(globalThis.exactSolutionFixture.lookups.splice(0), [target.id, sibling.id]);
});
