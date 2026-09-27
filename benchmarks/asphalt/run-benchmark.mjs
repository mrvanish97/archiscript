#!/usr/bin/env node
import { readFileSync } from 'node:fs';
import { dirname, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { spawnSync } from 'node:child_process';

const directory = dirname(fileURLToPath(import.meta.url));
const root = resolve(directory, '../..');
const catalog = JSON.parse(readFileSync(resolve(directory, 'seeded-defects.json'), 'utf8'));
const dimensions = JSON.parse(readFileSync(resolve(directory, 'state-dimensions.json'), 'utf8'));
const testSource = readFileSync(resolve(directory, 'control-plane.test.mjs'), 'utf8');
const leanSource = readFileSync(resolve(root, 'ArchiScriptExamples/Asphalt.lean'), 'utf8');
const testIds = [...testSource.matchAll(/test\('(AS-\d{3}) /g)].map(match => match[1]);
const ids = catalog.cases.map(entry => entry.id);
const branchCountMatch = leanSource.match(/#guard operationRegistry\.branchAddresses\.length == (\d+)/);

function assert(condition, message) { if (!condition) throw new Error(message); }
assert(new Set(ids).size === ids.length, 'duplicate catalog IDs');
assert(new Set(testIds).size === testIds.length, 'duplicate test IDs');
assert(branchCountMatch, 'missing checked canonical branch count');
assert(dimensions.dimensions.every(item => Number.isSafeInteger(item.states) && item.states > 0),
  'invalid state dimensions');
const naiveCartesianCombinations = dimensions.dimensions.reduce((value, item) =>
  value * item.states, 1);
for (const entry of catalog.cases) {
  assert(['executable', 'pending'].includes(entry.fixture), `invalid fixture status: ${entry.id}`);
  assert(Boolean(entry.expected && entry.boundary && entry.oracle), `incomplete oracle: ${entry.id}`);
  assert((entry.fixture === 'executable') === testIds.includes(entry.id),
    `fixture status disagrees with test file: ${entry.id}`);
}

function run(command, args, cwd) {
  const result = spawnSync(command, args, { cwd, encoding: 'utf8', maxBuffer: 8 * 1024 * 1024 });
  if (result.error) throw result.error;
  if (result.status !== 0) {
    process.stderr.write(result.stdout);
    process.stderr.write(result.stderr);
    process.exit(result.status || 1);
  }
}

function exportBoundary() {
  const result = spawnSync('lake', ['env', 'lean', '--run',
    'scripts/export-asphalt-boundary.lean'],
  { cwd: root, encoding: 'utf8', maxBuffer: 8 * 1024 * 1024 });
  if (result.error) throw result.error;
  if (result.status !== 0) {
    process.stderr.write(result.stdout);
    process.stderr.write(result.stderr);
    process.exit(result.status || 1);
  }
  return JSON.parse(result.stdout);
}

const started = performance.now();
run('lake', ['build', 'ArchiScriptExamples.Asphalt'], root);
const boundary = exportBoundary();
assert(boundary.admissionCarrierOrigin === 'trusted-external-root',
  'Asphalt admission origin must remain explicitly trusted');
assert(boundary.naturalCountCarrierOrigin === 'derived-contract',
  'Asphalt count narrowing must remain a checked modeled contract');
assert(boundary.naturalCountUpstreamOrigin === 'trusted-external-root',
  'derived count carrier must retain upstream origin');
assert(boundary.opaqueSupportingSubdomains.includes('externalScanPasses'),
  'opaque scan semantics must remain visible');
const leanMs = Math.round(performance.now() - started);
run('node', ['--test', resolve(directory, 'control-plane.test.mjs')], root);
const totalMs = Math.round(performance.now() - started);

process.stdout.write(`${JSON.stringify({
  benchmark: 'Project Asphalt',
  checkedLeanSlice: true,
  fixtureTestsPassed: testIds.length,
  catalogCases: ids.length,
  pendingCases: ids.length - testIds.length,
  checkedCanonicalBranches: Number(branchCountMatch[1]),
  carrierOrigins: {
    admission: boundary.admissionCarrierOrigin,
    naturalCount: boundary.naturalCountCarrierOrigin,
    naturalCountUpstream: boundary.naturalCountUpstreamOrigin,
  },
  opaqueSubdomainWarnings: boundary.opaqueSupportingSubdomains,
  naiveCartesianCombinations,
  comparisonArmsRun: 0,
  productionSafetyClaims: 0,
  leanBuildMs: leanMs,
  totalMs,
}, null, 2)}\n`);
