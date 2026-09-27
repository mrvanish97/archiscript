import test from 'node:test';
import assert from 'node:assert/strict';
import {
  AsphaltError, LeaseStore, CapacityStore, DeploymentLedger, IntentOutbox,
  RegionAuthority, deploymentAdmission, reachable, rollbackDecision, cacheKey,
  effectiveOverride, replayIdentity, DeploymentCoordinator,
} from './control-plane.mjs';

const denial = (code) => (error) => error instanceof AsphaltError && error.code === code;

function readyInput() {
  return {
    request: {
      requestId: 'http-1', logicalDeploymentId: 'deploy-20', attemptId: 'attempt-8',
      tenantId: 'tenant-a', artifactDigest: 'sha256:aaa', leaseEpoch: 10,
      requiredSchema: 42, attemptNumber: 1, maxAttempts: 3, nextRetryAt: 0,
    },
    world: {
      deployedDigest: 'sha256:old', currentAttemptId: 'attempt-8',
      leaseEpoch: 10, leaseExpiry: 100, now: 50,
      approval: { artifactDigest: 'sha256:aaa', policyRevision: 7 }, policyRevision: 7,
      schemaRevision: 42, rollbackCompatible: true, retryBudget: 2,
      networkEvidence: { topologyRevision: 3, result: 'no-path' }, topologyRevision: 3,
    },
  };
}

test('AS-001 stale owner loses authority after epoch advances', () => {
  const leases = new LeaseStore();
  const old = leases.acquire('env-prod', 'worker-a', 0, 5);
  const fresh = leases.acquire('env-prod', 'worker-b', 6, 5);
  assert.equal(fresh.epoch, old.epoch + 1);
  assert.throws(() => leases.mutate('env-prod', old, 7, () => 'write'), denial('stale_fence'));
  assert.equal(leases.mutate('env-prod', fresh, 7, () => 'write'), 'write');
});

test('AS-002 late success remains historical after supersession', () => {
  const ledger = new DeploymentLedger();
  ledger.start('prod', 'attempt-8');
  ledger.callback('prod', 'attempt-8', 'failed');
  ledger.start('prod', 'attempt-9');
  ledger.callback('prod', 'attempt-9', 'succeeded');
  assert.equal(ledger.callback('prod', 'attempt-8', 'succeeded'), 'historical-only');
  assert.equal(ledger.current('prod'), 'attempt-9');
});

test('AS-003 HTTP request, logical deployment, and attempt IDs are distinct', () => {
  const input = readyInput();
  const retry = structuredClone(input);
  retry.request.requestId = 'http-2';
  retry.request.attemptId = 'attempt-9';
  retry.world.currentAttemptId = 'attempt-9';
  assert.equal(input.request.logicalDeploymentId, retry.request.logicalDeploymentId);
  assert.notEqual(input.request.requestId, retry.request.requestId);
  assert.notEqual(input.request.attemptId, retry.request.attemptId);
});

test('AS-004 two observed capacity checks do not reserve five IPs from four', () => {
  const capacity = new CapacityStore({ cpu: 8, memory: 16, ips: 4 });
  const firstObservation = capacity.observedFree();
  const secondObservation = capacity.observedFree();
  assert.ok(firstObservation.ips >= 3 && secondObservation.ips >= 2);
  capacity.reserve('deploy-a', { cpu: 2, memory: 4, ips: 3 });
  assert.throws(() => capacity.reserve('deploy-b', { cpu: 2, memory: 4, ips: 2 }),
    denial('capacity_exhausted'));
  capacity.commit('deploy-a');
  assert.equal(capacity.observedFree().ips, 1);
});

test('AS-005 local private database checks miss transitive Internet path', () => {
  const graph = { Internet: ['Application'], Application: ['ProductionDatabase'] };
  const databaseHasPublicIp = false;
  assert.equal(databaseHasPublicIp, false);
  assert.equal(reachable(graph, 'Internet', 'ProductionDatabase'), true);
});

test('AS-006 tenant must be part of a shared cache key', () => {
  assert.notEqual(cacheKey('tenant-a', 'billing', 7), cacheKey('tenant-b', 'billing', 7));
  assert.equal(cacheKey('tenant-a', 'billing', 7), cacheKey('tenant-a', 'billing', 7));
});

test('AS-007 policy changes invalidate digest-bound approval at admission', () => {
  const input = readyInput();
  assert.equal(deploymentAdmission(input), 'requestReservation');
  input.world.policyRevision = 8;
  assert.equal(deploymentAdmission(input), 'staleApproval');
});

test('AS-008 mutable release tag cannot replace approved digest', () => {
  const input = readyInput();
  input.request.artifactDigest = 'sha256:bbb';
  assert.equal(deploymentAdmission(input), 'staleApproval');
});

test('AS-009 stale network analysis cannot authorize changed topology', () => {
  const input = readyInput();
  input.world.topologyRevision = 4;
  assert.equal(deploymentAdmission(input), 'evidenceUnknown');
});

test('AS-010 schema contraction blocks automatic rollback', () => {
  assert.equal(rollbackDecision({ oldVersionReadsNewSchema: false,
    irreversibleMigration: true, oldSecretUsable: true }), 'manual-review');
});

test('AS-011 provider timeout is unknown, not failed', () => {
  const outbox = new IntentOutbox();
  outbox.commitIntent('provider-op-1', { deployment: 'deploy-20' });
  assert.equal(outbox.providerCall('provider-op-1', true, true), 'unknown');
  assert.equal(outbox.reconcileProvider('provider-op-1'), 'completed');
});

test('AS-012 committed intent retains an unpublished event for retry', () => {
  const outbox = new IntentOutbox();
  outbox.commitIntent('deploy-20', { artifactDigest: 'sha256:aaa' });
  assert.equal(outbox.publish('deploy-20', false), 'pending');
  assert.equal(outbox.event('deploy-20').publishCount, 1);
  assert.equal(outbox.publish('deploy-20', true), 'delivered');
  assert.equal(outbox.event('deploy-20').publishCount, 2);
});

test('AS-013 DLQ replay mode must choose idempotency and attempt identities', () => {
  const event = { eventId: 'event-1', attemptId: 'attempt-8' };
  assert.deepEqual(replayIdentity(event, 'redelivery'), event);
  assert.deepEqual(replayIdentity(event, 'new-attempt'),
    { eventId: 'event-1', attemptId: 'attempt-8:replay' });
  assert.throws(() => replayIdentity(event), denial('replay_mode_required'));
});

test('AS-014 split-brain writes require the current region generation', () => {
  const authority = new RegionAuthority();
  const epochA = authority.promote('eu-west', 0);
  const epochB = authority.promote('eu-central', epochA);
  assert.throws(() => authority.write('eu-west', epochA), denial('not_primary'));
  assert.doesNotThrow(() => authority.write('eu-central', epochB));
});

test('AS-015 expired emergency override grants no authority', () => {
  const override = { actor: 'engineer-1', reason: 'incident', incidentId: 'INC-2',
    grants: ['maintenance-window'], expiresAt: 10 };
  assert.equal(effectiveOverride(override, 'maintenance-window', 9), true);
  assert.equal(effectiveOverride(override, 'maintenance-window', 10), false);
  assert.equal(effectiveOverride(override, 'network-isolation', 9), false);
});

test('AS-016 retry eligibility is evaluated against the current world', () => {
  const input = readyInput();
  input.request.nextRetryAt = 70;
  assert.equal(deploymentAdmission(input), 'retryDelayed');
  input.world.now = 80;
  input.world.currentAttemptId = 'attempt-9';
  assert.equal(deploymentAdmission(input), 'superseded');
});

test('AS-017 secret rotation can make rollback unsafe', () => {
  assert.equal(rollbackDecision({ oldVersionReadsNewSchema: true,
    irreversibleMigration: false, oldSecretUsable: false }), 'manual-review');
});

test('AS-018 clock boundary expires the authority', () => {
  const input = readyInput();
  input.world.now = input.world.leaseExpiry;
  assert.equal(deploymentAdmission(input), 'staleAuthority');
});

test('AS-031 crash between reservation and durable intent creates an orphan', () => {
  const capacity = new CapacityStore({ cpu: 4, memory: 8, ips: 4 });
  const outbox = new IntentOutbox();
  const ledger = new DeploymentLedger();
  const coordinator = new DeploymentCoordinator(capacity, outbox, ledger);
  const outcome = coordinator.begin(readyInput(), { cpu: 2, memory: 4, ips: 3 },
    'after-reserve');
  assert.equal(outcome.state, 'unknown');
  assert.equal(capacity.observedFree().ips, 1);
  assert.equal(outbox.event(outcome.reservationId), undefined);
  assert.deepEqual(ledger.history(), []);
});
