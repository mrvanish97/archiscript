/** Deterministic adapters for adversarial scenarios; not a cloud emulator. */
export class AsphaltError extends Error {
  constructor(code) {
    super(code);
    this.code = code;
  }
}

function requireCondition(ok, code) {
  if (!ok) throw new AsphaltError(code);
}

export class LeaseStore {
  #records = new Map();

  acquire(resource, owner, now, ttl) {
    requireCondition(ttl > 0, 'invalid_ttl');
    const prior = this.#records.get(resource);
    requireCondition(!prior || prior.expiresAt <= now, 'lease_held');
    const lease = { resource, owner, epoch: (prior?.epoch ?? 0) + 1, expiresAt: now + ttl };
    this.#records.set(resource, lease);
    return { ...lease };
  }

  mutate(resource, lease, now, action) {
    const current = this.#records.get(resource);
    requireCondition(current && current.owner === lease.owner &&
      current.epoch === lease.epoch && now < current.expiresAt, 'stale_fence');
    return action();
  }
}

export class CapacityStore {
  #total;
  #reservations = new Map();
  #committed = new Map();

  constructor(total) { this.#total = structuredClone(total); }

  observedFree() {
    const free = { ...this.#total };
    for (const allocation of [...this.#reservations.values(), ...this.#committed.values()]) {
      for (const key of Object.keys(free)) free[key] -= allocation[key] ?? 0;
    }
    return free;
  }

  reserve(id, request) {
    requireCondition(!this.#reservations.has(id) && !this.#committed.has(id), 'duplicate_reservation');
    const free = this.observedFree();
    requireCondition(Object.keys(this.#total).every(key =>
      (request[key] ?? 0) >= 0 && (request[key] ?? 0) <= free[key]), 'capacity_exhausted');
    this.#reservations.set(id, structuredClone(request));
    return id;
  }

  commit(id) {
    const value = this.#reservations.get(id);
    requireCondition(value, 'reservation_missing');
    this.#reservations.delete(id);
    this.#committed.set(id, value);
  }

  release(id) { this.#reservations.delete(id); this.#committed.delete(id); }
}

export function deploymentAdmission(input) {
  const { request, world } = input;
  if (!request.requestId || !request.logicalDeploymentId || !request.attemptId ||
      !request.tenantId || !request.artifactDigest) return 'malformed';
  if (world.deployedDigest === request.artifactDigest) return 'satisfied';
  if (world.currentAttemptId !== request.attemptId) return 'superseded';
  if (world.leaseEpoch !== request.leaseEpoch || world.now >= world.leaseExpiry)
    return 'staleAuthority';
  if (world.approval?.artifactDigest !== request.artifactDigest ||
      world.approval?.policyRevision !== world.policyRevision)
    return 'staleApproval';
  if (world.schemaRevision < request.requiredSchema || !world.rollbackCompatible)
    return 'migrationUnsafe';
  if (request.attemptNumber >= request.maxAttempts || world.retryBudget === 0)
    return 'retryExhausted';
  if (world.now < request.nextRetryAt) return 'retryDelayed';
  if (!world.networkEvidence || world.networkEvidence.topologyRevision !== world.topologyRevision ||
      world.networkEvidence.result !== 'no-path') return 'evidenceUnknown';
  return 'requestReservation';
}

export class DeploymentLedger {
  #current = new Map();
  #history = [];

  start(environment, attemptId) {
    this.#current.set(environment, attemptId);
    this.#history.push({ environment, attemptId, status: 'started' });
  }

  callback(environment, attemptId, status) {
    const prior = this.#history.findLast(row => row.environment === environment &&
      row.attemptId === attemptId);
    if (!prior) return 'unknown-attempt';
    if (prior.status === status) return 'duplicate';
    prior.status = status;
    return this.#current.get(environment) === attemptId ? 'current' : 'historical-only';
  }

  current(environment) { return this.#current.get(environment); }
  history() { return structuredClone(this.#history); }
}

export class IntentOutbox {
  #intents = new Map();
  #events = new Map();
  #provider = new Map();

  commitIntent(operationId, intent) {
    requireCondition(!this.#intents.has(operationId), 'duplicate_operation');
    this.#intents.set(operationId, structuredClone(intent));
    this.#events.set(operationId, { state: 'pending', publishCount: 0 });
  }

  publish(operationId, deliverySucceeded) {
    const event = this.#events.get(operationId);
    requireCondition(event, 'missing_intent');
    event.publishCount++;
    if (deliverySucceeded) event.state = 'delivered';
    return event.state;
  }

  providerCall(operationId, executes, responseLost) {
    requireCondition(this.#intents.has(operationId), 'missing_intent');
    if (executes) this.#provider.set(operationId, 'completed');
    return responseLost ? 'unknown' : (executes ? 'completed' : 'failed');
  }

  reconcileProvider(operationId) { return this.#provider.get(operationId) ?? 'not-observed'; }
  event(operationId) { return structuredClone(this.#events.get(operationId)); }
}

/** A deliberately non-transactional coordinator. Fault injection exposes an
 * orphan reservation between allocation and durable intent creation. */
export class DeploymentCoordinator {
  constructor(capacity, outbox, ledger) {
    this.capacity = capacity;
    this.outbox = outbox;
    this.ledger = ledger;
  }

  begin(input, demand, faultAt = null) {
    const admission = deploymentAdmission(input);
    if (admission !== 'requestReservation') return { state: admission };
    const { logicalDeploymentId, attemptId } = input.request;
    const reservationId = `${logicalDeploymentId}:${attemptId}`;
    this.capacity.reserve(reservationId, demand);
    if (faultAt === 'after-reserve') return { state: 'unknown', reservationId };
    this.outbox.commitIntent(reservationId, {
      tenantId: input.request.tenantId,
      artifactDigest: input.request.artifactDigest,
      attemptId,
    });
    this.ledger.start(input.request.logicalDeploymentId, attemptId);
    return { state: 'intent-committed', reservationId };
  }
}

export function reachable(graph, source, target) {
  const seen = new Set([source]);
  const pending = [source];
  while (pending.length) {
    const node = pending.shift();
    if (node === target) return true;
    for (const next of graph[node] ?? []) {
      if (!seen.has(next)) { seen.add(next); pending.push(next); }
    }
  }
  return false;
}

export class RegionAuthority {
  #generation = 0;
  #holder = null;

  promote(region, observedGeneration) {
    requireCondition(observedGeneration === this.#generation, 'stale_generation');
    this.#generation++;
    this.#holder = region;
    return this.#generation;
  }

  write(region, generation) {
    requireCondition(region === this.#holder && generation === this.#generation, 'not_primary');
  }

  snapshot() { return { region: this.#holder, generation: this.#generation }; }
}

export function rollbackDecision({ oldVersionReadsNewSchema, irreversibleMigration, oldSecretUsable }) {
  if (irreversibleMigration || !oldVersionReadsNewSchema || !oldSecretUsable)
    return 'manual-review';
  return 'rollback-eligible';
}

export function cacheKey(tenantId, serviceId, revision) {
  return JSON.stringify([tenantId, serviceId, revision]);
}

export function effectiveOverride(override, action, now) {
  return Boolean(override?.actor && override.reason && override.incidentId &&
    now < override.expiresAt && override.grants.includes(action));
}

export function replayIdentity(event, mode) {
  if (mode === 'redelivery') return { eventId: event.eventId, attemptId: event.attemptId };
  if (mode === 'new-attempt') return { eventId: event.eventId, attemptId: `${event.attemptId}:replay` };
  throw new AsphaltError('replay_mode_required');
}
