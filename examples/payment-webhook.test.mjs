import assert from 'node:assert/strict';
import test from 'node:test';
import { decide, handleWebhook, requestLedgerCommand } from './payment-webhook.mjs';

function observedEffects() {
  const calls = [];
  return {
    calls,
    recordFailure: async (id) => calls.push(['recordFailure', id]),
    recordPayment: async (id) => calls.push(['recordPayment', id]),
    enqueueFulfillment: async (id) => calls.push(['enqueueFulfillment', id]),
  };
}

test('all declared input members map to their checked decisions', () => {
  const cases = [
    [{ eventId: '', status: 'success', alreadyRecorded: false }, 'reject'],
    [{ eventId: 'p1', status: 'pending', alreadyRecorded: false }, 'ignore'],
    [{ eventId: 'p1', status: 'failed', alreadyRecorded: false }, 'recordFailure'],
    [{ eventId: 'p1', status: 'success', alreadyRecorded: false }, 'fulfill'],
    [{ eventId: 'p1', status: 'success', alreadyRecorded: true }, 'acknowledgeDuplicate'],
  ];
  for (const [input, expected] of cases) assert.equal(decide(input), expected);
});

test('duplicate success acknowledges without ledger or queue effects', async () => {
  const effects = observedEffects();
  const decision = await handleWebhook(
    { eventId: 'p1', status: 'success', alreadyRecorded: true }, effects);
  assert.equal(decision, 'acknowledgeDuplicate');
  assert.equal(requestLedgerCommand(decision), null);
  assert.deepEqual(effects.calls, []);
});

test('first success records payment and enqueues fulfillment', async () => {
  const effects = observedEffects();
  const decision = await handleWebhook(
    { eventId: 'p1', status: 'success', alreadyRecorded: false }, effects);
  assert.equal(decision, 'fulfill');
  assert.equal(requestLedgerCommand(decision), 'recordAndQueueFulfillment');
  assert.deepEqual(effects.calls, [
    ['recordPayment', 'p1'], ['enqueueFulfillment', 'p1'],
  ]);
});

test('failed payment requests a failure record', async () => {
  const effects = observedEffects();
  assert.equal(await handleWebhook(
    { eventId: 'p1', status: 'failed', alreadyRecorded: false }, effects), 'recordFailure');
  assert.deepEqual(effects.calls, [['recordFailure', 'p1']]);
});
