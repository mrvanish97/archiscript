// Companion implementation for the checked PaymentWebhook member mappings.
export function decide(input) {
  if (input.eventId === '') return 'reject';
  if (input.status === 'success') {
    return input.alreadyRecorded ? 'acknowledgeDuplicate' : 'fulfill';
  }
  if (input.status === 'failed') return 'recordFailure';
  return 'ignore';
}

export function requestLedgerCommand(decision) {
  switch (decision) {
    case 'recordFailure': return 'recordFailure';
    case 'fulfill': return 'recordAndQueueFulfillment';
    case 'reject':
    case 'ignore':
    case 'acknowledgeDuplicate': return null;
    default: throw new Error(`Unknown decision: ${decision}`);
  }
}

export async function handleWebhook(input, effects) {
  const decision = decide(input);
  const command = requestLedgerCommand(decision);
  if (command === 'recordFailure') await effects.recordFailure(input.eventId);
  if (command === 'recordAndQueueFulfillment') {
    await effects.recordPayment(input.eventId);
    await effects.enqueueFulfillment(input.eventId);
  }
  return decision;
}
