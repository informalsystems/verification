**fsPCBoundedBlocking.tla**

PlusCal algorithm that:
 - shows deadlock when queues are bounded and senders block on queue full,
 - is useful to inspect the generated TLA+ code (generate with cmd+T (mac) or ctrl+T (others)).

Run with:
- Constants:
   - MaxQueueSize <- 2
- Invariant:
   - ~NotFilledQueues
- Temporal Formulas:
   - Termination

Note: When running without the invariant, deadlock appears, otherwise invariant is violated

**fsPCBoundedUnblocking.tla**
