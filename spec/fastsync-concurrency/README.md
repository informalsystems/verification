# Fastsync Concurrency

The TLA+ specifications in this directory model the concurrent communication between the various Fastsync routines and the peers.
 There are four routines: 
   - *receive routine*, that receives messages from peers and forwards them to 
     the demux routine,
   - *demux routine*, which forwards messages between the peers, and the schedule and process routines,
   - *schedule routine*, and 
   - *process routine*.

The routines and peers communicate via buffers. A buffer is a sequence of 
 messages. Initially, each buffer is empty. 
 
 A routine `r` sends a message to a routine `s` by appending the message to
 the buffer `rToS`. A routine s receives a message from a buffer `rToS` by 
 writing the message at the head of the buffer `rToS` to the 
 variable 
 `sInboundMsg`. Initially, the value of `sInboundMsg` is `noMsg`, denoting the empty message, for every 
 routine `s`.

Two different TLA+ specifications capture two different 
scenarios in the concurrent communication in Fastsync:
  1. [FastsyncConcurrencyBoundedBlocking.tla](FastsyncConcurrencyBoundedBlocking.tla), where all buffers are *bounded and blocking*;
  2. [FastsyncConcurrency.tla](FastsyncConcurrency.tla), where:
      - the buffers incoming to the demux routine are *bounded and blocking*, 
      - the buffers outgoing from the demux routine to the peers are *bounded and blocking with a timeout*,
      - the remaining buffers are *unbounded*.

For both specifications, we express two invariants:
 - `TypeOK`, a type invariant
 - `GoodState`, an invariant that expresses that:
   1. if a bounded and blocking buffer `rToS`, incoming to a routine `s`, is full, then the routine's inbound message `sInboundMsg` is equal to `noMsg`,
   2. if the inbound message `rInboundMsg` of routine `r` is 
   different than `noMsg`, and it should be forwarded to a routine `s` via a bounded and blocking buffer `rToS`, then 
   the buffer `rToS` is not full.

The TLA+ specification [FastsyncConcurrencyBoundedBlocking.tla](FastsyncConcurrencyBoundedBlocking.tla) violates the invariant `GoodState`: a state where all bounded and blocking buffers are full, and all inbound messages are different than `noMsg` is reachable even in the case with only one peer, where the length of the buffers (defined by the constant `BufferMaxLen`) is 1. 

The TLA+ specification [FastsyncConcurrencyBoundedBlocking.tla](FastsyncConcurrency.tla) captures the concurrent commuication scenario currently implemented in the [reference Go code](https://github.com/tendermint/tendermint/tree/master/blockchain/v2). 
As in this case, we need to deal with unbounded queues, in order to be able to run TLC, we bound the length of the unbounded queues using the constant `UnboundedBufferMaxLen`.
The length of the bounded queues is given by the constant `BoundedBufferMaxLen`, and we assume that 
`BoundedBufferMaxLen <= UnboundedBufferMaxLen`.

To import the specifications in the TLA+ toolbox and run TLC:
- add the specification `FastsyncConcurrencyBoundedBlocking.tla` or `FastsyncConcurrency.tla` in TLA+ toolbox
- create a model
- assign values to the constants 
- choose "Temporal formula" as the behavior spec, and use the formula `Spec`
- add the invariant `Inv` (a conjunction of all the defined invariants)
- run TLC on the model  