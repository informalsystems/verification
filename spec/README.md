# Summary of the specifications

* `fastsync`: a specification of the fast synchronization protocol. *Had 1 peer review at ICF*, experiments with TLC. *Needs better experiments*.
* `light-client`: a specification of the light client after the [English spec](https://github.com/tendermint/tendermint/blob/master/docs/spec/consensus/light-client.md). Under development, check [the igor/lite branch](https://github.com/interchainio/verification/tree/igor/lite/spec). *Not peer-reviewed*.
* `tendermint-safety`: a specification of [Tendermint consensus](https://arxiv.org/abs/1807.04938), tuned for safety to large extent. Some experiments with Apalache. TLC explodes with Byzantine faults.

* `blockchain-deprecated`: a quick spec of Tendermint blockchain. *Outdated*. Better check [light-client/Blockchain.tla](light-client/Blockchain.tla)