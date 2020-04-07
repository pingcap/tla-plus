# TLA+ for Distributed Transaction

The module contains a abstract specification of the transaction system implemented in TiKV. The implementation can be found in [TiKV Transaction Module](https://github.com/tikv/tikv/blob/master/src/storage/mvcc/txn.rs).

The module contains two TLA+ files: `DistributedTransaction.tla` and `DistributedTransactionProofs.tla`.

In most cases you will only have an interest in `DistributedTransaction.tla`, where the whole specification and safety invariants are defined. Besides that, in `DistributedTransactionProofs.tla`, there are some proofs, which are supposed to be build up gradually, to the safety invariants.

To run formal proofs in `DistributedTransactionProofs.tla`, you'd better install [TLAPS](https://tla.msr-inria.inria.fr/tlaps/content/Download/Binaries.html) (TLA+ Proof System) first. It's not distributed altogether with the TLA toolbox.

