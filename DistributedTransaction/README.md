# TLA+ for Distributed Transaction

The module contains a abstract specification of the transaction system implemented in TiKV. The implementation can be found in [TiKV Transaction Module](https://github.com/tikv/tikv/blob/master/src/storage/mvcc/txn.rs).

The module contains two TLA+ files: `DistributedTransaction.tla` and `DistributedTransactionProofs.tla`.

In most cases you will likely have an interest in only `DistributedTransaction.tla`, where the specification and safety invariants are defined. Besides that, in `DistributedTransactionProofs.tla`, there are some formal proofs, which are supposed to be build up gradually (so it's not completed yet), to the safety invariants.

To run the formal proofs in `DistributedTransactionProofs.tla`, you'd like to install the [TLAPS](https://tla.msr-inria.inria.fr/tlaps/content/Download/Binaries.html) (TLA+ Proof System) first. It's not distributed altogether with the TLA toolbox.
