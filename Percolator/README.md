# TLA+ for Percolator

This directory contains the TLA+ specification of Percolator, the transaction protocol of [TiKV](https://github.com/pingcap/tikv).

- [TLA+ specification](Percolator.tla)
- [TLC configuration](Percolator.cfg)
- [TLA+ toolbox configuration](Percolator.toolbox/Percolator___PercolatorModel.launch) 

## How to run in TLA+ toolbox?

- Install [TLA+ toolbox](https://lamport.azurewebsites.net/tla/toolbox.html#installing).
- Install [TLAPS](https://tla.msr-inria.inria.fr/tlaps/content/Download/Binaries.html).
- Import the TLA+ toolbox configuration.

Note TLAPS is optional. You can remove all TLAPS proof, it does not affect the model.
