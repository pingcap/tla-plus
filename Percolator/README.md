# TLA+ for Percolator

This directory contains the TLA+ specification of Percolator, the transaction protocol of [TiKV](https://github.com/pingcap/tikv).

- [TLA+ specification](Percolator.tla)
- [TLC configuration](Percolator.cfg)
- [TLA+ toolbox configuration](Percolator.toolbox/Percolator___PercolatorModel.launch) 

## How to run in TLA+ toolbox?

- Install [TLA+ toolbox](https://lamport.azurewebsites.net/tla/toolbox.html#installing).
- Install [TLAPS](https://tla.msr-inria.inria.fr/tlaps/content/Download/Binaries.html).
- Import the TLA+ toolbox configuration.

## How to run in command line?

- Download [tla2tools.jar](https://tla.msr-inria.inria.fr/tlatoolbox/dist/tla2tools.jar).
- Install [TLAPS](https://tla.msr-inria.inria.fr/tlaps/content/Download/Binaries.html).
- Execute `java -cp ./tla2tools.jar tlc2.TLC -deadlock -workers 4 Percolator`. `-worker 4` sets the number of worker threads, which should equal to the number of cores on machine.
