README
======

The Vienna Verification Toolkit (*vvt* for short) is a collection of
libraries and tools for the verification of LLVM code.

Installation
------------

You need the following dependencies:

* smtlib2: From https://github.com/hguenther/smtlib2.git
  Install with "cabal install".
  You also need to install the following sub-packages:
  * **smtlib2-debug**, in "backends/debug"
  * **smtlib2-timing**, in "backends/timing"
  * **smtlib2-pipe**, in "backends/pipe"
  * **smtlib2-emulated-modulus**, in "extras/modulus-emulator"
    
* bindings-llvm: From https://github.com/hguenther/bindings-llvm.git
  Install with "cabal install".
  Make sure that your *llvm-config*-binary has version 3.5.

After installing those dependencies, you can install the toolkit using

	cabal install
