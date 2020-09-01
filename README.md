# Delphinium

**Authors:** Gabrielle Beck, Max Zinkus, Matthew D. Green

This code accompanies "Automating the Development of Chosen Ciphertext Attacks"
in Usenix Security 2020.

The full version of the paper can be found
[here](https://eprint.iacr.org/2019/958).

## Running Delphinium

Core Delphinium code can be found in `code/sandbox/`

In order to use Delphinium to attack a format oracle, the following is required:
* A format, implementing the following functions (see `formats/` for examples)
  * `checkFormat`: implementation of the format predicate which takes a
    bitvector in the form of an Int and returns 1 or 0 (for True and False,
    respectively)
  * `checkFormatSMT`: implementation of the format predicate which operates on
    solver bit vector objects. This takes the bit vector solver value
    representing the message, and the solver instance, and returns a solver
    value representing 1 or 0 (for True and False, respectively)
  * `makePaddedMessage`: For testing, the plaintext message being recovered
  * The format file must also contain the following constants:
    * `test_length`: the number of bits in a target message
    * optionally, `num_blocks`: The number of blocks of size `test_length` which
      make up the target message. Specifying `test_length = 128` is equivalent
      to specifying `test_length = 16` and `num_blocks = 8`
* If the format oracle must be reached over a network, a shim such as the one in
  `TLSCBC_For_Network_Test/shim.py` must be provided to abstract the network
  connection, and it must be used in `trimmed_test.py` as it is in
  `TLSCBC_For_Network_Test/tls_cbc.py` to replace calls to the example predicate
  oracle provided in `oracle.py`
  
Then, to run, `NAME=experiment_name python trimmed_test.py`.

`experiment_name` determines where log files are saved and should be unique and human-readable, e.g. `PCKS7_128bits`

Arguments:

Required Arguments:
* `-f --format`: Select which format file to use. e.g. `formats.PKCS7`

Optional Arguments:
* `--valid`: indicates to the solver that the known ciphertext encrypts a
  validly formatted message. Commonly the case, and can improve performance
  dramatically for some formats
* `-t --trials`: Indicates the number of trials (increasing certainly) to be
  used in the underlying `Max#SAT` oracle. Increases malleation string quality
  with diminishing returns (for tested formats) as the cost of increased runtime
* `-p --procs`: The number of cores to use for multiprocessing
* `-w --window`: The number of simultaneous `Max#SAT` tests to run for
  parallelism. Each solver instance receives `procs / window` cores for
  per-solver multithreading, and `window` such number of instances are launched
* `-i --invert`: Begin search at the low-count end of the range rather than the
  high-count. Useful if you know that the format does not admit *any*
  high-quality malleation strings
* `-r --random`: Parameter for underlying `Max#SAT` oracle. Required for
  stronger formal guarantees, but may increase runtime without improving
  practical performance
* `-c --cnf`: as CNF generation can be expensive, CNFs are logged as output in
  `.cnf` files. If re-running with a format, use this option to re-use the
  cached CNF and skip initial regeneration
* `--bootstrap`: If re-running a partially completed experiment, use this option
  to re-input the derived oracle queries and their results from a `.log` file
* `-q --quiet`: Show less output
* `-x --tmp`: Use a non-default `tmp` directory. Useful if you have a fast disk
  and are working with a complex format that may generate CNF files too large
  for the `tmp` filesystemh

## Extra Dependencies
Some of the functionalities provided by the solver class require the installation of [ApproxMC](https://github.com/meelgroup/approxmc). 
