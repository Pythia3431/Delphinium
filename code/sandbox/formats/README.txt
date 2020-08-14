In order to implement a format check, the following functions must be defined:

makePaddedMessage()
returns an integer representing a validly formatted message plaintext

checkFormat(msg)
  msg: an integer representing the bits of a message plaintext
returns a boolean representing the validity of the message

checkFormatSMT(msg, solver)
  msg: a symbolic solver value representing a message
  solver: the solver object
returns a boolean solver expression representing the validity of the message

Additionally the following constants must be defined:

test_length: the integer size in bits of the plaintext to be uncovered
hasIV: specifies whether or not there is IV information the attacker
has access to

Optionally, the following constants can be defined:

num_blocks: the multiple of test_length required to expand to the entire
plaintext to be uncovered. Usually used with block ciphers, where test_length is
set to be the width of a single block and num_blocks is used to define the
number of blocks of ciphertext being attacked

