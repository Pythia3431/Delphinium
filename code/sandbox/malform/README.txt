To implement a malformation, the following functions must be implemented:

maul(msg, str)
  msg: an integer representing the bits of the message to be mauled
  str: an integer representing the malleation string
returns an integer representing the bits of the mauled message

maulSMT(msg, str, solver)
  msg: a symbolic solver value representing the message
  str: a symbolic solver value representing the malleation string
  solver: the solver object
returns a symbolic solver value representing the mauled message

maulSMTMsg(msg, str, solver)
  msg: a symbolic solver value representing the message
  str: an integer representing the malleation string
  solver: the solver object
returns a symbolic solver value representing the mauled message

Additional constant that can be defined:
mallBotOutput: (True/False) determines if a malleation can 
possibly leave message in a useless state where any oracle
response is meaningless
