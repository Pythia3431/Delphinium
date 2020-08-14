# extra constraints --- come from modeling different
# attackers amount of information 
import formats

def AddIVKnowledge(final_solver, iterative_solver, m1_arr, m2_arr, fm, realM, numTrials):
    # Specific to Block Cipher Modes with a known IV    
    realMsgLength = realM & ((1 << formats.CURRENT_FORMAT.length_field_size) - 1)
    number_blocks = realMsgLength // formats.CURRENT_FORMAT.block_length
    realMsgIV = (realM >> ((number_blocks-1)*formats.CURRENT_FORMAT.block_length + formats.CURRENT_FORMAT.length_field_size))
    if not final_solver is None:
        final_solver.add(final_solver._eq(final_solver.extract(fm, formats.CURRENT_FORMAT.test_length-1, (number_blocks - 1) * formats.CURRENT_FORMAT.block_length + formats.CURRENT_FORMAT.length_field_size), realMsgIV))
    for i in range(numTrials):
        iterative_solver.add(
            iterative_solver._eq(iterative_solver.extract(m1_arr[i], formats.CURRENT_FORMAT.test_length-1, (number_blocks-1)*formats.CURRENT_FORMAT.block_length + formats.CURRENT_FORMAT.length_field_size), realMsgIV),
        )
        iterative_solver.add(
            iterative_solver._eq(iterative_solver.extract(m2_arr[i], formats.CURRENT_FORMAT.test_length-1, (number_blocks-1)*formats.CURRENT_FORMAT.block_length + formats.CURRENT_FORMAT.length_field_size), realMsgIV), 
        )
    return

def AddLengthKnowledge(final_solver, iterative_solver, m1_arr, m2_arr, fm, realM, numTrials):
    """ Add extra constraints corresponding to knowledge an attacker would
        have about the real message, this is formats.CURRENT_FORMAT and malleation dependent
    """
    try:
        print("Trying to add attacker knowledge...") 
        realMsgLength = realM & ((1 << formats.CURRENT_FORMAT.length_field_size) - 1)
        print("Length of the message is {}".format(realMsgLength))
        if not final_solver is None:
            final_solver.add(
                final_solver._eq(final_solver.extract(fm, formats.CURRENT_FORMAT.length_field_size-1, 0), realMsgLength)
            )
        for i in range(numTrials):
            iterative_solver.add(
                iterative_solver._eq(iterative_solver.extract(m1_arr[i], formats.CURRENT_FORMAT.length_field_size-1,0), realMsgLength)
            )
            iterative_solver.add(
                iterative_solver._eq(iterative_solver.extract(m2_arr[i], formats.CURRENT_FORMAT.length_field_size-1,0), realMsgLength)
            )
    except:
        print("Exception occurred while trying to inform solver of formats.CURRENT_FORMAT length")
        return
