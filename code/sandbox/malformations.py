byte_size = 8
import random
import formats.PKCS7MultBlocks as formats

try:
    LENGTH_SIZE = formats.length_field_size
except:
    LENGTH_SIZE = None

def xor_with_extension(msg,mall):
    """
    XOR where malleation string also has a length field, this is necessary because we are
    trying to support extension: for example, there is a difference between 00001 and 01 that
    we need to be able to capture 
    """
    msg_size = (1 << LENGTH_SIZE)-1
    msg_mask = ((1 << formats.max_msg_size)-1) << LENGTH_SIZE
    return_size = msg & msg_size
    if (mall & msg_size) > (msg & msg_size):
        return_size = mall & msg_size
    actual_msg = msg & msg_mask
    actual_mall = mall & msg_mask
    return (actual_mall ^ actual_msg) | return_size
 

def xor_SMT_with_extension(msg,mall,solver):
    """ 
    Needs to exist for the same reason the previous function 
    needs to exist
    """
    msg_size = (1 << LENGTH_SIZE)-1
    msg_mask = ((1 << formats.max_msg_size)-1) << LENGTH_SIZE
    return_msg = solver._if(solver._ugt(mall & msg_size, msg & msg_size), mall & msg_size, msg & msg_size)
    actual_msg = msg & msg_mask
    actual_mall = mall & msg_mask
    return return_msg | (actual_mall ^ actual_msg)
    
"""
XOR function that is "length field aware" in that it expects a malleation to not include
the length field -- meant to be used with a real valued message and malleation
"""
def xor(msg, mall):
    if LENGTH_SIZE:
        return (mall << LENGTH_SIZE) ^ msg
    else:
        return (msg ^ mall)

"""
XOR function that is "length field aware" in that it expects any symbolic malleation
to be shorter than the length field -- meant to be used with a symbolic message
"""
def xor_SMT(msg, solver, mall, symb_mall=True):
    if not symb_mall:
        return xor(msg, mall)

    if LENGTH_SIZE:
        if type(mall) is int or type(mall) is long:
            return (mall << LENGTH_SIZE) ^ msg
       
        ext_mall = solver.extend(mall, LENGTH_SIZE)
        return (ext_mall << LENGTH_SIZE) ^ msg
    else:
        return msg ^ mall

# for RSA
def multiply(msg,mall, modulus):
    return (msg * mall) % modulus



""" malleation is used with the following:
 1) The iterative solver in add structural constraints
    -> symbolic p, symbolic message
 2) Iterative and final solver
    -> concrete long p, symbolic message
 3) Real message and real truncation
    -> concrete long p, real Message long
"""
def truncate_SMT(msg, trunc, solver, symb_mall=True):
    length_field_mask = (1 << formats.length_field_size)-1
    original_msg_size = msg & length_field_mask
    if symb_mall:
        chop_left_bits = solver._rshift(trunc, formats.length_field_size)
    else:
        chop_left_bits = (trunc >> formats.length_field_size)
    chop_right_bits = trunc & length_field_mask
    total_chopped = chop_left_bits + chop_right_bits

    if symb_mall:
        padd_to_msg_length = original_msg_size.size() - total_chopped.size()
        long_chop = solver.extend(total_chopped, padd_to_msg_length)
        new_len = original_msg_size - long_chop
        shift_right = solver.extend(formats.length_field_size + chop_right_bits, padd_to_msg_length)
    else:
        new_len = original_msg_size - total_chopped
        shift_right = formats.length_field_size + chop_right_bits
    
    
    actual_msg = solver._rshift(msg, shift_right)
    actual_msg = actual_msg & ((1 << new_len)-1)

    return solver._lshift(actual_msg, formats.length_field_size) + new_len

"""
Assumes that the formats.length_field_size aligns with the function included in the 
test file being used. This first function assumes a long msg and a long trunc
"""
def truncate(msg, trunc):
    original_msg_size = msg & ((1 << formats.length_field_size) - 1)
    half_len = formats.length_field_size

    chop_left_bits = trunc >> half_len
    chop_right_bits = trunc & ((1 << half_len) - 1)

    total_chopped = chop_left_bits + chop_right_bits

    new_len = original_msg_size - total_chopped

    actual_msg = msg >> formats.length_field_size
    actual_msg = (actual_msg >> chop_right_bits) & ((1 << new_len)-1)
    return (actual_msg << formats.length_field_size) | new_len

#---------------Helper Functions for CBC Malleations --------------------------------------
"""
Meant to be used with a real valued message to get a block of ciphertext at index idx
"""
def grab_msg_block(msg, idx):
    return (msg >> (idx * formats.test_length + formats.length_field_size)) & ((1 << formats.test_length) - 1)

def grab_mall_block(mall, idx): 
    return (mall >> (idx * formats.test_length)) & ((1 << formats.test_length) - 1)
"""
Mean to be used with a symbolic valued message. Separation of this function is needed because >> is not equivalent to logical right shift
"""
def grab_symb_msg_block(msg,idx, solver):
    return solver.extract(msg, (idx+1)*formats.test_length + formats.length_field_size -1, idx*formats.test_length + formats.length_field_size) 

def grab_symb_mall_block(mall, idx, solver):
    return solver.extract(mall, (idx+1)*formats.test_length -1, idx*formats.test_length)

"""
Meant to create a mask of the form 1111.....0000000...111111 where block_idx corresponds to a block
of the message that should be dropped
"""
def excludeBlockMask(block_idx):
    mask = (1 << ((formats.num_blocks - block_idx - 1) * formats.test_length)) - 1
    mask = mask << ((formats.test_length * (block_idx + 1)) + formats.length_field_size)
    mask = mask | ((1 << ((formats.test_length * block_idx) + formats.length_field_size)) - 1)
    return mask

def trackMaul(block_num): 
    block_mask = (1 << formats.test_length)-1
    return block_mask << (block_num*formats.test_length)

#--------------------------- END HELPER FUNCTIONS ------------------------------------------------------

def CBC_MODE_symb_mall_msg(msg, solver, mall, trunc):
    res = truncate_SMT(msg, trunc, solver)
    mask = solver.bvconst(0, msg.size())
    length = solver.extract(res, formats.length_field_size-1,0)
    # "trash" any block of the msg by 0'ing it out if there is a malleation on that particular block 
    cbc_simulate = True
    res_blocks = [length]
    for block in range(0,formats.num_blocks-1):
        pt_block = grab_symb_msg_block(res, block, solver)
        mall_block = grab_symb_mall_block(mall, block, solver)
        prev_mall_block = grab_symb_mall_block(mall, block+1, solver)
        res_blocks.append(pt_block ^ prev_mall_block)
        # fill out a block saying these bits have been touched 
        mask = solver._if(solver._not(solver._eq(mall_block, 0)), solver._bitwiseor(mask, trackMaul(block)), mask)

    mall_block = grab_symb_mall_block(mall, formats.num_blocks-1, solver)

    mask = solver._if(solver._not(solver._eq(mall_block, 0)), solver._bitwiseor(mask, trackMaul(formats.num_blocks-1)), mask)

    last_highest_block = grab_symb_msg_block(res, formats.num_blocks-1, solver)
    res_blocks.append(last_highest_block)
    res_blocks.reverse()
    
    return (solver.concat(*res_blocks), mask)

def CBC_MODE_symb_msg(msg, solver, mall, trunc):
    res = truncate_SMT(msg, trunc, solver, symb_mall=False)
    mask = solver.bvconst(0, msg.size())
    length = solver.extract(msg,formats.length_field_size-1,0)
    # TODO: you may be able to leave this as not symbolic
    res_blocks = [length]
    for idx in range(0, formats.num_blocks - 1):
        pt_block = grab_symb_msg_block(res, idx, solver)
        mall_block = grab_mall_block(mall, idx)
        prev_mall_block = grab_mall_block(mall, idx + 1)

        if mall_block != 0:
            mask = solver._bitwiseor(mask, trackMaul(idx))

        res_blocks.append(pt_block ^ prev_mall_block)

    mall_block = grab_mall_block(mall, formats.num_blocks-1)
    last_block = grab_symb_msg_block(res, formats.num_blocks-1, solver)
    # different in this function than symbolic malleation
    if mall_block != 0:
        mask = solver._bitwiseor(mask, trackMaul(formats.num_blocks-1))
    
    res_blocks.append(last_block)
    
    res_blocks.reverse()
    return (solver.concat(*res_blocks), mask)

# real message and real malleation
def CBC_MODE(msg, mall, trunc):
    trunc_res = truncate(msg, trunc)
    final_res = trunc_res & ((1 << formats.length_field_size)-1)
    mask = 0
    for idx in range(0, formats.num_blocks-1):
        pt_block = grab_msg_block(trunc_res, idx)
        mall_block = grab_mall_block(mall, idx)
        prev_mall_block = grab_mall_block(mall, idx + 1)  
        final_res = final_res | ((prev_mall_block ^ pt_block) << (formats.test_length * idx + formats.length_field_size))
        if mall_block != 0:
            mask |= trackMaul(idx)
    if grab_msg_block(trunc_res, formats.num_blocks-1) != 0:
        mask |= trackMaul(formats.num_blocks-1)
    add_last_block = grab_msg_block(trunc_res, formats.num_blocks-1) << (formats.test_length * (formats.num_blocks-1) + formats.length_field_size)
    final_res = final_res | add_last_block
    
    return (final_res, mask)

# function needed to validate malleations because some are 
# nonsensical
def CBCMallIsValid(msg, solver, malleation, trunc):
    # enforce that it is impossible to truncate to a size less than the message
    length_mask = (1 << formats.length_field_size)-1

    truncating_len = solver._rshift(trunc,formats.length_field_size)

    truncating_len = truncating_len + (trunc & length_mask)
    stuffing_difference = msg.size() - truncating_len.size()
    truncate_long_bv = solver.extend(truncating_len, stuffing_difference)
    msg_len = msg & length_mask
    checks = solver._ult(truncate_long_bv, msg_len)
    # check added to enforce that malleations cannot be longer than 
    # the message (we are disallowing "extending" a message mainly
    # because it messes with length field size)
    # this will NOT create a weird case where some messages are invalidated
    # because adding the length to the solver will either invalidate all messages or none

    # quick dirty hack
    checks = solver._and(checks, 
        solver._ule(solver.extend(malleation,msg_len.size() - malleation.size()), (1 << (msg_len - truncate_long_bv))-1)
    )

    return checks


def xor_and_truncate(msg, mall, trunc):
    res = truncate(msg, trunc)
    return xor_with_extension(res, mall)

def xor_and_truncateSMT(msg, solver, mall, trunc, symb_mall=True):
    res = truncate_SMT(msg, trunc, solver, symb_mall)
    return xor_SMT_with_extension(res, mall, solver)

def sessionTicketValid(solver, mall, mall_trunc):
    # can't cut from the left
    # actually, disallow truncation altogether until you can 
    # get this working
    mask = (1 << formats.length_field_size) - 1
    return solver._and(
        solver._eq(mall_trunc , 0),
        solver._ule( solver._rshift(mall, formats.length_field_size), (1 << (mall & mask)) - 1)
    )

def all_pass(msg, solver, *malleation):
    return True
