import formats

# this should be set by the main executable file
format = formats.CURRENT_FORMAT

def xor_with_extension(msg,mall):
    """
    XOR where malleation string also has a length field, this is necessary because we are
    trying to support extension: for example, there is a difference between 00001 and 01 that
    we need to be able to capture 
    """
    msg_size = (1 << format.length_field_size)-1
    msg_mask = ((1 << format.max_msg_size)-1) << format.length_field_size
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
    msg_size = (1 << format.length_field_size)-1
    msg_mask = ((1 << format.max_msg_size)-1) << format.length_field_size
    return_size = solver._if(solver._ugt(mall & msg_size, msg & msg_size), mall & msg_size, msg & msg_size)
    actual_msg = msg & msg_mask
    actual_mall = mall & msg_mask
    return return_size | (actual_mall ^ actual_msg)
    
"""
XOR function for a real valued message and malleation
"""
def xor(msg, mall):
    return (msg ^ mall)

"""
XOR function for some combination of a symbolic message with a real or symbolic malleation. Even though this equivalent to previous XOR this is necessary because of the function signature that the MalleationOracle expects
"""
def xor_SMT(msg, solver, mall, symb_mall=True):
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
    -> concrete long p, real long message
"""
def truncate_SMT(msg, trunc, solver, symb_mall=True):
    length_field_mask = (1 << format.length_field_size)-1
    original_msg_size = msg & length_field_mask
    if symb_mall:
        chop_left_bits = solver._rshift(trunc, format.length_field_size)
    else:
        chop_left_bits = (trunc >> format.length_field_size)
    chop_right_bits = trunc & length_field_mask
    total_chopped = chop_left_bits + chop_right_bits

    if symb_mall:
        padd_to_msg_length = original_msg_size.size() - total_chopped.size()
        long_chop = solver.extend(total_chopped, padd_to_msg_length)
        new_len = original_msg_size - long_chop
        shift_right = solver.extend(format.length_field_size + chop_right_bits, padd_to_msg_length)
    else:
        new_len = original_msg_size - total_chopped
        shift_right = format.length_field_size + chop_right_bits
    
     
    actual_msg = solver._rshift(msg, shift_right)
    actual_msg = actual_msg & ((1 << new_len)-1)

    return solver._lshift(actual_msg, format.length_field_size) ^ new_len

"""
Assumes that msg has length field as long as format.length_field_size and that trunc is of length 2*format.length_field_size where trunc is formatted as high order bits [amount to cut from high | amount to cut from low ] low order bits 
"""
def truncate(msg, trunc):
    original_msg_size = msg & ((1 << format.length_field_size) - 1)
    half_len = format.length_field_size

    chop_left_bits = trunc >> half_len
    chop_right_bits = trunc & ((1 << half_len) - 1)

    total_chopped = chop_left_bits + chop_right_bits

    new_len = original_msg_size - total_chopped

    actual_msg = msg >> format.length_field_size
    if chop_right_bits < 0 or new_len < 0:
        raise ValueError("Truncating by a negative value is disallowed, left truncation was {} and right truncation was {}".format(chop_left_bits, chop_right_bits))
    actual_msg = (actual_msg >> chop_right_bits) & ((1 << new_len)-1)
    return (actual_msg << format.length_field_size) | new_len


def xor_and_truncate(msg, mall_packed):
    trunc = mall_packed & ((1 << (2*format.length_field_size))-1) 
    mall = mall_packed >> 2*format.length_field_size
    res = truncate(msg, trunc)
    return xor(res, mall)

def xor_and_truncateSMT(msg, solver, mall_packed):
    trunc = solver.extract(mall_packed, 2*format.length_field_size -1, 0)
    mall = solver.extract(mall_packed, mall_packed.size()-1, 2*format.length_field_size)
    res = truncate_SMT(msg, trunc, solver, True)
    return xor_SMT(res, solver, mall)

def xor_and_truncateSMTMsg(msg, solver, mall_packed):
    trunc = mall_packed & ((1 << (2*format.length_field_size))-1) 
    mall = mall_packed >> 2*format.length_field_size
    res = truncate_SMT(msg, trunc, solver, False)
    return xor_SMT(res, solver, mall)


def gcm_mall(msg, mall_packed):
    mall =  mall_packed >> (2 * format.length_field_size)
    trunc = mall_packed & ((1 << (2*format.length_field_size))-1)
    msg_truncated = truncate(msg, trunc)
    final_msg = xor_with_extension(msg_truncated, mall)
    return final_msg

def gcm_mallSymbMsg(msg, solver, mall_packed):
    mall =  mall_packed >> (2 * format.length_field_size)
    trunc = mall_packed & ((1 << (2*format.length_field_size))-1)
    msg_truncated = truncate_SMT(msg, trunc, solver, False)
    return xor_SMT_with_extension(msg_truncated, mall, solver)

def gcm_mallSymbMsgSymbMall(msg, solver, mall_packed):
    mall =  solver.extract(mall_packed, mall_packed.size()-1, 2 * format.length_field_size) 
    trunc = solver.extract(mall_packed, 2 * format.length_field_size-1, 0)
    msg_trunc = truncate_SMT(msg, trunc, solver)
    return xor_SMT_with_extension(msg_trunc, mall, solver)

def CheckExtensionBySafeValue(solver, mall_packed):
    mall = solver.extract(mall_packed, mall_packed.size()-1, 2*format.length_field_size)
    mall_trunc = solver.extract(mall_packed, 2*format.length_field_size-1,0)
    trunc_beg = mall_trunc & ((1 << format.length_field_size)-1) 
    trunc_end = solver._rshift(mall_trunc, format.length_field_size)
    mask = (1 << format.length_field_size) - 1
    # extension can only be for values that are not covered by
    # a format check (there is a breakdown in abstraction between extending by pt and extending by ciphertext) 
    return solver._and(
        solver._eq(solver._mod(trunc_beg, block_size), 0),
        solver._ule(trunc_beg + trunc_end, format.TLS_SECRET_SIZE * 8)
    )
 
def xor_and_trunc_valid(solver, mall_packed):
    trunc = solver.extract(mall_packed, 2*format.length_field_size -1, 0)
    trunc_beg = trunc & ((1 << format.length_field_size)-1)
    mall = solver.extract(mall_packed, mall_packed.size()-1, 2*format.length_field_size)
    return solver._and(
        solver._eq(solver.extract(mall, format.length_field_size-1, 0), 0),
        # allow updating the IV for ctr/gcm/cbc mode
        solver._eq(solver._mod(trunc_beg, block_size), 0)
    )   

def xor_trunc_per_msg(solver, msg, mall_packed):
    # after you truncate, the malleation should not extend the message 
    trunc = solver.extract(mall_packed, 2*format.length_field_size -1, 0)
    trunc_end = solver.extract(trunc, 2*format.length_field_size -1, format.length_field_size) 
    trunc_beg = solver.extract(trunc, format.length_field_size-1, 0) 
    mall = solver.extract(mall_packed, mall_packed.size()-1, 2*format.length_field_size)
    msg_len = solver.extract(msg, format.length_field_size-1,0)
    max_mall_length = solver.extend(msg_len - (trunc_beg+trunc_end),mall.size() - msg_len.size())
    return solver._ule(mall, (1 << max_mall_length)-1)

# supports extension
GCM_MALLS = [gcm_mall, gcm_mallSymbMsg, gcm_mallSymbMsgSymbMall]

# basic
XOR_MALLS = [xor, xor_SMT, xor_SMT]

# support xor'ing followed by truncation -- no extending
XOR_AND_TRUNC_MALLS = [xor_and_truncate, xor_and_truncateSMTMsg, xor_and_truncateSMT]

