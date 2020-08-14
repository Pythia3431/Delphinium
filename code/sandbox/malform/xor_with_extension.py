import formats

# this should be set by the main executable file
format = formats.CURRENT_FORMAT
mall_size = format.test_length 

def maul(msg,mall):
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

def maulSMT(msg,mall,solver):
    msg_size = (1 << format.length_field_size)-1
    msg_mask = ((1 << format.max_msg_size)-1) << format.length_field_size
    return_size = solver._if(solver._ugt(mall & msg_size, msg & msg_size), mall & msg_size, msg & msg_size)
    actual_msg = msg & msg_mask
    actual_mall = mall & msg_mask
    return return_size | (actual_mall ^ actual_msg)

maulSMTMsg = maulSMT

# this right now is specific to AMAZON TLS Session Tickets
def AddMalleationConstraints(solver, mall_packed, msg_vectors):
    mall = solver.extract(mall_packed, mall_packed.size()-1, 2*format.length_field_size)
    mall_trunc = solver.extract(mall_packed, 2*format.length_field_size-1,0)
    trunc_beg = mall_trunc & ((1 << format.length_field_size)-1)
    trunc_end = solver._rshift(mall_trunc, format.length_field_size)
    mask = (1 << format.length_field_size) - 1
    # extension can only be for values that are not covered by
    # a format check (there is a breakdown in abstraction between extending by pt and extending by ciphertext) 
    return solver._and(solver._eq(solver._mod(trunc_beg, format.block_length), 0),
        solver._ule(trunc_beg + trunc_end, format.TLS_SECRET_SIZE * 8)
    )
