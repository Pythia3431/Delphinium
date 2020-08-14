import formats

format = formats.CURRENT_FORMAT

try:
    mall_size = 2*(format.length_field_size)
except:
    raise Exception("To use truncation, your formats.CURRENT_FORMAT needs to have length implemented")


def maulSMT(msg, trunc, solver):
    length_field_mask = (1 << format.length_field_size)-1
    original_msg_size = msg & length_field_mask
    
    chop_left_bits = solver._rshift(trunc, format.length_field_size)

    chop_right_bits = trunc & length_field_mask
    total_chopped = chop_left_bits + chop_right_bits

    padd_to_msg_length = original_msg_size.size() - total_chopped.size()
    long_chop = solver.extend(total_chopped, padd_to_msg_length)
    new_len = solver._if(solver._ugt(long_chop, original_msg_size), solver.bvconst(0,original_msg_size.size()), original_msg_size - long_chop)

    shift_right = solver.extend(format.length_field_size + chop_right_bits, padd_to_msg_length)

    actual_msg = solver._rshift(msg, shift_right)
    actual_msg = actual_msg & ((1 << new_len)-1)

    return solver._lshift(actual_msg, format.length_field_size) ^ new_len

def maulSMTMsg(msg, trunc, solver): 
    length_field_mask = (1 << format.length_field_size)-1
    original_msg_size = msg & length_field_mask
    
    chop_left_bits = (trunc >> format.length_field_size)

    chop_right_bits = trunc & length_field_mask
    total_chopped = chop_left_bits + chop_right_bits
    new_len = solver._if(solver._ugt(total_chopped, original_msg_size), 0, original_msg_size - total_chopped)

    shift_right = format.length_field_size + chop_right_bits

    actual_msg = solver._rshift(msg, shift_right)
    actual_msg = actual_msg & ((1 << new_len)-1)

    return solver._lshift(actual_msg, format.length_field_size) ^ new_len

def maul(msg, trunc):
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

