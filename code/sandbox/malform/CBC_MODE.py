import truncate

import formats
format = formats.CURRENT_FORMAT
mall_size = (format.length_field_size*2) + format.test_length
mallBotOutput = True
#---------------------- Helper Functions for CBC Malleations --------------------------------------
"""
Meant to be used with a real valued message to get a block of ciphertext at index idx
"""
def grab_msg_block(msg, idx):
    return (msg >> (idx * format.block_length + format.length_field_size)) & ((1 << format.block_length) - 1)

def grab_mall_block(mall, idx):
    return (mall >> (idx * format.block_length)) & ((1 << format.block_length) - 1)
"""
Mean to be used with a symbolic valued message. Separation of this function is needed because >> is not equivalent to logical right shift
"""
def grab_symb_msg_block(msg,idx, solver):
    return solver.extract(msg, (idx+1)*format.block_length + format.length_field_size -1, idx*format.block_length + format.length_field_size)

def grab_symb_mall_block(mall, idx, solver):
    return solver.extract(mall, (idx+1)*format.block_length -1, idx*format.block_length)

"""
Meant to create a mask of the form 1111.....0000000...111111 where block_idx corresponds to a block
of the message that should be dropped
"""
def excludeBlockMask(block_idx):
    mask = (1 << ((format.num_blocks - block_idx - 1) * format.block_length)) - 1
    mask = mask << ((format.block_length * (block_idx + 1)) + format.length_field_size)
    mask = mask | ((1 << ((format.block_length * block_idx) + format.length_field_size)) - 1)
    return mask

def trackMaul(block_num):
    block_mask = (1 << format.block_length)-1
    return block_mask << (block_num*format.block_length)

#--------------------------- END HELPER FUNCTIONS ------------------------------------------------------

def maulSMT(msg, packed_mall, solver):
    trunc = solver.extract(packed_mall, 2*format.length_field_size-1,0)
    mall = solver.extract(packed_mall, packed_mall.size()-1, 2*format.length_field_size)
    res = truncate.maulSMT(msg, trunc, solver)
    mask = solver.bvconst(0, msg.size())
    length = solver.extract(res, format.length_field_size-1,0)
    # "trash" any block of the msg by 0'ing it out if there is a malleation on that particular block 
    cbc_simulate = True
    res_blocks = [length]
    for block in range(0,format.num_blocks-1):
        pt_block = grab_symb_msg_block(res, block, solver)
        mall_block = grab_symb_mall_block(mall, block, solver)
        prev_mall_block = grab_symb_mall_block(mall, block+1, solver)
        res_blocks.append(pt_block ^ prev_mall_block)
        # fill out a block saying these bits have been touched 
        mask = solver._if(solver._not(solver._eq(mall_block, 0)), solver._bitwiseor(mask, trackMaul(block)), mask)

    mall_block = grab_symb_mall_block(mall, format.num_blocks-1, solver)

    mask = solver._if(solver._not(solver._eq(mall_block, 0)), solver._bitwiseor(mask, trackMaul(format.num_blocks-1)), mask)

    last_highest_block = grab_symb_msg_block(res, format.num_blocks-1, solver)
    res_blocks.append(last_highest_block)
    res_blocks.reverse()

    return (solver.concat(*res_blocks), mask)

def maulSMTMsg(msg, packed_mall, solver):
    trunc = packed_mall & ((1 << (2* format.length_field_size))-1)
    mall = packed_mall >> (2 * format.length_field_size)
    res = truncate.maulSMTMsg(msg, trunc, solver)
    mask = solver.bvconst(0, msg.size())
    length = solver.extract(msg,format.length_field_size-1,0)
    res_blocks = [length]
    for idx in range(0, format.num_blocks - 1):
        pt_block = grab_symb_msg_block(res, idx, solver)
        mall_block = grab_mall_block(mall, idx)
        prev_mall_block = grab_mall_block(mall, idx + 1)

        if mall_block != 0:
            mask = solver._bitwiseor(mask, trackMaul(idx))

        res_blocks.append(pt_block ^ prev_mall_block)

    mall_block = grab_mall_block(mall, format.num_blocks-1)

    last_block = grab_symb_msg_block(res, format.num_blocks-1, solver)
    # different in this function than symbolic malleation
    if mall_block != 0:
        mask = solver._bitwiseor(mask, trackMaul(format.num_blocks-1))

    res_blocks.append(last_block)

    res_blocks.reverse()
    return (solver.concat(*res_blocks), mask)

# real message and real malleation
def maul(msg, packed_mall):
    trunc = packed_mall & ((1 << (2* format.length_field_size))-1)
    mall = packed_mall >> (2 * format.length_field_size)
    trunc_res = truncate.maul(msg, trunc)
    final_res = trunc_res & ((1 << format.length_field_size)-1)
    mask = 0
    for idx in range(0, format.num_blocks-1):
        pt_block = grab_msg_block(trunc_res, idx)
        mall_block = grab_mall_block(mall, idx)
        prev_mall_block = grab_mall_block(mall, idx + 1)
        final_res = final_res | ((prev_mall_block ^ pt_block) << (format.block_length * idx + format.length_field_size))
        if mall_block != 0:
            mask |= trackMaul(idx)
    if grab_msg_block(trunc_res, format.num_blocks-1) != 0:
        mask |= trackMaul(format.num_blocks-1)
    add_last_block = grab_msg_block(trunc_res, format.num_blocks-1) << (format.block_length * (format.num_blocks-1) + format.length_field_size)
    final_res = final_res | add_last_block

    return (final_res, mask)

def SinglePerMessageConstr(solver, msg, packed_mall):
    trunc = solver.extract(packed_mall, 2*format.length_field_size-1,0)
    malleation = solver.extract(packed_mall, packed_mall.size()-1, 2*format.length_field_size)

    # enforce that it is impossible to truncate to a size less than the message
    length_mask = (1 << format.length_field_size)-1

    truncate_right = solver._rshift(trunc,format.length_field_size)

    truncate_left = trunc & length_mask
    truncating_len = truncate_right + truncate_left
    stuffing_difference = msg.size() - truncating_len.size()
    truncate_long_bv = solver.extend(truncating_len, stuffing_difference)
    msg_len = msg & length_mask
    checks = solver._ult(truncate_long_bv, msg_len)
    # needed to ensure solver knows that it can only truncate off in block size amounts
    checks = solver._and(checks, solver._eq(solver._mod(truncate_right,format.block_length),0))
    checks = solver._and(checks, solver._eq(solver._mod(truncate_left,format.block_length),0))
    # check added to enforce that malleations cannot be longer than 
    # the message (we are disallowing extending a message for CBC)
    checks = solver._and(checks,
        solver._ule(solver.extend(malleation,msg_len.size() - malleation.size()), (1 << (msg_len - truncate_long_bv))-1)
    )

    return checks

def AddMalleationConstraints(solver, packed_mall, msg_vector):
    all_constr = solver.true()
    for msg in msg_vector:
        all_constr = solver._and(all_constr, SinglePerMessageConstr(solver, msg, packed_mall))
    solver.add(all_constr)
    return

