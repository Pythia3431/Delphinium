# CMS Utility Functions <--- Beware, here there be dragons
import struct
import os 
import random

def CreateParityConstraint(indices, is_random, k):
    """ Based on the remaining unconstrained indices and k,
        return a subset of indices which should be XOR'd over
        as a list of integers
        ISRANDOM determines whether to use a strategy which selects in
        expectation K indices but could select more or less
    """
    parity_indices = []
    if k > len(indices):
        raise ValueError("Number of variables in constraint is larger than actual size test")
    if is_random:
        prob_picking_var = min(k/float(len(indices)), 0.5)
        for idx in indices:
            if random.random() <= prob_picking_var:
                parity_indices.append(idx)
    else:
        random.shuffle(indices)
        parity_indices = list(indices[:k])
    return parity_indices


def SingleSizeExperimentXors(size, unknown_positions, num_trials, is_random, k):
    """ Based on the size and unconstrained indices,
        return a list[2][TRIALS][size][K] of integers
        which represent the selection of XORs. In other words:
            for each message (m1, m2)
                for each trial
                    provide size # of K-sized XOR as a list of lists of integers
        additionally, provide a list[2][TRIALS][size] of integers (0 or 1)
        which represent the parity coin-flips for each XOR of size K
        finally, return the random seed used so that this set of XORs and coins
        can be exactly replicated
    """
    seed = struct.unpack("<L", os.urandom(4))[0]
    random.seed(seed)
    xors = []
    coins = []
    indices = list(unknown_positions)
    for _ in range(2):
        msg_xors = []
        msg_coins = []
        for _ in range(num_trials):
            trial_xors = []
            trial_coins = []
            for _ in range(size):
                trial_xors.append(CreateParityConstraint(indices, is_random, k))
                trial_coins.append(random.randint(0,1))
            msg_xors.append(trial_xors)
            msg_coins.append(trial_coins)
        xors.append(msg_xors)
        coins.append(msg_coins)
    return xors, coins, seed
    
