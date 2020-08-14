import z3 # I know this is cheating
import random
from math import log, floor, ceil
from itertools import permutations

GRID_WIDTH = 3
GRID_HEIGHT = 3

UNFILLED = 0
word_size = int(floor(log(GRID_WIDTH*GRID_HEIGHT, 2)))+1
square_size = GRID_WIDTH*GRID_HEIGHT*word_size
grid_size = GRID_WIDTH*GRID_HEIGHT*square_size
test_length = grid_size
hasIV = False
isStateful = False

pack_line = lambda s: reduce(lambda a, b: (a << word_size)|b, s, 0)
PERMS = [pack_line(p) for p in permutations(range(1,GRID_WIDTH*GRID_HEIGHT+1))]

class Puzzle:
    def __init__(self):
        grid = []
        for _ in range(GRID_WIDTH): # grid = list of three rows of squares
            grid_row = []
            for _ in range(GRID_HEIGHT): # grid_row = list of three 3x3 squares
                square = []
                for _ in range(GRID_WIDTH): # square = list of three 3x1 rows
                    square_row = []
                    for _ in range(GRID_HEIGHT): # row = list of three values
                        square_row.append(UNFILLED)
                    square.append(square_row)
                grid_row.append(square)
            grid.append(grid_row)
        self.grid = grid

    def pretty(self):
        rows = ["" for _ in range(GRID_HEIGHT*GRID_HEIGHT)]
        for i in range(len(self.grid)):
            grid_row = self.grid[i]
            for square in grid_row:
                for j in range(len(square)):
                    row = square[j]
                    for value in row:
                        s = str(value) if value > 0 else " "
                        rows[GRID_HEIGHT*i + j] += "{} ".format(s)
        return "\n".join(rows)

    def pack(self):
        v = 0
        for grid_row in self.grid:
            for square in grid_row:
                for row in square:
                    for value in row:
                        v <<= word_size
                        v |= value
        return v

    def unpack(self, v):
        for i in range(GRID_WIDTH-1, -1, -1):
            for j in range(GRID_HEIGHT-1, -1, -1):
                for k in range(GRID_WIDTH-1, -1, -1):
                    for l in range(GRID_HEIGHT-1, -1, -1):
                        self.grid[i][j][k][l] = int(v & ((1 << word_size)-1))
                        v >>= word_size

    def check(self):
        correct_set = set([x for x in range(1, GRID_WIDTH*GRID_HEIGHT+1)])
        column_set = [set() for _ in range(GRID_WIDTH*GRID_WIDTH)]
        for grid_row in self.grid:
            row_set = [set() for _ in range(GRID_HEIGHT)]
            for i in range(len(grid_row)):
                square = grid_row[i]
                square_set = set()
                for j in range(len(square)):
                    row = square[j]
                    for l in range(len(row)):
                        value = row[l]
                        if value == UNFILLED:
                            return False
                        square_set.add(value)
                        row_set[j].add(value)
                        column_set[GRID_WIDTH*i + l].add(value)
                if square_set != correct_set:
                    return False
            for s in row_set:
                if s != correct_set:
                    return False
        for s in column_set:
            if s != correct_set:
                return False
        return True

if GRID_WIDTH*GRID_HEIGHT == 9:
    grid = [
            [[[4,9,7],
              [2,6,3],
              [1,5,8]], [[1,6,5],
                         [8,4,9],
                         [7,2,3]], [[3,2,8],
                                    [5,1,7],
                                    [4,6,9]]],
            [[[5,1,2],
              [9,8,6],
              [7,3,4]], [[4,8,7],
                         [3,5,2],
                         [9,1,6]], [[6,9,3],
                                    [1,7,4],
                                    [8,5,2]]],
            [[[8,7,9],
              [6,4,1],
              [3,2,5]], [[5,3,1],
                         [2,9,8],
                         [6,7,4]], [[2,4,6],
                                    [7,3,5],
                                    [9,8,1]]],
    ]
elif GRID_WIDTH*GRID_HEIGHT == 4:
    grid = [
            [[[1,4],
              [3,2]], [[2,3],
                       [4,1]]],
            [[[4,1],
              [2,3]], [[3,2],
                       [1,4]]],
    ]
solved = Puzzle()
from copy import deepcopy
solved.grid = deepcopy(grid)
assert solved.check()
solved.unpack(solved.pack())
assert solved.grid == grid
assert solved.check()

def checkFormat(v):
    puzzle = Puzzle()
    puzzle.unpack(v)
    return 1 if puzzle.check() else 0

def is_perm(solver, v, perms):
    if len(perms) > 1:
        left = perms[:int(ceil(len(perms)/2))]
        right = perms[int(ceil(len(perms)/2)):]
        return solver._or(is_perm(solver,v,left),
                          is_perm(solver,v,right))
    elif len(perms) == 1:
        return solver._eq(v, perms[0])
    else:
        return solver.false()

def get_val(solver, v, i):
    #return (v >> (word_size*(81-i+1))) & ((1 << word_size)-1)
    return solver.extract(v, test_length-word_size*i-1,
                             test_length-word_size*(i+1))

def extract_row(solver, v, row_i):
    vals = []
    start = (GRID_WIDTH*GRID_WIDTH*GRID_HEIGHT)*(int(row_i/GRID_HEIGHT)) + GRID_HEIGHT*(row_i % GRID_WIDTH)
    for i in range(GRID_WIDTH*GRID_HEIGHT):
        x = start+(i%GRID_WIDTH)+GRID_WIDTH*GRID_HEIGHT*int(i/GRID_HEIGHT)
        vals.append(get_val(solver, v, x))
    return z3.Concat(*vals)

def extract_col(solver, v, col_i):
    vals = []
    start = (col_i % GRID_WIDTH) + GRID_WIDTH*GRID_HEIGHT*int(col_i/GRID_WIDTH)
    for i in range(GRID_WIDTH*GRID_HEIGHT):
        x = start+(GRID_WIDTH*(i%GRID_HEIGHT))+GRID_WIDTH*GRID_HEIGHT*GRID_HEIGHT*int(i/GRID_WIDTH)
        vals.append(get_val(solver, v, x))
    return z3.Concat(*vals)

def extract_sq(solver, v, sq_i):
    vals = []
    start = sq_i*GRID_WIDTH*GRID_HEIGHT
    for i  in range(GRID_WIDTH*GRID_HEIGHT):
        x = start+i
        vals.append(get_val(solver, v, x))
    return z3.Concat(*vals)

def checkFormatSMT(v, solver):
    is_valid = solver.true()
    for i in range(GRID_WIDTH*GRID_HEIGHT):
        is_valid = solver._and(is_valid,
                               is_perm(solver, extract_row(solver, v, i), PERMS))
        is_valid = solver._and(is_valid,
                               is_perm(solver, extract_col(solver, v, i), PERMS))
        is_valid = solver._and(is_valid,
                               is_perm(solver, extract_sq(solver, v, i), PERMS))
    return solver._if(is_valid, solver.bvconst(1,2), solver.bvconst(0,2))

def makePaddedMessage():
    return solved.pack()

if __name__ == '__main__':
    puzzle = Puzzle()
