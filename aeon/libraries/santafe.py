import random

from .annotation import aefunction, aedocumentation
from aeon.libraries.list import *
from aeon.libraries.pair import *

''' Santa fe trail native binds in Aeon to Python '''
size = 10


@aefunction(f"""type BoundedInt as {{x:Integer | x >= 0 && x <= {size}}}""", None)
class BoundedInt(object):
    def __init__(self):
        pass

@aefunction(f"""type Grid {{
    grid : List[Pair[BoundedInt, BoundedInt]];
    {{food:Integer | food >= 0 && food <= ({size} * {size})}};
    position : Pair[BoundedInt, BoundedInt];
}}""", None)
class Grid(object):
    def __init__(self, grid, food, position):
        self.grid = grid
        self.food = food
        self.position = position
        
# Create grid
@aefunction(f'create_grid({{food:Integer | food >= 0 && food <= ({size} * {size})}}) -> {{g:Grid | g.food == food}} = native;', lambda x : create_grid(x))
def create_grid(food):
    position = create_pair(0, 0)
    grid = random_grid(food, 10, 10)
    return Grid(grid, food, position)


# Ugly code
def random_grid(food, size_x, size_y):
    def move_x(x):
        options = list()
        if x - 1 >= 0:
            options.append(x - 1)
        if x + 1 < size_x:
            options.append(x + 1)
        return random.choice(options)
    def move_y(y):
        options = list()
        if y - 1 >= 0:
            options.append(y - 1)
        if y + 1 < size_y:
            options.append(y + 1)
        return random.choice(options)
    def has_food_around(x, y, result):
        out = False
        if x - 1 >= 0:
            out = out or result[y][x - 1]
        if x + 1 < size_x:
            out = out or result[y][x + 1]
        if y - 1 >= 0:
            out = out or result[y - 1][x]  
        if y + 1 < size_y:
            out = out or result[y + 1][x]
        return out    

    result = [[0 for col in range(size_x)] for row in range(size_y)]
    x, y = 0, 0

    result[y][x] = 1
    food -= 1

    if random.random() < 0.5:
        new_x = move_x(x)
        new_y = y
    else:
        new_x = x
        new_y = move_y(y)

    prev_move = (new_x - x, new_y - y)
    x, y = new_x, new_y

    while food > 0:
            
        if random.random() < 0.25 or (prev_move[0] + x >= size_x or \
                                     prev_move[0] + x < 0 or \
                                     prev_move[1] + y >= size_y or \
                                     prev_move[1] + y < 0):
            if random.random() < 0.5:
                new_x = move_x(x)
                new_y = y
            else:
                new_x = x
                new_y = move_y(y)
        else:
            new_x, new_y = prev_move[0] + x, prev_move[1] + y

        if not result[y][x]:
            if not has_food_around(x, y, result) and ((new_x - x, new_y - y) == prev_move):
                result[y][x] = 1
                food -= 1
            else:
                if random.random() < 0.5:
                    result[y][x] = 1
                    food -= 1
        
        prev_move = (new_x - x, new_y - y)
        x, y = new_x, new_y
    
    return result

def inside_limites(value, minimum, maximum):
    return value >= minimum and value < maximum


@aefunction('food_present(g:Grid) -> {out:Integer | i >= 0 && i <= g.food} = native;', lambda grid: food_present(grid))
def food_present(grid):
    return grid.grid[grid.position[1]][grid.position[0]]

@aefunction('food_ahead(g:Grid) -> Boolean = native;', lambda grid: food_ahead(grid))
def food_ahead(grid):
    new_x = grid.position[0] + grid.direction[0] 
    new_y = grid.position[1] + grid.direction[1]
    return inside_limites(new_x, 0, len(grid.grid[0])) and \
           inside_limites(new_y, 0 len(grid.grid)) and \
           grid.grid[new_y][new_x]

@aefunction('left({g:Grid where g.position.elem1 > 0}) -> {g2:Grid where g2.position.elem1 == (g.position.elem1 - 1)} = native;', lambda grid: left(grid))
def left(grid):
    grid.position = (grid.position[0] - 1, grid.position[1])
    if grid.grid[grid.position[1]][grid.position[0]]:
        grid.food -= 1
        grid.grid[grid.position[1]][grid.position[0]] = 0
    return grid

@aefunction('right({g:Grid where g.position.elem1 < g.grid.size}) -> {g2:Grid where g2.position.elem1 == (g.position.elem1 + 1)} = native;', lambda grid: right(grid))
def right(grid):
    grid.position = (grid.position[0] + 1, grid.position[1])
    if grid.grid[grid.position[1]][grid.position[0]]:
        grid.food -= 1
        grid.grid[grid.position[1]][grid.position[0]] = 0
    return grid

@aefunction('up({g:Grid where g.position.elem2 > 0}) -> {g2:Grid where g2.position.elem2 == (g.position.elem2 - 1)} = native;', lambda up: up(grid))
def up(grid):
    grid.position = (grid.position[0], grid.position[1] - 1)
    if grid.grid[grid.position[1]][grid.position[0]]:
        grid.food -= 1
        grid.grid[grid.position[1]][grid.position[0]] = 0
    return grid

@aefunction('down({g:Grid where g.position.elem2 < g.grid.size}) -> {g2:Grid where g2.position.elem2 == (g.position.elem2 + 1)} = native;', lambda down: left(grid))
def down(grid):
    grid.position = (grid.position[0], grid.position[1] + 1)
    if grid.grid[grid.position[1]][grid.position[0]]:
        grid.food -= 1
        grid.grid[grid.position[1]][grid.position[0]] = 0
    return grid
