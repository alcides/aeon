import numpy as np

ERROR_NUMBER = 1


def calculate_fitness(level: tuple[list, list]) -> list[float]:
    chucks, enemies = level
    if len(enemies) < 2:
        return [ERROR_NUMBER, ERROR_NUMBER]
    level_elements = chucks + enemies
    map_w = 110
    map_h = 10
    map = np.zeros((map_w, map_h))

    max_chunks = map_w * map_h
    place_in(level_elements, map)

    number_of_chunks: float = float(max_chunks - float(np.sum(map)))
    conflicts: float = float(np.sum(map > 1))

    normalized_number_of_chunks = round(number_of_chunks / max_chunks, 5)
    normalized_conflicts = round(conflicts / max_chunks, 5)

    return [normalized_number_of_chunks, normalized_conflicts]


def place_in(level_elements, map):
    for level_element in level_elements:
        match level_element[0]:
            case " ":
                assert len(level_element) == 6
                x_coord = level_element[1]
                y_coord = level_element[2]
                w_gap = level_element[3]
                w_before = level_element[4]
                w_after = level_element[5]

                for i in range(0, w_before):
                    map[x_coord - i, y_coord] += 1

                for i in range(0, w_after):
                    map[x_coord + w_gap + i, y_coord] += 1

            case "P" | "H":
                assert len(level_element) == 4
                x_coord = level_element[1]
                y_coord = level_element[2]
                w = level_element[3]

                for i in range(0, w):
                    map[x_coord + i, y_coord] += 1

            case "C" | "T":
                assert len(level_element) == 6
                x_coord = level_element[1]
                y_coord = level_element[2]
                h = level_element[3]
                w_before = level_element[4]
                w_after = level_element[5]

                for i in range(0, h):
                    map[x_coord, y_coord + i] += 1

                for i in range(0, w_before):
                    map[x_coord - i, y_coord] += 1

                for i in range(0, w_after):
                    map[x_coord + i, y_coord] += 1

            case "c":
                assert len(level_element) == 4
                x_coord = level_element[1]
                y_coord = level_element[2]
                wc = level_element[3]

                for i in range(0, wc):
                    map[x_coord + i, y_coord] += 1

            case "bcoin" | "bpowerup" | "rcoin" | "rock":
                assert len(level_element) == 3
                x_coord = level_element[1]
                y_coord = level_element[2]

                map[x_coord, y_coord] += 1

            case "goomba" | "koopa":
                assert len(level_element) == 2
                x_coord = level_element[1]
                map[x_coord, 0] = 1
