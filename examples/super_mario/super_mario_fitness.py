import numpy as np


def calculate_linearity(level_elements) -> float:

    x_coords = [element[1] for element in level_elements if element[0] != ' ']
    y_coords = [element[2] for element in level_elements if len(element) > 2 and element[0] != ' ']

    if len(x_coords) < 2 or len(y_coords) < 2:
        return 0.0

    # y = m * x + b see genetic engine examples
    m, b = np.polyfit(x_coords, y_coords, 1)

    total_deviation = 0
    for x, y in zip(x_coords, y_coords):
        predicted_y = m * x + b
        deviation = abs(y - predicted_y)
        total_deviation += deviation

    max_possible_deviation = max(y_coords) - min(y_coords)
    if max_possible_deviation == 0:
        return 1.0

    linearity_score = 1 - (total_deviation / (max_possible_deviation * len(x_coords)))

    return  max(0, min(1, linearity_score))



def calculate_density(level_elements) -> float:
    occupied_area = 0
    for element in level_elements:
        chunk_type = element[0]
        #TODO  conflicts - overlapping chunks

        match chunk_type:
            case ' ':
                w_before = element[4]
                w_after = element[5]
                occupied_area += w_before + w_after

            case 'P':
                width = element[3]
                occupied_area += width

            case 'H':
                width = element[3]
                occupied_area += width

            case chunk_type if chunk_type in ['C', 'T']:
                height = element[3]
                w_before = element[4]
                w_after = element[5]
                occupied_area += height + w_before + w_after

            case 'c':
                width = element[3] if len(element)>3 else 1
                height = 1
                occupied_area += width * height

    x_coords = [elem[1] for elem in level_elements if len(elem) > 1]
    y_coords = [elem[2] for elem in level_elements if len(elem) > 2]

    horizontal_length = max(x_coords) - min(x_coords) if x_coords else 0
    vertical_length = max(y_coords) - min(y_coords) if y_coords else 0

    if horizontal_length == 0 or vertical_length == 0 or occupied_area == 0:
        return 0.0

    return occupied_area / (horizontal_length * vertical_length)


def calculate_leniency(level_elements) -> float:

    return 0.0


level_elements = [
    (' ', 5, 2, 3, 1, 1),
    ('P', 10, 3, 4),
    ('H', 20, 4, 2),
    ('C', 30, 1, 3, 1 ,1),
    ('T', 40, 2, 2, 1, 1),
    ('c', 50, 1, 2),
    ('c', 55, 3),
    ('p', 60, 1),
    ('R', 65, 2),
    ('r', 70, 3)
]


density_score = calculate_density(level_elements)
linearity_score = calculate_linearity(level_elements)
print(f"Linearity Score: {linearity_score}")
print(f"Density Score: {density_score}")
