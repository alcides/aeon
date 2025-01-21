def calculate_linearity(level_elements: list[tuple[...]]) -> float:
        x_coords = [element[1] for element in level_elements]
        x_coords.sort()

        differences = [x_coords[i + 1] - x_coords[i] for i in range(len(x_coords) - 1)]

        linearity = sum(1 / (diff + 1) for diff in differences)

        normalized_linearity = linearity / len(x_coords)

        return normalized_linearity


def calculate_density(level_elements) -> float:
    occupied_area = 0
    for element in level_elements:
        chunk_type = element[0]
        if chunk_type == ' ':
            continue

        match chunk_type:
            case 'P':
                width = element[3]
                height = 1
                occupied_area += width * height

            case 'H':
                width = element[3]
                height = 1
                occupied_area += width * height

            case 'c':
                width = element[3] if len(element)>3 else 1
                height = 1
                occupied_area += width * height

            case 'C':
                height = element[3]
                width = 1
                occupied_area += width * height

            case 'T':
                height = element[3]
                width = element[4] + element[5]
                occupied_area += width * height

    x_coords = [element[1] for element in level_elements if element[0] != ' ']
    horizontal_length = max(x_coords) - min(x_coords)

    y_coords = [element[2] for element in level_elements if len(element) > 2 and element[0] != ' ']
    vertical_length = max(y_coords) - min(y_coords) if y_coords else 0

    if horizontal_length == 0 or vertical_length == 0 or occupied_area == 0:
        return 0.0

    density = len([element for element in level_elements if element[0] != ' ']) / occupied_area

    return density


level_elements = [
    (' ', 5, 2, 3, 1, 1),
    ('P', 10, 3, 4),
    ('H', 20, 4, 2),
    ('C', 30, 1, 3),
    ('T', 40, 2, 2, 1, 1),
    ('c', 50, 1, 2),
    ('c', 55, 3),
    ('p', 60, 1),
    ('R', 65, 2),
    ('r', 70, 3)
]


density_score = calculate_density(level_elements)
print(f"Density Score: {density_score}")
