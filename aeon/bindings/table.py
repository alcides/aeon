from collections import defaultdict


def group_by(table, column):
    """
    Groups rows in the table by the value in the specified column.

    Parameters:
        table (list of dict): The table to group, as a list of dictionaries.
        column (str): The column name to group by.

    Returns:
        list of list of dict: A list of groups, each group is a list of rows (dicts) sharing the same value in the specified column.
    """
    groups = defaultdict(list)
    for row in table:
        groups[row[column]].append(row)
    return list(groups.values())


def pivot(table, index, columns, values):
    """
    Pivots the table to reorganize data, similar to a spreadsheet pivot.

    Parameters:
        table (list of dict): The table to pivot, as a list of dictionaries.
        index (str): The column to use as the new row index.
        columns (str): The column whose unique values will become new columns.
        values (str): The column whose values fill the new table.

    Returns:
        list of dict: The pivoted table as a list of dictionaries.
    """
    result = defaultdict(dict)
    for row in table:
        row_idx = row[index]
        col_key = row[columns]
        val = row[values]
        result[row_idx][col_key] = val
    # Convert to list of dicts, including index as a column
    return [dict({index: idx}, **cols) for idx, cols in result.items()]


def melt(table, id_vars, value_vars, var_name, value_name):
    """
    Unpivots the table from wide to long format.

    Parameters:
        table (list of dict): The table to melt, as a list of dictionaries.
        id_vars (list of str): Columns to use as identifier variables.
        value_vars (list of str): Columns to unpivot.
        var_name (str): Name to use for the variable column.
        value_name (str): Name to use for the value column.

    Returns:
        list of dict: The melted table as a list of dictionaries in long format.
    """
    result = []
    for row in table:
        for col in value_vars:
            melted = {k: row[k] for k in id_vars}
            melted[var_name] = col
            melted[value_name] = row[col]
            result.append(melted)
    return result
