"""Exercise MBPP contracts at boundaries beyond the upstream examples."""

import re
from pathlib import Path

import pytest

from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.synthesis.uis.api import SilentSynthesisUI


MBPP_DIR = Path(__file__).parent.parent / "examples/benchmarks/mbpp"


def source_for(task):
    source = (MBPP_DIR / f"mbpp_{task}.ae").read_text()
    return re.sub(r"^@(doc|example)\(.*\)\n", "", source, flags=re.MULTILINE)


def parse(source):
    driver = AeonDriver(AeonConfig("random_search", SilentSynthesisUI(), 0, no_main=True))
    return driver.parse(aeon_code=source)


@pytest.mark.parametrize(
    "task, call, valid",
    [
        (101, "kth_element [10, 20, 30] 1", True),
        (101, "kth_element [10, 20, 30] 3", True),
        (101, "kth_element [10, 20, 30] 0", False),
        (101, "kth_element [10, 20, 30] 4", False),
        (101, "kth_element ([] : (List Int)) 1", False),
        (597, "find_kth [1, 3] [2, 4] 4", True),
        (597, "find_kth [1, 3] [2, 4] 5", False),
        (170, "sum_range_list [10, 20, 30] 0 2", True),
        (170, "sum_range_list [10, 20, 30] 2 1", False),
        (170, "sum_range_list [10, 20, 30] 0 3", False),
        (4, "heap_queue_largest [1, 2] 3", True),
        (4, "heap_queue_largest ([] : (List Int)) 0", True),
        (62, "smallest_num [(-9)]", True),
        (62, "smallest_num ([] : (List Int))", False),
        (292, "find 9 0", False),
        (292, "find 9 (-2)", True),
        (471, "find_remainder [1, 2] 0", False),
        (471, "find_remainder [1, 2] 1", True),
        (261, "division_elements [4, 6, 8, 10] [2, 3, 0, 5]", False),
        (261, "division_elements [4, 6, 8, 10] [2, 3, (-4), 5]", True),
        (261, "division_elements [4, 6, 8] [2, 3, 4, 5]", False),
        (261, "division_elements [4, 6, 8, 10] [2, 3, 4]", False),
        (616, "tuple_modulo [4, 6, 8, 10] [2, 3, 0, 5]", False),
        (616, "tuple_modulo [4, 6, 8, 10] [2, 3, (-4), 5]", True),
        (116, "tuple_to_int [1, 2, 3]", True),
        (116, "tuple_to_int [1, (-2), 3]", False),
        (116, "tuple_to_int [1, 2]", False),
        (424, 'extract_rear ["ab", "cd", "ef"]', True),
        (424, 'extract_rear ["ab", "", "ef"]', False),
        (424, 'extract_rear ["ab", "cd"]', False),
        (250, "count_X [1, 2, 1] 1", True),
        (250, "count_X [] 1", True),
        (104, 'sort_sublists [["b", "a"]]', True),
        (106, "add_lists [] [1, 2, 3]", True),
        (470, "add_pairwise []", True),
        (470, "add_pairwise [1]", True),
        (788, 'new_tuple [] "a"', True),
        (809, "check_smaller [4, 5] [3, 4]", True),
        (809, "check_smaller [4, 5] [3]", True),
        (273, "substract_elements [4, 5] [3]", True),
        (740, "tuple_to_dict [1, 2, 3, 4]", True),
        (740, "tuple_to_dict [1, 2, 3]", False),
        (617, "min_Jumps (Pair.mk 0 3) 5", False),
        (617, "min_Jumps (Pair.mk 2 3) 0", True),
        (14, "find_Volume 2 3 (-1)", False),
        (14, "find_Volume 2 3 0", True),
        (264, "dog_age 1", True),
        (783, "rgb_to_hsv 256 0 0", False),
        (783, "rgb_to_hsv 255 0 0", True),
        (578, "interleave_lists [1, 2] [3] [4, 5]", False),
        (578, "interleave_lists [1, 2] [3, 4] [5, 6]", True),
        (723, "count_same_pair [1, 2] [1, 2, 3]", True),
        (223, "is_majority [1, 1, 2, 2] 4 1", True),
        (223, "is_majority [1, 1, 2, 2] 5 1", False),
        (223, "is_majority [1, 1, 2, 2] 3 1", False),
        (223, "is_majority [] 0 1", True),
    ],
)
def test_input_boundaries(task, call, valid):
    source = source_for(task) + f"\ndef probe (_:Int) : Unit := let result := {call} in unit;"
    assert (not parse(source)) == valid


@pytest.mark.parametrize(
    "task, implementation, valid",
    [
        (66, "(-1)", False),
        (66, "match list with | List.nil => 0 | List.cons x xs => 0", True),
        (66, "List.size list + 1", False),
        (8, "[]", False),
        (8, "match nums with | List.nil => [] | List.cons x xs => List.cons (x * x) (square_nums xs)", True),
        (435, "10", False),
        (435, "0", True),
        (783, "[360.0, 0.0, 0.0]", False),
        (783, "[359.0, 100.0, 100.0]", True),
        (783, "[359.0, 100.0]", False),
        (783, "[359.0, 100.0, 100.0, 0.0]", False),
        (783, "[359.0, 101.0, 100.0]", False),
        (783, "[359.0, 100.0, (-1.0)]", False),
        (264, "10.5", True),
    ],
)
def test_result_contracts(task, implementation, valid):
    source = source_for(task).replace("?hole", f"({implementation})")
    assert (not parse(source)) == valid


@pytest.mark.parametrize("first, second, valid", [(2, 3, True), (0, 3, False), (2, 0, False)])
def test_pair_constructor_exposes_field_measures(first, second, valid):
    source = f"""
import Pair
def steps : {{v:(Pair Int Int) | Pair.first v > 0 && Pair.second v > 0}} := Pair.mk {first} {second};
"""
    assert (not parse(source)) == valid
