# Non-benchmark examples

This inventory covers **410 `.ae` files and 3 legacy `.aef` files**, including the 11 local
microbenchmarks directly under `benchmarks/`, and excludes the DP-GP examples being
removed in a separate PR. These are local demos, tutorials, exercises,
regression fixtures, or examples without a documented correspondence to a published benchmark task.
The inventory does not claim that every unattributed program was originally written for Aeon.

The ARC- and Fandango-inspired tasks live in [benchmarks/arc/](benchmarks/arc/) and
[benchmarks/fandango/](benchmarks/fandango/). The [local synthesis overview](synthesis/README.md)
ranks the larger examples and records their provenance.

## Organized synthesis groups

- [control/](synthesis/control/README.md): 8 controller examples, including the reference runner.
- [puzzle/](synthesis/puzzle/README.md): 19 constraint, arithmetic, scheduling, and circuit problems.
- [leveldesign/](synthesis/leveldesign/README.md): Super Mario, dungeon generation, pizza assignment, and page layout.

Karel, neuroevolution, monotonicity, and the existing backend demo groups retain their own directories.
These local application groups remain separate from the named collections in `benchmarks/`.

## Other groups to review

- `99problems/`: a classic exercise collection of completed implementations, without a cited paper benchmark protocol.
- `liquidhaskell/`: tutorial/blog compatibility ports, retained separately from the equational-reasoning paper.
- `synthesis/karel/`: local regression worlds/programs; the published dataset adapter is documented there.
- `synthesis/neuroevolution/`, `monotonicity/`, and backend demo directories: locally assembled tasks.
- `synthesis/arborist/list_sum.ae`: a locally strengthened specification; the original paper example is under benchmarks.
- `benchmarks/bench_*.ae`: 11 local microbenchmarks still awaiting a placement decision.

Counts below include `.aef` files where present. Associated assets and documentation remain beside the programs.

## Directory inventory

| Directory | Programs |
| --- | ---: |
| [./](./) | 6 |
| [99problems/](99problems/) | 39 |
| [benchmarks/](benchmarks/) | 11 |
| [bugs/](bugs/) | 4 |
| [dataframe/](dataframe/) | 3 |
| [demos/](demos/) | 5 |
| [ffi/](ffi/) | 7 |
| [image/](image/) | 3 |
| [imports/](imports/) | 21 |
| [liquidhaskell/](liquidhaskell/) | 4 |
| [liquidhaskell/negative/](liquidhaskell/negative/) | 15 |
| [liquidhaskell/positive/](liquidhaskell/positive/) | 17 |
| [liquidhaskell/runtime/](liquidhaskell/runtime/) | 1 |
| [list/](list/) | 2 |
| [llvm/](llvm/) | 3 |
| [llvm/gpu/](llvm/gpu/) | 20 |
| [machine_learning/](machine_learning/) | 1 |
| [machine_learning/restrictions/](machine_learning/restrictions/) | 30 |
| [ml/](ml/) | 11 |
| [mutual/](mutual/) | 2 |
| [nn/](nn/) | 9 |
| [nn/mnist/](nn/mnist/) | 1 |
| [pbt/](pbt/) | 11 |
| [probabilistic/](probabilistic/) | 3 |
| [sets/](sets/) | 1 |
| [syntax/](syntax/) | 27 |
| [synthesis/](synthesis/) | 15 |
| [synthesis/afta/](synthesis/afta/) | 2 |
| [synthesis/amaze/](synthesis/amaze/) | 1 |
| [synthesis/arborist/](synthesis/arborist/) | 3 |
| [synthesis/boolean_bounded/](synthesis/boolean_bounded/) | 2 |
| [synthesis/bustle/](synthesis/bustle/) | 4 |
| [synthesis/cata/](synthesis/cata/) | 10 |
| [synthesis/control/](synthesis/control/) | 8 |
| [synthesis/fta/](synthesis/fta/) | 3 |
| [synthesis/karel/](synthesis/karel/) | 1 |
| [synthesis/karel/reference/](synthesis/karel/reference/) | 10 |
| [synthesis/karel/synth/](synthesis/karel/synth/) | 10 |
| [synthesis/leveldesign/](synthesis/leveldesign/) | 4 |
| [synthesis/monotonicity/](synthesis/monotonicity/) | 5 |
| [synthesis/neuroevolution/](synthesis/neuroevolution/) | 1 |
| [synthesis/noisy/](synthesis/noisy/) | 3 |
| [synthesis/ortools/](synthesis/ortools/) | 7 |
| [synthesis/puzzle/](synthesis/puzzle/) | 19 |
| [synthesis/structure_guided/](synthesis/structure_guided/) | 2 |
| [synthesis/type_constrained/](synthesis/type_constrained/) | 4 |
| [tactics/](tactics/) | 10 |
| [talk/](talk/) | 9 |
| [testing/](testing/) | 15 |
| [verification/](verification/) | 8 |

## Complete file inventory

### examples/

- [bug.ae](bug.ae)
- [factorial.ae](factorial.ae)
- [fibonacci.ae](fibonacci.ae)
- [knapsack_ga.ae](knapsack_ga.ae)
- [lethal_trifecta.ae](lethal_trifecta.ae)
- [pair.ae](pair.ae)

### examples/99problems/

- [p01_last.ae](99problems/p01_last.ae)
- [p02_secondLast.ae](99problems/p02_secondLast.ae)
- [p03_kth.ae](99problems/p03_kth.ae)
- [p04_length.ae](99problems/p04_length.ae)
- [p05_reverse.ae](99problems/p05_reverse.ae)
- [p06_palindrome.ae](99problems/p06_palindrome.ae)
- [p07_flatten.ae](99problems/p07_flatten.ae)
- [p08_compress.ae](99problems/p08_compress.ae)
- [p09_pack.ae](99problems/p09_pack.ae)
- [p10_encode.ae](99problems/p10_encode.ae)
- [p11_encode_modified.ae](99problems/p11_encode_modified.ae)
- [p12_decode.ae](99problems/p12_decode.ae)
- [p13_encode_direct.ae](99problems/p13_encode_direct.ae)
- [p14_duplicate.ae](99problems/p14_duplicate.ae)
- [p15_replicate.ae](99problems/p15_replicate.ae)
- [p16_drop_every.ae](99problems/p16_drop_every.ae)
- [p17_split.ae](99problems/p17_split.ae)
- [p18_slice.ae](99problems/p18_slice.ae)
- [p19_rotate.ae](99problems/p19_rotate.ae)
- [p20_remove_at.ae](99problems/p20_remove_at.ae)
- [p21_insert_at.ae](99problems/p21_insert_at.ae)
- [p22_range.ae](99problems/p22_range.ae)
- [p23_random_select.ae](99problems/p23_random_select.ae)
- [p24_lotto.ae](99problems/p24_lotto.ae)
- [p25_random_permutation.ae](99problems/p25_random_permutation.ae)
- [p26_combinations.ae](99problems/p26_combinations.ae)
- [p31_is_prime.ae](99problems/p31_is_prime.ae)
- [p32_gcd.ae](99problems/p32_gcd.ae)
- [p33_coprime.ae](99problems/p33_coprime.ae)
- [p34_totient.ae](99problems/p34_totient.ae)
- [p35_prime_factors.ae](99problems/p35_prime_factors.ae)
- [p36_prime_factors_mult.ae](99problems/p36_prime_factors_mult.ae)
- [p39_primes_range.ae](99problems/p39_primes_range.ae)
- [p40_goldbach.ae](99problems/p40_goldbach.ae)
- [p41_goldbach_list.ae](99problems/p41_goldbach_list.ae)
- [p46_truth_table.ae](99problems/p46_truth_table.ae)
- [p49_gray_code.ae](99problems/p49_gray_code.ae)
- [p55_balanced_tree.ae](99problems/p55_balanced_tree.ae)
- [p56_symmetric_tree.ae](99problems/p56_symmetric_tree.ae)

### examples/benchmarks/

- [bench_function_clamp.ae](benchmarks/bench_function_clamp.ae)
- [bench_function_increment.ae](benchmarks/bench_function_increment.ae)
- [bench_function_negate.ae](benchmarks/bench_function_negate.ae)
- [bench_int_bounded.ae](benchmarks/bench_int_bounded.ae)
- [bench_int_disjoint.ae](benchmarks/bench_int_disjoint.ae)
- [bench_int_divisible.ae](benchmarks/bench_int_divisible.ae)
- [bench_int_negative.ae](benchmarks/bench_int_negative.ae)
- [bench_list.ae](benchmarks/bench_list.ae)
- [bench_maybe.ae](benchmarks/bench_maybe.ae)
- [bench_peano.ae](benchmarks/bench_peano.ae)
- [bench_tree.ae](benchmarks/bench_tree.ae)

### examples/bugs/

- [bug_77_shadow.ae](bugs/bug_77_shadow.ae)
- [error.ae](bugs/error.ae)
- [nqueens_small.ae](bugs/nqueens_small.ae)
- [planet_orbit.ae](bugs/planet_orbit.ae)

### examples/dataframe/

- [etl_pipeline.ae](dataframe/etl_pipeline.ae)
- [feature_llvm.ae](dataframe/feature_llvm.ae)
- [groupby_agg.ae](dataframe/groupby_agg.ae)

### examples/demos/

- [1_hello.ae](demos/1_hello.ae)
- [2_image.ae](demos/2_image.ae)
- [3_dataset.ae](demos/3_dataset.ae)
- [4_errorcode.ae](demos/4_errorcode.ae)
- [errorcode.ae](demos/errorcode.ae)

### examples/ffi/

- [array_linear.ae](ffi/array_linear.ae)
- [custom_sort.ae](ffi/custom_sort.ae)
- [external.ae](ffi/external.ae)
- [forkjoin_divide.ae](ffi/forkjoin_divide.ae)
- [forkjoin_example.ae](ffi/forkjoin_example.ae)
- [native_test.ae](ffi/native_test.ae)
- [socket_linear.ae](ffi/socket_linear.ae)

### examples/image/

- [key.ae](image/key.ae)
- [pil_style.ae](image/pil_style.ae)
- [pixels.ae](image/pixels.ae)

### examples/imports/

- [args_example.ae](imports/args_example.ae)
- [database_example.ae](imports/database_example.ae)
- [deque_example.ae](imports/deque_example.ae)
- [downloader_example.ae](imports/downloader_example.ae)
- [email_example.ae](imports/email_example.ae)
- [http_example.ae](imports/http_example.ae)
- [import.ae](imports/import.ae)
- [import2.ae](imports/import2.ae)
- [iterator_example.ae](imports/iterator_example.ae)
- [json_example.ae](imports/json_example.ae)
- [lock_example.ae](imports/lock_example.ae)
- [order_example.ae](imports/order_example.ae)
- [os_example.ae](imports/os_example.ae)
- [path_example.ae](imports/path_example.ae)
- [random_linear.ae](imports/random_linear.ae)
- [reader_example.ae](imports/reader_example.ae)
- [stack_example.ae](imports/stack_example.ae)
- [subprocess_example.ae](imports/subprocess_example.ae)
- [subprocess_process_example.ae](imports/subprocess_process_example.ae)
- [sys_example.ae](imports/sys_example.ae)
- [writer_example.ae](imports/writer_example.ae)

### examples/liquidhaskell/

- [EList.ae](liquidhaskell/EList.ae)
- [IncList.ae](liquidhaskell/IncList.ae)
- [LList.ae](liquidhaskell/LList.ae)
- [PList.ae](liquidhaskell/PList.ae)

### examples/liquidhaskell/negative/

- [absolute.ae](liquidhaskell/negative/absolute.ae)
- [abstract_max.ae](liquidhaskell/negative/abstract_max.ae)
- [abstract_max_client.ae](liquidhaskell/negative/abstract_max_client.ae)
- [assertion.ae](liquidhaskell/negative/assertion.ae)
- [divide_zero.ae](liquidhaskell/negative/divide_zero.ae)
- [higher_order_map.ae](liquidhaskell/negative/higher_order_map.ae)
- [list_loop.ae](liquidhaskell/negative/list_loop.ae)
- [list_map.ae](liquidhaskell/negative/list_map.ae)
- [list_size.ae](liquidhaskell/negative/list_size.ae)
- [polymorphic_selection.ae](liquidhaskell/negative/polymorphic_selection.ae)
- [set_append.ae](liquidhaskell/negative/set_append.ae)
- [singleton.ae](liquidhaskell/negative/singleton.ae)
- [sorted_insert.ae](liquidhaskell/negative/sorted_insert.ae)
- [sorted_loop.ae](liquidhaskell/negative/sorted_loop.ae)
- [unreachable_nil.ae](liquidhaskell/negative/unreachable_nil.ae)

### examples/liquidhaskell/positive/

- [absolute.ae](liquidhaskell/positive/absolute.ae)
- [abstract_identity.ae](liquidhaskell/positive/abstract_identity.ae)
- [abstract_max.ae](liquidhaskell/positive/abstract_max.ae)
- [assertion.ae](liquidhaskell/positive/assertion.ae)
- [divide.ae](liquidhaskell/positive/divide.ae)
- [higher_order_map.ae](liquidhaskell/positive/higher_order_map.ae)
- [inferred_absolute.ae](liquidhaskell/positive/inferred_absolute.ae)
- [list_map.ae](liquidhaskell/positive/list_map.ae)
- [list_reverse.ae](liquidhaskell/positive/list_reverse.ae)
- [list_size.ae](liquidhaskell/positive/list_size.ae)
- [native_absolute.ae](liquidhaskell/positive/native_absolute.ae)
- [polymorphic_safe_head.ae](liquidhaskell/positive/polymorphic_safe_head.ae)
- [positive_guard.ae](liquidhaskell/positive/positive_guard.ae)
- [safe_head.ae](liquidhaskell/positive/safe_head.ae)
- [set_append.ae](liquidhaskell/positive/set_append.ae)
- [singletons.ae](liquidhaskell/positive/singletons.ae)
- [sorted_insert.ae](liquidhaskell/positive/sorted_insert.ae)

### examples/liquidhaskell/runtime/

- [native_violation.ae](liquidhaskell/runtime/native_violation.ae)

### examples/list/

- [map_parametric_refinements.ae](list/map_parametric_refinements.ae)
- [test_list_main.ae](list/test_list_main.ae)

### examples/llvm/

- [array_map_cpu.ae](llvm/array_map_cpu.ae)
- [functional_quicksort.ae](llvm/functional_quicksort.ae)
- [ndarray_reshape.ae](llvm/ndarray_reshape.ae)

### examples/llvm/gpu/

- [adt_box.ae](llvm/gpu/adt_box.ae)
- [adt_knapsack_smoke.ae](llvm/gpu/adt_knapsack_smoke.ae)
- [adt_list.ae](llvm/gpu/adt_list.ae)
- [array_map.ae](llvm/gpu/array_map.ae)
- [array_pipeline.ae](llvm/gpu/array_pipeline.ae)
- [array_return.ae](llvm/gpu/array_return.ae)
- [busy.ae](llvm/gpu/busy.ae)
- [cuda_download.ae](llvm/gpu/cuda_download.ae)
- [cuda_vector_add.ae](llvm/gpu/cuda_vector_add.ae)
- [filter.ae](llvm/gpu/filter.ae)
- [floyd_warshall.ae](llvm/gpu/floyd_warshall.ae)
- [knapsack_ga.ae](llvm/gpu/knapsack_ga.ae)
- [lazy_copy.ae](llvm/gpu/lazy_copy.ae)
- [nbody.ae](llvm/gpu/nbody.ae)
- [reductions.ae](llvm/gpu/reductions.ae)
- [sum.ae](llvm/gpu/sum.ae)
- [vector_map.ae](llvm/gpu/vector_map.ae)
- [zero_matrix.ae](llvm/gpu/zero_matrix.ae)
- [zero_matrix_2d.ae](llvm/gpu/zero_matrix_2d.ae)
- [zero_volume_3d.ae](llvm/gpu/zero_volume_3d.ae)

### examples/machine_learning/

- [titanic_dataset.ae](machine_learning/titanic_dataset.ae)

### examples/machine_learning/restrictions/

- [00_linear_type_invalid.ae](machine_learning/restrictions/00_linear_type_invalid.ae)
- [00_linear_type_valid.ae](machine_learning/restrictions/00_linear_type_valid.ae)
- [01_dataframe_target_invalid.ae](machine_learning/restrictions/01_dataframe_target_invalid.ae)
- [01_dataframe_target_valid.ae](machine_learning/restrictions/01_dataframe_target_valid.ae)
- [02_dataset_split_invalid.ae](machine_learning/restrictions/02_dataset_split_invalid.ae)
- [02_dataset_split_valid.ae](machine_learning/restrictions/02_dataset_split_valid.ae)
- [03_datasetsplit_consume_invalid.ae](machine_learning/restrictions/03_datasetsplit_consume_invalid.ae)
- [03_datasetsplit_consume_valid.ae](machine_learning/restrictions/03_datasetsplit_consume_valid.ae)
- [04_training_train_invalid.ae](machine_learning/restrictions/04_training_train_invalid.ae)
- [04_training_train_valid.ae](machine_learning/restrictions/04_training_train_valid.ae)
- [05_testing_accuracy_invalid.ae](machine_learning/restrictions/05_testing_accuracy_invalid.ae)
- [05_testing_accuracy_valid.ae](machine_learning/restrictions/05_testing_accuracy_valid.ae)
- [06_split_fraction_invalid.ae](machine_learning/restrictions/06_split_fraction_invalid.ae)
- [06_split_fraction_valid.ae](machine_learning/restrictions/06_split_fraction_valid.ae)
- [07_target_index_invalid.ae](machine_learning/restrictions/07_target_index_invalid.ae)
- [07_target_index_valid.ae](machine_learning/restrictions/07_target_index_valid.ae)
- [08_train_test_roles_invalid.ae](machine_learning/restrictions/08_train_test_roles_invalid.ae)
- [08_train_test_roles_valid.ae](machine_learning/restrictions/08_train_test_roles_valid.ae)
- [09_linear_resource_used_invalid.ae](machine_learning/restrictions/09_linear_resource_used_invalid.ae)
- [09_linear_resource_used_valid.ae](machine_learning/restrictions/09_linear_resource_used_valid.ae)
- [10_accuracy_bounds_invalid.ae](machine_learning/restrictions/10_accuracy_bounds_invalid.ae)
- [10_accuracy_bounds_valid.ae](machine_learning/restrictions/10_accuracy_bounds_valid.ae)
- [11_feature_compatibility_invalid.ae](machine_learning/restrictions/11_feature_compatibility_invalid.ae)
- [11_feature_compatibility_valid.ae](machine_learning/restrictions/11_feature_compatibility_valid.ae)
- [12_target_metadata_invalid.ae](machine_learning/restrictions/12_target_metadata_invalid.ae)
- [12_target_metadata_valid.ae](machine_learning/restrictions/12_target_metadata_valid.ae)
- [13_split_provenance_invalid.ae](machine_learning/restrictions/13_split_provenance_invalid.ae)
- [13_split_provenance_valid.ae](machine_learning/restrictions/13_split_provenance_valid.ae)
- [14_csv_shape_metadata_invalid.ae](machine_learning/restrictions/14_csv_shape_metadata_invalid.ae)
- [14_csv_shape_metadata_valid.ae](machine_learning/restrictions/14_csv_shape_metadata_valid.ae)

### examples/ml/

- [amltk_cv.ae](ml/amltk_cv.ae)
- [amltk_ensemble.ae](ml/amltk_ensemble.ae)
- [amltk_hpo.ae](ml/amltk_hpo.ae)
- [balanced_dataset.ae](ml/balanced_dataset.ae)
- [classification_pipeline.ae](ml/classification_pipeline.ae)
- [estimators.ae](ml/estimators.ae)
- [linear_regression.ae](ml/linear_regression.ae)
- [model_comparison.ae](ml/model_comparison.ae)
- [regression_pipeline.ae](ml/regression_pipeline.ae)
- [single_family.ae](ml/single_family.ae)
- [temporal_leakage_proof.ae](ml/temporal_leakage_proof.ae)

### examples/mutual/

- [even_odd.ae](mutual/even_odd.ae)
- [three_cycle.ae](mutual/three_cycle.ae)

### examples/nn/

- [classify.ae](nn/classify.ae)
- [domains.ae](nn/domains.ae)
- [mlp.ae](nn/mlp.ae)
- [models.ae](nn/models.ae)
- [propagation.ae](nn/propagation.ae)
- [relational.ae](nn/relational.ae)
- [relaxation.ae](nn/relaxation.ae)
- [robustness.ae](nn/robustness.ae)
- [train.ae](nn/train.ae)

### examples/nn/mnist/

- [verified_small.ae](nn/mnist/verified_small.ae)

### examples/pbt/

- [examples_decorator.ae](pbt/examples_decorator.ae)
- [pbt_int.ae](pbt/pbt_int.ae)
- [pbt_reverse.ae](pbt/pbt_reverse.ae)
- [properties_synth.ae](pbt/properties_synth.ae)
- [property_synth.ae](pbt/property_synth.ae)
- [props_args.ae](pbt/props_args.ae)
- [props_basic.ae](pbt/props_basic.ae)
- [props_dependent.ae](pbt/props_dependent.ae)
- [props_list.ae](pbt/props_list.ae)
- [props_maybe.ae](pbt/props_maybe.ae)
- [props_socket.ae](pbt/props_socket.ae)

### examples/probabilistic/

- [distributions_demo.ae](probabilistic/distributions_demo.ae)
- [normal_below_7_bad.ae](probabilistic/normal_below_7_bad.ae)
- [normal_below_7_good.ae](probabilistic/normal_below_7_good.ae)

### examples/sets/

- [verified_list.ae](sets/verified_list.ae)

### examples/syntax/

- [ackermann.ae](syntax/ackermann.ae)
- [axiom.ae](syntax/axiom.ae)
- [collection_literals.ae](syntax/collection_literals.ae)
- [factorial_decreasing.ae](syntax/factorial_decreasing.ae)
- [function_main.ae](syntax/function_main.ae)
- [hello_world_main.ae](syntax/hello_world_main.ae)
- [id.ae](syntax/id.ae)
- [implicit_id.ae](syntax/implicit_id.ae)
- [length.ae](syntax/length.ae)
- [linearity.ae](syntax/linearity.ae)
- [liquid_types_main.ae](syntax/liquid_types_main.ae)
- [math_example_main.ae](syntax/math_example_main.ae)
- [maxI.ae](syntax/maxI.ae)
- [method_call.ae](syntax/method_call.ae)
- [mult.ae](syntax/mult.ae)
- [mylist.ae](syntax/mylist.ae)
- [num_typeclass.ae](syntax/num_typeclass.ae)
- [pizza_check.ae](syntax/pizza_check.ae)
- [planets.ae](syntax/planets.ae)
- [pow.ae](syntax/pow.ae)
- [precedence.ae](syntax/precedence.ae)
- [refined_unit_args.ae](syntax/refined_unit_args.ae)
- [reflect_underscore.ae](syntax/reflect_underscore.ae)
- [shadow.ae](syntax/shadow.ae)
- [typeclasses.ae](syntax/typeclasses.ae)
- [typedecl.ae](syntax/typedecl.ae)
- [uninterpreted.ae](syntax/uninterpreted.ae)

### examples/synthesis/

- [cputime_energy.ae](synthesis/cputime_energy.ae)
- [dummy.ae](synthesis/dummy.ae)
- [function_refined_synthesis_args.ae](synthesis/function_refined_synthesis_args.ae)
- [hole.ae](synthesis/hole.ae)
- [hole_refined_synthesis.ae](synthesis/hole_refined_synthesis.ae)
- [int.ae](synthesis/int.ae)
- [list_Empty.aef](synthesis/list_Empty.aef)
- [list_Insert.aef](synthesis/list_Insert.aef)
- [list_Replicate.aef](synthesis/list_Replicate.aef)
- [minimize_size.ae](synthesis/minimize_size.ae)
- [multiobjective.ae](synthesis/multiobjective.ae)
- [polynomial.ae](synthesis/polynomial.ae)
- [polynomial_sketch.ae](synthesis/polynomial_sketch.ae)
- [simple_synthesis.ae](synthesis/simple_synthesis.ae)
- [synthesis_proposal.ae](synthesis/synthesis_proposal.ae)

### examples/synthesis/afta/

- [abstraction_refinement.ae](synthesis/afta/abstraction_refinement.ae)
- [pbe_firstname.ae](synthesis/afta/pbe_firstname.ae)

### examples/synthesis/amaze/

- [guard.ae](synthesis/amaze/guard.ae)

### examples/synthesis/arborist/

- [fold.ae](synthesis/arborist/fold.ae)
- [list_sum.ae](synthesis/arborist/list_sum.ae)
- [local.ae](synthesis/arborist/local.ae)

### examples/synthesis/boolean_bounded/

- [partial_relation.ae](synthesis/boolean_bounded/partial_relation.ae)
- [xor.ae](synthesis/boolean_bounded/xor.ae)

### examples/synthesis/bustle/

- [add.ae](synthesis/bustle/add.ae)
- [list.ae](synthesis/bustle/list.ae)
- [string.ae](synthesis/bustle/string.ae)
- [tree.ae](synthesis/bustle/tree.ae)

### examples/synthesis/cata/

- [conditional_select.ae](synthesis/cata/conditional_select.ae)
- [contata_pbe.ae](synthesis/cata/contata_pbe.ae)
- [double.ae](synthesis/cata/double.ae)
- [mutual_cosynth.ae](synthesis/cata/mutual_cosynth.ae)
- [mutual_pbe.ae](synthesis/cata/mutual_pbe.ae)
- [neg.ae](synthesis/cata/neg.ae)
- [operator_relational.ae](synthesis/cata/operator_relational.ae)
- [pred.ae](synthesis/cata/pred.ae)
- [relational_property.ae](synthesis/cata/relational_property.ae)
- [square.ae](synthesis/cata/square.ae)

### examples/synthesis/control/

- [cartpole.ae](synthesis/control/cartpole.ae)
- [cruise_control.ae](synthesis/control/cruise_control.ae)
- [pendulum.ae](synthesis/control/pendulum.ae)
- [pendulum_structure.ae](synthesis/control/pendulum_structure.ae)
- [reference.ae](synthesis/control/reference.ae)
- [thermostat.ae](synthesis/control/thermostat.ae)
- [thermostat_free.ae](synthesis/control/thermostat_free.ae)
- [thermostat_structure.ae](synthesis/control/thermostat_structure.ae)

### examples/synthesis/fta/

- [arithmetic_refinement.ae](synthesis/fta/arithmetic_refinement.ae)
- [input_from_csv.ae](synthesis/fta/input_from_csv.ae)
- [input_from_examples.ae](synthesis/fta/input_from_examples.ae)

### examples/synthesis/karel/

- [line.ae](synthesis/karel/line.ae)

### examples/synthesis/karel/reference/

- [conditional.ae](synthesis/karel/reference/conditional.ae)
- [harvest.ae](synthesis/karel/reference/harvest.ae)
- [left.ae](synthesis/karel/reference/left.ae)
- [move.ae](synthesis/karel/reference/move.ae)
- [pick.ae](synthesis/karel/reference/pick.ae)
- [put.ae](synthesis/karel/reference/put.ae)
- [repeat.ae](synthesis/karel/reference/repeat.ae)
- [right.ae](synthesis/karel/reference/right.ae)
- [turn.ae](synthesis/karel/reference/turn.ae)
- [while.ae](synthesis/karel/reference/while.ae)

### examples/synthesis/karel/synth/

- [conditional.ae](synthesis/karel/synth/conditional.ae)
- [harvest.ae](synthesis/karel/synth/harvest.ae)
- [left.ae](synthesis/karel/synth/left.ae)
- [move.ae](synthesis/karel/synth/move.ae)
- [pick.ae](synthesis/karel/synth/pick.ae)
- [put.ae](synthesis/karel/synth/put.ae)
- [repeat.ae](synthesis/karel/synth/repeat.ae)
- [right.ae](synthesis/karel/synth/right.ae)
- [turn.ae](synthesis/karel/synth/turn.ae)
- [while.ae](synthesis/karel/synth/while.ae)

### examples/synthesis/leveldesign/

- [dungeon.ae](synthesis/leveldesign/dungeon.ae)
- [page_layout.ae](synthesis/leveldesign/page_layout.ae)
- [pizza.ae](synthesis/leveldesign/pizza.ae)
- [supermario.ae](synthesis/leveldesign/supermario.ae)

### examples/synthesis/monotonicity/

- [identity.ae](synthesis/monotonicity/identity.ae)
- [nondecreasing.ae](synthesis/monotonicity/nondecreasing.ae)
- [relu.ae](synthesis/monotonicity/relu.ae)
- [shift.ae](synthesis/monotonicity/shift.ae)
- [strict.ae](synthesis/monotonicity/strict.ae)

### examples/synthesis/neuroevolution/

- [mnist.ae](synthesis/neuroevolution/mnist.ae)

### examples/synthesis/noisy/

- [identity.ae](synthesis/noisy/identity.ae)
- [precise.ae](synthesis/noisy/precise.ae)
- [successor.ae](synthesis/noisy/successor.ae)

### examples/synthesis/ortools/

- [array_float.ae](synthesis/ortools/array_float.ae)
- [array_int.ae](synthesis/ortools/array_int.ae)
- [float_quadratic.ae](synthesis/ortools/float_quadratic.ae)
- [int_booth.ae](synthesis/ortools/int_booth.ae)
- [int_constrained.ae](synthesis/ortools/int_constrained.ae)
- [int_let.ae](synthesis/ortools/int_let.ae)
- [int_sphere.ae](synthesis/ortools/int_sphere.ae)

### examples/synthesis/puzzle/

- [bank_deposit.ae](synthesis/puzzle/bank_deposit.ae)
- [candy_contribution.ae](synthesis/puzzle/candy_contribution.ae)
- [circle_points.ae](synthesis/puzzle/circle_points.ae)
- [coin.ae](synthesis/puzzle/coin.ae)
- [cryptarithmetic.ae](synthesis/puzzle/cryptarithmetic.ae)
- [distinct_triples.ae](synthesis/puzzle/distinct_triples.ae)
- [knapsack.ae](synthesis/puzzle/knapsack.ae)
- [linear_equation.ae](synthesis/puzzle/linear_equation.ae)
- [magic_square.ae](synthesis/puzzle/magic_square.ae)
- [map_coloring.ae](synthesis/puzzle/map_coloring.ae)
- [nand_full_adder.ae](synthesis/puzzle/nand_full_adder.ae)
- [nqueens.ae](synthesis/puzzle/nqueens.ae)
- [nurse_scheduling.ae](synthesis/puzzle/nurse_scheduling.ae)
- [pell_equation.ae](synthesis/puzzle/pell_equation.ae)
- [quadratic.ae](synthesis/puzzle/quadratic.ae)
- [scheduling.ae](synthesis/puzzle/scheduling.ae)
- [shift_assignment.ae](synthesis/puzzle/shift_assignment.ae)
- [stock_profit.ae](synthesis/puzzle/stock_profit.ae)
- [system_equations.ae](synthesis/puzzle/system_equations.ae)

### examples/synthesis/structure_guided/

- [paired_map.ae](synthesis/structure_guided/paired_map.ae)
- [tree_inorder.ae](synthesis/structure_guided/tree_inorder.ae)

### examples/synthesis/type_constrained/

- [application.ae](synthesis/type_constrained/application.ae)
- [conditional_let.ae](synthesis/type_constrained/conditional_let.ae)
- [function.ae](synthesis/type_constrained/function.ae)
- [refinement_retry.ae](synthesis/type_constrained/refinement_retry.ae)

### examples/tactics/

- [01_choose_literal.ae](tactics/01_choose_literal.ae)
- [02_choose_literal_refined.ae](tactics/02_choose_literal_refined.ae)
- [03_assumption.ae](tactics/03_assumption.ae)
- [04_apply.ae](tactics/04_apply.ae)
- [05_constructor_intro.ae](tactics/05_constructor_intro.ae)
- [06_constructor_apply.ae](tactics/06_constructor_apply.ae)
- [07_inst.ae](tactics/07_inst.ae)
- [08_split.ae](tactics/08_split.ae)
- [09_by_cases.ae](tactics/09_by_cases.ae)
- [10_pipeline.ae](tactics/10_pipeline.ae)

### examples/talk/

- [00_basic_synthesis.ae](talk/00_basic_synthesis.ae)
- [01_example.ae](talk/01_example.ae)
- [01_multiple_examples.ae](talk/01_multiple_examples.ae)
- [02_refinements.ae](talk/02_refinements.ae)
- [03_polymorphism.ae](talk/03_polymorphism.ae)
- [04_refinements_and_examples.ae](talk/04_refinements_and_examples.ae)
- [05_mutual_examples.ae](talk/05_mutual_examples.ae)
- [06_minimize.ae](talk/06_minimize.ae)
- [08_prompt.ae](talk/08_prompt.ae)

### examples/testing/

- [array_tests.ae](testing/array_tests.ae)
- [image_tests.ae](testing/image_tests.ae)
- [list_laws.ae](testing/list_laws.ae)
- [list_tests.ae](testing/list_tests.ae)
- [map_laws.ae](testing/map_laws.ae)
- [map_tests.ae](testing/map_tests.ae)
- [math_properties.ae](testing/math_properties.ae)
- [maybe_tests.ae](testing/maybe_tests.ae)
- [pair_tests.ae](testing/pair_tests.ae)
- [set_laws.ae](testing/set_laws.ae)
- [set_tests.ae](testing/set_tests.ae)
- [stack_properties.ae](testing/stack_properties.ae)
- [string_properties.ae](testing/string_properties.ae)
- [string_tests.ae](testing/string_tests.ae)
- [tuple_tests.ae](testing/tuple_tests.ae)

### examples/verification/

- [horn_tournament.ae](verification/horn_tournament.ae)
- [nn_acasxu_safety.ae](verification/nn_acasxu_safety.ae)
- [nn_classification_robustness.ae](verification/nn_classification_robustness.ae)
- [nn_classifier_margin.ae](verification/nn_classifier_margin.ae)
- [nn_dead_neuron.ae](verification/nn_dead_neuron.ae)
- [nn_monotonicity.ae](verification/nn_monotonicity.ae)
- [nn_robustness.ae](verification/nn_robustness.ae)
- [nn_verification.ae](verification/nn_verification.ae)
