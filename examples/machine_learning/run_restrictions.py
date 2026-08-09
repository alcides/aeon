"""
Executa os pares as restricoes da biblioteca ML.

Cada numero tem um programa ``valid`` e outro ``invalid``. Nos casos 01--10,
o programa invalido tem de ser recusado antes da execucao. O caso 11 mostra o
limite inevitavel da verificacao estatica: o conteudo de um CSV so pode ser
validado no runtime.
"""

from __future__ import annotations

import argparse
import math
import os
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Literal


REPOSITORY_ROOT = Path(__file__).resolve().parents[2]
RESTRICTIONS_DIR = REPOSITORY_ROOT / "examples" / "machine_learning" / "restrictions"

# Permite executar este ficheiro a partir de qualquer diretoria.
sys.path.insert(0, str(REPOSITORY_ROOT))
os.chdir(REPOSITORY_ROOT)

from aeon.bindings.machine_learning import MLRestrictionError  # noqa: E402
from aeon.facade.api import (  # noqa: E402
    LinearUnusedError,
    LinearUsedTooManyTimesError,
    LiquidTypeCheckingFailedRelation,
    UnificationSubtypingError,
)
from aeon.facade.driver import AeonConfig, AeonDriver  # noqa: E402
from aeon.logger.logger import setup_logger  # noqa: E402
from aeon.synthesis.uis.api import SilentSynthesisUI  # noqa: E402


RejectionPhase = Literal["static", "runtime"]


@dataclass(frozen=True)
class RestrictionCase:
    number: str
    title: str
    valid_name: str
    invalid_name: str
    rejection_phase: RejectionPhase
    expected_static_error: type[Exception] | None = None

    @property
    def valid_path(self) -> Path:
        return RESTRICTIONS_DIR / self.valid_name

    @property
    def invalid_path(self) -> Path:
        return RESTRICTIONS_DIR / self.invalid_name


CASES = (
    RestrictionCase(
        "01",
        "DataFrame: target consome uma vez",
        "01_dataframe_target_valid.ae",
        "01_dataframe_target_invalid.ae",
        "static",
        LinearUsedTooManyTimesError,
    ),
    RestrictionCase(
        "02",
        "Dataset: split consome uma vez",
        "02_dataset_split_valid.ae",
        "02_dataset_split_invalid.ae",
        "static",
        LinearUsedTooManyTimesError,
    ),
    RestrictionCase(
        "03",
        "DatasetSplit: consume_split usa uma vez",
        "03_datasetsplit_consume_valid.ae",
        "03_datasetsplit_consume_invalid.ae",
        "static",
        LinearUsedTooManyTimesError,
    ),
    RestrictionCase(
        "04",
        "TrainingDataset: treino usa uma vez",
        "04_training_train_valid.ae",
        "04_training_train_invalid.ae",
        "static",
        LinearUsedTooManyTimesError,
    ),
    RestrictionCase(
        "05",
        "TestingDataset: accuracy usa uma vez",
        "05_testing_accuracy_valid.ae",
        "05_testing_accuracy_invalid.ae",
        "static",
        LinearUsedTooManyTimesError,
    ),
    RestrictionCase(
        "06",
        "Fracao de split: 0.0 < f < 1.0",
        "06_split_fraction_valid.ae",
        "06_split_fraction_invalid.ae",
        "static",
        LiquidTypeCheckingFailedRelation,
    ),
    RestrictionCase(
        "07",
        "Indice do target dentro das colunas",
        "07_target_index_valid.ae",
        "07_target_index_invalid.ae",
        "static",
        LiquidTypeCheckingFailedRelation,
    ),
    RestrictionCase(
        "08",
        "Papeis nominais de treino e teste",
        "08_train_test_roles_valid.ae",
        "08_train_test_roles_invalid.ae",
        "static",
        UnificationSubtypingError,
    ),
    RestrictionCase(
        "09",
        "Recurso linear nao pode ser abandonado",
        "09_linear_resource_used_valid.ae",
        "09_linear_resource_used_invalid.ae",
        "static",
        LinearUnusedError,
    ),
    RestrictionCase(
        "10",
        "Accuracy limitada ao intervalo [0, 1]",
        "10_accuracy_bounds_valid.ae",
        "10_accuracy_bounds_invalid.ae",
        "static",
        LiquidTypeCheckingFailedRelation,
    ),
    RestrictionCase(
        "11",
        "Conteudo real do CSV validado no runtime",
        "11_runtime_data_valid.ae",
        "11_runtime_data_invalid.ae",
        "runtime",
    ),
)


def new_driver() -> AeonDriver:
    config = AeonConfig(
        synthesizer="none",
        synthesis_ui=SilentSynthesisUI(),
        synthesis_budget=0,
        no_main=False,
        contracts=False,
    )
    return AeonDriver(config)


def parse_program(path: Path) -> tuple[AeonDriver, list[Exception]]:
    driver = new_driver()
    return driver, list(driver.parse(filename=str(path)))


def valid_score(result: object) -> bool:
    return (
        not isinstance(result, bool)
        and isinstance(result, (int, float))
        and math.isfinite(float(result))
        and 0.0 <= float(result) <= 1.0
    )


def format_error(error: Exception) -> str:
    return " ".join(str(error).splitlines())


def check_valid(case: RestrictionCase, details: bool) -> bool:
    driver, errors = parse_program(case.valid_path)
    if errors:
        print(f"  [FALHOU] valid: rejeitado por {type(errors[0]).__name__}")
        if details:
            print(f"           {format_error(errors[0])}")
        return False

    try:
        result = driver.run()
    except Exception as error:  # runner de demonstracao: mostra qualquer falha inesperada
        print(f"  [FALHOU] valid: excecao inesperada {type(error).__name__}: {error}")
        return False

    if not valid_score(result):
        print(f"  [FALHOU] valid: resultado inesperado {result!r}")
        return False

    print(f"  [OK] valid: verificacao estatica + execucao; accuracy={float(result):.4f}")
    return True


def check_static_invalid(case: RestrictionCase, details: bool) -> bool:
    _, errors = parse_program(case.invalid_path)
    expected = case.expected_static_error
    if not errors:
        print("  [FALHOU] invalid: o compilador aceitou o anti-exemplo")
        return False
    if len(errors) != 1 or expected is None or not isinstance(errors[0], expected):
        names = ", ".join(type(error).__name__ for error in errors)
        expected_name = expected.__name__ if expected is not None else "erro estatico"
        print(f"  [FALHOU] invalid: esperava apenas {expected_name}; recebeu {names}")
        if details:
            for error in errors:
                print(f"           {format_error(error)}")
        return False

    print(f"  [OK] invalid: rejeicao estatica ({type(errors[0]).__name__})")
    if details:
        print(f"           {format_error(errors[0])}")
    return True


def check_runtime_invalid(case: RestrictionCase, details: bool) -> bool:
    driver, errors = parse_program(case.invalid_path)
    if errors:
        print(f"  [FALHOU] invalid: devia passar estaticamente; recebeu {type(errors[0]).__name__}")
        if details:
            print(f"           {format_error(errors[0])}")
        return False

    try:
        result = driver.run()
    except MLRestrictionError as error:
        print(f"  [OK] invalid: passou o tipo e foi rejeitado no runtime ({type(error).__name__})")
        if details:
            print(f"           {format_error(error)}")
        return True
    except Exception as error:  # distingue a restricao esperada de bugs acidentais
        print(f"  [FALHOU] invalid: excecao inesperada {type(error).__name__}: {error}")
        return False

    print(f"  [FALHOU] invalid: executou sem MLRestrictionError; resultado={result!r}")
    return False


def run_case(case: RestrictionCase, details: bool) -> tuple[bool, bool]:
    print(f"\n[{case.number}] {case.title}")
    valid_ok = check_valid(case, details)
    if case.rejection_phase == "static":
        invalid_ok = check_static_invalid(case, details)
    else:
        invalid_ok = check_runtime_invalid(case, details)
    return valid_ok, invalid_ok


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--caso",
        choices=[case.number for case in CASES],
        help="executa apenas um par, por exemplo --caso 04",
    )
    parser.add_argument(
        "--detalhes",
        action="store_true",
        help="mostra a mensagem completa da rejeicao esperada",
    )
    return parser.parse_args()


def main() -> int:
    # Evita que diagnosticos com caracteres de refinamentos falhem em terminais
    # Windows cuja pagina de codigo nao consegue representar esses caracteres.
    if hasattr(sys.stdout, "reconfigure"):
        sys.stdout.reconfigure(errors="backslashreplace")
    setup_logger()

    args = parse_args()
    selected = [case for case in CASES if args.caso is None or case.number == args.caso]
    print("Demonstracao das restricoes da biblioteca ML")
    print("valid = deve verificar e executar; invalid = deve ser bloqueado")

    checks = [result for case in selected for result in run_case(case, args.detalhes)]
    passed = sum(checks)
    total = len(checks)
    print(f"\nResumo: {passed}/{total} verificacoes passaram.")
    return 0 if passed == total else 1


if __name__ == "__main__":
    raise SystemExit(main())
