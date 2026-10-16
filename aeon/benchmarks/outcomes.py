"""Stable synthesis-failure classification, including legacy run diagnostics."""


def unsupported_goal(stderr: str) -> bool:
    """Recognize capability mismatches without hiding unrelated exceptions.

    Legacy CP-SAT runs exited one with a traceback. Current versions use the
    typed UnsupportedSynthesisGoal exception and a stable diagnostic prefix.
    """
    markers = (
        "Unsupported synthesis goal:",
        "CPSatHole cannot handle hole ",
        "CPSatHole cannot translate the objective (",
        "CPSatHole requires at least one @minimize/@maximize objective.",
        "CPSatHole objective must be a number, not an array.",
        "CPSatHole could not find objective function ",
    )
    return any(marker in stderr for marker in markers)
