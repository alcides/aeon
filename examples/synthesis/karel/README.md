# Embedded Karel DSL

Karel programs are Aeon functions of type `World -> World`; there is no second parser or language.
`Karel` supplies actions such as `move`, `turn_left`, and `pick_marker`; `repeat` and `if_karel`
are ordinary Aeon higher-order combinators. Run `line.ae` with `python -m aeon`.
