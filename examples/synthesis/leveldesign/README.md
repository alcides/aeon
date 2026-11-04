# Level design and assignments

Four synthesis examples generate structured layouts or assignments.

| Program | Task |
| --- | --- |
| [supermario.ae](supermario.ae) | Generate a level with positioned boxes and enemies; maximize coverage and minimize conflicts |
| [dungeon.ae](dungeon.ae) | Generate rooms, monsters, and loot under coverage/conflict objectives |
| [pizza.ae](pizza.ae) | Assign seven distinct pizzas while satisfying individual preferences |
| [page_layout.ae](page_layout.ae) | Place three rectangles inside a page without overlaps |

Super Mario and dungeon generation are local Aeon examples. Pizza assignment
cites a gist, and page layout cites a Z3 tutorial; the source headers preserve
those attributions. The folder groups their application domains rather than
identifying a published benchmark suite.

Run from the repository root:

```bash
python -m aeon --check --no-main examples/synthesis/leveldesign/supermario.ae
python -m aeon --no-main --budget 30 -s gp examples/synthesis/leveldesign/pizza.ae
```
