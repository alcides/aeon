# BNSynth: Bounded Boolean Functional Synthesis

## Boolean Function Synthesis:

BNSynth synthesizes Boolean functions under a specified bound (K) on formula size in terms of number of clauses. BNSynth uses a
counter-example guided, neural approach to solve the bounded BFS problem.

To know more about BNSynth, refer to the talk [video](https://youtu.be/xaaopov3eZc).

## Environment
Python 3

## Requirements
- PyTorch 
```
pip install torch==1.8.1+cu102 torchvision==0.9.1+cu102 torchaudio===0.8.1 -f https://download.pytorch.org/whl/torch_stable.html
```
- NumPy
```
pip install numpy
```
- ArgParse
```
pip install argparse
```
- z3py
```
pip install z3-solver
```
- Antlr4
```
pip install antlr4-python3-runtime
```

## Run individual benchmark
```
./bnsynth.sh lut1_2_2.v 10 cnf 1
```
- Arg1: Benchmark name (see benchmarks/custom_and_lut/)
- Arg2: Bound on number of clauses (K)
- Arg3: Formula format (CNF/DNF)
- Arg4: Architecture (1/2/3)

## Terminal output
![ss](experiments/ss_terminal.png)

## Run for all benchmarks in benchmarks/custom_and_lut/
```python experiments/evaluate.py```

## More information on options:
```
python bnsynth.py --help
```

## References:
- Manthan: https://arxiv.org/pdf/2005.06922.pdf
- GCLN: https://arxiv.org/pdf/2003.07959.pdf

## Collaborators:
- Ravi Raja
- Stanly Samuel
- Chiranjib Bhattacharyya
- Deepak D'Souza
- Aditya Kanade
