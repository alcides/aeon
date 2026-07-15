import numpy as np
import pandas as pd

def read_csv(path):
    """Read a CSV file into a pandas DataFrame (all columns kept)."""
    return pd.read_csv(path)

