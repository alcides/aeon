from aeon.bindings.binding_utils import curried

import numpy as np
import pandas as pd

from sklearn.tree import DecisionTreeClassifier


def read_csv(path):
    """Read a CSV file into a pandas DataFrame (all columns kept)."""
    return pd.read_csv(path)

@curried
def target(df, column):
    """Return a Dataset object with the target column specified by the column index."""
    x = df.drop(df.columns[column], axis=1).values
    y = df.iloc[:, column].values
    return (x, y)

@curried
def split(ds, train_size):
    """Split a dataset into training and testing sets."""
    x, y = ds
    n_samples = x.shape[0]
    n_train = int(n_samples * train_size)
    indices = np.random.permutation(n_samples)
    train_indices = indices[:n_train]
    test_indices = indices[n_train:]
    return (x[train_indices], y[train_indices]), (x[test_indices], y[test_indices])

@curried
def train_model(model, ds):
    """Train a model on the given dataset."""
    x, y = ds
    model.fit(x, y)
    return model

def decision_tree_classifier(ds):
    """Train a Decision Tree Classifier on the given dataset."""
    return train_model(DecisionTreeClassifier(), ds)

def accuracy(model, ds):
    """Test a model on the given dataset and return the accuracy."""
    x, y = ds
    return model.score(x, y)




def train_of(parts):
    """Return the training part of a split dataset."""
    return parts[0]

def test_of(parts):
    """Return the testing part of a split dataset."""
    return parts[1]