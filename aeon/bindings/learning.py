import sklearn.model_selection
import numpy as np
from sklearn.ensemble import RandomForestClassifier
from collections import Counter
from imblearn.over_sampling import SMOTE
from sklearn.metrics import accuracy_score, confusion_matrix
from sklearn.preprocessing import StandardScaler, MinMaxScaler
import pandas as pd

def train_test_split_pairs(X, y, test_size):
    """
    Splits features X and labels y into training and test sets, then zips them into (x, y) pairs.

    Parameters:
        X (list): List of feature vectors.
        y (list): List of labels.
        test_size (float): Fraction of the dataset to use as the test set.

    Returns:
        tuple: (train, test), where train and test are lists of (x, y) pairs.
    """
    X_train, X_test, y_train, y_test = sklearn.model_selection.train_test_split(X, y, test_size=test_size)
    train = list(zip(X_train, y_train))
    test = list(zip(X_test, y_test))
    return train, test

def balanced(ds):
    """
    Checks if a dataset is balanced (all classes have the same number of samples).

    Parameters:
        ds (tuple): Tuple (X, y), where X is a list of feature vectors and y is a list of labels.

    Returns:
        bool: True if all classes have the same count, False otherwise.
    """
    _, y = ds
    counts = Counter(y) # count occurrences of each class label
    return len(set(counts.values())) == 1 # ensure all classes have the same count

def load_dataset(filename):
    """
    Loads a dataset from a CSV file, assuming the last column is the label.

    Parameters:
        filename (str): Path to the CSV file.

    Returns:
        tuple: (X, y), where X is a list of feature vectors and y is a list of labels.
    """
    df = pd.read_csv(filename)
    X = df.iloc[:, :-1].values.tolist()
    y = df.iloc[:, -1].tolist()
    return (X, y)

def split_dataset(ds, fraction):
    """
    Splits a dataset into training and test sets according to the given fraction.

    Parameters:
        ds (tuple): Tuple (X, y), where X is a list of feature vectors and y is a list of labels.
        fraction (float): Fraction of the dataset to use as the training set.

    Returns:
        tuple: ((X_train, y_train), (X_test, y_test))
    """
    X, y = ds
    X_train, X_test, y_train, y_test = sklearn.model_selection.train_test_split(
        X, y, test_size=1-fraction
    )
    return ( (X_train, y_train), (X_test, y_test) )

def train_random_forest(dataset):
    """
    Trains a RandomForestClassifier on the given dataset.

    Parameters:
        dataset (tuple): Tuple (X, y), where X is a list of feature vectors and y is a list of labels.

    Returns:
        RandomForestClassifier: The trained classifier.
    """
    X, y = dataset
    clf = RandomForestClassifier()
    clf.fit(X, y)
    return clf

def smote_oversample(ds):
    """
    Applies SMOTE oversampling to balance the classes in the dataset.

    Parameters:
        ds (tuple): Tuple (X, y), where X is a list of feature vectors and y is a list of labels.

    Returns:
        tuple: (X_res, y_res), the oversampled features and labels as lists.
    """
    X, y = ds
    X_res, y_res = SMOTE().fit_resample(X, y)
    return (X_res.tolist(), y_res.tolist())

def predict(model, ds):
    """
    Uses the given model to predict labels for the features in ds.

    Parameters:
        model: Trained classifier with a predict method.
        ds (tuple): Tuple (X, _), where X is a list of feature vectors.

    Returns:
        list: Predicted labels.
    """
    X, _ = ds
    y_pred = model.predict(X)
    return y_pred.tolist()

def score(model, ds):
    """
    Computes the accuracy score of the model on the given dataset.

    Parameters:
        model: Trained classifier with a score method.
        ds (tuple): Tuple (X, y), where X is a list of feature vectors and y is a list of labels.

    Returns:
        float: Accuracy score.
    """
    X, y = ds
    return float(model.score(X, y))

def confusion_matrix_(model, ds):
    """
    Computes the confusion matrix for the model's predictions on the dataset.

    Parameters:
        model: Trained classifier with a predict method.
        ds (tuple): Tuple (X, y), where X is a list of feature vectors and y is a list of labels.

    Returns:
        list: Confusion matrix as a nested list.
    """
    X, y = ds
    y_pred = model.predict(X)
    cm = confusion_matrix(y, y_pred)
    return cm.tolist()

def standard_scale(ds):
    """
    Scales features in the dataset to have zero mean and unit variance.

    Parameters:
        ds (tuple): Tuple (X, y), where X is a list of feature vectors and y is a list of labels.

    Returns:
        tuple: (X_scaled, y), where X_scaled is the scaled features as a list.
    """
    X, y = ds
    scaler = StandardScaler()
    X_scaled = scaler.fit_transform(X)
    return (X_scaled.tolist(), y)

def minmax_scale(ds):
    """
    Scales features in the dataset to the [0, 1] range.

    Parameters:
        ds (tuple): Tuple (X, y), where X is a list of feature vectors and y is a list of labels.

    Returns:
        tuple: (X_scaled, y), where X_scaled is the scaled features as a list.
    """
    X, y = ds
    scaler = MinMaxScaler()
    X_scaled = scaler.fit_transform(X)
    return (X_scaled.tolist(), y)