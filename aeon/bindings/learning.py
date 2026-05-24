"""Python bindings for the Aeon ``Learning`` library.

Each function exposed to Aeon is named ``Learning_<name>`` and curried so
that the native string ``Learning_<name>(a, b)`` can be partially or fully
applied. Aeon's ``Dataset`` is a plain ``(X, y)`` Python tuple — the
splitting of features and target is hidden from the surface language so
users never have to think about ``X``/``y`` directly. ``DataFrame`` is a
pandas ``DataFrame`` retained when the source still has all columns
together.
"""

from __future__ import annotations

import math
from typing import Any

import numpy as np
import pandas as pd
from sklearn.ensemble import (
    GradientBoostingClassifier,
    GradientBoostingRegressor,
    RandomForestClassifier,
    RandomForestRegressor,
)
from sklearn.impute import SimpleImputer
from sklearn.linear_model import (
    ElasticNet,
    Lasso,
    LinearRegression,
    LogisticRegression,
    Ridge,
)
from sklearn.metrics import (
    accuracy_score,
    classification_report,
    confusion_matrix,
    explained_variance_score,
    f1_score,
    mean_absolute_error,
    mean_squared_error,
    precision_score,
    r2_score,
    recall_score,
    roc_auc_score,
)
from sklearn.model_selection import train_test_split
from sklearn.naive_bayes import ComplementNB, GaussianNB, MultinomialNB
from sklearn.neighbors import KNeighborsClassifier, KNeighborsRegressor
from sklearn.neural_network import MLPClassifier, MLPRegressor
from sklearn.preprocessing import MinMaxScaler, RobustScaler, StandardScaler
from sklearn.svm import SVC, SVR
from sklearn.tree import DecisionTreeClassifier, DecisionTreeRegressor

from aeon.bindings.binding_utils import curried


# ─── helpers (not exposed to Aeon) ───────────────────────────────────────


def _as_xy(ds: Any) -> tuple[Any, Any]:
    X, y = ds
    return X, y


def _xy(X: Any, y: Any) -> tuple[Any, Any]:
    return (X, y)


def _counts(y: Any) -> dict[Any, int]:
    s = pd.Series(y)
    return s.value_counts().to_dict()


def _smote_lazy() -> Any:
    from imblearn.over_sampling import SMOTE

    return SMOTE


def _random_oversampler_lazy() -> Any:
    from imblearn.over_sampling import RandomOverSampler

    return RandomOverSampler


def _random_undersampler_lazy() -> Any:
    from imblearn.under_sampling import RandomUnderSampler

    return RandomUnderSampler


# ─── Loading / target selection ─────────────────────────────────────────


@curried
def Learning_read_csv(path):
    """Read a CSV file into a pandas DataFrame (all columns kept)."""
    return pd.read_csv(path)


@curried
def Learning_target(df, column):
    """Designate ``column`` as the target; return the ``(X, y)`` Dataset."""
    y = df[column].tolist()
    X = df.drop(columns=[column]).values.tolist()
    return _xy(X, y)


@curried
def Learning_target_at(df, index):
    """Designate the column at ``index`` (0-based) as the target."""
    column = df.columns[index]
    return Learning_target(df, column)


@curried
def Learning_load(path):
    """Convenience: read a CSV and use the *last* column as the target."""
    df = pd.read_csv(path)
    return Learning_target_at(df, len(df.columns) - 1)


@curried
def Learning_columns(df):
    """Return the list of column names."""
    return list(df.columns)


@curried
def Learning_has_column(df, column):
    return column in df.columns


# ─── Dataset introspection ──────────────────────────────────────────────


@curried
def Learning_n_rows(ds):
    X, _ = _as_xy(ds)
    return len(X)


@curried
def Learning_n_features(ds):
    X, _ = _as_xy(ds)
    if len(X) == 0:
        return 0
    return len(X[0])


@curried
def Learning_is_balanced(ds):
    _, y = _as_xy(ds)
    counts = _counts(y)
    return len(set(counts.values())) == 1


@curried
def Learning_class_counts(ds):
    """Return a list of (label, count) tuples sorted by label."""
    _, y = _as_xy(ds)
    items = sorted(_counts(y).items(), key=lambda kv: str(kv[0]))
    return [list(kv) for kv in items]


# ─── Splitting ──────────────────────────────────────────────────────────


@curried
def Learning_split(ds, fraction):
    """Split into (training, testing). ``fraction`` is the training share."""
    X, y = _as_xy(ds)
    X_train, X_test, y_train, y_test = train_test_split(X, y, test_size=1 - fraction)
    return (_xy(X_train, y_train), _xy(X_test, y_test))


@curried
def Learning_split_training(ds, fraction):
    return Learning_split(ds, fraction)[0]


@curried
def Learning_split_testing(ds, fraction):
    return Learning_split(ds, fraction)[1]


# ─── Resampling / balancing ─────────────────────────────────────────────


@curried
def Learning_smote(ds):
    X, y = _as_xy(ds)
    smote = _smote_lazy()()
    X_res, y_res = smote.fit_resample(X, y)
    return _xy(np.asarray(X_res).tolist(), list(y_res))


@curried
def Learning_random_oversample(ds):
    X, y = _as_xy(ds)
    ros = _random_oversampler_lazy()()
    X_res, y_res = ros.fit_resample(X, y)
    return _xy(np.asarray(X_res).tolist(), list(y_res))


@curried
def Learning_random_undersample(ds):
    X, y = _as_xy(ds)
    rus = _random_undersampler_lazy()()
    X_res, y_res = rus.fit_resample(X, y)
    return _xy(np.asarray(X_res).tolist(), list(y_res))


# ─── Scaling ────────────────────────────────────────────────────────────


def _scale(ds, scaler):
    X, y = _as_xy(ds)
    X_scaled = scaler.fit_transform(X).tolist()
    return _xy(X_scaled, y)


@curried
def Learning_standard_scale(ds):
    return _scale(ds, StandardScaler())


@curried
def Learning_minmax_scale(ds):
    return _scale(ds, MinMaxScaler())


@curried
def Learning_robust_scale(ds):
    return _scale(ds, RobustScaler())


# ─── Missing-value imputation ───────────────────────────────────────────


def _impute(ds, strategy, fill_value=None):
    X, y = _as_xy(ds)
    imp = SimpleImputer(strategy=strategy, fill_value=fill_value)
    X_imp = imp.fit_transform(X).tolist()
    return _xy(X_imp, y)


@curried
def Learning_fill_mean(ds):
    return _impute(ds, "mean")


@curried
def Learning_fill_median(ds):
    return _impute(ds, "median")


@curried
def Learning_fill_most_frequent(ds):
    return _impute(ds, "most_frequent")


@curried
def Learning_fill_constant(ds, value):
    return _impute(ds, "constant", fill_value=value)


# ─── Classifier training ────────────────────────────────────────────────


def _fit(model, ds):
    X, y = _as_xy(ds)
    model.fit(X, y)
    return model


@curried
def Learning_random_forest_classifier(ds):
    return _fit(RandomForestClassifier(), ds)


@curried
def Learning_random_forest_classifier_n(n, ds):
    return _fit(RandomForestClassifier(n_estimators=n), ds)


@curried
def Learning_logistic_regression(ds):
    return _fit(LogisticRegression(max_iter=1000), ds)


@curried
def Learning_decision_tree_classifier(ds):
    return _fit(DecisionTreeClassifier(), ds)


@curried
def Learning_gradient_boosting_classifier(ds):
    return _fit(GradientBoostingClassifier(), ds)


@curried
def Learning_knn_classifier(ds):
    return _fit(KNeighborsClassifier(), ds)


@curried
def Learning_knn_classifier_k(k, ds):
    return _fit(KNeighborsClassifier(n_neighbors=k), ds)


@curried
def Learning_svc(ds):
    return _fit(SVC(probability=True), ds)


@curried
def Learning_gaussian_nb(ds):
    return _fit(GaussianNB(), ds)


@curried
def Learning_multinomial_nb(ds):
    return _fit(MultinomialNB(), ds)


@curried
def Learning_complement_nb(ds):
    return _fit(ComplementNB(), ds)


@curried
def Learning_mlp_classifier(ds):
    return _fit(MLPClassifier(max_iter=500), ds)


# ─── Regressor training ─────────────────────────────────────────────────


@curried
def Learning_linear_regression(ds):
    return _fit(LinearRegression(), ds)


@curried
def Learning_ridge(ds):
    return _fit(Ridge(), ds)


@curried
def Learning_ridge_alpha(alpha, ds):
    return _fit(Ridge(alpha=alpha), ds)


@curried
def Learning_lasso(ds):
    return _fit(Lasso(), ds)


@curried
def Learning_lasso_alpha(alpha, ds):
    return _fit(Lasso(alpha=alpha), ds)


@curried
def Learning_elastic_net(ds):
    return _fit(ElasticNet(), ds)


@curried
def Learning_random_forest_regressor(ds):
    return _fit(RandomForestRegressor(), ds)


@curried
def Learning_random_forest_regressor_n(n, ds):
    return _fit(RandomForestRegressor(n_estimators=n), ds)


@curried
def Learning_decision_tree_regressor(ds):
    return _fit(DecisionTreeRegressor(), ds)


@curried
def Learning_gradient_boosting_regressor(ds):
    return _fit(GradientBoostingRegressor(), ds)


@curried
def Learning_knn_regressor(ds):
    return _fit(KNeighborsRegressor(), ds)


@curried
def Learning_svr(ds):
    return _fit(SVR(), ds)


@curried
def Learning_mlp_regressor(ds):
    return _fit(MLPRegressor(max_iter=500), ds)


# ─── Prediction ─────────────────────────────────────────────────────────


@curried
def Learning_predict(model, ds):
    X, _ = _as_xy(ds)
    return list(model.predict(X))


@curried
def Learning_predict_proba(model, ds):
    X, _ = _as_xy(ds)
    return model.predict_proba(X).tolist()


# ─── Classification metrics ─────────────────────────────────────────────


def _predicted_pair(model, ds):
    X, y = _as_xy(ds)
    return list(y), list(model.predict(X))


@curried
def Learning_accuracy(model, ds):
    y_true, y_pred = _predicted_pair(model, ds)
    return float(accuracy_score(y_true, y_pred))


@curried
def Learning_precision(model, ds):
    y_true, y_pred = _predicted_pair(model, ds)
    return float(precision_score(y_true, y_pred, average="weighted", zero_division=0))


@curried
def Learning_recall(model, ds):
    y_true, y_pred = _predicted_pair(model, ds)
    return float(recall_score(y_true, y_pred, average="weighted", zero_division=0))


@curried
def Learning_f1(model, ds):
    y_true, y_pred = _predicted_pair(model, ds)
    return float(f1_score(y_true, y_pred, average="weighted", zero_division=0))


@curried
def Learning_roc_auc(model, ds):
    X, y = _as_xy(ds)
    proba = model.predict_proba(X)
    classes = list(getattr(model, "classes_", []))
    if len(classes) == 2:
        return float(roc_auc_score(y, proba[:, 1]))
    return float(roc_auc_score(y, proba, multi_class="ovr", average="weighted"))


@curried
def Learning_confusion_matrix(model, ds):
    y_true, y_pred = _predicted_pair(model, ds)
    return confusion_matrix(y_true, y_pred).tolist()


@curried
def Learning_classification_report(model, ds):
    y_true, y_pred = _predicted_pair(model, ds)
    return classification_report(y_true, y_pred, zero_division=0)


# ─── Regression metrics ─────────────────────────────────────────────────


@curried
def Learning_mse(model, ds):
    y_true, y_pred = _predicted_pair(model, ds)
    return float(mean_squared_error(y_true, y_pred))


@curried
def Learning_rmse(model, ds):
    y_true, y_pred = _predicted_pair(model, ds)
    return float(math.sqrt(mean_squared_error(y_true, y_pred)))


@curried
def Learning_mae(model, ds):
    y_true, y_pred = _predicted_pair(model, ds)
    return float(mean_absolute_error(y_true, y_pred))


@curried
def Learning_r2(model, ds):
    y_true, y_pred = _predicted_pair(model, ds)
    return float(r2_score(y_true, y_pred))


@curried
def Learning_explained_variance(model, ds):
    y_true, y_pred = _predicted_pair(model, ds)
    return float(explained_variance_score(y_true, y_pred))
