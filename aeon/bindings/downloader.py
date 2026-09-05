"""Runtime helpers for ``libraries/Downloader.ae``."""

from __future__ import annotations


def new_downloader():
    return {"state": "created", "progress": 0}


def start(session):
    return {"state": "downloading", "progress": 0}


def update(session, percentage):
    return {"state": "downloading", "progress": percentage}


def finish(session):
    return {"state": "completed", "progress": 100}
