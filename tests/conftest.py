"""Reproducible CI properties; larger generated campaigns run on a schedule."""

import os

from hypothesis import settings

settings.register_profile("ci", max_examples=40, derandomize=True, deadline=None)
settings.register_profile("nightly", max_examples=200, deadline=None)
settings.load_profile(os.environ.get("HYPOTHESIS_PROFILE", "default"))
