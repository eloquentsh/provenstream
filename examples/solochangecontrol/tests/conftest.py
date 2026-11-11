# Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
# SPDX-License-Identifier: MIT
"""The expensive layer is opt-in: `--mutants` runs tests/mutants.py (dozens of engine builds) as a test."""
import pytest


def pytest_addoption(parser):
    parser.addoption("--mutants", action="store_true", default=False,
                     help="build every engine mutant of the layer and require the state machine to kill it")


@pytest.fixture
def mutants_requested(request):
    return request.config.getoption("--mutants")
