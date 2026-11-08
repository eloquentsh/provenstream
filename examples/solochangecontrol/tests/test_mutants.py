# Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
# SPDX-License-Identifier: MIT
"""The mutant layer as a test, opt-in (`pytest --mutants`): every rule mutant and every killable order mutant of the
layer dies under the state machine; the provably equivalent order mutants survive (mutants.py)."""
import os, sys

import pytest

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)


def test_every_mutant_is_killed(mutants_requested):
    if not mutants_requested:
        pytest.skip("pass --mutants to build and run the engine mutants (minutes)")
    import mutants
    assert mutants.main([]) == 0, "see MUTANTS.md beside the tests"
