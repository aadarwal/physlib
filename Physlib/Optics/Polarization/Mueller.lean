/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Polarization.Mueller.Regression
public import Physlib.Optics.Polarization.Mueller.Trace
public import Physlib.Optics.Polarization.Mueller.Unitary

/-!
# Deterministic Jones-induced Mueller transformations

This module exports the raw Mueller carrier, the Jones-induced Stokes action and commuting-square
theorems, its Pauli trace formula, identity/cascade/scalar laws, unitary Poincare consequences, and
sign-sensitive convention regressions.

The exported construction is deterministic and nondepolarizing. An arbitrary raw `MuellerMatrix`
is not thereby physically admissible or Jones-induced, and general depolarizing transformations
require a later positive-map layer on coherency data.
-/
