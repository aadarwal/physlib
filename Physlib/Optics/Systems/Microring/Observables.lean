/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Systems.Microring.ObservablesFrequency

/-!
# Microring observables

## i. Overview

This module collects the fixed-frequency add-drop power observables and the proof-gated N5F
frequency response. It introduces no declarations or additional claims.

## ii. Key results

- `AddDrop.throughPower_eq_closedForm` and `AddDrop.dropPower_eq_closedForm`.
- `AddDrop.lossless_through_drop_power_balance`.
- `AddDrop.NondispersiveGroupIndexModel.nondispersive_throughPower_periodic` and
  `AddDrop.NondispersiveGroupIndexModel.nondispersive_dropPower_periodic`.

## iii. Table of contents

- A. Module contents

## iv. References

The imported modules state their N5F, N6, and N7 declaration locations and their respective
non-claims.

## A. Module contents
-/
