/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Components.Retarder.Coherency
public import Physlib.Optics.Components.Retarder.MuellerRegression

/-!
# Ideal linear retarders and wave plates

## i. Overview

This module exports the ideal linear-retarder phase convention, spectral Jones matrix, structural
and unitarity laws, equal-amplitude relative-phase action, pure-coherency outputs, deterministic
Mueller block and action, quarter-wave and half-wave specializations, and sign-sensitive canonical
regressions.

Jones and Stokes intensity statements remain reduced amplitude coordinates. Unguarded convention
statement (review only): the export surface assigns no circular-polarization handedness name.
It assigns no electromagnetic irradiance or power interpretation either.

## ii. Key results

The public declarations are documented in the imported semantic and regression modules.

## iii. Table of contents

- A. Export surface

## iv. References

This export-only module introduces no additional physical claim.
-/

/-!

## A. Export surface
-/
