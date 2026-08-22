/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Components.Polarizer.Coherency
public import Physlib.Optics.Components.Polarizer.Mueller
public import Physlib.Optics.Components.Polarizer.Regression

/-!
# Ideal linear polarizers

## i. Overview

This module exports the normalized linear-axis Jones projector, its projection and contraction
properties, coherent and squared-intensity forms of Malus' law, coherency transport, and the exact
Jones-induced Mueller action on arbitrary raw Stokes data.

The exported intensity results concern squared raw Jones amplitude and raw Stokes coordinates.
They make no claim about electromagnetic irradiance, Poynting flux, or normalized modal power.

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
