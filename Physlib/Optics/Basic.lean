/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

/-!

# Optics

## i. Scope

The optics API describes reduced models of light and optical components built on the field-level
theory in `Physlib.Electromagnetism`. Its intended scope includes monochromatic phasors,
polarization and ray representations, optical interfaces and observables, finite-mode scattering
models, and the composition of components into optical systems.

## ii. Layering

Generic geometry, complex linear algebra and Fourier analysis remain in Mathlib or the relevant
mathematical Physlib APIs. Field-level electromagnetic concepts, including material constitutive
data and energy flux, belong in `Physlib.Electromagnetism`; Optics should depend on those APIs as
they are developed rather than introduce competing definitions. Optics owns reduced optical states,
component laws derived from field theory, and their system-level composition.

-/

@[expose] public section
