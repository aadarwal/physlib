/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.SpaceAndTime.Space.DistOfFunction
public import Physlib.SpaceAndTime.Space.OrientedAffineHyperplane

/-!
# Sidewise function distributions across oriented affine hyperplanes

## i. Overview

This file represents ambient extensions of two independently supplied side functions as one
ambient distribution. Each extension contributes only on its corresponding strict open
half-space, so its values on the carrier and the opposite side are ignored. The carrier itself is
omitted from both integrals; no boundary trace, surface source, or jump law is inserted by this
definition.

## ii. Key results

- `OrientedAffineHyperplane.distOfSidewiseFunction`: the sum of the two open-half-space function
  distributions.
- `OrientedAffineHyperplane.distOfSidewiseFunction_apply`: its literal two-integral action.

## iii. Table of contents

- A. Sidewise function distributions

## iv. References

This is neutral distribution infrastructure. It does not derive a distributional derivative
formula, identify a hyperplane-supported term, or assume a physical interface law.
-/

@[expose] public section

open MeasureTheory SchwartzMap

namespace Space

noncomputable section

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]

namespace OrientedAffineHyperplane

/-!
## A. Sidewise function distributions
-/

/-- The ambient distribution obtained by integrating the negative- and positive-side functions
over their respective strict open half-spaces. Values outside the selected side are ignored, and
the hyperplane carrier belongs to neither term. -/
def distOfSidewiseFunction {d : ℕ} (plane : OrientedAffineHyperplane d)
    (f : Side → Space d → F) (hf : ∀ side, IsDistBounded (f side)) :
    (Space d) →d[ℝ] F :=
  distOfFunctionOn (plane.openHalfSpace .negative)
      (plane.measurableSet_openHalfSpace .negative) (f .negative) (hf .negative) +
    distOfFunctionOn (plane.openHalfSpace .positive)
      (plane.measurableSet_openHalfSpace .positive) (f .positive) (hf .positive)

/-- A sidewise function distribution acts by the sum of its two strict-half-space integrals. -/
lemma distOfSidewiseFunction_apply {d : ℕ} (plane : OrientedAffineHyperplane d)
    (f : Side → Space d → F) (hf : ∀ side, IsDistBounded (f side))
    (η : SchwartzMap (Space d) ℝ) :
    plane.distOfSidewiseFunction f hf η =
      (∫ x in plane.openHalfSpace .negative, η x • f .negative x) +
        ∫ x in plane.openHalfSpace .positive, η x • f .positive x := by
  rw [distOfSidewiseFunction, _root_.add_apply, distOfFunctionOn_apply,
    distOfFunctionOn_apply]

end OrientedAffineHyperplane
end
end Space
