/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Mathlib.Analysis.Normed.Module.Normalize
public import Physlib.Optics.Polarization.Frame

/-!
# Polarization frames for non-normal incidence

## i. Overview

This file constructs the `s`/`p` polarization frame selected by an oriented interface normal and a
non-normal propagation direction. For interface-normal vector `n` and unit propagation vector `k`,
the convention is

```text
s = normalize (n × k), p = k × s, Jones order = (s, p).
```

Consequently `s × p = k`, so the frame has the orientation required by `PolarizationFrame`.
The Jones components are full electric-vector amplitudes along these unit axes, not tangential
`p`-amplitudes.

The cross-product condition excludes both parallel and antiparallel normal incidence, where the
plane of incidence does not select a transverse axis. At normal incidence callers must instead use
`PolarizationFrame.ofAxisZero` with independently selected unit tangent data. Grazing incidence is
geometrically non-normal and is not excluded here; later power normalization must treat its zero
normal admittance separately.

## ii. Key results

- `IsNonNormalIncidence`: the exact nondegeneracy condition for the incidence plane.
- `sPolarizationAxis` and `pPolarizationAxis`: the ordered unit polarization axes.
- `incidencePolarizationFrame`: the resulting oriented `s`/`p` frame.
- `incidencePolarizationFrame_realizeJones_eq`: explicit `s`/`p` decomposition of a realized
  Jones amplitude.

## iii. Table of contents

- A. Non-normal incidence axes
- B. The oriented incidence frame

## iv. References

The construction is derived from the imported Physlib polarization-frame and Euclidean
cross-product APIs. This file does not define an interface point or half-space, classify a direction
as incident or outgoing, derive reflection or refraction, introduce Fresnel coefficients, or make
an irradiance or power claim.
-/

@[expose] public section

namespace Optics

open Space Matrix InnerProductSpace

noncomputable section

/-!

## A. Non-normal incidence axes

-/

/-- A propagation direction is non-normal to an oriented interface normal when their coordinate
vectors have nonzero cross product.

This geometric predicate includes grazing propagation. It supplies no interface point, side, or
incoming/outgoing interpretation. -/
def IsNonNormalIncidence (propagationDirection interfaceNormal : Space.Direction 3) : Prop :=
  Space.basis.repr interfaceNormal.unit ⨯ₑ₃
    Space.basis.repr propagationDirection.unit ≠ 0

/-- The `s`-polarization unit axis selected by non-normal incidence.

The sign convention is the normalized interface-normal cross propagation vector, `n × k`. -/
def sPolarizationAxis (propagationDirection interfaceNormal : Space.Direction 3)
    (_h : IsNonNormalIncidence propagationDirection interfaceNormal) :
    EuclideanSpace ℝ (Fin 3) :=
  NormedSpace.normalize
    (Space.basis.repr interfaceNormal.unit ⨯ₑ₃
      Space.basis.repr propagationDirection.unit)

/-- The `s`-polarization axis has unit norm at non-normal incidence. -/
lemma sPolarizationAxis_norm (propagationDirection interfaceNormal : Space.Direction 3)
    (h : IsNonNormalIncidence propagationDirection interfaceNormal) :
    ‖sPolarizationAxis propagationDirection interfaceNormal h‖ = 1 := by
  exact NormedSpace.norm_normalize h

/-- The `s`-polarization axis is tangent to the oriented interface. -/
lemma inner_interfaceNormal_sPolarizationAxis
    (propagationDirection interfaceNormal : Space.Direction 3)
    (h : IsNonNormalIncidence propagationDirection interfaceNormal) :
    inner ℝ (Space.basis.repr interfaceNormal.unit)
      (sPolarizationAxis propagationDirection interfaceNormal h) = 0 := by
  rw [sPolarizationAxis, NormedSpace.normalize, real_inner_smul_right,
    Space.inner_self_cross, mul_zero]

/-- The `s`-polarization axis is transverse to the propagation direction. -/
lemma inner_propagation_sPolarizationAxis
    (propagationDirection interfaceNormal : Space.Direction 3)
    (h : IsNonNormalIncidence propagationDirection interfaceNormal) :
    inner ℝ (Space.basis.repr propagationDirection.unit)
      (sPolarizationAxis propagationDirection interfaceNormal h) = 0 := by
  rw [sPolarizationAxis, NormedSpace.normalize, real_inner_smul_right,
    Space.inner_cross_self, mul_zero]

/-- The `p`-polarization unit axis completing the right-handed transverse frame.

The order `k × s` is essential: with Jones order `(s, p)`, it gives `s × p = k`. -/
def pPolarizationAxis (propagationDirection interfaceNormal : Space.Direction 3)
    (h : IsNonNormalIncidence propagationDirection interfaceNormal) :
    EuclideanSpace ℝ (Fin 3) :=
  Space.basis.repr propagationDirection.unit ⨯ₑ₃
    sPolarizationAxis propagationDirection interfaceNormal h

/-!

## B. The oriented incidence frame

-/

/-- The oriented `s`/`p` polarization frame selected by non-normal interface incidence.

Axis zero is `s = normalize (n × k)` and axis one is `p = k × s`. The definition is purely
geometric and does not assert that the propagation direction is physically incident, reflected,
or transmitted. -/
def incidencePolarizationFrame (propagationDirection interfaceNormal : Space.Direction 3)
    (h : IsNonNormalIncidence propagationDirection interfaceNormal) :
    PolarizationFrame propagationDirection :=
  PolarizationFrame.ofAxisZero propagationDirection
    (sPolarizationAxis propagationDirection interfaceNormal h)
    (sPolarizationAxis_norm propagationDirection interfaceNormal h)
    (inner_propagation_sPolarizationAxis propagationDirection interfaceNormal h)

/-- The first incidence-frame axis is the `s`-polarization axis. -/
@[simp]
lemma incidencePolarizationFrame_axis_zero
    (propagationDirection interfaceNormal : Space.Direction 3)
    (h : IsNonNormalIncidence propagationDirection interfaceNormal) :
    (incidencePolarizationFrame propagationDirection interfaceNormal h).axis 0 =
      sPolarizationAxis propagationDirection interfaceNormal h := rfl

/-- The second incidence-frame axis is the `p`-polarization axis. -/
@[simp]
lemma incidencePolarizationFrame_axis_one
    (propagationDirection interfaceNormal : Space.Direction 3)
    (h : IsNonNormalIncidence propagationDirection interfaceNormal) :
    (incidencePolarizationFrame propagationDirection interfaceNormal h).axis 1 =
      pPolarizationAxis propagationDirection interfaceNormal h := rfl

/-- A Jones amplitude realized in the incidence frame is its scalar `s` and `p` realizations along
the corresponding physical unit axes. -/
lemma incidencePolarizationFrame_realizeJones_eq
    (propagationDirection interfaceNormal : Space.Direction 3)
    (h : IsNonNormalIncidence propagationDirection interfaceNormal)
    (J : JonesVector) (carrierPhase : ℝ) :
    (incidencePolarizationFrame propagationDirection interfaceNormal h).realizeJones
        J carrierPhase =
      Phasor.realize (J.components 0) carrierPhase •
          sPolarizationAxis propagationDirection interfaceNormal h +
        Phasor.realize (J.components 1) carrierPhase •
          pPolarizationAxis propagationDirection interfaceNormal h := by
  rw [PolarizationFrame.realizeJones_eq_sum, Fin.sum_univ_two]
  rfl

end

end Optics
