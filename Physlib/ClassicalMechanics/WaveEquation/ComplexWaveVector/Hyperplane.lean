/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.ClassicalMechanics.WaveEquation.ComplexWaveVector
public import Physlib.SpaceAndTime.Space.OrientedAffineHyperplane

/-!
# Complex wave vectors relative to oriented hyperplanes

## i. Overview

This file decomposes a dimension-generic complex wave vector relative to the real unit normal of an
oriented affine hyperplane. Its complex normal component uses the complex-bilinear wave-vector
pairing, and its tangential projection subtracts that component times the complexified normal.
The vector is recovered exactly as the sum of its tangential and normal parts.

For `K = q - I a`, complex tangential projection acts separately on the real phase vector `q` and
the real attenuation vector `a`. Consequently, two complex vectors have equal tangential
projections exactly when their complex-bilinear pairings agree against every real tangent
displacement. This basis-free characterization retains both tangential phase and tangential
attenuation data.

Adding an arbitrary complex multiple of the real normal leaves the tangential projection
unchanged. Thus tangent data cannot determine a complex normal component or a full wave vector.
The construction assigns no medium, interface side, propagation direction, material-dispersion,
square-root branch, evanescent-wave, observable, or power meaning.

## ii. Key results

- `ComplexWaveVector.hyperplaneTangentialProjection_add_normal`: exact complex normal--tangential
  decomposition.
- `ComplexWaveVector.hyperplaneTangentialProjection_ofPhaseAttenuation`: projection acts
  separately on phase and attenuation vectors.
- `ComplexWaveVector.hyperplaneTangentialProjection_eq_iff_bilinearDot_eq_on_tangent`: equality
  of complex tangential projections is exactly equality of every real-tangent pairing.
- `ComplexWaveVector.hyperplaneTangentialProjection_add_smul_normalVector`: arbitrary complex
  normal shifts are invisible to tangential projection.

## iii. Table of contents

- A. Complex normal and tangential components
- B. Phase and attenuation compatibility
- C. Tangent-pairing characterization

## iv. References

The construction combines Physlib's complex-wave-vector and oriented-hyperplane APIs. No external
formal-development source is copied or translated here.
-/

@[expose] public section

namespace ClassicalMechanics

open Space InnerProductSpace

noncomputable section

namespace ComplexWaveVector

variable {d : ℕ}

/-!

## A. Complex normal and tangential components

-/

/-- The complex-bilinear scalar component of a complex vector along an oriented real unit
normal. -/
def hyperplaneNormalComponent (plane : OrientedAffineHyperplane d)
    (z : ComplexWaveVector d) : ℂ :=
  bilinearDot (ofReal plane.normalVector) z

/-- The complex tangential projection obtained by subtracting the oriented normal component. -/
def hyperplaneTangentialProjection (plane : OrientedAffineHyperplane d)
    (z : ComplexWaveVector d) : ComplexWaveVector d :=
  z - hyperplaneNormalComponent plane z • ofReal plane.normalVector

private lemma bilinearDot_hyperplaneNormal_self (plane : OrientedAffineHyperplane d) :
    bilinearDot (ofReal plane.normalVector) (ofReal plane.normalVector) = 1 := by
  rw [bilinearDot_ofReal, plane.inner_normalVector_self]
  norm_num

/-- A complex vector is the sum of its hyperplane-tangential and oriented normal parts. -/
lemma hyperplaneTangentialProjection_add_normal
    (plane : OrientedAffineHyperplane d) (z : ComplexWaveVector d) :
    hyperplaneTangentialProjection plane z +
        hyperplaneNormalComponent plane z • ofReal plane.normalVector = z := by
  simp [hyperplaneTangentialProjection]

/-- A complex tangential projection has zero complex-bilinear normal component. -/
@[simp]
lemma hyperplaneNormalComponent_hyperplaneTangentialProjection
    (plane : OrientedAffineHyperplane d) (z : ComplexWaveVector d) :
    hyperplaneNormalComponent plane (hyperplaneTangentialProjection plane z) = 0 := by
  rw [hyperplaneNormalComponent, hyperplaneTangentialProjection,
    bilinearDot_sub_right, bilinearDot_smul_right,
    bilinearDot_hyperplaneNormal_self]
  simp [hyperplaneNormalComponent]

/-!

## B. Phase and attenuation compatibility

-/

/-- Complex tangential projection acts separately on the phase and attenuation vectors. -/
lemma hyperplaneTangentialProjection_ofPhaseAttenuation
    (plane : OrientedAffineHyperplane d) (q a : WaveVector d) :
    hyperplaneTangentialProjection plane (ofPhaseAttenuation q a) =
      ofPhaseAttenuation (plane.tangentialProjection q)
        (plane.tangentialProjection a) := by
  have hnormal :
      hyperplaneNormalComponent plane (ofPhaseAttenuation q a) =
        (inner ℝ plane.normalVector q : ℂ) -
          Complex.I * (inner ℝ plane.normalVector a : ℂ) := by
    rw [hyperplaneNormalComponent, bilinearDot_comm,
      bilinearDot_ofPhaseAttenuation_ofReal,
      real_inner_comm q plane.normalVector, real_inner_comm a plane.normalVector]
  rw [hyperplaneTangentialProjection, hnormal]
  ext i
  apply Complex.ext
  · simp [ofPhaseAttenuation_apply, OrientedAffineHyperplane.tangentialProjection,
      OrientedAffineHyperplane.normalComponent]
  · simp [ofPhaseAttenuation_apply, OrientedAffineHyperplane.tangentialProjection,
      OrientedAffineHyperplane.normalComponent]
    ring

/-!

## C. Tangent-pairing characterization

-/

private lemma phase_attenuation_tangent_pairings_eq
    (plane : OrientedAffineHyperplane d) (z w : ComplexWaveVector d)
    (h : ∀ v : plane.tangentSubmodule,
      bilinearDot z (ofReal (v : EuclideanSpace ℝ (Fin d))) =
        bilinearDot w (ofReal (v : EuclideanSpace ℝ (Fin d)))) :
    (∀ v : plane.tangentSubmodule,
      inner ℝ (phaseVector z) (v : EuclideanSpace ℝ (Fin d)) =
        inner ℝ (phaseVector w) (v : EuclideanSpace ℝ (Fin d))) ∧
      ∀ v : plane.tangentSubmodule,
        inner ℝ (attenuationVector z) (v : EuclideanSpace ℝ (Fin d)) =
          inner ℝ (attenuationVector w) (v : EuclideanSpace ℝ (Fin d)) := by
  constructor
  · intro v
    have hv := h v
    rw [← ofPhaseAttenuation_phaseVector_attenuationVector z,
      ← ofPhaseAttenuation_phaseVector_attenuationVector w,
      bilinearDot_ofPhaseAttenuation_ofReal,
      bilinearDot_ofPhaseAttenuation_ofReal] at hv
    simpa using congrArg Complex.re hv
  · intro v
    have hv := h v
    rw [← ofPhaseAttenuation_phaseVector_attenuationVector z,
      ← ofPhaseAttenuation_phaseVector_attenuationVector w,
      bilinearDot_ofPhaseAttenuation_ofReal,
      bilinearDot_ofPhaseAttenuation_ofReal] at hv
    simpa using congrArg Complex.im hv

private lemma bilinearDot_hyperplaneTangentialProjection_of_tangent
    (plane : OrientedAffineHyperplane d) (z : ComplexWaveVector d)
    (v : plane.tangentSubmodule) :
    bilinearDot (hyperplaneTangentialProjection plane z)
        (ofReal (v : EuclideanSpace ℝ (Fin d))) =
      bilinearDot z (ofReal (v : EuclideanSpace ℝ (Fin d))) := by
  have hv : inner ℝ plane.normalVector (v : EuclideanSpace ℝ (Fin d)) = 0 :=
    ((plane.mem_tangentSubmodule v).mp v.property)
  rw [hyperplaneTangentialProjection, bilinearDot_sub_left,
    bilinearDot_smul_left, bilinearDot_ofReal, hv]
  simp

/-- Two complex vectors have the same hyperplane-tangential projection exactly when their
complex-bilinear pairings agree against every real tangent displacement. -/
lemma hyperplaneTangentialProjection_eq_iff_bilinearDot_eq_on_tangent
    (plane : OrientedAffineHyperplane d) (z w : ComplexWaveVector d) :
    hyperplaneTangentialProjection plane z = hyperplaneTangentialProjection plane w ↔
      ∀ v : plane.tangentSubmodule,
        bilinearDot z (ofReal (v : EuclideanSpace ℝ (Fin d))) =
          bilinearDot w (ofReal (v : EuclideanSpace ℝ (Fin d))) := by
  constructor
  · intro hprojection v
    rw [← bilinearDot_hyperplaneTangentialProjection_of_tangent plane z v,
      hprojection, bilinearDot_hyperplaneTangentialProjection_of_tangent]
  · intro h
    have hpairings := phase_attenuation_tangent_pairings_eq plane z w h
    have hphase :=
      (plane.tangentialProjection_eq_iff_inner_eq_on_tangent
        (phaseVector z) (phaseVector w)).mpr hpairings.1
    have hattenuation :=
      (plane.tangentialProjection_eq_iff_inner_eq_on_tangent
        (attenuationVector z) (attenuationVector w)).mpr hpairings.2
    rw [← ofPhaseAttenuation_phaseVector_attenuationVector z,
      ← ofPhaseAttenuation_phaseVector_attenuationVector w,
      hyperplaneTangentialProjection_ofPhaseAttenuation,
      hyperplaneTangentialProjection_ofPhaseAttenuation, hphase, hattenuation]

/-- Adding an arbitrary complex multiple of the oriented real normal leaves the complex
tangential projection unchanged. -/
lemma hyperplaneTangentialProjection_add_smul_normalVector
    (plane : OrientedAffineHyperplane d) (z : ComplexWaveVector d) (c : ℂ) :
    hyperplaneTangentialProjection plane (z + c • ofReal plane.normalVector) =
      hyperplaneTangentialProjection plane z := by
  apply (hyperplaneTangentialProjection_eq_iff_bilinearDot_eq_on_tangent
    plane (z + c • ofReal plane.normalVector) z).mpr
  intro v
  have hv : inner ℝ plane.normalVector (v : EuclideanSpace ℝ (Fin d)) = 0 :=
    ((plane.mem_tangentSubmodule v).mp v.property)
  rw [bilinearDot_add_left, bilinearDot_smul_left, bilinearDot_ofReal, hv]
  simp

end ComplexWaveVector

end
end ClassicalMechanics
