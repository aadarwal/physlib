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

For `K = q - I a`, the complex normal component is the real phase normal component minus `I`
times the real attenuation normal component. Complex tangential projection acts separately on
`q` and `a`. Consequently, two complex vectors have equal tangential projections exactly when
their complex-bilinear pairings agree against every real tangent displacement. This basis-free
characterization retains both tangential phase and tangential attenuation data.

Adding an arbitrary complex multiple of the real normal leaves the tangential projection
unchanged. Thus tangent data cannot determine a complex normal component or a full wave vector.
Flipping the complex normal component defines hyperplane reflection. It preserves the tangential
projection and complex-bilinear square and is involutive. On phase and attenuation vectors it has
the familiar real formula that subtracts twice the oriented normal component. Conversely, two
vectors with equal tangential projections and equal bilinear squares are either equal or related
by this reflection; the alternatives coincide when their normal component vanishes.
The construction assigns no medium, interface side, propagation direction, material-dispersion,
square-root branch, evanescent-wave, observable, or power meaning.

## ii. Key results

- `ComplexWaveVector.hyperplaneTangentialProjection_add_normal`: exact complex normal--tangential
  decomposition.
- `ComplexWaveVector.hyperplaneTangentialProjection_ofPhaseAttenuation`: projection acts
  separately on phase and attenuation vectors.
- `ComplexWaveVector.hyperplaneNormalComponent_ofPhaseAttenuation`: the complex normal component
  separates into its real phase and attenuation components.
- `ComplexWaveVector.hyperplaneTangentialProjection_eq_iff_bilinearDot_eq_on_tangent`: equality
  of complex tangential projections is exactly equality of every real-tangent pairing.
- `ComplexWaveVector.hyperplaneTangentialProjection_add_smul_normalVector`: arbitrary complex
  normal shifts are invisible to tangential projection.
- `ComplexWaveVector.hyperplaneReflection`: reflection across the complexified tangent plane.
- `ComplexWaveVector.hyperplaneReflection_ofPhaseAttenuation`: reflection acts separately on
  phase and attenuation vectors by the real mirror formula.
- `eq_or_eq_hyperplaneReflection_of_tangentialProjection_eq_of_bilinearDot_self_eq`:
  the exact two-root classification at fixed tangential projection and bilinear square.

## iii. Table of contents

- A. Complex normal and tangential components
- B. Phase and attenuation compatibility
- C. Tangent-pairing characterization
- D. Complex hyperplane reflection

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

/-- The complex normal component of `q - I * a` consists of the real phase normal component minus
`I` times the real attenuation normal component. -/
@[simp]
lemma hyperplaneNormalComponent_ofPhaseAttenuation
    (plane : OrientedAffineHyperplane d) (q a : WaveVector d) :
    hyperplaneNormalComponent plane (ofPhaseAttenuation q a) =
      (plane.normalComponent q : ℂ) -
        Complex.I * (plane.normalComponent a : ℂ) := by
  simp only [OrientedAffineHyperplane.normalComponent]
  rw [hyperplaneNormalComponent, bilinearDot_comm,
    bilinearDot_ofPhaseAttenuation_ofReal,
    real_inner_comm q plane.normalVector, real_inner_comm a plane.normalVector]

/-- The real part of the complex normal component is the oriented normal component of the phase
vector. -/
@[simp]
lemma hyperplaneNormalComponent_re
    (plane : OrientedAffineHyperplane d) (z : ComplexWaveVector d) :
    (hyperplaneNormalComponent plane z).re =
      plane.normalComponent (phaseVector z) := by
  rw [← ofPhaseAttenuation_phaseVector_attenuationVector z,
    hyperplaneNormalComponent_ofPhaseAttenuation]
  simp

/-- The imaginary part of the complex normal component is minus the oriented normal component of
the attenuation vector. -/
@[simp]
lemma hyperplaneNormalComponent_im
    (plane : OrientedAffineHyperplane d) (z : ComplexWaveVector d) :
    (hyperplaneNormalComponent plane z).im =
      -plane.normalComponent (attenuationVector z) := by
  rw [← ofPhaseAttenuation_phaseVector_attenuationVector z,
    hyperplaneNormalComponent_ofPhaseAttenuation]
  simp

/-- Complex tangential projection acts separately on the phase and attenuation vectors. -/
lemma hyperplaneTangentialProjection_ofPhaseAttenuation
    (plane : OrientedAffineHyperplane d) (q a : WaveVector d) :
    hyperplaneTangentialProjection plane (ofPhaseAttenuation q a) =
      ofPhaseAttenuation (plane.tangentialProjection q)
        (plane.tangentialProjection a) := by
  rw [hyperplaneTangentialProjection, hyperplaneNormalComponent_ofPhaseAttenuation]
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

/-!

## D. Complex hyperplane reflection

-/

/-- The complex-bilinear square splits into tangential and oriented-normal squares relative to an
oriented affine hyperplane. -/
lemma bilinearDot_self_eq_tangential_add_normal_sq
    (plane : OrientedAffineHyperplane d) (z : ComplexWaveVector d) :
    bilinearDot z z =
      bilinearDot (hyperplaneTangentialProjection plane z)
          (hyperplaneTangentialProjection plane z) +
        hyperplaneNormalComponent plane z ^ 2 := by
  have hnormalTangential :
      bilinearDot (ofReal plane.normalVector)
          (hyperplaneTangentialProjection plane z) = 0 := by
    simpa only [hyperplaneNormalComponent] using
      hyperplaneNormalComponent_hyperplaneTangentialProjection plane z
  have htangentialNormal :
      bilinearDot (hyperplaneTangentialProjection plane z)
          (ofReal plane.normalVector) = 0 := by
    rw [bilinearDot_comm]
    exact hnormalTangential
  calc
    bilinearDot z z =
        bilinearDot
            (hyperplaneTangentialProjection plane z +
              hyperplaneNormalComponent plane z • ofReal plane.normalVector)
            (hyperplaneTangentialProjection plane z +
              hyperplaneNormalComponent plane z • ofReal plane.normalVector) := by
      rw [hyperplaneTangentialProjection_add_normal]
    _ = bilinearDot (hyperplaneTangentialProjection plane z)
          (hyperplaneTangentialProjection plane z) +
        hyperplaneNormalComponent plane z ^ 2 := by
      simp only [bilinearDot_add_left, bilinearDot_add_right,
        bilinearDot_smul_left, bilinearDot_smul_right,
        hnormalTangential, htangentialNormal,
        bilinearDot_hyperplaneNormal_self]
      ring

/-- At a fixed complex tangential projection, equality of complex-bilinear squares is equivalent
to equality of the squared oriented normal components. -/
lemma bilinearDot_self_eq_iff_normalComponent_sq_eq_of_tangentialProjection_eq
    (plane : OrientedAffineHyperplane d) (z w : ComplexWaveVector d)
    (hTangential : hyperplaneTangentialProjection plane z =
      hyperplaneTangentialProjection plane w) :
    bilinearDot z z = bilinearDot w w ↔
      hyperplaneNormalComponent plane z ^ 2 =
        hyperplaneNormalComponent plane w ^ 2 := by
  rw [bilinearDot_self_eq_tangential_add_normal_sq plane z,
    bilinearDot_self_eq_tangential_add_normal_sq plane w, hTangential]
  constructor
  · exact add_left_cancel
  · intro hNormal
    exact congrArg
      (fun c : ℂ =>
        bilinearDot (hyperplaneTangentialProjection plane w)
            (hyperplaneTangentialProjection plane w) + c)
      hNormal

/-- At a fixed complex tangential projection, the difference of squared oriented normal components
equals the difference of complex-bilinear squares. -/
lemma normalComponent_sq_sub_eq_bilinearDot_self_sub_of_tangentialProjection_eq
    (plane : OrientedAffineHyperplane d) (z w : ComplexWaveVector d)
    (hTangential : hyperplaneTangentialProjection plane z =
      hyperplaneTangentialProjection plane w) :
    hyperplaneNormalComponent plane z ^ 2 -
        hyperplaneNormalComponent plane w ^ 2 =
      bilinearDot z z - bilinearDot w w := by
  rw [bilinearDot_self_eq_tangential_add_normal_sq plane z,
    bilinearDot_self_eq_tangential_add_normal_sq plane w, hTangential]
  ring

/-- At fixed complex tangential projection and complex-bilinear square, the oriented normal
components are equal or negatives. -/
lemma normalComponent_eq_or_eq_neg_of_tangentialProjection_eq_of_bilinearDot_self_eq
    (plane : OrientedAffineHyperplane d) (z w : ComplexWaveVector d)
    (hTangential : hyperplaneTangentialProjection plane z =
      hyperplaneTangentialProjection plane w)
    (hSquare : bilinearDot z z = bilinearDot w w) :
    hyperplaneNormalComponent plane z = hyperplaneNormalComponent plane w ∨
      hyperplaneNormalComponent plane z = -hyperplaneNormalComponent plane w :=
  eq_or_eq_neg_of_sq_eq_sq _ _
    ((bilinearDot_self_eq_iff_normalComponent_sq_eq_of_tangentialProjection_eq
      plane z w hTangential).mp hSquare)

/-- Reflect a complex wave vector across the complexified tangent plane by negating its oriented
normal component. -/
def hyperplaneReflection (plane : OrientedAffineHyperplane d)
    (z : ComplexWaveVector d) : ComplexWaveVector d :=
  hyperplaneTangentialProjection plane z -
    hyperplaneNormalComponent plane z • ofReal plane.normalVector

/-- Hyperplane reflection has the familiar formula `z - 2 * normalComponent z * normalVector`. -/
lemma hyperplaneReflection_eq_sub_two_smul_normalVector
    (plane : OrientedAffineHyperplane d) (z : ComplexWaveVector d) :
    hyperplaneReflection plane z =
      z - (2 * hyperplaneNormalComponent plane z) • ofReal plane.normalVector := by
  rw [hyperplaneReflection, hyperplaneTangentialProjection]
  module

/-- Hyperplane reflection acts separately on the real phase and attenuation vectors, subtracting
twice each oriented normal component. -/
lemma hyperplaneReflection_ofPhaseAttenuation
    (plane : OrientedAffineHyperplane d) (q a : WaveVector d) :
    hyperplaneReflection plane (ofPhaseAttenuation q a) =
      ofPhaseAttenuation
        (q - (2 * plane.normalComponent q) • plane.normalVector)
        (a - (2 * plane.normalComponent a) • plane.normalVector) := by
  rw [hyperplaneReflection_eq_sub_two_smul_normalVector,
    hyperplaneNormalComponent_ofPhaseAttenuation]
  ext i
  apply Complex.ext
  · simp [ofPhaseAttenuation_apply]
  · simp [ofPhaseAttenuation_apply]
    ring

/-- The phase vector of a reflected complex wave vector obeys the real hyperplane-mirror
formula. -/
@[simp]
lemma phaseVector_hyperplaneReflection
    (plane : OrientedAffineHyperplane d) (z : ComplexWaveVector d) :
    phaseVector (hyperplaneReflection plane z) =
      phaseVector z -
        (2 * plane.normalComponent (phaseVector z)) • plane.normalVector := by
  nth_rewrite 1 [← ofPhaseAttenuation_phaseVector_attenuationVector z]
  rw [hyperplaneReflection_ofPhaseAttenuation]
  simp

/-- The attenuation vector of a reflected complex wave vector obeys the real hyperplane-mirror
formula. -/
@[simp]
lemma attenuationVector_hyperplaneReflection
    (plane : OrientedAffineHyperplane d) (z : ComplexWaveVector d) :
    attenuationVector (hyperplaneReflection plane z) =
      attenuationVector z -
        (2 * plane.normalComponent (attenuationVector z)) • plane.normalVector := by
  nth_rewrite 1 [← ofPhaseAttenuation_phaseVector_attenuationVector z]
  rw [hyperplaneReflection_ofPhaseAttenuation]
  simp

/-- Hyperplane reflection negates the oriented normal component of the real phase vector. -/
lemma normalComponent_phaseVector_hyperplaneReflection
    (plane : OrientedAffineHyperplane d) (z : ComplexWaveVector d) :
    plane.normalComponent (phaseVector (hyperplaneReflection plane z)) =
      -plane.normalComponent (phaseVector z) := by
  rw [phaseVector_hyperplaneReflection,
    OrientedAffineHyperplane.normalComponent, inner_sub_right, inner_smul_right,
    plane.inner_normalVector_self]
  simp [OrientedAffineHyperplane.normalComponent]
  ring

/-- Hyperplane reflection negates the oriented normal component of the real attenuation vector. -/
lemma normalComponent_attenuationVector_hyperplaneReflection
    (plane : OrientedAffineHyperplane d) (z : ComplexWaveVector d) :
    plane.normalComponent (attenuationVector (hyperplaneReflection plane z)) =
      -plane.normalComponent (attenuationVector z) := by
  rw [attenuationVector_hyperplaneReflection,
    OrientedAffineHyperplane.normalComponent, inner_sub_right, inner_smul_right,
    plane.inner_normalVector_self]
  simp [OrientedAffineHyperplane.normalComponent]
  ring

/-- Hyperplane reflection preserves the complex tangential projection. -/
@[simp]
lemma hyperplaneTangentialProjection_hyperplaneReflection
    (plane : OrientedAffineHyperplane d) (z : ComplexWaveVector d) :
    hyperplaneTangentialProjection plane (hyperplaneReflection plane z) =
      hyperplaneTangentialProjection plane z := by
  rw [hyperplaneReflection_eq_sub_two_smul_normalVector]
  simpa only [sub_eq_add_neg, neg_smul] using
    hyperplaneTangentialProjection_add_smul_normalVector plane z
      (-(2 * hyperplaneNormalComponent plane z))

/-- Hyperplane reflection negates the complex oriented normal component. -/
@[simp]
lemma hyperplaneNormalComponent_hyperplaneReflection
    (plane : OrientedAffineHyperplane d) (z : ComplexWaveVector d) :
    hyperplaneNormalComponent plane (hyperplaneReflection plane z) =
      -hyperplaneNormalComponent plane z := by
  have hnormalTangential :
      bilinearDot (ofReal plane.normalVector)
          (hyperplaneTangentialProjection plane z) = 0 := by
    simpa only [hyperplaneNormalComponent] using
      hyperplaneNormalComponent_hyperplaneTangentialProjection plane z
  rw [hyperplaneNormalComponent, hyperplaneReflection, bilinearDot_sub_right,
    bilinearDot_smul_right, hnormalTangential, bilinearDot_hyperplaneNormal_self]
  ring

/-- Complex hyperplane reflection is involutive. -/
@[simp]
lemma hyperplaneReflection_hyperplaneReflection
    (plane : OrientedAffineHyperplane d) (z : ComplexWaveVector d) :
    hyperplaneReflection plane (hyperplaneReflection plane z) = z := by
  rw [hyperplaneReflection, hyperplaneTangentialProjection_hyperplaneReflection,
    hyperplaneNormalComponent_hyperplaneReflection]
  simpa only [neg_smul, sub_neg_eq_add] using
    hyperplaneTangentialProjection_add_normal plane z

/-- Complex hyperplane reflection is an involutive function. -/
lemma hyperplaneReflection_involutive (plane : OrientedAffineHyperplane d) :
    Function.Involutive (hyperplaneReflection plane) :=
  hyperplaneReflection_hyperplaneReflection plane

/-- A complex wave vector is fixed by hyperplane reflection exactly when its oriented normal
component vanishes. -/
@[simp]
lemma hyperplaneReflection_eq_self_iff_normalComponent_eq_zero
    (plane : OrientedAffineHyperplane d) (z : ComplexWaveVector d) :
    hyperplaneReflection plane z = z ↔ hyperplaneNormalComponent plane z = 0 := by
  constructor
  · intro hReflection
    have hNormal := congrArg (hyperplaneNormalComponent plane) hReflection
    rw [hyperplaneNormalComponent_hyperplaneReflection] at hNormal
    exact CharZero.neg_eq_self_iff.mp hNormal
  · intro hNormal
    rw [hyperplaneReflection_eq_sub_two_smul_normalVector, hNormal]
    simp

/-- Complex hyperplane reflection preserves the complex-bilinear square. -/
@[simp]
lemma bilinearDot_hyperplaneReflection_self
    (plane : OrientedAffineHyperplane d) (z : ComplexWaveVector d) :
    bilinearDot (hyperplaneReflection plane z) (hyperplaneReflection plane z) =
      bilinearDot z z := by
  calc
    bilinearDot (hyperplaneReflection plane z) (hyperplaneReflection plane z) =
        bilinearDot
            (hyperplaneTangentialProjection plane (hyperplaneReflection plane z))
            (hyperplaneTangentialProjection plane (hyperplaneReflection plane z)) +
          hyperplaneNormalComponent plane (hyperplaneReflection plane z) ^ 2 :=
      bilinearDot_self_eq_tangential_add_normal_sq plane _
    _ = bilinearDot (hyperplaneTangentialProjection plane z)
          (hyperplaneTangentialProjection plane z) +
        hyperplaneNormalComponent plane z ^ 2 := by rw [
      hyperplaneTangentialProjection_hyperplaneReflection,
      hyperplaneNormalComponent_hyperplaneReflection, neg_sq]
    _ = bilinearDot z z := (bilinearDot_self_eq_tangential_add_normal_sq plane z).symm

/-- At fixed complex tangential projection and complex-bilinear square, two vectors are either
equal or related by hyperplane reflection.

The alternatives need not be exclusive: they coincide when the common normal component is zero. -/
lemma eq_or_eq_hyperplaneReflection_of_tangentialProjection_eq_of_bilinearDot_self_eq
    (plane : OrientedAffineHyperplane d) (z w : ComplexWaveVector d)
    (hTangential : hyperplaneTangentialProjection plane z =
      hyperplaneTangentialProjection plane w)
    (hSquare : bilinearDot z z = bilinearDot w w) :
    z = w ∨ z = hyperplaneReflection plane w := by
  rcases normalComponent_eq_or_eq_neg_of_tangentialProjection_eq_of_bilinearDot_self_eq
      plane z w hTangential hSquare with hNormal | hNormal
  · left
    rw [← hyperplaneTangentialProjection_add_normal plane z, hTangential, hNormal,
      hyperplaneTangentialProjection_add_normal]
  · right
    rw [← hyperplaneTangentialProjection_add_normal plane z, hTangential, hNormal,
      hyperplaneReflection]
    simp only [sub_eq_add_neg, neg_smul]

end ComplexWaveVector

end
end ClassicalMechanics
