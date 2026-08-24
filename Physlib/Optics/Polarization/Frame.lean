/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Polarization.Basic
public import Physlib.SpaceAndTime.Space.CrossProduct

/-!
# Oriented polarization frames

## i. Overview

This file embeds two-component Jones amplitudes into three-dimensional complex electric
amplitudes. A `PolarizationFrame` is an ordered orthonormal pair whose cross product is the
specified propagation direction. The orientation equality is proof-bearing data: it excludes a
reflected transverse coordinate pair without assigning observer-dependent circular-polarization
names.

For Jones coordinates `J = (z₀, z₁)` and frame axes `(e₀, e₁)`, the spatial phasor is
`z₀ e₀ + z₁ e₁`. Its real and imaginary parts give two real transverse quadratures, and realization
uses the existing convention `Re (A * exp (I * carrierPhase))`. The embedding preserves squared
Jones intensity as a raw electric-amplitude identity. It does not identify that quantity with
irradiance or power.

## ii. Key results

- `PolarizationFrame.ofAxisZero`: construct a frame from one unit transverse axis.
- `PolarizationFrame.propagationVector_cross_axis_zero` and
  `PolarizationFrame.propagationVector_cross_axis_one`: the oriented-frame quarter-turn.
- `PolarizationFrame.embedJones_norm_sq`: preservation of squared Jones intensity.
- `PolarizationFrame.embedJones_scale`: complex scaling commutes with spatial embedding.
- `PolarizationFrame.electricReal_norm_sq_add_electricImag_norm_sq`: the two real quadratures
  recover squared Jones intensity.
- `PolarizationFrame.realizeJones_eq`: exact cosine-sine realization.
- `PolarizationFrame.realizeJones_eq_sum`: realization directly in the two frame axes.
- `PolarizationFrame.realizeJones_propagationCross`: the oriented magnetic quarter-turn.
- `PolarizationFrame.electricReal_propagationCross` and
  `PolarizationFrame.electricImag_propagationCross`: the corresponding quadrature identities.

## iii. Table of contents

- A. Oriented transverse geometry
- B. Complex Jones embedding
- C. Real quadratures
- D. Phasor realization
- E. Coherent phase and oriented quarter-turn

## iv. References

The construction is derived from the imported Physlib Jones and Euclidean cross-product APIs. The
frame is local data; this file does not choose a global frame over all propagation directions. It
contains no material model, field equation, interface convention, electromagnetic power,
potential, gauge, or circular-handedness claim.
-/

@[expose] public section

namespace Optics

open Space Matrix InnerProductSpace
open scoped ComplexConjugate

noncomputable section

/-!

## A. Oriented transverse geometry

-/

/-- An oriented orthonormal polarization frame transverse to a propagation direction.

The ordered axes satisfy `axis 0 × axis 1 = n`, where `n` is the Euclidean coordinate vector of
the unit propagation direction. Thus the orientation is mathematical right-handedness of the
ordered triad, not an observer-dependent name for a circular-polarization state. -/
@[ext]
structure PolarizationFrame (direction : Space.Direction 3) where
  /-- The two ordered real polarization axes. -/
  axis : Fin 2 → EuclideanSpace ℝ (Fin 3)
  /-- The polarization axes are orthonormal. -/
  orthonormal_axis : Orthonormal ℝ axis
  /-- The ordered axes have the specified propagation orientation. -/
  orientation : axis 0 ⨯ₑ₃ axis 1 = Space.basis.repr direction.unit

namespace PolarizationFrame

variable {direction : Space.Direction 3}

/-- The Euclidean coordinate vector of the frame's propagation direction. -/
def propagationVector (_frame : PolarizationFrame direction) :
    EuclideanSpace ℝ (Fin 3) :=
  Space.basis.repr direction.unit

/-- The propagation vector of a polarization frame has unit norm. -/
lemma propagationVector_norm (frame : PolarizationFrame direction) :
    ‖frame.propagationVector‖ = 1 := by
  simp [propagationVector, direction.norm]

/-- Each polarization axis is transverse to the propagation direction. -/
lemma inner_propagationVector_axis (frame : PolarizationFrame direction) (i : Fin 2) :
    ⟪frame.propagationVector, frame.axis i⟫_ℝ = 0 := by
  rw [propagationVector, ← frame.orientation]
  fin_cases i
  · rw [real_inner_comm]
    exact inner_self_cross _ _
  · rw [real_inner_comm]
    exact inner_cross_self _ _

/-- Crossing the propagation vector with the first frame axis gives the second axis. -/
lemma propagationVector_cross_axis_zero (frame : PolarizationFrame direction) :
    frame.propagationVector ⨯ₑ₃ frame.axis 0 = frame.axis 1 := by
  rw [propagationVector, ← frame.orientation, Space.cross_cross_eq_smul_sub_smul]
  have h := orthonormal_iff_ite.mp frame.orthonormal_axis
  rw [h 0 0, h 1 0]
  simp

/-- Crossing the propagation vector with the second frame axis gives minus the first axis. -/
lemma propagationVector_cross_axis_one (frame : PolarizationFrame direction) :
    frame.propagationVector ⨯ₑ₃ frame.axis 1 = -frame.axis 0 := by
  rw [propagationVector, ← frame.orientation, Space.cross_cross_eq_smul_sub_smul]
  have h := orthonormal_iff_ite.mp frame.orthonormal_axis
  rw [h 0 1, h 1 1]
  simp

/-- Construct an oriented polarization frame from a chosen unit transverse first axis.

The second axis is the cross product of the propagation vector with the supplied first axis. This
constructor keeps the choice explicit, which is essential when incidence geometry does not select
a canonical transverse axis. -/
def ofAxisZero (direction : Space.Direction 3)
    (axisZero : EuclideanSpace ℝ (Fin 3))
    (haxisZero_norm : ‖axisZero‖ = 1)
    (haxisZero_transverse :
      inner ℝ (Space.basis.repr direction.unit) axisZero = 0) :
    PolarizationFrame direction where
  axis := ![axisZero, Space.basis.repr direction.unit ⨯ₑ₃ axisZero]
  orthonormal_axis := by
    rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j
    · change inner ℝ axisZero axisZero = 1
      simp [haxisZero_norm]
    · change inner ℝ axisZero
        (Space.basis.repr direction.unit ⨯ₑ₃ axisZero) = 0
      exact Space.inner_cross_self axisZero (Space.basis.repr direction.unit)
    · change inner ℝ
        (Space.basis.repr direction.unit ⨯ₑ₃ axisZero) axisZero = 0
      rw [real_inner_comm]
      exact Space.inner_cross_self axisZero (Space.basis.repr direction.unit)
    · change inner ℝ (Space.basis.repr direction.unit ⨯ₑ₃ axisZero)
          (Space.basis.repr direction.unit ⨯ₑ₃ axisZero) = 1
      have haxisZero_transverse' :
          inner ℝ axisZero (Space.basis.repr direction.unit) = 0 := by
        rw [real_inner_comm]
        exact haxisZero_transverse
      rw [Space.inner_cross_cross, real_inner_self_eq_norm_sq,
        real_inner_self_eq_norm_sq]
      simp [direction.norm, haxisZero_norm, haxisZero_transverse,
        haxisZero_transverse']
  orientation := by
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    change axisZero ⨯ₑ₃ (Space.basis.repr direction.unit ⨯ₑ₃ axisZero) = _
    rw [Space.cross_cross_eq_smul_sub_smul', real_inner_self_eq_norm_sq,
      haxisZero_norm, haxisZero_transverse]
    simp

/-- The first axis of `ofAxisZero` is the supplied transverse axis. -/
@[simp]
lemma ofAxisZero_axis_zero (direction : Space.Direction 3)
    (axisZero : EuclideanSpace ℝ (Fin 3))
    (haxisZero_norm : ‖axisZero‖ = 1)
    (haxisZero_transverse :
      inner ℝ (Space.basis.repr direction.unit) axisZero = 0) :
    (ofAxisZero direction axisZero haxisZero_norm haxisZero_transverse).axis 0 =
      axisZero := rfl

/-- The second axis of `ofAxisZero` is the propagation cross the supplied first axis. -/
@[simp]
lemma ofAxisZero_axis_one (direction : Space.Direction 3)
    (axisZero : EuclideanSpace ℝ (Fin 3))
    (haxisZero_norm : ‖axisZero‖ = 1)
    (haxisZero_transverse :
      inner ℝ (Space.basis.repr direction.unit) axisZero = 0) :
    (ofAxisZero direction axisZero haxisZero_norm haxisZero_transverse).axis 1 =
      Space.basis.repr direction.unit ⨯ₑ₃ axisZero := rfl

/-!

## B. Complex Jones embedding

-/

/-- A real polarization axis regarded componentwise as a complex Euclidean vector. -/
def complexAxis (frame : PolarizationFrame direction) (i : Fin 2) :
    EuclideanSpace ℂ (Fin 3) :=
  WithLp.toLp 2 fun k ↦ (frame.axis i k : ℂ)

/-- Complexification preserves the coordinates of a polarization axis. -/
@[simp]
lemma complexAxis_apply (frame : PolarizationFrame direction) (i : Fin 2) (k : Fin 3) :
    frame.complexAxis i k = (frame.axis i k : ℂ) := rfl

/-- Complexification preserves inner products of real polarization axes. -/
lemma inner_complexAxis (frame : PolarizationFrame direction) (i j : Fin 2) :
    ⟪frame.complexAxis i, frame.complexAxis j⟫_ℂ =
      (⟪frame.axis i, frame.axis j⟫_ℝ : ℂ) := by
  rw [PiLp.inner_apply, PiLp.inner_apply, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp [complexAxis, RCLike.inner_apply]

/-- The complexified polarization axes remain orthonormal. -/
lemma orthonormal_complexAxis (frame : PolarizationFrame direction) :
    Orthonormal ℂ frame.complexAxis := by
  rw [orthonormal_iff_ite]
  intro i j
  rw [frame.inner_complexAxis, orthonormal_iff_ite.mp frame.orthonormal_axis i j]
  split_ifs <;> simp

/-- Embed Jones coordinates into the complexified physical transverse plane. -/
def embedJones (frame : PolarizationFrame direction) (J : JonesVector) :
    EuclideanSpace ℂ (Fin 3) :=
  ∑ i : Fin 2, J.components i • frame.complexAxis i

/-- The embedded Jones amplitude is the transverse-axis linear combination componentwise. -/
@[simp]
lemma embedJones_apply (frame : PolarizationFrame direction) (J : JonesVector) (k : Fin 3) :
    frame.embedJones J k = ∑ i : Fin 2, J.components i * frame.axis i k := by
  simp [embedJones, complexAxis]

/-- Scaling all Jones coordinates multiplies the embedded complex spatial phasor by the same
complex scalar. -/
lemma embedJones_scale (frame : PolarizationFrame direction)
    (z : ℂ) (J : JonesVector) :
    frame.embedJones (JonesVector.scale z J) = z • frame.embedJones J := by
  rw [embedJones, embedJones]
  simp only [JonesVector.scale, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [smul_smul]

/-- Inner product with a complexified polarization axis recovers its Jones coordinate. -/
lemma inner_complexAxis_embedJones (frame : PolarizationFrame direction)
    (J : JonesVector) (i : Fin 2) :
    ⟪frame.complexAxis i, frame.embedJones J⟫_ℂ = J.components i := by
  exact frame.orthonormal_complexAxis.inner_right_fintype J.components i

/-- Embedding in an orthonormal polarization frame preserves squared Jones intensity. -/
lemma embedJones_norm_sq (frame : PolarizationFrame direction) (J : JonesVector) :
    ‖frame.embedJones J‖ ^ 2 = J.intensity := by
  rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ),
    JonesVector.intensity_eq_sum_normSq]
  change Complex.re ⟪∑ i, J.components i • frame.complexAxis i,
    ∑ i, J.components i • frame.complexAxis i⟫_ℂ = _
  rw [frame.orthonormal_complexAxis.inner_sum J.components J.components Finset.univ]
  simp [Complex.normSq_apply]

/-!

## C. Real quadratures

-/

/-- The real quadrature of a Jones amplitude embedded in a polarization frame. -/
def electricReal (frame : PolarizationFrame direction) (J : JonesVector) :
    EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 fun k ↦ (frame.embedJones J k).re

/-- The imaginary quadrature of a Jones amplitude embedded in a polarization frame. -/
def electricImag (frame : PolarizationFrame direction) (J : JonesVector) :
    EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 fun k ↦ (frame.embedJones J k).im

/-- Each embedded Jones component is recovered from its real and imaginary electric
quadratures. -/
lemma embedJones_apply_eq_electricReal_add_electricImag_mul_I
    (frame : PolarizationFrame direction) (J : JonesVector) (k : Fin 3) :
    frame.embedJones J k =
      (frame.electricReal J k : ℂ) + (frame.electricImag J k : ℂ) * Complex.I := by
  exact (Complex.re_add_im (frame.embedJones J k)).symm

/-- The real quadrature is the real-coordinate polarization-axis combination. -/
lemma electricReal_eq_sum (frame : PolarizationFrame direction) (J : JonesVector) :
    frame.electricReal J = ∑ i : Fin 2, (J.components i).re • frame.axis i := by
  ext k
  simp [electricReal, embedJones, complexAxis]

/-- The imaginary quadrature is the imaginary-coordinate polarization-axis combination. -/
lemma electricImag_eq_sum (frame : PolarizationFrame direction) (J : JonesVector) :
    frame.electricImag J = ∑ i : Fin 2, (J.components i).im • frame.axis i := by
  ext k
  simp [electricImag, embedJones, complexAxis]

/-- The real embedded quadrature is transverse to the propagation direction. -/
lemma inner_propagationVector_electricReal (frame : PolarizationFrame direction)
    (J : JonesVector) :
    ⟪frame.propagationVector, frame.electricReal J⟫_ℝ = 0 := by
  rw [electricReal_eq_sum, inner_sum]
  simp [inner_smul_right, frame.inner_propagationVector_axis]

/-- The imaginary embedded quadrature is transverse to the propagation direction. -/
lemma inner_propagationVector_electricImag (frame : PolarizationFrame direction)
    (J : JonesVector) :
    ⟪frame.propagationVector, frame.electricImag J⟫_ℝ = 0 := by
  rw [electricImag_eq_sum, inner_sum]
  simp [inner_smul_right, frame.inner_propagationVector_axis]

/-- A real quadrature coordinate is the real part of the corresponding Jones coordinate. -/
lemma inner_axis_electricReal (frame : PolarizationFrame direction)
    (J : JonesVector) (i : Fin 2) :
    ⟪frame.axis i, frame.electricReal J⟫_ℝ = (J.components i).re := by
  rw [electricReal_eq_sum]
  exact frame.orthonormal_axis.inner_right_fintype (fun j ↦ (J.components j).re) i

/-- An imaginary quadrature coordinate is the imaginary part of the corresponding Jones
coordinate. -/
lemma inner_axis_electricImag (frame : PolarizationFrame direction)
    (J : JonesVector) (i : Fin 2) :
    ⟪frame.axis i, frame.electricImag J⟫_ℝ = (J.components i).im := by
  rw [electricImag_eq_sum]
  exact frame.orthonormal_axis.inner_right_fintype (fun j ↦ (J.components j).im) i

/-- The squared norm of the real quadrature is the sum of squared real Jones coordinates. -/
lemma electricReal_norm_sq (frame : PolarizationFrame direction) (J : JonesVector) :
    ‖frame.electricReal J‖ ^ 2 = ∑ i : Fin 2, (J.components i).re ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, electricReal_eq_sum]
  rw [frame.orthonormal_axis.inner_sum (fun i ↦ (J.components i).re)
    (fun i ↦ (J.components i).re) Finset.univ]
  simp [pow_two]

/-- The squared norm of the imaginary quadrature is the sum of squared imaginary Jones
coordinates. -/
lemma electricImag_norm_sq (frame : PolarizationFrame direction) (J : JonesVector) :
    ‖frame.electricImag J‖ ^ 2 = ∑ i : Fin 2, (J.components i).im ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, electricImag_eq_sum]
  rw [frame.orthonormal_axis.inner_sum (fun i ↦ (J.components i).im)
    (fun i ↦ (J.components i).im) Finset.univ]
  simp [pow_two]

/-- The two real quadrature squared norms sum to squared Jones intensity. -/
lemma electricReal_norm_sq_add_electricImag_norm_sq
    (frame : PolarizationFrame direction) (J : JonesVector) :
    ‖frame.electricReal J‖ ^ 2 + ‖frame.electricImag J‖ ^ 2 = J.intensity := by
  rw [electricReal_norm_sq, electricImag_norm_sq, JonesVector.intensity_eq_sum_normSq,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [Complex.normSq_apply]
  ring

/-!

## D. Phasor realization

-/

/-- Realize an embedded Jones amplitude using the repository phasor convention. -/
def realizeJones (frame : PolarizationFrame direction) (J : JonesVector)
    (carrierPhase : ℝ) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 fun k ↦ Phasor.realize (frame.embedJones J k) carrierPhase

/-- Realization of the embedded amplitude is the cosine-sine quadrature combination. -/
lemma realizeJones_eq (frame : PolarizationFrame direction) (J : JonesVector)
    (carrierPhase : ℝ) :
    frame.realizeJones J carrierPhase =
      Real.cos carrierPhase • frame.electricReal J -
        Real.sin carrierPhase • frame.electricImag J := by
  ext k
  simp [realizeJones, Phasor.realize, electricReal, electricImag, Complex.mul_re,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  ring

/-- Realization is the sum of the scalar Jones-component realizations along the frame axes. -/
lemma realizeJones_eq_sum (frame : PolarizationFrame direction) (J : JonesVector)
    (carrierPhase : ℝ) :
    frame.realizeJones J carrierPhase =
      ∑ i : Fin 2, Phasor.realize (J.components i) carrierPhase • frame.axis i := by
  ext k
  simp [realizeJones, embedJones, complexAxis, Phasor.realize, Complex.mul_re,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  ring

/-- Every realized Jones field is transverse to the propagation direction. -/
lemma inner_propagationVector_realizeJones (frame : PolarizationFrame direction)
    (J : JonesVector) (carrierPhase : ℝ) :
    ⟪frame.propagationVector, frame.realizeJones J carrierPhase⟫_ℝ = 0 := by
  rw [realizeJones_eq, inner_sub_right, inner_smul_right, inner_smul_right,
    frame.inner_propagationVector_electricReal,
    frame.inner_propagationVector_electricImag]
  simp

end PolarizationFrame

/-!

## E. Coherent phase and oriented quarter-turn

-/

namespace JonesVector

/-- The Jones-coordinate quarter-turn induced by `n × E`, with propagation vector `n` on the left.

In every oriented polarization frame this sends coordinates `(z₀, z₁)` to `(-z₁, z₀)`. It does
not assign a circular-polarization handedness name. -/
def propagationCross (J : JonesVector) : JonesVector :=
  ofComponents (-J.components 1) (J.components 0)

/-- The first coordinate after the propagation-cross quarter-turn. -/
@[simp]
lemma propagationCross_components_zero (J : JonesVector) :
    J.propagationCross.components 0 = -J.components 1 := rfl

/-- The second coordinate after the propagation-cross quarter-turn. -/
@[simp]
lemma propagationCross_components_one (J : JonesVector) :
    J.propagationCross.components 1 = J.components 0 := rfl

/-- The propagation-cross quarter-turn preserves squared Jones intensity. -/
@[simp]
lemma intensity_propagationCross (J : JonesVector) :
    J.propagationCross.intensity = J.intensity := by
  rw [intensity_eq_sum_normSq, intensity_eq_sum_normSq, Fin.sum_univ_two,
    Fin.sum_univ_two]
  simp [Complex.normSq_neg]
  ring

/-- The propagation-cross quarter-turn commutes with a common Jones phase shift. -/
lemma propagationCross_phaseShift (J : JonesVector) (phase : ℝ) :
    (J.phaseShift phase).propagationCross = J.propagationCross.phaseShift phase := by
  ext i
  fin_cases i <;> simp [propagationCross, phaseShift, scale]

end JonesVector

namespace PolarizationFrame

variable {direction : Space.Direction 3}

/-- A common Jones phase multiplies the embedded complex spatial phasor by the same phase. -/
lemma embedJones_phaseShift (frame : PolarizationFrame direction)
    (J : JonesVector) (phase : ℝ) :
    frame.embedJones (J.phaseShift phase) =
      Complex.exp ((phase : ℂ) * Complex.I) • frame.embedJones J := by
  rw [embedJones, embedJones]
  simp only [JonesVector.phaseShift, JonesVector.scale, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [smul_smul]

/-- A common Jones phase shift advances the carrier phase of the realized spatial field. -/
lemma realizeJones_phaseShift (frame : PolarizationFrame direction)
    (J : JonesVector) (phase carrierPhase : ℝ) :
    frame.realizeJones (J.phaseShift phase) carrierPhase =
      frame.realizeJones J (carrierPhase + phase) := by
  rw [realizeJones_eq_sum, realizeJones_eq_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [JonesVector.phaseShift, JonesVector.scale]
  exact congrArg (fun r : ℝ => r • frame.axis i)
    (Phasor.realize_exp_mul (J.components i) phase carrierPhase)

/-- Realizing the propagation-cross Jones coordinates equals crossing the realized electric
amplitude with the propagation vector. -/
lemma realizeJones_propagationCross (frame : PolarizationFrame direction)
    (J : JonesVector) (carrierPhase : ℝ) :
    frame.realizeJones J.propagationCross carrierPhase =
      frame.propagationVector ⨯ₑ₃ frame.realizeJones J carrierPhase := by
  rw [realizeJones_eq_sum, realizeJones_eq_sum, Fin.sum_univ_two, Fin.sum_univ_two,
    Space.cross_add, Space.cross_smul, Space.cross_smul,
    frame.propagationVector_cross_axis_zero, frame.propagationVector_cross_axis_one]
  simp [JonesVector.propagationCross, Phasor.realize, Complex.mul_re]
  module

/-- The real quadrature of the propagation-cross Jones state is the propagation vector crossed
with the original real quadrature. -/
lemma electricReal_propagationCross (frame : PolarizationFrame direction)
    (J : JonesVector) :
    frame.electricReal J.propagationCross =
      frame.propagationVector ⨯ₑ₃ frame.electricReal J := by
  simpa [realizeJones_eq] using frame.realizeJones_propagationCross J 0

/-- The imaginary quadrature of the propagation-cross Jones state is the propagation vector
crossed with the original imaginary quadrature. -/
lemma electricImag_propagationCross (frame : PolarizationFrame direction)
    (J : JonesVector) :
    frame.electricImag J.propagationCross =
      frame.propagationVector ⨯ₑ₃ frame.electricImag J := by
  simpa [realizeJones_eq, Real.cos_neg, Real.sin_neg] using
    frame.realizeJones_propagationCross J (-(Real.pi / 2))

/-- The positive-`I` quadrature state realizes with a negative sine coefficient on the second
oriented frame axis. This is an algebraic sign regression, not a handedness name. -/
lemma realizeJones_plusIQuadrature (frame : PolarizationFrame direction)
    (carrierPhase : ℝ) :
    frame.realizeJones JonesVector.plusIQuadrature carrierPhase =
      JonesVector.unitEqualAmplitude •
        (Real.cos carrierPhase • frame.axis 0 - Real.sin carrierPhase • frame.axis 1) := by
  rw [realizeJones_eq_sum, Fin.sum_univ_two]
  simp [JonesVector.plusIQuadrature, Phasor.realize_eq_re_cos_sub_im_sin]
  module

/-- The negative-`I` quadrature state realizes with a positive sine coefficient on the second
oriented frame axis. This is an algebraic sign regression, not a handedness name. -/
lemma realizeJones_minusIQuadrature (frame : PolarizationFrame direction)
    (carrierPhase : ℝ) :
    frame.realizeJones JonesVector.minusIQuadrature carrierPhase =
      JonesVector.unitEqualAmplitude •
        (Real.cos carrierPhase • frame.axis 0 + Real.sin carrierPhase • frame.axis 1) := by
  rw [realizeJones_eq_sum, Fin.sum_univ_two]
  simp [JonesVector.minusIQuadrature, Phasor.realize_eq_re_cos_sub_im_sin]
  module

end PolarizationFrame

end

end Optics
