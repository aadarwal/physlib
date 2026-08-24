/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Polarization.IncidenceFrame
public import Physlib.Optics.Polarization.PlanarFrame

/-!
# Incidence polarization-frame sign regressions

## i. Overview

This file pins the cross-product and axis-order conventions of the incidence polarization frame in
exact coordinates. The non-normal fixture uses interface normal `(0, 0, 1)` and propagation
direction `(3/5, 0, 4/5)`. It verifies `s = (0, 1, 0)` and
`p = (-4/5, 0, 3/5)`.

The normal-incidence fixture supplies the tangent axis `(0, 1, 0)` explicitly. Reversing the
propagation direction preserves that selected first axis and negates the derived second axis. This
is the sign behavior later full-vector Fresnel coefficients must respect; it does not itself define
or derive such coefficients.

## ii. Key results

- `incidenceRegression_sPolarizationAxis` and `incidenceRegression_pPolarizationAxis`: the exact
  non-normal `s` and `p` axes.
- `normalIncidenceRegressionFrames_axis_zero_eq`: forward and backward normal frames share the
  selected first axis.
- `normalIncidenceRegressionFrames_axis_one_neg`: their derived second axes have opposite signs.
- `normalIncidenceRegressionForwardFrame_isSelectedTangentNormalIncidence` and
  `normalIncidenceRegressionBackwardFrame_isSelectedTangentNormalIncidence`: the same frames carry
  the exact positive- and negative-side normal-incidence relations.

## iii. Table of contents

- A. A non-normal coordinate fixture
- B. Selected-tangent normal-incidence frames

## iv. References

The regressions are direct exact-coordinate consequences of the imported Physlib incidence-frame
API. They add no interface side, boundary condition, reflection, refraction, irradiance, or power
semantics.
-/

@[expose] public section

namespace Optics

open Space Matrix InnerProductSpace

noncomputable section

/-!

## A. A non-normal coordinate fixture

-/

/-- The positive third-coordinate interface normal used by the incidence-frame regression. -/
def incidenceRegressionNormal : Space.Direction 3 :=
  ⟨⟨![0, 0, 1]⟩, by
    rw [Space.norm_eq]
    simp [Fin.sum_univ_three]⟩

/-- The unit `(3/5, 0, 4/5)` propagation direction used by the incidence-frame regression. -/
def incidenceRegressionDirection : Space.Direction 3 where
  unit := ⟨![3 / 5, 0, 4 / 5]⟩
  norm := by
    rw [Space.norm_eq]
    simp [Fin.sum_univ_three]
    norm_num

/-- The coordinate regression direction is non-normal to its interface normal. -/
lemma incidenceRegression_isNonNormal :
    IsNonNormalIncidence incidenceRegressionDirection incidenceRegressionNormal := by
  intro h
  have hy := congrArg (fun v : EuclideanSpace ℝ (Fin 3) ↦ v 1) h
  norm_num [IsNonNormalIncidence, incidenceRegressionDirection, incidenceRegressionNormal,
    crossProduct, Matrix.cons_val_two, Matrix.head_cons] at hy

/-- The coordinate regression selects the positive second-coordinate `s` axis. -/
lemma incidenceRegression_sPolarizationAxis :
    sPolarizationAxis incidenceRegressionDirection incidenceRegressionNormal
      incidenceRegression_isNonNormal = WithLp.toLp 2 ![0, 1, 0] := by
  have hsqrt25 : Real.sqrt 25 = 5 := by
    rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
  have hsqrt9 : Real.sqrt 9 = 3 := by
    rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
  ext i
  fin_cases i <;>
    norm_num [sPolarizationAxis, NormedSpace.normalize, incidenceRegressionDirection,
      incidenceRegressionNormal, crossProduct, EuclideanSpace.norm_eq, Fin.sum_univ_three,
      Matrix.cons_val_two, Matrix.head_cons, hsqrt25, hsqrt9]

/-- The coordinate regression selects `(-4/5, 0, 3/5)` as the oriented `p` axis. -/
lemma incidenceRegression_pPolarizationAxis :
    pPolarizationAxis incidenceRegressionDirection incidenceRegressionNormal
      incidenceRegression_isNonNormal = WithLp.toLp 2 ![-4 / 5, 0, 3 / 5] := by
  rw [pPolarizationAxis, incidenceRegression_sPolarizationAxis]
  ext i
  fin_cases i <;>
    norm_num [incidenceRegressionDirection, crossProduct, Matrix.cons_val_two,
      Matrix.head_cons]

/-!

## B. Selected-tangent normal-incidence frames

-/

/-- The negative third-coordinate propagation direction used by the normal-incidence
regression. -/
def normalIncidenceRegressionBackwardDirection : Space.Direction 3 where
  unit := ⟨![0, 0, -1]⟩
  norm := by
    rw [Space.norm_eq]
    simp [Fin.sum_univ_three]

/-- The independently selected second-coordinate tangent axis at normal incidence. -/
def normalIncidenceRegressionTangentAxis : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![0, 1, 0]

/-- The oriented coordinate plane used to test the selected-tangent normal-incidence relation. -/
def normalIncidenceRegressionPlane : OrientedAffineHyperplane 3 where
  point := 0
  normal := incidenceRegressionNormal

/-- The selected normal-incidence tangent axis has unit norm. -/
lemma normalIncidenceRegressionTangentAxis_norm :
    ‖normalIncidenceRegressionTangentAxis‖ = 1 := by
  simp [normalIncidenceRegressionTangentAxis, EuclideanSpace.norm_eq, Fin.sum_univ_three]

/-- The selected tangent axis is transverse to the positive-normal propagation direction. -/
lemma normalIncidenceRegressionTangentAxis_forward_transverse :
    inner ℝ (Space.basis.repr incidenceRegressionNormal.unit)
      normalIncidenceRegressionTangentAxis = 0 := by
  norm_num [incidenceRegressionNormal, normalIncidenceRegressionTangentAxis, PiLp.inner_apply,
    Fin.sum_univ_three, RCLike.inner_apply, Matrix.cons_val_two, Matrix.head_cons]

/-- The selected tangent axis is transverse to the negative-normal propagation direction. -/
lemma normalIncidenceRegressionTangentAxis_backward_transverse :
    inner ℝ (Space.basis.repr normalIncidenceRegressionBackwardDirection.unit)
      normalIncidenceRegressionTangentAxis = 0 := by
  norm_num [normalIncidenceRegressionBackwardDirection, normalIncidenceRegressionTangentAxis,
    PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, Matrix.cons_val_two,
    Matrix.head_cons]

/-- The selected-tangent polarization frame propagating along the positive interface normal. -/
def normalIncidenceRegressionForwardFrame : PolarizationFrame incidenceRegressionNormal :=
  PolarizationFrame.ofAxisZero incidenceRegressionNormal normalIncidenceRegressionTangentAxis
    normalIncidenceRegressionTangentAxis_norm
    normalIncidenceRegressionTangentAxis_forward_transverse

/-- The selected-tangent polarization frame propagating opposite the interface normal. -/
def normalIncidenceRegressionBackwardFrame :
    PolarizationFrame normalIncidenceRegressionBackwardDirection :=
  PolarizationFrame.ofAxisZero normalIncidenceRegressionBackwardDirection
    normalIncidenceRegressionTangentAxis normalIncidenceRegressionTangentAxis_norm
    normalIncidenceRegressionTangentAxis_backward_transverse

/-- Both normal-incidence propagation directions retain the independently selected first axis. -/
lemma normalIncidenceRegressionFrames_axis_zero_eq :
    normalIncidenceRegressionBackwardFrame.axis 0 =
      normalIncidenceRegressionForwardFrame.axis 0 := by
  simp [normalIncidenceRegressionBackwardFrame, normalIncidenceRegressionForwardFrame]

/-- The forward normal-incidence frame has second axis `(-1, 0, 0)`. -/
lemma normalIncidenceRegressionForwardFrame_axis_one :
    normalIncidenceRegressionForwardFrame.axis 1 = WithLp.toLp 2 ![-1, 0, 0] := by
  rw [normalIncidenceRegressionForwardFrame, PolarizationFrame.ofAxisZero_axis_one]
  ext i
  fin_cases i <;>
    norm_num [incidenceRegressionNormal, normalIncidenceRegressionTangentAxis, crossProduct,
      Matrix.cons_val_two, Matrix.head_cons]

/-- The backward normal-incidence frame has second axis `(1, 0, 0)`. -/
lemma normalIncidenceRegressionBackwardFrame_axis_one :
    normalIncidenceRegressionBackwardFrame.axis 1 = WithLp.toLp 2 ![1, 0, 0] := by
  rw [normalIncidenceRegressionBackwardFrame, PolarizationFrame.ofAxisZero_axis_one]
  ext i
  fin_cases i <;>
    norm_num [normalIncidenceRegressionBackwardDirection, normalIncidenceRegressionTangentAxis,
      crossProduct, Matrix.cons_val_two, Matrix.head_cons]

/-- Reversing normal-incidence propagation negates the derived second axis while preserving the
selected first axis. -/
lemma normalIncidenceRegressionFrames_axis_one_neg :
    normalIncidenceRegressionBackwardFrame.axis 1 =
      -normalIncidenceRegressionForwardFrame.axis 1 := by
  rw [normalIncidenceRegressionForwardFrame_axis_one,
    normalIncidenceRegressionBackwardFrame_axis_one]
  ext i
  fin_cases i <;>
    norm_num [Matrix.cons_val_two, Matrix.head_cons]

/-- The forward exact frame uses the selected tangent and the positive side normal. -/
lemma normalIncidenceRegressionForwardFrame_isSelectedTangentNormalIncidence :
    normalIncidenceRegressionForwardFrame.IsSelectedTangentNormalIncidence
      normalIncidenceRegressionPlane normalIncidenceRegressionForwardFrame .positive := by
  constructor
  · rfl
  · ext i
    fin_cases i <;>
      norm_num [PolarizationFrame.propagationVector, normalIncidenceRegressionPlane,
        incidenceRegressionNormal, OrientedAffineHyperplane.sideNormalVector,
        OrientedAffineHyperplane.normalVector, Matrix.cons_val_two, Matrix.head_cons]

/-- The backward exact frame uses the same selected tangent and the negative side normal. -/
lemma normalIncidenceRegressionBackwardFrame_isSelectedTangentNormalIncidence :
    normalIncidenceRegressionBackwardFrame.IsSelectedTangentNormalIncidence
      normalIncidenceRegressionPlane normalIncidenceRegressionForwardFrame .negative := by
  constructor
  · exact normalIncidenceRegressionFrames_axis_zero_eq
  · ext i
    fin_cases i <;>
      norm_num [PolarizationFrame.propagationVector, normalIncidenceRegressionPlane,
        incidenceRegressionNormal, normalIncidenceRegressionBackwardDirection,
        OrientedAffineHyperplane.sideNormalVector, OrientedAffineHyperplane.normalVector,
        Matrix.cons_val_two, Matrix.head_cons]

/-- The forward frame's fixed-plane `p` coordinate is its full-vector second Jones component. -/
lemma normalIncidenceRegressionForwardFrame_normalScaledSecondComponent (J : JonesVector) :
    normalIncidenceRegressionForwardFrame.normalScaledSecondComponent
      normalIncidenceRegressionPlane J = J.components 1 := by
  have h := normalIncidenceRegressionForwardFrame_isSelectedTangentNormalIncidence
  simpa using h.normalScaledSecondComponent_eq J

/-- The backward frame's fixed-plane `p` coordinate negates its full-vector second Jones
component. -/
lemma normalIncidenceRegressionBackwardFrame_normalScaledSecondComponent (J : JonesVector) :
    normalIncidenceRegressionBackwardFrame.normalScaledSecondComponent
      normalIncidenceRegressionPlane J = -J.components 1 := by
  have h := normalIncidenceRegressionBackwardFrame_isSelectedTangentNormalIncidence
  simpa using h.normalScaledSecondComponent_eq J

end

end Optics
