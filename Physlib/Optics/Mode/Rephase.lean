/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Mathlib.Analysis.Complex.Circle
public import Physlib.Optics.Mode.Reindex

/-!
# Unit-phase coordinate changes for finite optical modes

## i. Overview

This file defines unit-complex phase changes of finite power-normalized modal coordinates.
Rephasing amplitudes is a complex-linear isometry, while mode transforms and scattering matrices
change covariantly so that their action represents the same linear map in the new coordinates.

## ii. Phase convention

For an input phase gauge `gIn` and output phase gauge `gOut`, amplitudes change as
`a' i = gIn i * a i` and a transform changes entrywise as
`T' o i = gOut o * T o i * (gIn i)⁻¹`. Thus
`(T' a') o = gOut o * (T a) o` componentwise.

The input and output gauges are deliberately independent. This covers abstract unitary diagonal
coordinate changes, but does not by itself encode a physical reference-plane displacement or a
time-reversal pairing. In particular, no matrix-symmetry or reciprocity claim follows from this
file; those require additional port and propagation conventions.

`rephase` is a passive coordinate change: both an amplitude and its represented transform change.
It is not an optical component that changes a signal while keeping its coordinates fixed. A
physical reference-plane change must instead obtain related input and output gauges from a stated
propagation convention.

## iii. Main definitions

- `ModePhaseGauge`: a unit-complex phase for each mode.
- `ModeAmplitude.rephase`: the isometric phase change of modal amplitudes.
- `ModeTransform.rephase`: the covariant phase change of a transform.
- `ScatteringMatrix.rephase`: independently rephasing its incident and outgoing coordinates.

-/

@[expose] public section

namespace Optics

noncomputable section

/-! ## A. Phase gauges and mode amplitudes -/

/-- A choice of unit complex coordinate phase for every mode indexed by `ι`. -/
abbrev ModePhaseGauge (ι : Type*) := ι → Circle

/-- Relabel a phase gauge along an equivalence from old mode labels to new mode labels. -/
def ModePhaseGauge.reindex {ι ι' : Type*} (e : ι ≃ ι') (g : ModePhaseGauge ι) :
    ModePhaseGauge ι' :=
  g ∘ e.symm

/-- Combine phase gauges on disjoint mode families. -/
def ModePhaseGauge.directSum {ι κ : Type*} (g : ModePhaseGauge ι)
    (h : ModePhaseGauge κ) : ModePhaseGauge (ι ⊕ κ) :=
  Sum.elim g h

/-- A relabeled phase gauge evaluates at the corresponding old mode label. -/
@[simp]
lemma ModePhaseGauge.reindex_apply {ι ι' : Type*} (e : ι ≃ ι')
    (g : ModePhaseGauge ι) (i : ι') : g.reindex e i = g (e.symm i) := rfl

/-- A direct-sum phase gauge restricts to its first gauge on the left summand. -/
@[simp]
lemma ModePhaseGauge.directSum_apply_inl {ι κ : Type*} (g : ModePhaseGauge ι)
    (h : ModePhaseGauge κ) (i : ι) : g.directSum h (Sum.inl i) = g i := rfl

/-- A direct-sum phase gauge restricts to its second gauge on the right summand. -/
@[simp]
lemma ModePhaseGauge.directSum_apply_inr {ι κ : Type*} (g : ModePhaseGauge ι)
    (h : ModePhaseGauge κ) (i : κ) : g.directSum h (Sum.inr i) = h i := rfl

/-- Relabeling a direct-sum gauge is the direct sum of the relabeled gauges. -/
lemma ModePhaseGauge.reindex_directSum {ι ι' κ κ' : Type*} (e : ι ≃ ι')
    (f : κ ≃ κ') (g : ModePhaseGauge ι) (h : ModePhaseGauge κ) :
    (g.directSum h).reindex (e.sumCongr f) = (g.reindex e).directSum (h.reindex f) := by
  funext i
  rcases i with i | i <;> rfl

/-- Rephasing finite mode amplitudes by unit complex phases is a complex-linear isometry. -/
def ModeAmplitude.rephase {ι : Type*} [Fintype ι] (g : ModePhaseGauge ι) :
    ModeAmplitude ι ≃ₗᵢ[ℂ] ModeAmplitude ι :=
  LinearIsometryEquiv.piLpCongrRight 2 fun i =>
    LinearIsometryEquiv.mk (LinearEquiv.smulOfUnit (Circle.toUnits (g i))) (by
      intro x
      change ‖(Circle.toUnits (g i) : ℂ) • x‖ = ‖x‖
      rw [norm_smul]
      change ‖(g i : ℂ)‖ * ‖x‖ = ‖x‖
      rw [Circle.norm_coe, one_mul])

/-- Rephasing multiplies each modal amplitude by its selected unit complex phase. -/
@[simp]
lemma ModeAmplitude.rephase_apply {ι : Type*} [Fintype ι] (g : ModePhaseGauge ι)
    (a : ModeAmplitude ι) (i : ι) :
    ModeAmplitude.rephase g a i = (g i : ℂ) * a i := rfl

/-- Rephasing a finite mode-amplitude family preserves its modal power. -/
@[simp]
lemma ModeAmplitude.power_rephase {ι : Type*} [Fintype ι] (g : ModePhaseGauge ι)
    (a : ModeAmplitude ι) : (ModeAmplitude.rephase g a).power = a.power := by
  simp [ModeAmplitude.power]

/-- Rephasing by the inverse gauge recovers the original amplitudes. -/
@[simp]
lemma ModeAmplitude.rephase_inv_rephase {ι : Type*} [Fintype ι]
    (g : ModePhaseGauge ι) (a : ModeAmplitude ι) :
    ModeAmplitude.rephase g⁻¹ (ModeAmplitude.rephase g a) = a := by
  ext i
  simp [Circle.coe_inv, Circle.coe_ne_zero]

/-- Rephasing by a gauge after removing it recovers the original amplitudes. -/
@[simp]
lemma ModeAmplitude.rephase_rephase_inv {ι : Type*} [Fintype ι]
    (g : ModePhaseGauge ι) (a : ModeAmplitude ι) :
    ModeAmplitude.rephase g (ModeAmplitude.rephase g⁻¹ a) = a := by
  ext i
  simp [Circle.coe_inv, Circle.coe_ne_zero]

/-- Relabeling after rephasing agrees with rephasing by the relabeled gauge. -/
lemma ModeAmplitude.reindex_rephase {ι ι' : Type*} [Fintype ι] [Fintype ι']
    (e : ι ≃ ι') (g : ModePhaseGauge ι) (a : ModeAmplitude ι) :
    ModeAmplitude.reindex e (ModeAmplitude.rephase g a) =
      ModeAmplitude.rephase (g.reindex e) (ModeAmplitude.reindex e a) := by
  ext i
  rfl

/-- Rephasing by a direct-sum gauge distributes over direct-sum amplitudes. -/
lemma ModeAmplitude.rephase_directSum {ι κ : Type*} [Fintype ι] [Fintype κ]
    (g : ModePhaseGauge ι) (h : ModePhaseGauge κ) (a : ModeAmplitude ι)
    (b : ModeAmplitude κ) :
    ModeAmplitude.rephase (g.directSum h) (a.directSum b) =
      (ModeAmplitude.rephase g a).directSum (ModeAmplitude.rephase h b) := by
  apply WithLp.ofLp_injective 2
  funext i
  rcases i with i | i <;> rfl

/-! ## B. Covariant mode transforms -/

/-- Change the input and output phase coordinates of a mode transform.

The convention is `T' o i = gOut o * T o i * (gIn i)⁻¹`, so the transformed matrix sends
rephased input coordinates to the corresponding rephased output coordinates. -/
def ModeTransform.rephase {ι κ : Type*} (gIn : ModePhaseGauge ι)
    (gOut : ModePhaseGauge κ) (T : ModeTransform ι κ) : ModeTransform ι κ :=
  fun o i => (gOut o : ℂ) * T o i * (gIn i : ℂ)⁻¹

/-- Rephasing a transform applies the output phase and inverse input phase entrywise. -/
@[simp]
lemma ModeTransform.rephase_apply {ι κ : Type*} (gIn : ModePhaseGauge ι)
    (gOut : ModePhaseGauge κ) (T : ModeTransform ι κ) (o : κ) (i : ι) :
    T.rephase gIn gOut o i = (gOut o : ℂ) * T o i * (gIn i : ℂ)⁻¹ := rfl

/-- Rephasing a transform by the inverse input and output gauges recovers it. -/
@[simp]
lemma ModeTransform.rephase_inv_rephase {ι κ : Type*} (gIn : ModePhaseGauge ι)
    (gOut : ModePhaseGauge κ) (T : ModeTransform ι κ) :
    ModeTransform.rephase gIn⁻¹ gOut⁻¹ (T.rephase gIn gOut) = T := by
  ext o i
  simp only [ModeTransform.rephase_apply, Pi.inv_apply, Circle.coe_inv]
  field_simp [Circle.coe_ne_zero]

/-- Rephasing by input and output gauges after removing them recovers the original transform. -/
@[simp]
lemma ModeTransform.rephase_rephase_inv {ι κ : Type*} (gIn : ModePhaseGauge ι)
    (gOut : ModePhaseGauge κ) (T : ModeTransform ι κ) :
    ModeTransform.rephase gIn gOut (T.rephase gIn⁻¹ gOut⁻¹) = T := by
  ext o i
  simp only [ModeTransform.rephase_apply, Pi.inv_apply, Circle.coe_inv]
  field_simp [Circle.coe_ne_zero]

/-- A rephased transform sends rephased inputs to the corresponding rephased outputs. -/
lemma ModeTransform.toLinearMap_rephase_apply {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] (gIn : ModePhaseGauge ι)
    (gOut : ModePhaseGauge κ) (T : ModeTransform ι κ) (a : ModeAmplitude ι) :
    (T.rephase gIn gOut).toLinearMap (ModeAmplitude.rephase gIn a) =
      ModeAmplitude.rephase gOut (T.toLinearMap a) := by
  apply WithLp.ofLp_injective 2
  funext o
  simp only [Matrix.ofLp_toLpLin, Matrix.toLin'_apply, ModeTransform.rephase,
    ModeAmplitude.rephase_apply, Matrix.mulVec, dotProduct]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  field_simp [Circle.coe_ne_zero]

/-- The action of a rephased transform on arbitrary new coordinates is obtained by first
removing the input gauge and then applying the output gauge. -/
lemma ModeTransform.toLinearMap_rephase_eq {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] (gIn : ModePhaseGauge ι)
    (gOut : ModePhaseGauge κ) (T : ModeTransform ι κ) (a : ModeAmplitude ι) :
    (T.rephase gIn gOut).toLinearMap a =
      ModeAmplitude.rephase gOut (T.toLinearMap (ModeAmplitude.rephase gIn⁻¹ a)) := by
  simpa only [ModeAmplitude.rephase_rephase_inv] using
    ModeTransform.toLinearMap_rephase_apply gIn gOut T (ModeAmplitude.rephase gIn⁻¹ a)

/-! ## C. Invariance of modal predicates -/

/-- Unit-phase changes of input and output coordinates preserve and reflect power preservation. -/
lemma ModeTransform.isPowerPreserving_rephase_iff {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] (gIn : ModePhaseGauge ι)
    (gOut : ModePhaseGauge κ) (T : ModeTransform ι κ) :
    (T.rephase gIn gOut).IsPowerPreserving ↔ T.IsPowerPreserving := by
  constructor
  · intro hT a
    have ha := hT (ModeAmplitude.rephase gIn a)
    rw [ModeTransform.toLinearMap_rephase_apply] at ha
    simpa only [ModeAmplitude.power_rephase] using ha
  · intro hT a'
    obtain ⟨a, rfl⟩ := (ModeAmplitude.rephase gIn).surjective a'
    rw [ModeTransform.toLinearMap_rephase_apply]
    simpa only [ModeAmplitude.power_rephase] using hT a

/-- Unit-phase changes of input and output coordinates preserve and reflect passivity. -/
lemma ModeTransform.isPassive_rephase_iff {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] (gIn : ModePhaseGauge ι)
    (gOut : ModePhaseGauge κ) (T : ModeTransform ι κ) :
    (T.rephase gIn gOut).IsPassive ↔ T.IsPassive := by
  constructor
  · intro hT a
    have ha := hT (ModeAmplitude.rephase gIn a)
    rw [ModeTransform.toLinearMap_rephase_apply] at ha
    simpa only [ModeAmplitude.power_rephase] using ha
  · intro hT a'
    obtain ⟨a, rfl⟩ := (ModeAmplitude.rephase gIn).surjective a'
    rw [ModeTransform.toLinearMap_rephase_apply]
    simpa only [ModeAmplitude.power_rephase] using hT a

/-! ## D. Compatibility with transform composition -/

/-- Rephasing a cascade cancels the shared intermediate coordinate gauge. -/
lemma ModeTransform.rephase_mul {ι κ μ : Type*} [Fintype κ] (gIn : ModePhaseGauge ι)
    (gMid : ModePhaseGauge κ) (gOut : ModePhaseGauge μ) (T : ModeTransform ι κ)
    (U : ModeTransform κ μ) :
    ModeTransform.rephase gIn gOut (U * T) =
      U.rephase gMid gOut * T.rephase gIn gMid := by
  ext o i
  simp only [ModeTransform.rephase_apply, Matrix.mul_apply]
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  field_simp [Circle.coe_ne_zero]

/-- Rephasing by direct-sum gauges distributes over block-diagonal parallel composition. -/
lemma ModeTransform.rephase_directSum {ι κ μ ν : Type*} (gIn : ModePhaseGauge ι)
    (gOut : ModePhaseGauge κ) (hIn : ModePhaseGauge μ) (hOut : ModePhaseGauge ν)
    (T : ModeTransform ι κ) (U : ModeTransform μ ν) :
    (T.directSum U).rephase (gIn.directSum hIn) (gOut.directSum hOut) =
      (T.rephase gIn gOut).directSum (U.rephase hIn hOut) := by
  ext (o | o) (i | i) <;>
    simp [ModeTransform.rephase, ModeTransform.directSum, ModePhaseGauge.directSum]

/-- Relabeling after rephasing a transform agrees with rephasing by the relabeled input and output
gauges. -/
lemma ModeTransform.reindex_rephase {ι ι' κ κ' : Type*} (eIn : ι ≃ ι')
    (eOut : κ ≃ κ') (gIn : ModePhaseGauge ι) (gOut : ModePhaseGauge κ)
    (T : ModeTransform ι κ) :
    ModeTransform.reindex eIn eOut (T.rephase gIn gOut) =
      (T.reindex eIn eOut).rephase (gIn.reindex eIn) (gOut.reindex eOut) := by
  ext o i
  rfl

/-! ## E. Scattering-coordinate changes -/

/-- Independently change the incident and outgoing phase coordinates of a scattering matrix. -/
def ScatteringMatrix.rephase {ι : Type*} (gIn gOut : ModePhaseGauge ι)
    (S : ScatteringMatrix ι) : ScatteringMatrix ι where
  toModeTransform := S.toModeTransform.rephase gIn gOut

/-- The underlying transform of a rephased scattering matrix is the rephased transform. -/
@[simp]
lemma ScatteringMatrix.toModeTransform_rephase {ι : Type*} (gIn gOut : ModePhaseGauge ι)
    (S : ScatteringMatrix ι) :
    (S.rephase gIn gOut).toModeTransform = S.toModeTransform.rephase gIn gOut := rfl

/-- Rephasing a scattering matrix by the inverse incident and outgoing gauges recovers it. -/
@[simp]
lemma ScatteringMatrix.rephase_inv_rephase {ι : Type*} (gIn gOut : ModePhaseGauge ι)
    (S : ScatteringMatrix ι) : (S.rephase gIn gOut).rephase gIn⁻¹ gOut⁻¹ = S := by
  cases S
  simp only [ScatteringMatrix.rephase, ModeTransform.rephase_inv_rephase]

/-- Rephasing after removing the incident and outgoing gauges recovers the scattering matrix. -/
@[simp]
lemma ScatteringMatrix.rephase_rephase_inv {ι : Type*} (gIn gOut : ModePhaseGauge ι)
    (S : ScatteringMatrix ι) : (S.rephase gIn⁻¹ gOut⁻¹).rephase gIn gOut = S := by
  cases S
  simp only [ScatteringMatrix.rephase, ModeTransform.rephase_rephase_inv]

/-- Direct-sum phase gauges distribute over independent parallel composition of scattering
matrices. -/
lemma ScatteringMatrix.rephase_directSum {ι κ : Type*} (gIn gOut : ModePhaseGauge ι)
    (hIn hOut : ModePhaseGauge κ) (S : ScatteringMatrix ι) (R : ScatteringMatrix κ) :
    (S.directSum R).rephase (gIn.directSum hIn) (gOut.directSum hOut) =
      (S.rephase gIn gOut).directSum (R.rephase hIn hOut) := by
  cases S
  cases R
  simp only [ScatteringMatrix.directSum, ScatteringMatrix.rephase,
    ModeTransform.rephase_directSum]

/-- Relabeling after rephasing a scattering matrix agrees with rephasing by the relabeled incident
and outgoing gauges. -/
lemma ScatteringMatrix.reindex_rephase {ι κ : Type*} (e : ι ≃ κ)
    (gIn gOut : ModePhaseGauge ι) (S : ScatteringMatrix ι) :
    (S.rephase gIn gOut).reindex e =
      (S.reindex e).rephase (gIn.reindex e) (gOut.reindex e) := by
  cases S
  simp only [ScatteringMatrix.reindex, ScatteringMatrix.rephase,
    ModeTransform.reindex_rephase]

/-- Independent unit-phase changes of incident and outgoing coordinates preserve and reflect
scattering losslessness. -/
lemma ScatteringMatrix.isLossless_rephase_iff {ι : Type*}
    [Fintype ι] [DecidableEq ι] (gIn gOut : ModePhaseGauge ι)
    (S : ScatteringMatrix ι) : (S.rephase gIn gOut).IsLossless ↔ S.IsLossless := by
  calc
    (S.rephase gIn gOut).IsLossless ↔
        ModeTransform.IsPowerPreserving (S.rephase gIn gOut).toModeTransform :=
      ScatteringMatrix.isLossless_iff_isPowerPreserving _
    _ ↔ ModeTransform.IsPowerPreserving S.toModeTransform := by
      simpa only [ScatteringMatrix.toModeTransform_rephase] using
        ModeTransform.isPowerPreserving_rephase_iff gIn gOut S.toModeTransform
    _ ↔ S.IsLossless := (ScatteringMatrix.isLossless_iff_isPowerPreserving S).symm

end

end Optics
