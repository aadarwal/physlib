/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Mode.Basic

/-!
# Relabeling finite optical modes

## i. Overview

This file defines the convention-free relabeling of finite power-normalized optical modes along
equivalences of their index types. Amplitudes are relabeled by a complex-linear isometry, while
mode transforms and scattering matrices change covariantly so that their action represents the
same linear map in the new labels.

Relabeling changes only the names of modes. It does not select propagation directions, physical
reference planes, or time-reversal partners. Consequently, this file makes no reciprocity claim.

## ii. Main definitions

- `ModeAmplitude.reindex`: the isometric relabeling of modal amplitudes.
- `ModeTransform.reindex`: relabeling the input and output indices of a transform.
- `ScatteringMatrix.reindex`: relabeling the channels of a scattering matrix.

-/

@[expose] public section

namespace Optics

noncomputable section

/-! ## A. Mode amplitudes -/

/-- Relabeling finite mode amplitudes is a complex-linear isometry. -/
def ModeAmplitude.reindex {ι ι' : Type*} [Fintype ι] [Fintype ι'] (e : ι ≃ ι') :
    ModeAmplitude ι ≃ₗᵢ[ℂ] ModeAmplitude ι' :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e

/-- Relabeling evaluates an amplitude at the corresponding old mode label. -/
@[simp]
lemma ModeAmplitude.reindex_apply {ι ι' : Type*} [Fintype ι] [Fintype ι']
    (e : ι ≃ ι') (a : ModeAmplitude ι) (i : ι') :
    ModeAmplitude.reindex e a i = a (e.symm i) := rfl

/-- Relabeling a finite mode-amplitude family preserves its modal power. -/
@[simp]
lemma ModeAmplitude.power_reindex {ι ι' : Type*} [Fintype ι] [Fintype ι']
    (e : ι ≃ ι') (a : ModeAmplitude ι) :
    (ModeAmplitude.reindex e a).power = a.power := by
  simp [ModeAmplitude.power]

/-- Relabeling back along the inverse equivalence recovers the original amplitudes. -/
@[simp]
lemma ModeAmplitude.reindex_symm_reindex {ι ι' : Type*} [Fintype ι] [Fintype ι']
    (e : ι ≃ ι') (a : ModeAmplitude ι) :
    ModeAmplitude.reindex e.symm (ModeAmplitude.reindex e a) = a := by
  ext i
  simp

/-- Relabeling from new labels back to old and then forward again recovers the new amplitudes. -/
@[simp]
lemma ModeAmplitude.reindex_reindex_symm {ι ι' : Type*} [Fintype ι] [Fintype ι']
    (e : ι ≃ ι') (a : ModeAmplitude ι') :
    ModeAmplitude.reindex e (ModeAmplitude.reindex e.symm a) = a := by
  ext i
  simp

/-- Relabeling distributes over the direct sum of two amplitude families. -/
lemma ModeAmplitude.reindex_directSum {ι ι' κ κ' : Type*}
    [Fintype ι] [Fintype ι'] [Fintype κ] [Fintype κ'] (e : ι ≃ ι') (f : κ ≃ κ')
    (a : ModeAmplitude ι) (b : ModeAmplitude κ) :
    ModeAmplitude.reindex (e.sumCongr f) (a.directSum b) =
      (ModeAmplitude.reindex e a).directSum (ModeAmplitude.reindex f b) := by
  apply WithLp.ofLp_injective 2
  funext i
  rcases i with i | i <;> rfl

/-! ## B. Covariant mode transforms -/

/-- Relabel the input and output indices of a mode transform by equivalences. -/
def ModeTransform.reindex {ι ι' κ κ' : Type*} (eIn : ι ≃ ι') (eOut : κ ≃ κ')
    (T : ModeTransform ι κ) : ModeTransform ι' κ' :=
  Matrix.reindex eOut eIn T

/-- Relabeling a transform evaluates its entries at the corresponding old mode labels. -/
@[simp]
lemma ModeTransform.reindex_apply {ι ι' κ κ' : Type*} (eIn : ι ≃ ι')
    (eOut : κ ≃ κ') (T : ModeTransform ι κ) (o : κ') (i : ι') :
    T.reindex eIn eOut o i = T (eOut.symm o) (eIn.symm i) := rfl

/-- Relabeling a transform back along the inverse input and output equivalences recovers it. -/
@[simp]
lemma ModeTransform.reindex_symm_reindex {ι ι' κ κ' : Type*} (eIn : ι ≃ ι')
    (eOut : κ ≃ κ') (T : ModeTransform ι κ) :
    ModeTransform.reindex eIn.symm eOut.symm (T.reindex eIn eOut) = T := by
  ext o i
  simp only [ModeTransform.reindex_apply, Equiv.symm_symm, Equiv.symm_apply_apply]

/-- Relabeling from new labels back to old and then forward again recovers the new transform. -/
@[simp]
lemma ModeTransform.reindex_reindex_symm {ι ι' κ κ' : Type*} (eIn : ι ≃ ι')
    (eOut : κ ≃ κ') (T : ModeTransform ι' κ') :
    ModeTransform.reindex eIn eOut (T.reindex eIn.symm eOut.symm) = T := by
  ext o i
  simp only [ModeTransform.reindex_apply, Equiv.symm_symm, Equiv.apply_symm_apply]

/-- A relabeled transform acts on relabeled amplitudes as the original transform does in the old
coordinates. -/
lemma ModeTransform.toLinearMap_reindex_apply {ι ι' κ κ' : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] [Fintype κ] [Fintype κ']
    (eIn : ι ≃ ι') (eOut : κ ≃ κ') (T : ModeTransform ι κ) (a : ModeAmplitude ι) :
    (T.reindex eIn eOut).toLinearMap (ModeAmplitude.reindex eIn a) =
      ModeAmplitude.reindex eOut (T.toLinearMap a) := by
  apply WithLp.ofLp_injective 2
  funext o
  simp only [Matrix.ofLp_toLpLin, ModeAmplitude.reindex_apply,
    ModeTransform.reindex_apply, Matrix.toLin'_apply, Matrix.mulVec, dotProduct]
  exact eIn.symm.sum_comp fun i => T (eOut.symm o) i * WithLp.ofLp a i

/-- The action of a relabeled transform on arbitrary new coordinates is obtained by first
returning the input to its old labels and then relabeling the output. -/
lemma ModeTransform.toLinearMap_reindex_eq {ι ι' κ κ' : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] [Fintype κ] [Fintype κ']
    (eIn : ι ≃ ι') (eOut : κ ≃ κ') (T : ModeTransform ι κ) (a : ModeAmplitude ι') :
    (T.reindex eIn eOut).toLinearMap a =
      ModeAmplitude.reindex eOut (T.toLinearMap (ModeAmplitude.reindex eIn.symm a)) := by
  simpa only [ModeAmplitude.reindex_reindex_symm] using
    ModeTransform.toLinearMap_reindex_apply eIn eOut T (ModeAmplitude.reindex eIn.symm a)

/-! ## C. Invariance of modal predicates -/

/-- Relabeling input and output modes preserves and reflects power preservation. -/
lemma ModeTransform.isPowerPreserving_reindex_iff {ι ι' κ κ' : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] [Fintype κ] [Fintype κ']
    (eIn : ι ≃ ι') (eOut : κ ≃ κ') (T : ModeTransform ι κ) :
    (T.reindex eIn eOut).IsPowerPreserving ↔ T.IsPowerPreserving := by
  constructor
  · intro hT a
    have ha := hT (ModeAmplitude.reindex eIn a)
    rw [ModeTransform.toLinearMap_reindex_apply] at ha
    simpa only [ModeAmplitude.power_reindex] using ha
  · intro hT a'
    obtain ⟨a, rfl⟩ := (ModeAmplitude.reindex eIn).surjective a'
    rw [ModeTransform.toLinearMap_reindex_apply]
    simpa only [ModeAmplitude.power_reindex] using hT a

/-- Relabeling input and output modes preserves and reflects passivity. -/
lemma ModeTransform.isPassive_reindex_iff {ι ι' κ κ' : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] [Fintype κ] [Fintype κ']
    (eIn : ι ≃ ι') (eOut : κ ≃ κ') (T : ModeTransform ι κ) :
    (T.reindex eIn eOut).IsPassive ↔ T.IsPassive := by
  constructor
  · intro hT a
    have ha := hT (ModeAmplitude.reindex eIn a)
    rw [ModeTransform.toLinearMap_reindex_apply] at ha
    simpa only [ModeAmplitude.power_reindex] using ha
  · intro hT a'
    obtain ⟨a, rfl⟩ := (ModeAmplitude.reindex eIn).surjective a'
    rw [ModeTransform.toLinearMap_reindex_apply]
    simpa only [ModeAmplitude.power_reindex] using hT a

/-! ## D. Compatibility with transform composition -/

/-- Relabeling a cascade is the cascade of the consistently relabeled transforms. -/
lemma ModeTransform.reindex_mul {ι ι' κ κ' μ μ' : Type*} [Fintype κ] [Fintype κ']
    (eIn : ι ≃ ι') (eMid : κ ≃ κ') (eOut : μ ≃ μ') (T : ModeTransform ι κ)
    (U : ModeTransform κ μ) :
    ModeTransform.reindex eIn eOut (U * T) =
      U.reindex eMid eOut * T.reindex eIn eMid := by
  simpa only [ModeTransform.reindex, Matrix.coe_reindexLinearEquiv] using
    (Matrix.reindexLinearEquiv_mul ℂ ℂ eOut eMid eIn U T).symm

/-- Relabeling distributes over block-diagonal parallel composition. -/
lemma ModeTransform.reindex_directSum {ι ι' κ κ' μ μ' ν ν' : Type*}
    (eIn : ι ≃ ι') (eOut : κ ≃ κ') (fIn : μ ≃ μ') (fOut : ν ≃ ν')
    (T : ModeTransform ι κ) (U : ModeTransform μ ν) :
    (T.directSum U).reindex (eIn.sumCongr fIn) (eOut.sumCongr fOut) =
      (T.reindex eIn eOut).directSum (U.reindex fIn fOut) := by
  ext (o | o) (i | i) <;> rfl

/-! ## E. Scattering-coordinate changes -/

/-- Relabel the common incident and outgoing channel index of a scattering matrix. -/
def ScatteringMatrix.reindex {ι κ : Type*} (e : ι ≃ κ)
    (S : ScatteringMatrix ι) : ScatteringMatrix κ where
  toModeTransform := S.toModeTransform.reindex e e

/-- The underlying transform of a relabeled scattering matrix is the relabeled transform. -/
@[simp]
lemma ScatteringMatrix.toModeTransform_reindex {ι κ : Type*} (e : ι ≃ κ)
    (S : ScatteringMatrix ι) :
    (S.reindex e).toModeTransform = S.toModeTransform.reindex e e := rfl

/-- Relabeling a scattering matrix back along the inverse channel equivalence recovers it. -/
@[simp]
lemma ScatteringMatrix.reindex_symm_reindex {ι κ : Type*} (e : ι ≃ κ)
    (S : ScatteringMatrix ι) : (S.reindex e).reindex e.symm = S := by
  cases S
  simp only [ScatteringMatrix.reindex, ModeTransform.reindex_symm_reindex]

/-- Relabeling from new channel labels back to old and then forward again recovers the new
scattering matrix. -/
@[simp]
lemma ScatteringMatrix.reindex_reindex_symm {ι κ : Type*} (e : ι ≃ κ)
    (S : ScatteringMatrix κ) : (S.reindex e.symm).reindex e = S := by
  cases S
  simp only [ScatteringMatrix.reindex, ModeTransform.reindex_reindex_symm]

/-- Relabeling distributes over independent parallel composition of scattering matrices. -/
lemma ScatteringMatrix.reindex_directSum {ι ι' κ κ' : Type*} (e : ι ≃ ι')
    (f : κ ≃ κ') (S : ScatteringMatrix ι) (R : ScatteringMatrix κ) :
    (S.directSum R).reindex (e.sumCongr f) = (S.reindex e).directSum (R.reindex f) := by
  cases S
  cases R
  simp only [ScatteringMatrix.directSum, ScatteringMatrix.reindex,
    ModeTransform.reindex_directSum]

/-- Channel relabeling preserves and reflects scattering losslessness. -/
lemma ScatteringMatrix.isLossless_reindex_iff {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ) (S : ScatteringMatrix ι) :
    (S.reindex e).IsLossless ↔ S.IsLossless := by
  calc
    (S.reindex e).IsLossless ↔
        ModeTransform.IsPowerPreserving (S.reindex e).toModeTransform :=
      ScatteringMatrix.isLossless_iff_isPowerPreserving _
    _ ↔ ModeTransform.IsPowerPreserving S.toModeTransform := by
      simpa only [ScatteringMatrix.toModeTransform_reindex] using
        ModeTransform.isPowerPreserving_reindex_iff e e S.toModeTransform
    _ ↔ S.IsLossless := (ScatteringMatrix.isLossless_iff_isPowerPreserving S).symm

end

end Optics
