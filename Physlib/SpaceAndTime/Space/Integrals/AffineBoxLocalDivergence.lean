/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.SpaceAndTime.Space.Integrals.OrientedBox

/-!
# Local-regularity divergence identities for affine boxes

## i. Overview

This file gives the oriented affine-box divergence identity under hypotheses local to one closed
parameter box. The pulled-back field is continuous on the box, differentiable in its interior
away from a countable exceptional set, and its pulled-back divergence density is integrable.

This is neutral calculus infrastructure. It does not construct one-sided extensions across an
interface, specialize to a pillbox, identify a carrier face with a sheet source, state a Maxwell
equation, or prove a shrinking-cell limit.

## ii. Key results

- `AffineBoxDivergenceRegularity`: local continuity, differentiability, and integrability data.
- `setIntegral_div_affineBox_of_localRegularity`: the affine-box divergence theorem in the set
  integral form used by the underlying divergence theorem.
- `integral3_div_affineBox_of_localRegularity`: the corresponding displayed iterated-integral
  identity.

## iii. Table of contents

- A. Local affine-box regularity
- B. Set-integral divergence theorem
- C. Iterated affine-box divergence theorem

## iv. References

This is neutral calculus infrastructure for the E4b split-half pillbox construction.
-/

@[expose] public section

open Matrix MeasureTheory
open scoped Interval

namespace Space

noncomputable section

/-! ## A. Local affine-box regularity -/

/-- Regularity of one ambient vector field on one parameterized affine box.

The countable exceptional set lives in parameter space and is excluded only from the interior
differentiability hypothesis. No behavior away from the closed box is constrained. -/
structure AffineBoxDivergenceRegularity
    (field : Space → EuclideanSpace ℝ (Fin 3))
    (center first second third : Space)
    (a₁ a₂ a₃ b₁ b₂ b₃ : ℝ)
    (exceptionalSet : Set (Fin 3 → ℝ)) : Prop where
  /-- The exceptional parameter set is countable. -/
  exceptionalSet_countable : exceptionalSet.Countable
  /-- The pulled-back field is continuous on the closed parameter box. -/
  continuousOn : ContinuousOn
    (fun q ↦ field (affineBoxCoordinatePoint center first second third q))
    (Set.Icc ![a₁, a₂, a₃] ![b₁, b₂, b₃])
  /-- The ambient field has its Fréchet derivative at interior points outside the exception set. -/
  hasFDerivAt : ∀ q ∈
      (Set.pi Set.univ fun i ↦ Set.Ioo (![a₁, a₂, a₃] i) (![b₁, b₂, b₃] i)) \
        exceptionalSet,
    HasFDerivAt field
      (fderiv ℝ field (affineBoxCoordinatePoint center first second third q))
      (affineBoxCoordinatePoint center first second third q)
  /-- The signed pulled-back divergence density is integrable on the closed parameter box. -/
  divergenceIntegrable : IntegrableOn
    (fun q ↦ (∇ ⬝ field) (affineBoxCoordinatePoint center first second third q) *
      inner ℝ (basis.repr first) (basis.repr second ⨯ₑ₃ basis.repr third))
    (Set.Icc ![a₁, a₂, a₃] ![b₁, b₂, b₃])

namespace AffineBoxDivergenceRegularity

/-- A globally differentiable field supplies local continuity and differentiability; divergence
integrability on the selected box remains explicit. -/
lemma of_differentiable
    (field : Space → EuclideanSpace ℝ (Fin 3))
    (center first second third : Space)
    (a₁ a₂ a₃ b₁ b₂ b₃ : ℝ)
    (hfield : Differentiable ℝ field)
    (hdiv : IntegrableOn
      (fun q ↦ (∇ ⬝ field) (affineBoxCoordinatePoint center first second third q) *
        inner ℝ (basis.repr first) (basis.repr second ⨯ₑ₃ basis.repr third))
      (Set.Icc ![a₁, a₂, a₃] ![b₁, b₂, b₃])) :
    AffineBoxDivergenceRegularity field center first second third
      a₁ a₂ a₃ b₁ b₂ b₃ ∅ where
  exceptionalSet_countable := Set.countable_empty
  continuousOn := by
    exact (hfield.continuous.comp
      (by
        change Continuous fun q : Fin 3 → ℝ ↦
          center + q 0 • first + q 1 • second + q 2 • third
        fun_prop)).continuousOn
  hasFDerivAt := fun q _ ↦ (hfield _).hasFDerivAt
  divergenceIntegrable := hdiv

end AffineBoxDivergenceRegularity

/-! ## B. Set-integral divergence theorem -/

/-- The local regularity record supplies continuity of every cofactor-weighted flux coordinate. -/
private lemma affineBoxFlux_continuousOn
    (field : Space → EuclideanSpace ℝ (Fin 3))
    (center first second third : Space)
    (a₁ a₂ a₃ b₁ b₂ b₃ : ℝ) (exceptionalSet : Set (Fin 3 → ℝ))
    (regularity : AffineBoxDivergenceRegularity field center first second third
      a₁ a₂ a₃ b₁ b₂ b₃ exceptionalSet) (i : Fin 3) :
    ContinuousOn
      (fun q ↦ inner ℝ
        (field (affineBoxCoordinatePoint center first second third q))
        (![basis.repr second ⨯ₑ₃ basis.repr third,
          basis.repr third ⨯ₑ₃ basis.repr first,
          basis.repr first ⨯ₑ₃ basis.repr second] i))
      (Set.Icc ![a₁, a₂, a₃] ![b₁, b₂, b₃]) :=
  regularity.continuousOn.inner continuousOn_const

/-- Restricting a continuous affine-box flux coordinate to any retained face gives an integrable
face density. -/
private lemma affineBoxFaceFlux_integrable
    (field : Space → EuclideanSpace ℝ (Fin 3))
    (center first second third : Space)
    (a₁ a₂ a₃ b₁ b₂ b₃ : ℝ) (exceptionalSet : Set (Fin 3 → ℝ))
    (regularity : AffineBoxDivergenceRegularity field center first second third
      a₁ a₂ a₃ b₁ b₂ b₃ exceptionalSet)
    (i : Fin 3) (c : ℝ)
    (hc : ![a₁, a₂, a₃] i ≤ c ∧ c ≤ ![b₁, b₂, b₃] i) :
    IntegrableOn
      (fun x ↦ inner ℝ
        (field (affineBoxCoordinatePoint center first second third (i.insertNth c x)))
        (![basis.repr second ⨯ₑ₃ basis.repr third,
          basis.repr third ⨯ₑ₃ basis.repr first,
          basis.repr first ⨯ₑ₃ basis.repr second] i))
      (Set.Icc
        (![a₁, a₂, a₃] ∘ i.succAbove)
        (![b₁, b₂, b₃] ∘ i.succAbove)) := by
  have hInsert : Continuous fun x : Fin 2 → ℝ ↦
      @Fin.insertNth 2 (fun _ : Fin 3 ↦ ℝ) i c x := by
    exact (continuous_const : Continuous (fun _ : Fin 2 → ℝ ↦ c)).finInsertNth i
      (continuous_id : Continuous (fun x : Fin 2 → ℝ ↦ x))
  have hContinuous : ContinuousOn
      (fun x ↦ inner ℝ
        (field (affineBoxCoordinatePoint center first second third (i.insertNth c x)))
        (![basis.repr second ⨯ₑ₃ basis.repr third,
          basis.repr third ⨯ₑ₃ basis.repr first,
          basis.repr first ⨯ₑ₃ basis.repr second] i))
      (Set.Icc
        (![a₁, a₂, a₃] ∘ i.succAbove)
        (![b₁, b₂, b₃] ∘ i.succAbove)) := by
    refine (affineBoxFlux_continuousOn field center first second third
      a₁ a₂ a₃ b₁ b₂ b₃ exceptionalSet regularity i).comp
        hInsert.continuousOn ?_
    intro x hx
    simp only [Set.mem_Icc] at hx ⊢
    constructor
    · rw [Fin.le_insertNth_iff]
      exact ⟨hc.1, hx.1⟩
    · rw [Fin.insertNth_le_iff]
      exact ⟨hc.2, hx.2⟩
  exact hContinuous.integrableOn_compact isCompact_Icc

/-- Off the exceptional set, the sum of the three parameter derivatives is the signed pulled-back
ambient divergence. -/
private lemma affineBox_derivativeDensity_eq_divergenceDensity
    (field : Space → EuclideanSpace ℝ (Fin 3))
    (center first second third : Space)
    (a₁ a₂ a₃ b₁ b₂ b₃ : ℝ) (exceptionalSet : Set (Fin 3 → ℝ))
    (regularity : AffineBoxDivergenceRegularity field center first second third
      a₁ a₂ a₃ b₁ b₂ b₃ exceptionalSet)
    (q : Fin 3 → ℝ)
    (hq : q ∈
      (Set.pi Set.univ fun i ↦ Set.Ioo (![a₁, a₂, a₃] i) (![b₁, b₂, b₃] i)) \
        exceptionalSet) :
    (∑ i : Fin 3, fderiv ℝ
        (fun p ↦ inner ℝ
          (field (affineBoxCoordinatePoint center first second third p))
          (![basis.repr second ⨯ₑ₃ basis.repr third,
            basis.repr third ⨯ₑ₃ basis.repr first,
            basis.repr first ⨯ₑ₃ basis.repr second] i))
        q (Pi.single i 1)) =
      (∇ ⬝ field) (affineBoxCoordinatePoint center first second third q) *
        inner ℝ (basis.repr first)
          (basis.repr second ⨯ₑ₃ basis.repr third) := by
  have hfPoint : DifferentiableAt ℝ field
      (affineBoxCoordinatePoint center first second third q) :=
    (regularity.hasFDerivAt q hq).differentiableAt
  rw [Fin.sum_univ_three]
  change
    fderiv ℝ (fun p ↦ inner ℝ
        (field (affineBoxCoordinatePoint center first second third p))
        (basis.repr second ⨯ₑ₃ basis.repr third)) q (Pi.single 0 1) +
      fderiv ℝ (fun p ↦ inner ℝ
        (field (affineBoxCoordinatePoint center first second third p))
        (basis.repr third ⨯ₑ₃ basis.repr first)) q (Pi.single 1 1) +
      fderiv ℝ (fun p ↦ inner ℝ
        (field (affineBoxCoordinatePoint center first second third p))
        (basis.repr first ⨯ₑ₃ basis.repr second)) q (Pi.single 2 1) = _
  rw [fderiv_inner_affineBoxCoordinatePoint field center first second third
      (basis.repr second ⨯ₑ₃ basis.repr third) q 0 hfPoint,
    fderiv_inner_affineBoxCoordinatePoint field center first second third
      (basis.repr third ⨯ₑ₃ basis.repr first) q 1 hfPoint,
    fderiv_inner_affineBoxCoordinatePoint field center first second third
      (basis.repr first ⨯ₑ₃ basis.repr second) q 2 hfPoint]
  exact (div_mul_inner_cross_eq_sum_inner_fderiv field
    (affineBoxCoordinatePoint center first second third q)
    first second third hfPoint).symm

/-- The parameter-derivative density agrees almost everywhere on the box with the signed ambient
divergence density. -/
private lemma affineBox_derivativeDensity_ae_eq_divergenceDensity
    (field : Space → EuclideanSpace ℝ (Fin 3))
    (center first second third : Space)
    (a₁ a₂ a₃ b₁ b₂ b₃ : ℝ) (exceptionalSet : Set (Fin 3 → ℝ))
    (regularity : AffineBoxDivergenceRegularity field center first second third
      a₁ a₂ a₃ b₁ b₂ b₃ exceptionalSet) :
    (fun q ↦ ∑ i : Fin 3, fderiv ℝ
      (fun p ↦ inner ℝ
        (field (affineBoxCoordinatePoint center first second third p))
        (![basis.repr second ⨯ₑ₃ basis.repr third,
          basis.repr third ⨯ₑ₃ basis.repr first,
          basis.repr first ⨯ₑ₃ basis.repr second] i))
      q (Pi.single i 1)) =ᵐ[
        volume.restrict (Set.Icc ![a₁, a₂, a₃] ![b₁, b₂, b₃])]
      (fun q ↦ (∇ ⬝ field) (affineBoxCoordinatePoint center first second third q) *
        inner ℝ (basis.repr first)
          (basis.repr second ⨯ₑ₃ basis.repr third)) := by
  change ∀ᵐ q ∂volume.restrict (Set.Icc ![a₁, a₂, a₃] ![b₁, b₂, b₃]),
    (∑ i : Fin 3, fderiv ℝ
      (fun p ↦ inner ℝ
        (field (affineBoxCoordinatePoint center first second third p))
        (![basis.repr second ⨯ₑ₃ basis.repr third,
          basis.repr third ⨯ₑ₃ basis.repr first,
          basis.repr first ⨯ₑ₃ basis.repr second] i))
      q (Pi.single i 1)) =
        (∇ ⬝ field) (affineBoxCoordinatePoint center first second third q) *
          inner ℝ (basis.repr first)
            (basis.repr second ⨯ₑ₃ basis.repr third)
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
  filter_upwards [Measure.univ_pi_Ioo_ae_eq_Icc,
    compl_mem_ae_iff.mpr
      (regularity.exceptionalSet_countable.measure_zero volume)] with q hqInterior hqExceptional
  intro hq
  exact affineBox_derivativeDensity_eq_divergenceDensity field center first second third
    a₁ a₂ a₃ b₁ b₂ b₃ exceptionalSet regularity q
    ⟨fun i _ ↦ hqInterior.mpr hq i (Set.mem_univ i), hqExceptional⟩

/-- Under local affine-box regularity, the pulled-back divergence set integral equals the sum of
the six signed cofactor-weighted face set integrals. -/
lemma setIntegral_div_affineBox_of_localRegularity
    (field : Space → EuclideanSpace ℝ (Fin 3))
    (center first second third : Space)
    (a₁ a₂ a₃ b₁ b₂ b₃ : ℝ)
    (ha₁ : a₁ ≤ b₁) (ha₂ : a₂ ≤ b₂) (ha₃ : a₃ ≤ b₃)
    (exceptionalSet : Set (Fin 3 → ℝ))
    (regularity : AffineBoxDivergenceRegularity field center first second third
      a₁ a₂ a₃ b₁ b₂ b₃ exceptionalSet) :
    (∫ q in Set.Icc ![a₁, a₂, a₃] ![b₁, b₂, b₃],
        (∇ ⬝ field) (affineBoxCoordinatePoint center first second third q) *
          inner ℝ (basis.repr first)
            (basis.repr second ⨯ₑ₃ basis.repr third)) =
      ∑ i : Fin 3,
        ((∫ x in Set.Icc
            (![a₁, a₂, a₃] ∘ i.succAbove)
            (![b₁, b₂, b₃] ∘ i.succAbove),
            inner ℝ
              (field (affineBoxCoordinatePoint center first second third
                (i.insertNth (![b₁, b₂, b₃] i) x)))
              (![basis.repr second ⨯ₑ₃ basis.repr third,
                basis.repr third ⨯ₑ₃ basis.repr first,
                basis.repr first ⨯ₑ₃ basis.repr second] i)) -
          ∫ x in Set.Icc
            (![a₁, a₂, a₃] ∘ i.succAbove)
            (![b₁, b₂, b₃] ∘ i.succAbove),
            inner ℝ
              (field (affineBoxCoordinatePoint center first second third
                (i.insertNth (![a₁, a₂, a₃] i) x)))
              (![basis.repr second ⨯ₑ₃ basis.repr third,
                basis.repr third ⨯ₑ₃ basis.repr first,
                basis.repr first ⨯ₑ₃ basis.repr second] i)) := by
  let lower : Fin 3 → ℝ := ![a₁, a₂, a₃]
  let upper : Fin 3 → ℝ := ![b₁, b₂, b₃]
  let point := affineBoxCoordinatePoint center first second third
  let cofactor : Fin 3 → EuclideanSpace ℝ (Fin 3) :=
    ![basis.repr second ⨯ₑ₃ basis.repr third,
      basis.repr third ⨯ₑ₃ basis.repr first,
      basis.repr first ⨯ₑ₃ basis.repr second]
  let flux : Fin 3 → (Fin 3 → ℝ) → ℝ := fun i q ↦
    inner ℝ (field (point q)) (cofactor i)
  let derivativeDensity := fun q ↦ ∑ i, fderiv ℝ (flux i) q (Pi.single i 1)
  let divergenceDensity := fun q ↦
    (∇ ⬝ field) (point q) * inner ℝ (basis.repr first)
      (basis.repr second ⨯ₑ₃ basis.repr third)
  have hBounds : lower ≤ upper := by
    intro i
    fin_cases i <;> simpa [lower, upper]
  have hPointDifferentiable (q : Fin 3 → ℝ) : DifferentiableAt ℝ point q := by
    change DifferentiableAt ℝ (fun p : Fin 3 → ℝ ↦
      center + p 0 • first + p 1 • second + p 2 • third) q
    fun_prop
  have hFluxDifferentiable (q) (hq : q ∈
      (Set.pi Set.univ fun i ↦ Set.Ioo (lower i) (upper i)) \
        exceptionalSet) (i : Fin 3) : DifferentiableAt ℝ (flux i) q := by
    exact ((regularity.hasFDerivAt q (by simpa [lower, upper] using hq)).differentiableAt.comp q
      (hPointDifferentiable q)).inner ℝ (differentiableAt_const _)
  have hFluxContinuous (i : Fin 3) :
      ContinuousOn (flux i) (Set.Icc lower upper) := by
    simpa [flux, point, cofactor, lower, upper] using
      affineBoxFlux_continuousOn field center first second third
        a₁ a₂ a₃ b₁ b₂ b₃ exceptionalSet regularity i
  have hDensityAE : derivativeDensity =ᵐ[volume.restrict (Set.Icc lower upper)]
      divergenceDensity := by
    simpa [derivativeDensity, divergenceDensity, flux, cofactor, point, lower, upper] using
      affineBox_derivativeDensity_ae_eq_divergenceDensity field center first second third
        a₁ a₂ a₃ b₁ b₂ b₃ exceptionalSet regularity
  have hDerivativeIntegrable : IntegrableOn derivativeDensity (Set.Icc lower upper) :=
    (show IntegrableOn divergenceDensity (Set.Icc lower upper) by
      simpa [divergenceDensity, point, lower, upper] using
        regularity.divergenceIntegrable).congr_fun_ae hDensityAE.symm
  have hGauss := MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable'
    (n := 2) lower upper hBounds flux (fun i q ↦ fderiv ℝ (flux i) q)
    exceptionalSet regularity.exceptionalSet_countable hFluxContinuous
    (fun q hq i ↦ (hFluxDifferentiable q hq i).hasFDerivAt)
    hDerivativeIntegrable
  calc
    _ = ∫ q in Set.Icc lower upper, divergenceDensity q := by rfl
    _ = ∫ q in Set.Icc lower upper, derivativeDensity q :=
      integral_congr_ae hDensityAE.symm
    _ = _ := by rw [hGauss]

/-! ## C. Iterated affine-box divergence theorem -/

/-- The first-coordinate face flux converts to its ordered `(second, third)` iterated integral. -/
private lemma affineBoxFaceZeroFlux_setIntegral_eq_iterated
    (field : Space → EuclideanSpace ℝ (Fin 3))
    (center first second third : Space)
    (a₁ a₂ a₃ b₁ b₂ b₃ : ℝ)
    (ha₂ : a₂ ≤ b₂) (ha₃ : a₃ ≤ b₃)
    (exceptionalSet : Set (Fin 3 → ℝ))
    (regularity : AffineBoxDivergenceRegularity field center first second third
      a₁ a₂ a₃ b₁ b₂ b₃ exceptionalSet)
    (c : ℝ) (hc : a₁ ≤ c ∧ c ≤ b₁) :
    (∫ x in Set.Icc (![a₁, a₂, a₃] ∘ (0 : Fin 3).succAbove)
        (![b₁, b₂, b₃] ∘ (0 : Fin 3).succAbove),
        inner ℝ
          (field (affineBoxCoordinatePoint center first second third
            ((0 : Fin 3).insertNth c x)))
          (basis.repr second ⨯ₑ₃ basis.repr third)) =
      ∫ v in a₂..b₂, ∫ w in a₃..b₃,
        inner ℝ (field (affineBoxPoint center first second third c v w))
          (basis.repr second ⨯ₑ₃ basis.repr third) := by
  have hIntegrable := affineBoxFaceFlux_integrable field center first second third
    a₁ a₂ a₃ b₁ b₂ b₃ exceptionalSet regularity (0 : Fin 3) c hc
  simpa only [affineBoxCoordinatePoint, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Function.comp_apply] using
    (finThree_faceZero_setIntegral_Icc_eq_iterated_of_integrable
      (fun q ↦ inner ℝ
        (field (affineBoxCoordinatePoint center first second third q))
        (basis.repr second ⨯ₑ₃ basis.repr third))
      c a₁ a₂ a₃ b₁ b₂ b₃ ha₂ ha₃ hIntegrable)

/-- The second-coordinate face flux converts to its ordered `(first, third)` iterated integral. -/
private lemma affineBoxFaceOneFlux_setIntegral_eq_iterated
    (field : Space → EuclideanSpace ℝ (Fin 3))
    (center first second third : Space)
    (a₁ a₂ a₃ b₁ b₂ b₃ : ℝ)
    (ha₁ : a₁ ≤ b₁) (ha₃ : a₃ ≤ b₃)
    (exceptionalSet : Set (Fin 3 → ℝ))
    (regularity : AffineBoxDivergenceRegularity field center first second third
      a₁ a₂ a₃ b₁ b₂ b₃ exceptionalSet)
    (c : ℝ) (hc : a₂ ≤ c ∧ c ≤ b₂) :
    (∫ x in Set.Icc (![a₁, a₂, a₃] ∘ (1 : Fin 3).succAbove)
        (![b₁, b₂, b₃] ∘ (1 : Fin 3).succAbove),
        inner ℝ
          (field (affineBoxCoordinatePoint center first second third
            ((1 : Fin 3).insertNth c x)))
          (basis.repr third ⨯ₑ₃ basis.repr first)) =
      ∫ u in a₁..b₁, ∫ w in a₃..b₃,
        inner ℝ (field (affineBoxPoint center first second third u c w))
          (basis.repr third ⨯ₑ₃ basis.repr first) := by
  have hIntegrable := affineBoxFaceFlux_integrable field center first second third
    a₁ a₂ a₃ b₁ b₂ b₃ exceptionalSet regularity (1 : Fin 3) c hc
  simpa only [affineBoxCoordinatePoint, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Function.comp_apply] using
    (finThree_faceOne_setIntegral_Icc_eq_iterated_of_integrable
      (fun q ↦ inner ℝ
        (field (affineBoxCoordinatePoint center first second third q))
        (basis.repr third ⨯ₑ₃ basis.repr first))
      c a₁ a₂ a₃ b₁ b₂ b₃ ha₁ ha₃ hIntegrable)

/-- The third-coordinate face flux converts to its ordered `(first, second)` iterated integral. -/
private lemma affineBoxFaceTwoFlux_setIntegral_eq_iterated
    (field : Space → EuclideanSpace ℝ (Fin 3))
    (center first second third : Space)
    (a₁ a₂ a₃ b₁ b₂ b₃ : ℝ)
    (ha₁ : a₁ ≤ b₁) (ha₂ : a₂ ≤ b₂)
    (exceptionalSet : Set (Fin 3 → ℝ))
    (regularity : AffineBoxDivergenceRegularity field center first second third
      a₁ a₂ a₃ b₁ b₂ b₃ exceptionalSet)
    (c : ℝ) (hc : a₃ ≤ c ∧ c ≤ b₃) :
    (∫ x in Set.Icc (![a₁, a₂, a₃] ∘ (2 : Fin 3).succAbove)
        (![b₁, b₂, b₃] ∘ (2 : Fin 3).succAbove),
        inner ℝ
          (field (affineBoxCoordinatePoint center first second third
            ((2 : Fin 3).insertNth c x)))
          (basis.repr first ⨯ₑ₃ basis.repr second)) =
      ∫ u in a₁..b₁, ∫ v in a₂..b₂,
        inner ℝ (field (affineBoxPoint center first second third u v c))
          (basis.repr first ⨯ₑ₃ basis.repr second) := by
  have hIntegrable := affineBoxFaceFlux_integrable field center first second third
    a₁ a₂ a₃ b₁ b₂ b₃ exceptionalSet regularity (2 : Fin 3) c hc
  simpa only [affineBoxCoordinatePoint, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Function.comp_apply] using
    (finThree_faceTwo_setIntegral_Icc_eq_iterated_of_integrable
      (fun q ↦ inner ℝ
        (field (affineBoxCoordinatePoint center first second third q))
        (basis.repr first ⨯ₑ₃ basis.repr second))
      c a₁ a₂ a₃ b₁ b₂ b₃ ha₁ ha₂ hIntegrable)

/-- The integral of divergence over an ordered affine box equals the six oriented face fluxes
under regularity confined to that box.

The face orders and cofactors agree with `integral3_div_affineBox`; this theorem weakens its global
`ContDiff` premise to local continuity, interior differentiability off a countable set, and
integrability of the displayed divergence density. -/
lemma integral3_div_affineBox_of_localRegularity
    (field : Space → EuclideanSpace ℝ (Fin 3))
    (center first second third : Space)
    (a₁ a₂ a₃ b₁ b₂ b₃ : ℝ)
    (ha₁ : a₁ ≤ b₁) (ha₂ : a₂ ≤ b₂) (ha₃ : a₃ ≤ b₃)
    (exceptionalSet : Set (Fin 3 → ℝ))
    (regularity : AffineBoxDivergenceRegularity field center first second third
      a₁ a₂ a₃ b₁ b₂ b₃ exceptionalSet) :
    (∫ u in a₁..b₁, ∫ v in a₂..b₂, ∫ w in a₃..b₃,
        (∇ ⬝ field) (affineBoxPoint center first second third u v w) *
          inner ℝ (basis.repr first)
            (basis.repr second ⨯ₑ₃ basis.repr third)) =
      ((∫ v in a₂..b₂, ∫ w in a₃..b₃,
            inner ℝ (field (affineBoxPoint center first second third b₁ v w))
              (basis.repr second ⨯ₑ₃ basis.repr third)) -
        ∫ v in a₂..b₂, ∫ w in a₃..b₃,
            inner ℝ (field (affineBoxPoint center first second third a₁ v w))
              (basis.repr second ⨯ₑ₃ basis.repr third)) +
      ((∫ u in a₁..b₁, ∫ w in a₃..b₃,
            inner ℝ (field (affineBoxPoint center first second third u b₂ w))
              (basis.repr third ⨯ₑ₃ basis.repr first)) -
        ∫ u in a₁..b₁, ∫ w in a₃..b₃,
            inner ℝ (field (affineBoxPoint center first second third u a₂ w))
              (basis.repr third ⨯ₑ₃ basis.repr first)) +
      ((∫ u in a₁..b₁, ∫ v in a₂..b₂,
            inner ℝ (field (affineBoxPoint center first second third u v b₃))
              (basis.repr first ⨯ₑ₃ basis.repr second)) -
        ∫ u in a₁..b₁, ∫ v in a₂..b₂,
            inner ℝ (field (affineBoxPoint center first second third u v a₃))
              (basis.repr first ⨯ₑ₃ basis.repr second)) := by
  have hVolume := finThree_setIntegral_Icc_eq_iterated_of_integrable
    (fun q ↦ (∇ ⬝ field) (affineBoxCoordinatePoint center first second third q) *
      inner ℝ (basis.repr first) (basis.repr second ⨯ₑ₃ basis.repr third))
    a₁ a₂ a₃ b₁ b₂ b₃ ha₁ ha₂ ha₃ regularity.divergenceIntegrable
  have hCoordinatePoint (u v w : ℝ) :
      affineBoxCoordinatePoint center first second third ![u, v, w] =
        affineBoxPoint center first second third u v w := rfl
  simp only [hCoordinatePoint] at hVolume
  have hSet := setIntegral_div_affineBox_of_localRegularity
    field center first second third a₁ a₂ a₃ b₁ b₂ b₃
    ha₁ ha₂ ha₃ exceptionalSet regularity
  have hFace0Upper := affineBoxFaceZeroFlux_setIntegral_eq_iterated
    field center first second third a₁ a₂ a₃ b₁ b₂ b₃ ha₂ ha₃
    exceptionalSet regularity b₁ ⟨ha₁, le_rfl⟩
  have hFace0Lower := affineBoxFaceZeroFlux_setIntegral_eq_iterated
    field center first second third a₁ a₂ a₃ b₁ b₂ b₃ ha₂ ha₃
    exceptionalSet regularity a₁ ⟨le_rfl, ha₁⟩
  have hFace1Upper := affineBoxFaceOneFlux_setIntegral_eq_iterated
    field center first second third a₁ a₂ a₃ b₁ b₂ b₃ ha₁ ha₃
    exceptionalSet regularity b₂ ⟨ha₂, le_rfl⟩
  have hFace1Lower := affineBoxFaceOneFlux_setIntegral_eq_iterated
    field center first second third a₁ a₂ a₃ b₁ b₂ b₃ ha₁ ha₃
    exceptionalSet regularity a₂ ⟨le_rfl, ha₂⟩
  have hFace2Upper := affineBoxFaceTwoFlux_setIntegral_eq_iterated
    field center first second third a₁ a₂ a₃ b₁ b₂ b₃ ha₁ ha₂
    exceptionalSet regularity b₃ ⟨ha₃, le_rfl⟩
  have hFace2Lower := affineBoxFaceTwoFlux_setIntegral_eq_iterated
    field center first second third a₁ a₂ a₃ b₁ b₂ b₃ ha₁ ha₂
    exceptionalSet regularity a₃ ⟨le_rfl, ha₃⟩
  rw [← hVolume, hSet, Fin.sum_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rw [hFace0Upper, hFace0Lower, hFace1Upper, hFace1Lower,
    hFace2Upper, hFace2Lower]

end
end Space
