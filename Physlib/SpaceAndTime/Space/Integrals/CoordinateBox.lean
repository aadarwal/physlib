/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Mathlib.MeasureTheory.Integral.DivergenceTheorem

/-!
# Coordinate box integrals in dimensions two and three

## i. Overview

This file converts set integrals over ordered coordinate boxes in `Fin 2` and `Fin 3` into
iterated interval integrals. It also specializes the two-dimensional conversion to each face of a
three-dimensional box, preserving the order of the two retained coordinates.

These lemmas isolate the finite-product measure bookkeeping needed by affine divergence formulas.
All interval endpoints are explicitly ordered; no orientation sign is hidden in a set integral.

## ii. Key results

- `finTwo_setIntegral_Icc_eq_iterated`: a two-dimensional box set integral as two interval
  integrals.
- `finThree_setIntegral_Icc_eq_iterated`: a three-dimensional box set integral as three interval
  integrals.
- `finTwo_setIntegral_Icc_eq_iterated_of_integrable` and
  `finThree_setIntegral_Icc_eq_iterated_of_integrable`: the corresponding conversions under
  `IntegrableOn` hypotheses.
- `finThree_faceZero_setIntegral_Icc_eq_iterated`,
  `finThree_faceOne_setIntegral_Icc_eq_iterated`, and
  `finThree_faceTwo_setIntegral_Icc_eq_iterated`: the three ordered face conversions.

## iii. Table of contents

- A. Coordinate box integrals
- B. Coordinate face integrals

## iv. References

This is neutral measure-theory infrastructure.
-/

@[expose] public section

open Matrix MeasureTheory
open scoped Interval

namespace Space

noncomputable section

/-! ## A. Coordinate box integrals -/

/-- An integrable scalar function on an ordered `Fin 2` box has the corresponding ordered
iterated interval integral. -/
lemma finTwo_setIntegral_Icc_eq_iterated_of_integrable
    (f : (Fin 2 → ℝ) → ℝ)
    (a₀ a₁ b₀ b₁ : ℝ) (h₀ : a₀ ≤ b₀) (h₁ : a₁ ≤ b₁)
    (hf : IntegrableOn f (Set.Icc ![a₀, a₁] ![b₀, b₁])) :
    (∫ x in Set.Icc ![a₀, a₁] ![b₀, b₁], f x) =
      ∫ u in a₀..b₀, ∫ v in a₁..b₁, f ![u, v] := by
  let e : (ℝ × ℝ) ≃ᵐ (Fin 2 → ℝ) := MeasurableEquiv.finTwoArrow.symm
  let eL : (ℝ × ℝ) ≃L[ℝ] (Fin 2 → ℝ) :=
    (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm
  have hem : MeasurePreserving e (volume.prod volume) volume :=
    (measurePreserving_finTwoArrow volume).symm
  have he_apply (p : ℝ × ℝ) : e p = eL p := rfl
  have he_vec (p : ℝ × ℝ) : eL p = ![p.1, p.2] := rfl
  have heIcc : e ⁻¹' Set.Icc ![a₀, a₁] ![b₀, b₁] =
      Set.Icc a₀ b₀ ×ˢ Set.Icc a₁ b₁ :=
    ((OrderIso.finTwoArrowIso ℝ).symm.preimage_Icc _ _).trans
      (Set.Icc_prod_eq _ _)
  have hPullback : IntegrableOn (f ∘ e)
      (Set.Icc a₀ b₀ ×ˢ Set.Icc a₁ b₁) (volume.prod volume) := by
    rw [← heIcc]
    exact (hem.integrableOn_comp_preimage e.measurableEmbedding).2 hf
  have hPullbackLambda : IntegrableOn (fun p ↦ f (e p))
      (Set.Icc a₀ b₀ ×ˢ Set.Icc a₁ b₁) (volume.prod volume) := by
    simpa only [Function.comp_def] using hPullback
  rw [← hem.map_eq, MeasureTheory.setIntegral_map_equiv, heIcc]
  rw [MeasureTheory.setIntegral_prod _ hPullbackLambda]
  simp only [intervalIntegral.integral_of_le, h₀, h₁,
    MeasureTheory.setIntegral_congr_set
      (Ioc_ae_eq_Icc (α := ℝ) (μ := volume))]
  simp only [he_apply, he_vec]

/-- An integrable scalar function on an ordered `Fin 3` box has the corresponding ordered
triple interval integral. -/
lemma finThree_setIntegral_Icc_eq_iterated_of_integrable
    (f : (Fin 3 → ℝ) → ℝ)
    (a₀ a₁ a₂ b₀ b₁ b₂ : ℝ)
    (h₀ : a₀ ≤ b₀) (h₁ : a₁ ≤ b₁) (h₂ : a₂ ≤ b₂)
    (hf : IntegrableOn f (Set.Icc ![a₀, a₁, a₂] ![b₀, b₁, b₂])) :
    (∫ x in Set.Icc ![a₀, a₁, a₂] ![b₀, b₁, b₂], f x) =
      ∫ u in a₀..b₀, ∫ v in a₁..b₁, ∫ w in a₂..b₂, f ![u, v, w] := by
  let e : (ℝ × (Fin 2 → ℝ)) ≃ᵐ (Fin 3 → ℝ) :=
    (MeasurableEquiv.piFinSuccAbove (fun _ ↦ ℝ) 0).symm
  have hem : MeasurePreserving e
      (volume.prod (Measure.pi fun _ : Fin 2 ↦ volume))
      (Measure.pi fun _ : Fin 3 ↦ volume) :=
    (measurePreserving_piFinSuccAbove (fun _ : Fin 3 ↦ volume) 0).symm
  have he_order (p : ℝ × (Fin 2 → ℝ)) :
      e p = (Fin.insertNthOrderIso (fun _ ↦ ℝ) (0 : Fin 3)) p := rfl
  have he_cons (p : ℝ × (Fin 2 → ℝ)) : e p = Fin.cons p.1 p.2 := by
    ext i
    fin_cases i <;>
      simp [e, MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv]
  have heIcc : e ⁻¹' Set.Icc ![a₀, a₁, a₂] ![b₀, b₁, b₂] =
      Set.Icc a₀ b₀ ×ˢ Set.Icc ![a₁, a₂] ![b₁, b₂] := by
    have hePreimage : e ⁻¹' Set.Icc ![a₀, a₁, a₂] ![b₀, b₁, b₂] =
        (⇑(Fin.insertNthOrderIso (fun _ ↦ ℝ) (0 : Fin 3))) ⁻¹'
          Set.Icc ![a₀, a₁, a₂] ![b₀, b₁, b₂] := by
      ext p
      simp only [Set.mem_preimage, he_order]
    rw [hePreimage]
    rw [(Fin.insertNthOrderIso (fun _ ↦ ℝ) (0 : Fin 3)).preimage_Icc]
    have ha : (Fin.insertNthOrderIso (fun _ ↦ ℝ) (0 : Fin 3)).symm
        ![a₀, a₁, a₂] = (a₀, ![a₁, a₂]) := by
      rfl
    have hb : (Fin.insertNthOrderIso (fun _ ↦ ℝ) (0 : Fin 3)).symm
        ![b₀, b₁, b₂] = (b₀, ![b₁, b₂]) := by
      rfl
    rw [ha, hb, Set.Icc_prod_eq]
  have hPullback : IntegrableOn (f ∘ e)
      (Set.Icc a₀ b₀ ×ˢ Set.Icc ![a₁, a₂] ![b₁, b₂])
      (volume.prod (Measure.pi fun _ : Fin 2 ↦ volume)) := by
    rw [← heIcc]
    exact (hem.integrableOn_comp_preimage e.measurableEmbedding).2 (by
      simpa only [volume_pi] using hf)
  have hPullbackProd : Integrable (f ∘ e)
      ((volume.restrict (Set.Icc a₀ b₀)).prod
        ((Measure.pi fun _ : Fin 2 ↦ volume).restrict
          (Set.Icc ![a₁, a₂] ![b₁, b₂]))) := by
    simpa only [IntegrableOn, Measure.prod_restrict] using hPullback
  have hPullbackLambda : IntegrableOn (fun p ↦ f (e p))
      (Set.Icc a₀ b₀ ×ˢ Set.Icc ![a₁, a₂] ![b₁, b₂])
      (volume.prod (Measure.pi fun _ : Fin 2 ↦ volume)) := by
    simpa only [Function.comp_def] using hPullback
  have hSlice : ∀ᵐ u ∂volume.restrict (Set.Icc a₀ b₀),
      IntegrableOn (fun y ↦ f (e (u, y)))
        (Set.Icc ![a₁, a₂] ![b₁, b₂]) := by
    simpa only [IntegrableOn, Function.comp_apply, volume_pi] using
      hPullbackProd.prod_right_ae
  have hInner :
      (fun u ↦ ∫ y in Set.Icc ![a₁, a₂] ![b₁, b₂], f (e (u, y))
        ∂Measure.pi (fun _ : Fin 2 ↦ volume)) =ᵐ[
        volume.restrict (Set.Icc a₀ b₀)]
      (fun u ↦ ∫ v in a₁..b₁, ∫ w in a₂..b₂, f ![u, v, w]) := by
    filter_upwards [hSlice] with u hu
    have hCons (v w : ℝ) : Fin.cons u ![v, w] = ![u, v, w] := rfl
    simpa only [he_cons, hCons, volume_pi] using
      (finTwo_setIntegral_Icc_eq_iterated_of_integrable
        (fun y ↦ f (Fin.cons u y)) a₁ a₂ b₁ b₂ h₁ h₂ (by
          simpa only [he_cons] using hu))
  rw [show (volume : Measure (Fin 3 → ℝ)) =
      Measure.pi (fun _ : Fin 3 ↦ volume) from volume_pi]
  rw [← hem.map_eq, MeasureTheory.setIntegral_map_equiv, heIcc]
  rw [MeasureTheory.setIntegral_prod _ hPullbackLambda]
  rw [integral_congr_ae hInner]
  simp only [intervalIntegral.integral_of_le, h₀,
    MeasureTheory.setIntegral_congr_set
      (Ioc_ae_eq_Icc (α := ℝ) (μ := volume))]

/-- A continuous scalar function integrated over an ordered `Fin 2` box is the corresponding
ordered iterated interval integral. -/
lemma finTwo_setIntegral_Icc_eq_iterated
    (f : (Fin 2 → ℝ) → ℝ) (hf : Continuous f)
    (a₀ a₁ b₀ b₁ : ℝ) (h₀ : a₀ ≤ b₀) (h₁ : a₁ ≤ b₁) :
    (∫ x in Set.Icc ![a₀, a₁] ![b₀, b₁], f x) =
      ∫ u in a₀..b₀, ∫ v in a₁..b₁, f ![u, v] := by
  let e : (ℝ × ℝ) ≃ᵐ (Fin 2 → ℝ) := MeasurableEquiv.finTwoArrow.symm
  let eL : (ℝ × ℝ) ≃L[ℝ] (Fin 2 → ℝ) :=
    (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm
  have hem : MeasurePreserving e :=
    (volume_preserving_finTwoArrow ℝ).symm _
  have he_apply (p : ℝ × ℝ) : e p = eL p := rfl
  have heIcc : e ⁻¹' Set.Icc ![a₀, a₁] ![b₀, b₁] =
      Set.Icc a₀ b₀ ×ˢ Set.Icc a₁ b₁ :=
    ((OrderIso.finTwoArrowIso ℝ).symm.preimage_Icc _ _).trans
      (Set.Icc_prod_eq _ _)
  rw [← hem.map_eq, MeasureTheory.setIntegral_map_equiv, heIcc,
    Measure.volume_eq_prod]
  rw [MeasureTheory.setIntegral_prod]
  · simp only [intervalIntegral.integral_of_le, h₀, h₁,
      MeasureTheory.setIntegral_congr_set
        (Ioc_ae_eq_Icc (α := ℝ) (μ := volume))]
    rfl
  · simpa only [he_apply] using
      ((show Continuous (fun p : ℝ × ℝ ↦ f (eL p)) from
          hf.comp eL.continuous).continuousOn.integrableOn_compact
          (isCompact_Icc.prod isCompact_Icc))

/-- A continuous scalar function integrated over an ordered `Fin 3` box is the corresponding
ordered iterated interval integral. -/
lemma finThree_setIntegral_Icc_eq_iterated
    (f : (Fin 3 → ℝ) → ℝ) (hf : Continuous f)
    (a₀ a₁ a₂ b₀ b₁ b₂ : ℝ)
    (h₀ : a₀ ≤ b₀) (h₁ : a₁ ≤ b₁) (h₂ : a₂ ≤ b₂) :
    (∫ x in Set.Icc ![a₀, a₁, a₂] ![b₀, b₁, b₂], f x) =
      ∫ u in a₀..b₀, ∫ v in a₁..b₁, ∫ w in a₂..b₂, f ![u, v, w] := by
  let e : (ℝ × (Fin 2 → ℝ)) ≃ᵐ (Fin 3 → ℝ) :=
    (MeasurableEquiv.piFinSuccAbove (fun _ ↦ ℝ) 0).symm
  have hem : MeasurePreserving e :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin 3 ↦ ℝ) 0).symm _
  have he_order (p : ℝ × (Fin 2 → ℝ)) :
      e p = (Fin.insertNthOrderIso (fun _ ↦ ℝ) (0 : Fin 3)) p := rfl
  have he_cons (p : ℝ × (Fin 2 → ℝ)) : e p = Fin.cons p.1 p.2 := by
    ext i
    fin_cases i <;>
      simp [e, MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv]
  have heIcc : e ⁻¹' Set.Icc ![a₀, a₁, a₂] ![b₀, b₁, b₂] =
      Set.Icc a₀ b₀ ×ˢ Set.Icc ![a₁, a₂] ![b₁, b₂] := by
    have hePreimage : e ⁻¹' Set.Icc ![a₀, a₁, a₂] ![b₀, b₁, b₂] =
        (⇑(Fin.insertNthOrderIso (fun _ ↦ ℝ) (0 : Fin 3))) ⁻¹'
          Set.Icc ![a₀, a₁, a₂] ![b₀, b₁, b₂] := by
      ext p
      simp only [Set.mem_preimage, he_order]
    rw [hePreimage]
    rw [(Fin.insertNthOrderIso (fun _ ↦ ℝ) (0 : Fin 3)).preimage_Icc]
    have ha : (Fin.insertNthOrderIso (fun _ ↦ ℝ) (0 : Fin 3)).symm
        ![a₀, a₁, a₂] = (a₀, ![a₁, a₂]) := by
      rfl
    have hb : (Fin.insertNthOrderIso (fun _ ↦ ℝ) (0 : Fin 3)).symm
        ![b₀, b₁, b₂] = (b₀, ![b₁, b₂]) := by
      rfl
    rw [ha, hb, Set.Icc_prod_eq]
  rw [← hem.map_eq, MeasureTheory.setIntegral_map_equiv, heIcc,
    Measure.volume_eq_prod]
  rw [MeasureTheory.setIntegral_prod]
  · simp only [he_cons, intervalIntegral.integral_of_le, h₀,
      MeasureTheory.setIntegral_congr_set
        (Ioc_ae_eq_Icc (α := ℝ) (μ := volume))]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
    intro u hu
    have hCons (v w : ℝ) : Fin.cons u ![v, w] = ![u, v, w] := by
      rfl
    simpa only [hCons] using
      (finTwo_setIntegral_Icc_eq_iterated (fun y ↦ f (Fin.cons u y))
        (by fun_prop) a₁ a₂ b₁ b₂ h₁ h₂)
  · have hContinuous : Continuous
        (fun p : ℝ × (Fin 2 → ℝ) ↦ f (e p)) := by
      simpa only [he_cons] using
        (show Continuous
          (fun p : ℝ × (Fin 2 → ℝ) ↦ f (Fin.cons p.1 p.2)) by
            fun_prop)
    exact hContinuous.continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)

/-! ## B. Coordinate face integrals -/

/-- Fixing coordinate zero of a `Fin 3` box leaves coordinates one and two in that order. -/
lemma finThree_faceZero_setIntegral_Icc_eq_iterated
    (f : (Fin 3 → ℝ) → ℝ) (hf : Continuous f) (t : ℝ)
    (a₀ a₁ a₂ b₀ b₁ b₂ : ℝ) (h₁ : a₁ ≤ b₁) (h₂ : a₂ ≤ b₂) :
    (∫ x in Set.Icc (![a₀, a₁, a₂] ∘ (0 : Fin 3).succAbove)
        (![b₀, b₁, b₂] ∘ (0 : Fin 3).succAbove),
      f ((0 : Fin 3).insertNth t x)) =
      ∫ u in a₁..b₁, ∫ v in a₂..b₂, f ![t, u, v] := by
  have hLower : ![a₀, a₁, a₂] ∘ (0 : Fin 3).succAbove = ![a₁, a₂] := by
    funext i
    fin_cases i <;> rfl
  have hUpper : ![b₀, b₁, b₂] ∘ (0 : Fin 3).succAbove = ![b₁, b₂] := by
    funext i
    fin_cases i <;> rfl
  have hInsert (x : Fin 2 → ℝ) :
      (0 : Fin 3).insertNth t x = ![t, x 0, x 1] := by
    ext i
    fin_cases i <;> rfl
  rw [hLower, hUpper]
  simp_rw [hInsert]
  exact finTwo_setIntegral_Icc_eq_iterated
    (fun x ↦ f ![t, x 0, x 1]) (by fun_prop) a₁ a₂ b₁ b₂ h₁ h₂

/-- Fixing coordinate one of a `Fin 3` box leaves coordinates zero and two in that order. -/
lemma finThree_faceOne_setIntegral_Icc_eq_iterated
    (f : (Fin 3 → ℝ) → ℝ) (hf : Continuous f) (t : ℝ)
    (a₀ a₁ a₂ b₀ b₁ b₂ : ℝ) (h₀ : a₀ ≤ b₀) (h₂ : a₂ ≤ b₂) :
    (∫ x in Set.Icc (![a₀, a₁, a₂] ∘ (1 : Fin 3).succAbove)
        (![b₀, b₁, b₂] ∘ (1 : Fin 3).succAbove),
      f ((1 : Fin 3).insertNth t x)) =
      ∫ u in a₀..b₀, ∫ v in a₂..b₂, f ![u, t, v] := by
  have hLower : ![a₀, a₁, a₂] ∘ (1 : Fin 3).succAbove = ![a₀, a₂] := by
    funext i
    fin_cases i <;> rfl
  have hUpper : ![b₀, b₁, b₂] ∘ (1 : Fin 3).succAbove = ![b₀, b₂] := by
    funext i
    fin_cases i <;> rfl
  have hInsert (x : Fin 2 → ℝ) :
      (1 : Fin 3).insertNth t x = ![x 0, t, x 1] := by
    ext i
    fin_cases i <;> rfl
  rw [hLower, hUpper]
  simp_rw [hInsert]
  exact finTwo_setIntegral_Icc_eq_iterated
    (fun x ↦ f ![x 0, t, x 1]) (by fun_prop) a₀ a₂ b₀ b₂ h₀ h₂

/-- Fixing coordinate two of a `Fin 3` box leaves coordinates zero and one in that order. -/
lemma finThree_faceTwo_setIntegral_Icc_eq_iterated
    (f : (Fin 3 → ℝ) → ℝ) (hf : Continuous f) (t : ℝ)
    (a₀ a₁ a₂ b₀ b₁ b₂ : ℝ) (h₀ : a₀ ≤ b₀) (h₁ : a₁ ≤ b₁) :
    (∫ x in Set.Icc (![a₀, a₁, a₂] ∘ (2 : Fin 3).succAbove)
        (![b₀, b₁, b₂] ∘ (2 : Fin 3).succAbove),
      f ((2 : Fin 3).insertNth t x)) =
      ∫ u in a₀..b₀, ∫ v in a₁..b₁, f ![u, v, t] := by
  have hLower : ![a₀, a₁, a₂] ∘ (2 : Fin 3).succAbove = ![a₀, a₁] := by
    funext i
    fin_cases i <;> rfl
  have hUpper : ![b₀, b₁, b₂] ∘ (2 : Fin 3).succAbove = ![b₀, b₁] := by
    funext i
    fin_cases i <;> rfl
  have hInsert (x : Fin 2 → ℝ) :
      (2 : Fin 3).insertNth t x = ![x 0, x 1, t] := by
    ext i
    fin_cases i <;> rfl
  rw [hLower, hUpper]
  simp_rw [hInsert]
  exact finTwo_setIntegral_Icc_eq_iterated
    (fun x ↦ f ![x 0, x 1, t]) (by fun_prop) a₀ a₁ b₀ b₁ h₀ h₁

end
end Space
