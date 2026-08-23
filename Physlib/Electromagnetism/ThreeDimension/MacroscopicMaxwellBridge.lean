/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Electromagnetism.ThreeDimension.Energy
public import Physlib.Electromagnetism.ThreeDimension.MaxwellEquations

/-!

# The free-space bridge to macroscopic Maxwell equations

## i. Overview

This module connects the existing potential-derived free-space Maxwell laws to the macroscopic
four-field formulation. Given a smooth electromagnetic potential and Lorentz current satisfying
`IsExtrema`, it constructs `D = ε₀ E` and `H = B / μ₀` and proves the macroscopic equations
with the charge and current extracted from the same Lorentz current.

The bridge is intentionally one-way. The existing laws start from a potential; no converse claim
that every macroscopic solution admits a global potential, gauge choice, or `IsExtrema` witness is
made here. For a source-free extremum, the bridge also gives the explicit local vacuum Poynting
theorem in terms of `ε₀`, `μ₀`, `E`, and `B`.

## ii. Key results

- `isMacroscopicMaxwellSolution_of_isExtrema`: the connected free-space material solution.
- `poyntingTheorem_sourceFree_of_isExtrema`: the explicit local source-free vacuum energy
  equation.

## iii. Table of contents

- A. Free-space solution bridge
- B. Source-free vacuum energy

## iv. References

- J. D. Jackson, *Classical Electrodynamics*, third edition, section 6.6.

-/

@[expose] public section

namespace Electromagnetism
namespace ThreeDimension

open Time Space Matrix ElectromagneticPotential ContDiff

/-!

## A. Free-space solution bridge

-/

/-- A smooth potential-derived free-space solution induces the canonical macroscopic fields for
the corresponding homogeneous isotropic medium. -/
lemma isMacroscopicMaxwellSolution_of_isExtrema {𝓕 : FreeSpace}
    (V : ElectromagneticPotential 3) (J₄ : LorentzCurrentDensity 3)
    (h : IsExtrema 𝓕 V J₄) (hV : ContDiff ℝ ∞ V) (hJ : ContDiff ℝ ∞ J₄) :
    𝓕.toHomogeneousIsotropicMedium.IsMacroscopicMaxwellSolution
      (V.electricField 𝓕.c)
      (𝓕.toHomogeneousIsotropicMedium.electricDisplacement (V.electricField 𝓕.c))
      (V.magneticField 𝓕.c)
      (𝓕.toHomogeneousIsotropicMedium.magneticFieldStrength (V.magneticField 𝓕.c))
      (J₄.chargeDensity 𝓕.c) (J₄.currentDensity 𝓕.c) := by
  let E := V.electricField 𝓕.c
  let B := V.magneticField 𝓕.c
  let 𝓜 := 𝓕.toHomogeneousIsotropicMedium
  have hV2 : ContDiff ℝ 2 V := hV.of_le ENat.LEInfty.out
  have hE : Differentiable ℝ ↿E := electricField_differentiable hV2
  have hB : Differentiable ℝ ↿B := magneticField_differentiable hV2
  apply HomogeneousIsotropicMedium.IsMacroscopicMaxwellSolution.of_maxwellEquations
  refine ⟨hE, hE.const_smul 𝓜.ε, hB, hB.const_smul 𝓜.μ⁻¹, ?_, ?_, ?_, ?_⟩
  · intro t x
    change (∇ ⬝ (𝓜.ε • E t)) x = J₄.chargeDensity 𝓕.c t x
    rw [Space.div_smul (E t) 𝓜.ε
        (hE.comp (f := fun x => (t, x)) (by fun_prop))]
    simp only [Pi.smul_apply]
    rw [ThreeDimension.gaussLawElectric V J₄ t x h hV hJ]
    change 𝓕.ε₀ * (J₄.chargeDensity 𝓕.c t x / 𝓕.ε₀) =
      J₄.chargeDensity 𝓕.c t x
    exact mul_div_cancel₀ _ 𝓕.ε₀_ne_zero
  · intro t x
    exact ThreeDimension.gaussLawMagnetic V t x hV
  · intro t x
    change (∇ ⨯ (𝓜.μ⁻¹ • B t)) x =
      J₄.currentDensity 𝓕.c t x + ∂ₜ (fun s => 𝓜.ε • E s x) t
    rw [Space.curl_smul (B t) 𝓜.μ⁻¹
        (hB.comp (f := fun x => (t, x)) (by fun_prop))]
    simp only [Pi.smul_apply]
    rw [ThreeDimension.ampereLaw V J₄ t x h hV hJ, Time.deriv_smul]
    · simp [E, 𝓜, smul_add, smul_smul, 𝓕.μ₀_ne_zero]
    · exact hE.comp (f := fun s => (s, x)) (by fun_prop)
  · intro t x
    exact ThreeDimension.faradayLaw V t x hV

/-!

## B. Source-free vacuum energy

-/

/-- A smooth source-free potential extremum obeys the explicit local vacuum Poynting theorem.

The stored density is `1 / 2 * (ε₀ E · E + μ₀⁻¹ B · B)` and the Poynting vector is
`μ₀⁻¹ • (E × B)`. No factor of the speed of light occurs in this rationalized convention.
This is an instantaneous pointwise differential equation, not an integrated, time-averaged,
irradiance, or modal-power statement. -/
theorem poyntingTheorem_sourceFree_of_isExtrema {𝓕 : FreeSpace}
    (V : ElectromagneticPotential 3) (h : IsExtrema 𝓕 V 0)
    (hV : ContDiff ℝ ∞ V) (t : Time) (x : Space) :
    ∂ₜ (fun s =>
      (1 / 2) *
        (𝓕.ε₀ * inner ℝ (V.electricField 𝓕.c s x) (V.electricField 𝓕.c s x) +
          𝓕.μ₀⁻¹ * inner ℝ (V.magneticField 𝓕.c s x)
            (V.magneticField 𝓕.c s x))) t +
      (∇ ⬝ (fun y => 𝓕.μ₀⁻¹ •
        (V.electricField 𝓕.c t y ⨯ₑ₃ V.magneticField 𝓕.c t y))) x = 0 := by
  have hs := isMacroscopicMaxwellSolution_of_isExtrema V 0 h hV contDiff_zero_fun
  rw [LorentzCurrentDensity.chargeDensity_zero,
    LorentzCurrentDensity.currentDensity_zero] at hs
  have hp := hs.poyntingTheorem_sourceFree t x
  simp_rw [HomogeneousIsotropicMedium.energyDensity_magneticFieldStrength] at hp
  rw [HomogeneousIsotropicMedium.poyntingVector_magneticFieldStrength] at hp
  simpa only [FreeSpace.toHomogeneousIsotropicMedium_ε,
    FreeSpace.toHomogeneousIsotropicMedium_μ] using hp

end ThreeDimension
end Electromagnetism
