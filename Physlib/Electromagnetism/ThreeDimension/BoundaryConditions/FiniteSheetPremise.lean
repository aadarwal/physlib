/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Electromagnetism.ThreeDimension.BoundaryConditions.SidewiseMacroscopicMaxwell
public import Physlib.SpaceAndTime.Space.Integrals.PlanarPillboxDivergence
public import Physlib.SpaceAndTime.Space.Integrals.PlanarThinLoopStokes

/-!
# Finite sheet premise for planar macroscopic Maxwell fields

## i. Overview

This file states the explicit finite-sheet hypothesis connecting two independent sidewise
differential Maxwell solutions to literal carrier-supported charge and current integrals. It also
records the local half-cell calculus and the two witnessed differentiation-under-the-integral
identities needed to compare pointwise Maxwell equations with the existing finite-cell flux rates.

Crucially, the premise never assumes a pointwise interface jump. Its four carrier fields identify
finite retained face or line integrals: electric displacement with the supplied surface charge,
magnetic induction with zero magnetic sheet, electric field with zero magnetic sheet current, and
magnetic field strength with the supplied free surface current. A future weak or measure-valued
Maxwell layer may derive these finite identifications; they remain explicit here.

## ii. Key results

- `HasPlanarFiniteSheetMaxwellPremise`: the named finite-sheet, local-calculus, integrability, and
  time-interchange hypothesis.
- `HasPlanarFiniteSheetMaxwellPremise.electricGaussBulk`: differential electric Gauss law inside
  the split pillbox.
- `HasPlanarFiniteSheetMaxwellPremise.magneticGaussBulk`: differential magnetic Gauss law inside
  the split pillbox.
- `HasPlanarFiniteSheetMaxwellPremise.faradayBulk`: differential Faraday law inside the split
  loop, including its minus sign.
- `HasPlanarFiniteSheetMaxwellPremise.ampereMaxwellBulk`: differential Ampere--Maxwell law inside
  the split loop, including both current terms.

## iii. Table of contents

- A. Finite-sheet premise
- B. Divergence consequences
- C. Curl consequences

## iv. References

This is a Physlib-original E4b construction. The finite carrier identifications are explicit
hypotheses; deriving them from weak or measure-valued Maxwell equations remains future work.
-/

@[expose] public section

open Matrix MeasureTheory
open scoped Interval

namespace Electromagnetism
namespace ThreeDimension

open Space Time

noncomputable section

/-!
## A. Finite-sheet premise
-/

/-- Finite carrier-source identifications, local split-cell calculus, and witnessed flux
interchanges for two sidewise differential Maxwell extensions.

Every theorem consuming this premise keeps it as an explicit hypothesis. The structure assumes no
pointwise jump law and no weak or measure-valued Maxwell equation. -/
structure HasPlanarFiniteSheetMaxwellPremise
    {plane : OrientedAffineHyperplane 3}
    (sidewise : PlanarSidewiseMacroscopicMaxwell plane)
    (surfaceCharge : PlanarFreeSurfaceChargeDensity plane)
    (surfaceCurrent : PlanarFreeSurfaceCurrentDensity plane)
    (cells : PlanarMaxwellThinCells plane)
    (rates : PlanarMaxwellThinCellFluxRates sidewise.fields cells) : Prop where
  /-- Integrability of every term in the target finite integral Maxwell laws. -/
  integrable : ArePlanarMaxwellThinCellTermsIntegrable sidewise.fields sidewise.sources
    surfaceCharge surfaceCurrent cells
  /-- Local split-pillbox divergence calculus for electric displacement. -/
  electricDisplacementDivergence : ∀ (t : Time) (x : plane.carrier) (scale : ℕ),
    ∃ negativeExceptionalSet positiveExceptionalSet : Set (Fin 3 → ℝ),
      (cells.pillbox x).DivergenceRegularity sidewise.negativeElectricDisplacement
        sidewise.positiveElectricDisplacement t x scale
        negativeExceptionalSet positiveExceptionalSet
  /-- Integrability of the negative-side bulk-charge half-volume. -/
  negativeChargeVolume : ∀ (t : Time) (x : plane.carrier) (scale : ℕ),
    (cells.pillbox x).AmbientHalfVolumeIntegrable sidewise.negativeChargeDensity
      t x scale (-(cells.pillbox x).halfThickness scale) 0
  /-- Integrability of the positive-side bulk-charge half-volume. -/
  positiveChargeVolume : ∀ (t : Time) (x : plane.carrier) (scale : ℕ),
    (cells.pillbox x).AmbientHalfVolumeIntegrable sidewise.positiveChargeDensity
      t x scale 0 ((cells.pillbox x).halfThickness scale)
  /-- The retained electric-displacement carrier-face jump is the literal surface-charge
  average. -/
  electricCarrierFace : ∀ (t : Time) (x : plane.carrier) (scale : ℕ),
    ((2 * (cells.pillbox x).radius scale) ^ 2)⁻¹ *
        affineSplitBoxCarrierJump (sidewise.negativeElectricDisplacement t)
          (sidewise.positiveElectricDisplacement t) (x : Space)
          (cells.pillbox x).tangentDirection (cells.pillbox x).quarterTurnDirection
          (cells.pillbox x).normalDirection ((cells.pillbox x).radius scale) =
      (cells.pillbox x).surfaceFaceAverage surfaceCharge t x scale
  /-- Local split-pillbox divergence calculus for magnetic induction. -/
  magneticInductionDivergence : ∀ (t : Time) (x : plane.carrier) (scale : ℕ),
    ∃ negativeExceptionalSet positiveExceptionalSet : Set (Fin 3 → ℝ),
      (cells.pillbox x).DivergenceRegularity sidewise.negativeMagneticInduction
        sidewise.positiveMagneticInduction t x scale
        negativeExceptionalSet positiveExceptionalSet
  /-- The retained magnetic-induction carrier-face jump is zero: no magnetic sheet charge is
  introduced. -/
  magneticCarrierFace : ∀ (t : Time) (x : plane.carrier) (scale : ℕ),
    ((2 * (cells.pillbox x).radius scale) ^ 2)⁻¹ *
        affineSplitBoxCarrierJump (sidewise.negativeMagneticInduction t)
          (sidewise.positiveMagneticInduction t) (x : Space)
          (cells.pillbox x).tangentDirection (cells.pillbox x).quarterTurnDirection
          (cells.pillbox x).normalDirection ((cells.pillbox x).radius scale) = 0
  /-- Local split-rectangle Stokes calculus for electric field. -/
  electricFieldStokes : ∀ (t : Time) (x : plane.carrier)
      (tangent : plane.tangentSubmodule) (scale : ℕ),
    PlanarSplitRectangleStokesRegularity (sidewise.negativeElectricField t)
      (sidewise.positiveElectricField t) (x : Space)
      (cells.loop x tangent).tangentDirection (cells.loop x tangent).normalDirection
      ((cells.loop x tangent).radius scale) ((cells.loop x tangent).halfThickness scale)
  /-- The retained electric-field carrier-line jump is zero: no magnetic sheet current is
  introduced. -/
  electricCarrierLine : ∀ (t : Time) (x : plane.carrier)
      (tangent : plane.tangentSubmodule) (scale : ℕ),
    (2 * (cells.loop x tangent).radius scale)⁻¹ *
        planarSplitRectangleCarrierJump (sidewise.negativeElectricField t)
          (sidewise.positiveElectricField t) (x : Space)
          (cells.loop x tangent).tangentDirection (cells.loop x tangent).normalDirection
          ((cells.loop x tangent).radius scale) = 0
  /-- Both iterated levels of the negative-side magnetic time-derivative flux are integrable. -/
  negativeMagneticRateFlux : ∀ (t : Time) (x : plane.carrier)
      (tangent : plane.tangentSubmodule) (scale : ℕ),
    (cells.loop x tangent).AmbientHalfSpanningIntegrable
      (fun s y ↦ ∂ₜ (fun q ↦ sidewise.negativeMagneticInduction q y) s)
      t x scale (-(cells.loop x tangent).halfThickness scale) 0
  /-- Both iterated levels of the positive-side magnetic time-derivative flux are integrable. -/
  positiveMagneticRateFlux : ∀ (t : Time) (x : plane.carrier)
      (tangent : plane.tangentSubmodule) (scale : ℕ),
    (cells.loop x tangent).AmbientHalfSpanningIntegrable
      (fun s y ↦ ∂ₜ (fun q ↦ sidewise.positiveMagneticInduction q y) s)
      t x scale 0 ((cells.loop x tangent).halfThickness scale)
  /-- Witnessed differentiation under the split magnetic-flux integral. -/
  magneticFluxInterchange : ∀ (t : Time) (x : plane.carrier)
      (tangent : plane.tangentSubmodule) (scale : ℕ),
    rates.magneticFluxRate t x tangent scale =
      (2 * (cells.loop x tangent).radius scale)⁻¹ *
        planarSplitRectangleFlux
          (fun y ↦ ∂ₜ (fun s ↦ sidewise.negativeMagneticInduction s y) t)
          (fun y ↦ ∂ₜ (fun s ↦ sidewise.positiveMagneticInduction s y) t)
          (x : Space) (cells.loop x tangent).tangentDirection
          (cells.loop x tangent).normalDirection ((cells.loop x tangent).radius scale)
          ((cells.loop x tangent).halfThickness scale)
  /-- Local split-rectangle Stokes calculus for magnetic field strength. -/
  magneticFieldStokes : ∀ (t : Time) (x : plane.carrier)
      (tangent : plane.tangentSubmodule) (scale : ℕ),
    PlanarSplitRectangleStokesRegularity (sidewise.negativeMagneticFieldStrength t)
      (sidewise.positiveMagneticFieldStrength t) (x : Space)
      (cells.loop x tangent).tangentDirection (cells.loop x tangent).normalDirection
      ((cells.loop x tangent).radius scale) ((cells.loop x tangent).halfThickness scale)
  /-- Both iterated levels of the negative-side bulk-current flux are integrable. -/
  negativeCurrentFlux : ∀ (t : Time) (x : plane.carrier)
      (tangent : plane.tangentSubmodule) (scale : ℕ),
    (cells.loop x tangent).AmbientHalfSpanningIntegrable sidewise.negativeCurrentDensity
      t x scale (-(cells.loop x tangent).halfThickness scale) 0
  /-- Both iterated levels of the positive-side bulk-current flux are integrable. -/
  positiveCurrentFlux : ∀ (t : Time) (x : plane.carrier)
      (tangent : plane.tangentSubmodule) (scale : ℕ),
    (cells.loop x tangent).AmbientHalfSpanningIntegrable sidewise.positiveCurrentDensity
      t x scale 0 ((cells.loop x tangent).halfThickness scale)
  /-- Both iterated levels of the negative-side electric time-derivative flux are integrable. -/
  negativeElectricRateFlux : ∀ (t : Time) (x : plane.carrier)
      (tangent : plane.tangentSubmodule) (scale : ℕ),
    (cells.loop x tangent).AmbientHalfSpanningIntegrable
      (fun s y ↦ ∂ₜ (fun q ↦ sidewise.negativeElectricDisplacement q y) s)
      t x scale (-(cells.loop x tangent).halfThickness scale) 0
  /-- Both iterated levels of the positive-side electric time-derivative flux are integrable. -/
  positiveElectricRateFlux : ∀ (t : Time) (x : plane.carrier)
      (tangent : plane.tangentSubmodule) (scale : ℕ),
    (cells.loop x tangent).AmbientHalfSpanningIntegrable
      (fun s y ↦ ∂ₜ (fun q ↦ sidewise.positiveElectricDisplacement q y) s)
      t x scale 0 ((cells.loop x tangent).halfThickness scale)
  /-- Witnessed differentiation under the split electric-displacement flux integral. -/
  electricFluxInterchange : ∀ (t : Time) (x : plane.carrier)
      (tangent : plane.tangentSubmodule) (scale : ℕ),
    rates.electricFluxRate t x tangent scale =
      (2 * (cells.loop x tangent).radius scale)⁻¹ *
        planarSplitRectangleFlux
          (fun y ↦ ∂ₜ (fun s ↦ sidewise.negativeElectricDisplacement s y) t)
          (fun y ↦ ∂ₜ (fun s ↦ sidewise.positiveElectricDisplacement s y) t)
          (x : Space) (cells.loop x tangent).tangentDirection
          (cells.loop x tangent).normalDirection ((cells.loop x tangent).radius scale)
          ((cells.loop x tangent).halfThickness scale)
  /-- The retained magnetic-field-strength carrier-line jump is the literal free
  surface-current average. -/
  magneticCarrierLine : ∀ (t : Time) (x : plane.carrier)
      (tangent : plane.tangentSubmodule) (scale : ℕ),
    (2 * (cells.loop x tangent).radius scale)⁻¹ *
        planarSplitRectangleCarrierJump (sidewise.negativeMagneticFieldStrength t)
          (sidewise.positiveMagneticFieldStrength t) (x : Space)
          (cells.loop x tangent).tangentDirection (cells.loop x tangent).normalDirection
          ((cells.loop x tangent).radius scale) =
      (cells.loop x tangent).surfaceLineAverage surfaceCurrent t x scale

namespace HasPlanarFiniteSheetMaxwellPremise

variable {plane : OrientedAffineHyperplane 3}
  {sidewise : PlanarSidewiseMacroscopicMaxwell plane}
  {surfaceCharge : PlanarFreeSurfaceChargeDensity plane}
  {surfaceCurrent : PlanarFreeSurfaceCurrentDensity plane}
  {cells : PlanarMaxwellThinCells plane}
  {rates : PlanarMaxwellThinCellFluxRates sidewise.fields cells}

/-!
## B. Divergence consequences
-/

/-- The normalized split-pillbox divergence of electric displacement is the literal bulk free-
charge volume average. The finite-sheet premise supplies only the integral regrouping; the
integrand equality is differential electric Gauss law on each side. -/
lemma electricGaussBulk
    (premise : HasPlanarFiniteSheetMaxwellPremise sidewise surfaceCharge surfaceCurrent
      cells rates)
    (t : Time) (x : plane.carrier) (scale : ℕ) :
    ((2 * (cells.pillbox x).radius scale) ^ 2)⁻¹ *
        affineSplitBoxBulkDivergence (sidewise.negativeElectricDisplacement t)
          (sidewise.positiveElectricDisplacement t) (x : Space)
          (cells.pillbox x).tangentDirection (cells.pillbox x).quarterTurnDirection
          (cells.pillbox x).normalDirection ((cells.pillbox x).radius scale)
          ((cells.pillbox x).halfThickness scale) =
      (cells.pillbox x).volumeAverage sidewise.sources.chargeDensity t x scale := by
  change _ = (cells.pillbox x).volumeAverage
    (OrientedAffineHyperplane.TwoSidedField.ofFields plane
      sidewise.negativeChargeDensity sidewise.positiveChargeDensity) t x scale
  rw [(cells.pillbox x).volumeAverage_ofFields_eq_normalized_affineSplitVolume
    sidewise.negativeChargeDensity sidewise.positiveChargeDensity t x scale
    (premise.negativeChargeVolume t x scale) (premise.positiveChargeVolume t x scale)]
  apply congrArg (((2 * (cells.pillbox x).radius scale) ^ 2)⁻¹ * ·)
  unfold affineSplitBoxBulkDivergence
  rw [(cells.pillbox x).orientedVolume]
  simp only [mul_one]
  congr 1
  · apply intervalIntegral.integral_congr
    intro u _
    apply intervalIntegral.integral_congr
    intro v _
    apply intervalIntegral.integral_congr
    intro w _
    exact sidewise.negativeMaxwell.gaussLawElectric t _
  · apply intervalIntegral.integral_congr
    intro u _
    apply intervalIntegral.integral_congr
    intro v _
    apply intervalIntegral.integral_congr
    intro w _
    exact sidewise.positiveMaxwell.gaussLawElectric t _

/-- The normalized split-pillbox divergence of magnetic induction vanishes by differential
magnetic Gauss law on each side. -/
lemma magneticGaussBulk
    (t : Time) (x : plane.carrier) (scale : ℕ) :
    ((2 * (cells.pillbox x).radius scale) ^ 2)⁻¹ *
        affineSplitBoxBulkDivergence (sidewise.negativeMagneticInduction t)
          (sidewise.positiveMagneticInduction t) (x : Space)
          (cells.pillbox x).tangentDirection (cells.pillbox x).quarterTurnDirection
          (cells.pillbox x).normalDirection ((cells.pillbox x).radius scale)
          ((cells.pillbox x).halfThickness scale) = 0 := by
  unfold affineSplitBoxBulkDivergence
  rw [(cells.pillbox x).orientedVolume]
  simp_rw [sidewise.negativeMaxwell.gaussLawMagnetic,
    sidewise.positiveMaxwell.gaussLawMagnetic]
  simp

/-!
## C. Curl consequences
-/

/-- Differential Faraday law identifies the split electric curl flux with minus the split
magnetic time-derivative flux before any finite-flux interchange is used. -/
lemma faradayCurlFlux
    (t : Time) (x : plane.carrier) (tangent : plane.tangentSubmodule) (scale : ℕ) :
    planarSplitRectangleCurlFlux (sidewise.negativeElectricField t)
        (sidewise.positiveElectricField t) (x : Space)
        (cells.loop x tangent).tangentDirection (cells.loop x tangent).normalDirection
        ((cells.loop x tangent).radius scale) ((cells.loop x tangent).halfThickness scale) =
      -planarSplitRectangleFlux
        (fun y ↦ ∂ₜ (fun s ↦ sidewise.negativeMagneticInduction s y) t)
        (fun y ↦ ∂ₜ (fun s ↦ sidewise.positiveMagneticInduction s y) t)
        (x : Space) (cells.loop x tangent).tangentDirection
        (cells.loop x tangent).normalDirection ((cells.loop x tangent).radius scale)
        ((cells.loop x tangent).halfThickness scale) := by
  unfold planarSplitRectangleCurlFlux planarSplitRectangleFlux
  simp_rw [sidewise.negativeMaxwell.faradayLaw,
    sidewise.positiveMaxwell.faradayLaw, inner_neg_left,
    intervalIntegral.integral_neg]
  ring

/-- The normalized split-loop curl flux of electric field is the negative of the witnessed
magnetic-flux rate. The sign comes from differential Faraday law on each side, while the equality
with the derivative of the actual finite flux is an explicit field of the finite-sheet premise. -/
lemma faradayBulk
    (premise : HasPlanarFiniteSheetMaxwellPremise sidewise surfaceCharge surfaceCurrent
      cells rates)
    (t : Time) (x : plane.carrier) (tangent : plane.tangentSubmodule) (scale : ℕ) :
    (2 * (cells.loop x tangent).radius scale)⁻¹ *
        planarSplitRectangleCurlFlux (sidewise.negativeElectricField t)
          (sidewise.positiveElectricField t) (x : Space)
          (cells.loop x tangent).tangentDirection (cells.loop x tangent).normalDirection
          ((cells.loop x tangent).radius scale)
          ((cells.loop x tangent).halfThickness scale) =
      -rates.magneticFluxRate t x tangent scale := by
  rw [faradayCurlFlux, premise.magneticFluxInterchange t x tangent scale]
  ring

/-- The normalized affine split-rectangle flux of the two ambient bulk currents is the existing
two-sided thin-loop current average. -/
lemma currentSurfaceBulk
    (premise : HasPlanarFiniteSheetMaxwellPremise sidewise surfaceCharge surfaceCurrent
      cells rates)
    (t : Time) (x : plane.carrier) (tangent : plane.tangentSubmodule) (scale : ℕ) :
    (2 * (cells.loop x tangent).radius scale)⁻¹ *
        planarSplitRectangleFlux (sidewise.negativeCurrentDensity t)
          (sidewise.positiveCurrentDensity t) (x : Space)
          (cells.loop x tangent).tangentDirection (cells.loop x tangent).normalDirection
          ((cells.loop x tangent).radius scale)
          ((cells.loop x tangent).halfThickness scale) =
      (cells.loop x tangent).spanningSurfaceAverage sidewise.sources.currentDensity
        t x scale := by
  change _ = (cells.loop x tangent).spanningSurfaceAverage
    (OrientedAffineHyperplane.TwoSidedField.ofFields plane
      sidewise.negativeCurrentDensity sidewise.positiveCurrentDensity) t x scale
  rw [(cells.loop x tangent).spanningSurfaceAverage_ofFields_eq_normalized_affineSplitIntegral
    sidewise.negativeCurrentDensity sidewise.positiveCurrentDensity t x scale
    (premise.negativeCurrentFlux t x tangent scale)
    (premise.positiveCurrentFlux t x tangent scale)]
  rfl

/-- Differential Ampere--Maxwell law identifies the split magnetic curl flux with the split flux
of bulk current plus electric-displacement time derivative, before integral additivity or the
finite-flux interchange is used. -/
lemma ampereMaxwellCurlFlux
    (t : Time) (x : plane.carrier) (tangent : plane.tangentSubmodule) (scale : ℕ) :
    planarSplitRectangleCurlFlux (sidewise.negativeMagneticFieldStrength t)
        (sidewise.positiveMagneticFieldStrength t) (x : Space)
        (cells.loop x tangent).tangentDirection (cells.loop x tangent).normalDirection
        ((cells.loop x tangent).radius scale) ((cells.loop x tangent).halfThickness scale) =
      planarSplitRectangleFlux
        (sidewise.negativeCurrentDensity t +
          fun y ↦ ∂ₜ (fun s ↦ sidewise.negativeElectricDisplacement s y) t)
        (sidewise.positiveCurrentDensity t +
          fun y ↦ ∂ₜ (fun s ↦ sidewise.positiveElectricDisplacement s y) t)
        (x : Space) (cells.loop x tangent).tangentDirection
        (cells.loop x tangent).normalDirection ((cells.loop x tangent).radius scale)
        ((cells.loop x tangent).halfThickness scale) := by
  unfold planarSplitRectangleCurlFlux planarSplitRectangleFlux
  congr 1
  · apply intervalIntegral.integral_congr
    intro u _
    apply intervalIntegral.integral_congr
    intro v _
    dsimp only
    rw [sidewise.negativeMaxwell.ampereMaxwellLaw]
    rfl
  · apply intervalIntegral.integral_congr
    intro u _
    apply intervalIntegral.integral_congr
    intro v _
    dsimp only
    rw [sidewise.positiveMaxwell.ampereMaxwellLaw]
    rfl

/-- The normalized split-loop curl flux of magnetic field strength is the sum of the literal bulk
current average and the witnessed electric-displacement flux rate. The two plus signs come from
differential Ampere--Maxwell law and iterated-integral additivity under the premise's explicit
integrability hypotheses. -/
lemma ampereMaxwellBulk
    (premise : HasPlanarFiniteSheetMaxwellPremise sidewise surfaceCharge surfaceCurrent
      cells rates)
    (t : Time) (x : plane.carrier) (tangent : plane.tangentSubmodule) (scale : ℕ) :
    (2 * (cells.loop x tangent).radius scale)⁻¹ *
        planarSplitRectangleCurlFlux (sidewise.negativeMagneticFieldStrength t)
          (sidewise.positiveMagneticFieldStrength t) (x : Space)
          (cells.loop x tangent).tangentDirection (cells.loop x tangent).normalDirection
          ((cells.loop x tangent).radius scale)
          ((cells.loop x tangent).halfThickness scale) =
      (cells.loop x tangent).spanningSurfaceAverage sidewise.sources.currentDensity t x scale +
        rates.electricFluxRate t x tangent scale := by
  have hCurrentIntegrable :=
    (cells.loop x tangent).planarSplitRectangleFluxIntegrable
      sidewise.negativeCurrentDensity sidewise.positiveCurrentDensity t x scale
      (premise.negativeCurrentFlux t x tangent scale)
      (premise.positiveCurrentFlux t x tangent scale)
  have hRateIntegrable :=
    (cells.loop x tangent).planarSplitRectangleFluxIntegrable
      (fun s y ↦ ∂ₜ (fun q ↦ sidewise.negativeElectricDisplacement q y) s)
      (fun s y ↦ ∂ₜ (fun q ↦ sidewise.positiveElectricDisplacement q y) s)
      t x scale (premise.negativeElectricRateFlux t x tangent scale)
      (premise.positiveElectricRateFlux t x tangent scale)
  have hAdd := planarSplitRectangleFlux_add
    (sidewise.negativeCurrentDensity t) (sidewise.positiveCurrentDensity t)
    (fun y ↦ ∂ₜ (fun s ↦ sidewise.negativeElectricDisplacement s y) t)
    (fun y ↦ ∂ₜ (fun s ↦ sidewise.positiveElectricDisplacement s y) t) (x : Space)
    (cells.loop x tangent).tangentDirection (cells.loop x tangent).normalDirection
    ((cells.loop x tangent).radius scale) ((cells.loop x tangent).halfThickness scale)
    hCurrentIntegrable hRateIntegrable
  rw [ampereMaxwellCurlFlux, hAdd, mul_add,
    premise.currentSurfaceBulk t x tangent scale]
  change _ + (2 * (cells.loop x tangent).radius scale)⁻¹ *
      planarSplitRectangleFlux
        (fun y ↦ ∂ₜ (fun s ↦ sidewise.negativeElectricDisplacement s y) t)
        (fun y ↦ ∂ₜ (fun s ↦ sidewise.positiveElectricDisplacement s y) t)
        (x : Space) (cells.loop x tangent).tangentDirection
        (cells.loop x tangent).normalDirection ((cells.loop x tangent).radius scale)
        ((cells.loop x tangent).halfThickness scale) = _
  rw [← premise.electricFluxInterchange t x tangent scale]

end HasPlanarFiniteSheetMaxwellPremise

end
end ThreeDimension
end Electromagnetism
