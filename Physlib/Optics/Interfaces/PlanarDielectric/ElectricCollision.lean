/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public
import Physlib.Electromagnetism.ThreeDimension.MonochromaticPlaneWave.ComplexBoundaryNoncancellation
public import Physlib.Optics.Interfaces.PlanarDielectric.WaveBoundary

/-!
# Electric coefficient collisions at a planar dielectric boundary

## i. Overview

This file packages the incident-plus-reflected-minus-transmitted joint electric boundary
amplitudes as a finite map keyed by exact complex boundary exponents. The incident and reflected
amplitudes use the interface's negative-side medium, while the transmitted amplitude uses its
positive-side medium. Equal exponents are aggregated by the map, and keys whose aggregate
coefficient is zero are absent from its support.

A two-law electric boundary with zero free surface charge makes the corresponding ordinary-real
harmonic sum vanish at every boundary parameter. Every stored wave has strictly positive temporal
rate on the same unit-time probe, so finite harmonic uniqueness makes the entire aggregated
coefficient map zero. In the reverse direction, a zero coefficient map gives the all-parameter
character identity and therefore reconstructs exactly the electric boundary laws. A full local
boundary projects to this result while its free surface current remains arbitrary.

The zero-map conclusion is not a labelwise amplitude identity or an exponent-conservation result.
For example, waves with the same exponent may cancel at that key, and a zero electric amplitude
places no constraint on its wave label. This file assumes no common frequency, phase matching,
Maxwell equation, or material dispersion. Unguarded convention statement (review only): it selects
no propagation or decay branch. It assumes no Fresnel coefficient, irradiance, or power
normalization. The conditional label-matching and reverse connection results needed for
fixed-frequency reduction are separate.

## ii. Key results

- `PlanarDielectricWaveConfiguration.jointElectricBoundaryCoefficients`: the signed,
  exponent-aggregated coefficient map.
- `isElectricBoundary_iff_jointElectricBoundaryCoefficients_eq_zero`:
  exact equivalence between the zero-charge electric boundary and zero coefficient map.

## iii. Table of contents

- A. Signed boundary coefficients
- B. Ordinary-real harmonic evaluation
- C. Boundary-law consequence

## iv. References

This module specializes existing Physlib boundary-character and finite positive-rate uniqueness
results. No external formal-development source is copied or translated here.
-/

@[expose] public section

namespace Optics

open Electromagnetism Electromagnetism.ThreeDimension
open Electromagnetism.ThreeDimension.ComplexMonochromaticPlaneWave

noncomputable section

namespace PlanarDielectricWaveConfiguration

/-!

## A. Signed boundary coefficients

-/

/-- The signed, exponent-aggregated joint electric coefficients of a planar dielectric three-wave
configuration.

The incident and reflected coefficients have positive sign and use the negative-side medium; the
transmitted coefficient has negative sign and uses the positive-side medium. Equal boundary
exponents are combined by the `Finsupp`. -/
def jointElectricBoundaryCoefficients
    (configuration : PlanarDielectricWaveConfiguration) :
    (BoundaryParameter configuration.interface.plane →ₗ[ℝ] ℂ) →₀
      JointElectricTraceAmplitude :=
  Finsupp.single
      (configuration.incident.boundaryExponent configuration.interface.plane)
      (referencedMediumJointElectricTraceAmplitude configuration.interface.plane
        configuration.interface.negativeMedium configuration.incident) +
    Finsupp.single
      (configuration.reflected.boundaryExponent configuration.interface.plane)
      (referencedMediumJointElectricTraceAmplitude configuration.interface.plane
        configuration.interface.negativeMedium configuration.reflected) -
    Finsupp.single
      (configuration.transmitted.boundaryExponent configuration.interface.plane)
      (referencedMediumJointElectricTraceAmplitude configuration.interface.plane
        configuration.interface.positiveMedium configuration.transmitted)

/-!

## B. Ordinary-real harmonic evaluation

-/

/-- Ordinary-real realization after multiplication by a fixed complex scalar is additive in the
joint electric amplitude. -/
private def jointElectricRealizationAddHom (c : ℂ) :
    JointElectricTraceAmplitude →+ EuclideanSpace ℝ (Fin 3) × ℝ where
  toFun A := realPartJointElectricTraceAmplitude (c • A)
  map_zero' := by
    apply Prod.ext
    · ext i
      simp [realPartJointElectricTraceAmplitude,
        ClassicalMechanics.ComplexWaveVector.realPart]
    · simp [realPartJointElectricTraceAmplitude]
  map_add' A B := by
    apply Prod.ext
    · ext i
      simp [realPartJointElectricTraceAmplitude,
        ClassicalMechanics.ComplexWaveVector.realPart]
    · simp [realPartJointElectricTraceAmplitude]

private lemma jointElectricHarmonicSum_single
    {V : Type*} [AddCommMonoid V] [Module ℝ V]
    (L : V →ₗ[ℝ] ℂ) (A : JointElectricTraceAmplitude) (v : V) :
    jointElectricHarmonicSum (Finsupp.single L A) v =
      realPartJointElectricTraceAmplitude (Complex.exp (L v) • A) := by
  exact Finsupp.sum_single_index
    (jointElectricRealizationAddHom (Complex.exp (L v))).map_zero

private lemma jointElectricHarmonicSum_add
    {V : Type*} [AddCommMonoid V] [Module ℝ V]
    (a b : (V →ₗ[ℝ] ℂ) →₀ JointElectricTraceAmplitude) (v : V) :
    jointElectricHarmonicSum (a + b) v =
      jointElectricHarmonicSum a v + jointElectricHarmonicSum b v := by
  exact Finsupp.sum_add_index'
    (fun L ↦ (jointElectricRealizationAddHom (Complex.exp (L v))).map_zero)
    (fun L ↦ (jointElectricRealizationAddHom (Complex.exp (L v))).map_add)

private lemma jointElectricHarmonicSum_sub
    {V : Type*} [AddCommMonoid V] [Module ℝ V]
    (a b : (V →ₗ[ℝ] ℂ) →₀ JointElectricTraceAmplitude) (v : V) :
    jointElectricHarmonicSum (a - b) v =
      jointElectricHarmonicSum a v - jointElectricHarmonicSum b v := by
  exact Finsupp.sum_sub_index
    (fun L ↦ (jointElectricRealizationAddHom (Complex.exp (L v))).map_sub)

private lemma jointElectricBoundaryCoefficients_im_pos
    (configuration : PlanarDielectricWaveConfiguration)
    (L : BoundaryParameter configuration.interface.plane →ₗ[ℝ] ℂ)
    (hL : L ∈ configuration.jointElectricBoundaryCoefficients.support) :
    0 < (L (boundaryTimeProbe configuration.interface.plane)).im := by
  by_cases hi : L = configuration.incident.boundaryExponent configuration.interface.plane
  · subst L
    exact configuration.incident.boundaryExponent_boundaryTimeProbe_im_pos
      configuration.interface.plane
  by_cases hr : L = configuration.reflected.boundaryExponent configuration.interface.plane
  · subst L
    exact configuration.reflected.boundaryExponent_boundaryTimeProbe_im_pos
      configuration.interface.plane
  by_cases ht : L = configuration.transmitted.boundaryExponent configuration.interface.plane
  · subst L
    exact configuration.transmitted.boundaryExponent_boundaryTimeProbe_im_pos
      configuration.interface.plane
  exfalso
  apply Finsupp.mem_support_iff.mp hL
  simp [jointElectricBoundaryCoefficients, hi, hr, ht]

private lemma jointElectricHarmonicSum_boundaryCoefficients
    (configuration : PlanarDielectricWaveConfiguration)
    (p : BoundaryParameter configuration.interface.plane) :
    jointElectricHarmonicSum configuration.jointElectricBoundaryCoefficients p =
      realPartJointElectricTraceAmplitude
            (Complex.exp (configuration.incident.boundaryExponent
                configuration.interface.plane p) •
              referencedMediumJointElectricTraceAmplitude configuration.interface.plane
                configuration.interface.negativeMedium configuration.incident) +
          realPartJointElectricTraceAmplitude
            (Complex.exp (configuration.reflected.boundaryExponent
                configuration.interface.plane p) •
              referencedMediumJointElectricTraceAmplitude configuration.interface.plane
                configuration.interface.negativeMedium configuration.reflected) -
        realPartJointElectricTraceAmplitude
          (Complex.exp (configuration.transmitted.boundaryExponent
              configuration.interface.plane p) •
            referencedMediumJointElectricTraceAmplitude configuration.interface.plane
              configuration.interface.positiveMedium configuration.transmitted) := by
  rw [jointElectricBoundaryCoefficients, jointElectricHarmonicSum_sub,
    jointElectricHarmonicSum_add, jointElectricHarmonicSum_single,
    jointElectricHarmonicSum_single, jointElectricHarmonicSum_single]

private lemma jointElectricHarmonicSum_boundaryCoefficients_eq_zero
    {configuration : PlanarDielectricWaveConfiguration}
    (h : configuration.IsElectricBoundary 0)
    (p : BoundaryParameter configuration.interface.plane) :
    jointElectricHarmonicSum configuration.jointElectricBoundaryCoefficients p = 0 := by
  rw [jointElectricHarmonicSum_boundaryCoefficients]
  exact sub_eq_zero.mpr (h.jointElectricBoundaryCharacter_sum_eq p)

/-!

## C. Boundary-law consequence

-/

namespace IsElectricBoundary

variable {configuration : PlanarDielectricWaveConfiguration}

/-- An electric planar boundary with zero free surface charge has zero signed,
exponent-aggregated joint electric coefficient map.

This is an aggregated coefficient identity: it does not assert that the incident, reflected, and
transmitted exponents or labeled amplitudes vanish or agree separately. -/
lemma jointElectricBoundaryCoefficients_eq_zero
    (h : configuration.IsElectricBoundary 0) :
    configuration.jointElectricBoundaryCoefficients = 0 := by
  apply (jointElectricHarmonicSum_eq_zero_iff_of_im_pos
    configuration.jointElectricBoundaryCoefficients
    (boundaryTimeProbe configuration.interface.plane)
    (jointElectricBoundaryCoefficients_im_pos configuration)).mp
  exact jointElectricHarmonicSum_boundaryCoefficients_eq_zero h

end IsElectricBoundary

variable {configuration : PlanarDielectricWaveConfiguration}

/-- The zero-charge electric planar boundary laws hold exactly when the signed,
exponent-aggregated joint electric coefficient map vanishes. -/
lemma isElectricBoundary_iff_jointElectricBoundaryCoefficients_eq_zero :
    configuration.IsElectricBoundary 0 ↔
      configuration.jointElectricBoundaryCoefficients = 0 := by
  constructor
  · exact fun h ↦ h.jointElectricBoundaryCoefficients_eq_zero
  · intro hCoefficients
    apply isElectricBoundary_iff_jointElectricBoundaryCharacter_sum_eq.mpr
    have hHarmonic :
        ∀ p : BoundaryParameter configuration.interface.plane,
          jointElectricHarmonicSum configuration.jointElectricBoundaryCoefficients p = 0 := by
      intro p
      rw [hCoefficients]
      simp [jointElectricHarmonicSum]
    intro p
    have hp := hHarmonic p
    rw [jointElectricHarmonicSum_boundaryCoefficients] at hp
    exact sub_eq_zero.mp hp

namespace IsLocalBoundary

variable {configuration : PlanarDielectricWaveConfiguration}
  {surfaceCurrent : PlanarFreeSurfaceCurrentDensity configuration.interface.plane}

/-- A full local boundary with zero free surface charge has zero signed,
exponent-aggregated joint electric coefficient map; the free surface current remains arbitrary. -/
lemma jointElectricBoundaryCoefficients_eq_zero
    (h : configuration.IsLocalBoundary 0 surfaceCurrent) :
    configuration.jointElectricBoundaryCoefficients = 0 :=
  h.isElectricBoundary.jointElectricBoundaryCoefficients_eq_zero

end IsLocalBoundary

end PlanarDielectricWaveConfiguration

end
end Optics
