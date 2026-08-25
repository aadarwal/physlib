/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.HarmonicFlux.ModeSynthesis

/-!
# Aperture-flux normalization of finite optical mode families

## i. Overview

This file declares when a finite family of supplied harmonic field profiles is pairwise integrable,
mutually flux-orthogonal, and unit normalized relative to the stored normal on an explicitly
measured profile domain. An explicitly declared wave role selects positive signed flux for
outgoing profiles and negative signed flux for incident profiles.

The coherent cross-term expansion then proves, rather than stores, that synthesis identifies
outgoing integrated normal flux with `ModeAmplitude.power` and identifies the negative of incident
integrated normal flux with that same nonnegative coordinate power. These conclusions hold only on
the synthesis image of the supplied finite family; they assert no electromagnetic modal
completeness or absence of omitted radiation and absorption channels.

## ii. Key results

- `IsApertureFluxOrthonormal.pairing_modeSynthesis`: normalized pairing is the role sign times the
  modal Hermitian pairing.
- `IsApertureFluxOrthonormal.integratedMeanNormalFlux_modeSynthesis`: exact signed-flux formula.
- `IsApertureFluxOrthonormal.outgoing_modeSynthesis_power`: outgoing flux equals modal power.
- `IsApertureFluxOrthonormal.incident_modeSynthesis_power`: negative incident flux equals power.

## iii. Table of contents

- A. Declared wave roles
- B. Flux-orthogonal normalized families
- C. Modal pairing and power bridges

## iv. References

This bridge is Physlib-original relative to the audited HOL optics corpus. A role is declared, not
inferred from the geometric side or phase-vector direction. Common carrier frequency and Maxwell
qualification are not fields of the predicate and must be supplied by a later physical connector.
The results do not derive interface boundary laws, modal completeness, reciprocity, or device
losslessness.
-/

@[expose] public section

namespace Optics

open InnerProductSpace MeasureTheory
open scoped ComplexConjugate

noncomputable section

/-!

## A. Declared wave roles

-/

/-- A declared wave role relative to a cross-section whose stored normal is taken as outward.

The constructors do not infer a wave role from plane geometry. They select the sign required of a
separately supplied normalized family. -/
inductive ApertureWaveRole
  | incident
  | outgoing
  deriving DecidableEq

namespace ApertureWaveRole

/-- Signed normal-flux normalization selected by a declared aperture wave role. -/
@[simp]
def normalFluxSign : ApertureWaveRole → ℝ
  | incident => -1
  | outgoing => 1

end ApertureWaveRole

namespace HarmonicFieldProfile

/-!

## B. Flux-orthogonal normalized families

-/

/-- Pairwise integrable, mutually flux-orthogonal, unit-normalized profiles of one declared role.

The pairing uses magnetic field strength `H`, not magnetic induction `B`. Common carrier frequency,
Maxwell qualification, and geometric-aperture interpretation are external requirements, not fields
of this predicate. The predicate does not say that the family spans arbitrary fields. -/
def IsApertureFluxOrthonormal {A ι : Type*} [MeasurableSpace A]
    (measure : Measure A) (plane : Space.OrientedAffineHyperplane 3)
    (role : ApertureWaveRole) (modes : ι → HarmonicFieldProfile A) : Prop :=
  (∀ i j, IsSignedNormalFluxIntegrable measure plane (modes i) (modes j)) ∧
  (∀ i, integratedMeanNormalFlux measure plane (modes i) = role.normalFluxSign) ∧
  ∀ i j, i ≠ j → signedNormalFluxPairing measure plane (modes i) (modes j) = 0

namespace IsApertureFluxOrthonormal

/-!

## C. Modal pairing and power bridges

-/

/-- Synthesis by a flux-orthonormal family turns the field pairing into the role sign times the
modal Hermitian pairing, with reversed arguments because the field pairing is linear first. -/
lemma pairing_modeSynthesis {A ι : Type*} [MeasurableSpace A] [Fintype ι]
    {measure : Measure A} {plane : Space.OrientedAffineHyperplane 3}
    {role : ApertureWaveRole} {modes : ι → HarmonicFieldProfile A}
    (h : IsApertureFluxOrthonormal measure plane role modes)
    (first second : ModeAmplitude ι) :
    signedNormalFluxPairing measure plane (modeSynthesis modes first)
        (modeSynthesis modes second) =
      (role.normalFluxSign : ℂ) * inner ℂ second first := by
  classical
  rw [signedNormalFluxPairing_modeSynthesis measure plane modes h.1]
  rw [PiLp.inner_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  calc
    (∑ j, (first i * star (second j)) *
        signedNormalFluxPairing measure plane (modes i) (modes j)) =
        (first i * star (second i)) *
          signedNormalFluxPairing measure plane (modes i) (modes i) := by
      apply Finset.sum_eq_single i
      · intro j _ hji
        rw [h.2.2 i j (Ne.symm hji)]
        ring
      · simp
    _ = (role.normalFluxSign : ℂ) *
        star (second i) * first i := by
      rw [signedNormalFluxPairing_self, h.2.1]
      ring
    _ = (role.normalFluxSign : ℂ) * ⟪second i, first i⟫_ℂ := by
      rw [RCLike.inner_apply]
      change (role.normalFluxSign : ℂ) * star (second i) * first i =
        (role.normalFluxSign : ℂ) * (first i * star (second i))
      ring

/-- The integrated mean normal flux of a synthesized normalized family is its role sign times
the nonnegative modal coordinate power. -/
lemma integratedMeanNormalFlux_modeSynthesis {A ι : Type*}
    [MeasurableSpace A] [Fintype ι]
    {measure : Measure A} {plane : Space.OrientedAffineHyperplane 3}
    {role : ApertureWaveRole} {modes : ι → HarmonicFieldProfile A}
    (h : IsApertureFluxOrthonormal measure plane role modes)
    (amplitude : ModeAmplitude ι) :
    integratedMeanNormalFlux measure plane (modeSynthesis modes amplitude) =
      role.normalFluxSign * amplitude.power := by
  apply Complex.ofReal_injective
  rw [← signedNormalFluxPairing_self, h.pairing_modeSynthesis,
    ← ModeAmplitude.ofReal_power_eq_inner_self]
  norm_cast

/-- For a family declared outgoing relative to the stored outward normal, integrated mean normal
flux equals normalized modal power on the family's synthesis image. -/
lemma outgoing_modeSynthesis_power {A ι : Type*} [MeasurableSpace A] [Fintype ι]
    {measure : Measure A} {plane : Space.OrientedAffineHyperplane 3}
    {modes : ι → HarmonicFieldProfile A}
    (h : IsApertureFluxOrthonormal measure plane .outgoing modes)
    (amplitude : ModeAmplitude ι) :
    integratedMeanNormalFlux measure plane (modeSynthesis modes amplitude) =
      amplitude.power := by
  simpa using h.integratedMeanNormalFlux_modeSynthesis amplitude

/-- For a family declared incident relative to the stored outward normal, the negative integrated
mean normal flux equals normalized modal power on the family's synthesis image. -/
lemma incident_modeSynthesis_power {A ι : Type*} [MeasurableSpace A] [Fintype ι]
    {measure : Measure A} {plane : Space.OrientedAffineHyperplane 3}
    {modes : ι → HarmonicFieldProfile A}
    (h : IsApertureFluxOrthonormal measure plane .incident modes)
    (amplitude : ModeAmplitude ι) :
    -integratedMeanNormalFlux measure plane (modeSynthesis modes amplitude) =
      amplitude.power := by
  have hflux := h.integratedMeanNormalFlux_modeSynthesis amplitude
  simpa using congrArg Neg.neg hflux

end IsApertureFluxOrthonormal

end HarmonicFieldProfile

end

end Optics
