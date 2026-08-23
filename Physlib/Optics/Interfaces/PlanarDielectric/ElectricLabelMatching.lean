/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Interfaces.PlanarDielectric.ElectricCollision

/-!
# Conditional electric label matching at a planar dielectric boundary

## i. Overview

This file turns the exponent-aggregated joint electric coefficient identity at a planar dielectric
boundary into a conditional conclusion about the three wave labels. The guard is the exact negative-
side coefficient carried by the incident boundary exponent:
`Aᵢ + if Lᵣ = Lᵢ then Aᵣ else 0`. Thus it is `Aᵢ + Aᵣ` when the reflected and
incident exponents coincide, but only `Aᵢ` when they differ.

For a zero-charge electric boundary, if this incident-key aggregate is nonzero, evaluating the
zero coefficient map at the incident key forces the transmitted exponent to equal the incident
exponent. Evaluation at the reflected key then proves that the reflected electric amplitude is
zero or its exponent also equals the incident exponent. In exactly those branches, evaluation at
the incident key gives the stored-point-referenced joint tangential-`E`/normal-`D` coefficient
balance `Aₜ = Aᵢ + Aᵣ`. The reflected disjunction is a conclusion, not an additional
hypothesis.
A full local boundary inherits this result through its electric projection.

The conditional guard is essential. A nonzero incident amplitude is insufficient when an
equal-exponent reflected amplitude cancels it. The unconditional sum `Aᵢ + Aᵣ` is also
insufficient when the reflected exponent differs and its contribution instead matches the
transmitted key. A zero reflected amplitude leaves its exponent as unconstrained dummy data, which
is why the theorem preserves the zero-reflection branch.

The resulting exponent equalities can be decoded by `boundaryExponent_eq_iff` into frequency and
tangent-pairing equalities. They do not give full wave-vector equality. This file assigns no
propagation direction or one-sided-illumination semantics and proves no Maxwell/on-shell condition,
material dispersion, branch choice, Fresnel coefficient, irradiance, or power result. Its
coefficient balance is not an equality of raw electric phasors or full electromagnetic amplitudes.

## ii. Key results

- `PlanarDielectricWaveConfiguration.incidentExponentJointElectricAggregate`: the exact
  negative-side coefficient at the incident boundary exponent.
- `PlanarDielectricWaveConfiguration.IsElectricBoundary.jointElectricBoundaryLabelMatching`:
  transmitted/incident exponent equality, the zero-reflection-preserving reflected alternative,
  and referenced joint-coefficient balance.

## iii. Table of contents

- A. Incident-key aggregate
- B. Three-key coefficient algebra
- C. Conditional boundary label matching

## iv. References

This module specializes Physlib's exact planar electric coefficient identity. No external
formal-development source is copied or translated here.
-/

@[expose] public section

namespace Optics

open Electromagnetism Electromagnetism.ThreeDimension
open Electromagnetism.ThreeDimension.ComplexMonochromaticPlaneWave

noncomputable section

namespace PlanarDielectricWaveConfiguration

/-!

## A. Incident-key aggregate

-/

open Classical in
/-- The total negative-side referenced joint electric amplitude carried by the incident boundary
exponent.

The reflected contribution is included exactly when its boundary exponent equals the incident
one. This is the noncancellation guard used for label matching; it is not unconditionally the sum
of the two negative-side labeled amplitudes. -/
def incidentExponentJointElectricAggregate
    (configuration : PlanarDielectricWaveConfiguration) : JointElectricTraceAmplitude :=
  referencedMediumJointElectricTraceAmplitude configuration.interface.plane
      configuration.interface.negativeMedium configuration.incident +
    if configuration.reflected.boundaryExponent configuration.interface.plane =
        configuration.incident.boundaryExponent configuration.interface.plane then
      referencedMediumJointElectricTraceAmplitude configuration.interface.plane
        configuration.interface.negativeMedium configuration.reflected
    else 0

/-!

## B. Three-key coefficient algebra

-/

private lemma threeCoefficientCollision
    {κ A : Type*} [DecidableEq κ] [AddCommGroup A]
    (Lᵢ Lᵣ Lₜ : κ) (Aᵢ Aᵣ Aₜ : A)
    (hCoefficients :
      Finsupp.single Lᵢ Aᵢ + Finsupp.single Lᵣ Aᵣ - Finsupp.single Lₜ Aₜ = 0)
    (hAggregate : (Aᵢ + if Lᵣ = Lᵢ then Aᵣ else 0) ≠ 0) :
    Lₜ = Lᵢ ∧ (Aᵣ = 0 ∨ Lᵣ = Lᵢ) ∧ Aₜ = Aᵢ + Aᵣ := by
  have hti : Lₜ = Lᵢ := by
    by_contra hti
    have hAtIncident := DFunLike.congr_fun hCoefficients Lᵢ
    apply hAggregate
    simpa [Finsupp.single_apply, hti] using hAtIncident
  have hbranch : Aᵣ = 0 ∨ Lᵣ = Lᵢ := by
    by_cases hri : Lᵣ = Lᵢ
    · exact Or.inr hri
    · left
      have hAtReflected := DFunLike.congr_fun hCoefficients Lᵣ
      simpa [Finsupp.single_apply, hti, hri] using hAtReflected
  have hamplitude : Aₜ = Aᵢ + Aᵣ := by
    have hAtIncident := DFunLike.congr_fun hCoefficients Lᵢ
    rcases hbranch with hrzero | hri
    · have hbalance : Aᵢ - Aₜ = 0 := by
        simpa [Finsupp.single_apply, hti, hrzero] using hAtIncident
      simpa [hrzero] using (sub_eq_zero.mp hbalance).symm
    · have hbalance : Aᵢ + Aᵣ - Aₜ = 0 := by
        simpa [Finsupp.single_apply, hti, hri] using hAtIncident
      exact (sub_eq_zero.mp hbalance).symm
  exact ⟨hti, hbranch, hamplitude⟩

/-!

## C. Conditional boundary label matching

-/

namespace IsElectricBoundary

variable {configuration : PlanarDielectricWaveConfiguration}

/-- A zero-free-surface-charge electric boundary with a nonzero incident-key aggregate matches the
transmitted boundary exponent to the incident one, and either removes the reflected electric
amplitude or matches its exponent too.

The final equality is a stored-point-referenced, medium-dependent joint tangential-`E`/normal-`D`
coefficient balance. No surface current occurs in the premise. -/
lemma jointElectricBoundaryLabelMatching
    (h : configuration.IsElectricBoundary 0)
    (hAggregate : configuration.incidentExponentJointElectricAggregate ≠ 0) :
    configuration.transmitted.boundaryExponent configuration.interface.plane =
        configuration.incident.boundaryExponent configuration.interface.plane ∧
      (configuration.reflected.electricAmplitude = 0 ∨
        configuration.reflected.boundaryExponent configuration.interface.plane =
          configuration.incident.boundaryExponent configuration.interface.plane) ∧
      referencedMediumJointElectricTraceAmplitude configuration.interface.plane
          configuration.interface.positiveMedium configuration.transmitted =
        referencedMediumJointElectricTraceAmplitude configuration.interface.plane
            configuration.interface.negativeMedium configuration.incident +
          referencedMediumJointElectricTraceAmplitude configuration.interface.plane
            configuration.interface.negativeMedium configuration.reflected := by
  classical
  let Lᵢ := configuration.incident.boundaryExponent configuration.interface.plane
  let Lᵣ := configuration.reflected.boundaryExponent configuration.interface.plane
  let Lₜ := configuration.transmitted.boundaryExponent configuration.interface.plane
  let Aᵢ := referencedMediumJointElectricTraceAmplitude configuration.interface.plane
    configuration.interface.negativeMedium configuration.incident
  let Aᵣ := referencedMediumJointElectricTraceAmplitude configuration.interface.plane
    configuration.interface.negativeMedium configuration.reflected
  let Aₜ := referencedMediumJointElectricTraceAmplitude configuration.interface.plane
    configuration.interface.positiveMedium configuration.transmitted
  have hCollision := threeCoefficientCollision Lᵢ Lᵣ Lₜ Aᵢ Aᵣ Aₜ
    (by simpa [jointElectricBoundaryCoefficients, Lᵢ, Lᵣ, Lₜ, Aᵢ, Aᵣ, Aₜ] using
      h.jointElectricBoundaryCoefficients_eq_zero)
    (by simpa [incidentExponentJointElectricAggregate, Lᵢ, Lᵣ, Aᵢ, Aᵣ] using hAggregate)
  refine ⟨by simpa [Lᵢ, Lₜ] using hCollision.1, ?_,
    by simpa [Aᵢ, Aᵣ, Aₜ] using hCollision.2.2⟩
  rcases hCollision.2.1 with hrzero | hrexp
  · exact Or.inl ((referencedMediumJointElectricTraceAmplitude_eq_zero_iff
      configuration.interface.plane configuration.interface.negativeMedium
        configuration.reflected).mp (by simpa [Aᵣ] using hrzero))
  · exact Or.inr (by simpa [Lᵢ, Lᵣ] using hrexp)

end IsElectricBoundary

namespace IsLocalBoundary

variable {configuration : PlanarDielectricWaveConfiguration}
  {surfaceCurrent : PlanarFreeSurfaceCurrentDensity configuration.interface.plane}

/-- A zero-free-surface-charge full local boundary with a nonzero incident-key aggregate matches
the active electric boundary labels and their referenced joint coefficients. -/
lemma jointElectricBoundaryLabelMatching
    (h : configuration.IsLocalBoundary 0 surfaceCurrent)
    (hAggregate : configuration.incidentExponentJointElectricAggregate ≠ 0) :
    configuration.transmitted.boundaryExponent configuration.interface.plane =
        configuration.incident.boundaryExponent configuration.interface.plane ∧
      (configuration.reflected.electricAmplitude = 0 ∨
        configuration.reflected.boundaryExponent configuration.interface.plane =
          configuration.incident.boundaryExponent configuration.interface.plane) ∧
      referencedMediumJointElectricTraceAmplitude configuration.interface.plane
          configuration.interface.positiveMedium configuration.transmitted =
        referencedMediumJointElectricTraceAmplitude configuration.interface.plane
            configuration.interface.negativeMedium configuration.incident +
          referencedMediumJointElectricTraceAmplitude configuration.interface.plane
            configuration.interface.negativeMedium configuration.reflected :=
  h.isElectricBoundary.jointElectricBoundaryLabelMatching hAggregate

end IsLocalBoundary

end PlanarDielectricWaveConfiguration

end
end Optics
