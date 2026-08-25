/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Physlib.Optics.Components.ReflectionlessTwoPort

/-!
# Fixed-carrier matched propagation

## i. Overview

This file specifies a fixed-carrier, reflectionless propagation component on one finite mode
family. Its two reference planes use the same mode labels, and every mode acquires the common
complex coefficient

`a * exp (-I * φ)`,

represented as a real amplitude factor `a` times the circle phase at `-φ`.
`Parameters.IsValid` selects the canonical passive range `0 ≤ a ≤ 1`. The independently
stated behavior is

`bL = t • aR` and `bR = t • aL`.

The scattering realization specializes `ReflectionlessTwoPort` to the scalar transform `t I` in
both directions and is proved to realize that behavior exactly. Using the same coefficient in
both directions is part of this component model; it is not a reciprocity theorem.

"Matched" means only that the declared component has zero reflection, preserves the mode labels,
and does not mix modes between its two reference planes. It is not an impedance-matching
derivation. This is a fixed-carrier phase law, not a time delay: it asserts no frequency response,
group delay, dispersion, causality, bandwidth, or Laplace-domain behavior. It also asserts no
material realization, electromagnetic power normalization, absorption mechanism, or completeness
of physical loss channels. Modal-power classification is provided in a separate stacked module.

## ii. Key results

- `MatchedPropagation.transmissionCoefficient`: the common complex amplitude coefficient.
- `MatchedPropagation.behavior`: the independent two-direction propagation law.
- `MatchedPropagation.scattering`: its zero-reflection scattering realization.
- `MatchedPropagation.scattering_realizes_behavior`: exact graph equality.

## iii. Table of contents

- A. Fixed-carrier parameters and scalar transmission
- B. Independent behavioral specification
- C. Scattering realization

## iv. References

This reusable component law is Physlib-original and source-neutral. Comparison with DATE 2014 and
SysCon 2015 microring and continuity notation is deferred to a separately human-audited source
bridge.
-/

@[expose] public section

namespace Optics

noncomputable section

universe u

namespace MatchedPropagation

/-! ## A. Fixed-carrier parameters and scalar transmission -/

/-- Parameters of a fixed-carrier matched propagation component.

`amplitudeTransmission` is the retained normalized-modal-amplitude factor. Its square, rather than
the factor itself, scales normalized modal power. `carrierPathPhase` is the phase accumulated
between the two declared reference planes, represented modulo `2 * π`. The structure is total:
values outside `Parameters.IsValid` remain algebraically defined, but receive no passive-component
classification.
-/
structure Parameters where
  /-- The retained normalized-modal-amplitude factor. -/
  amplitudeTransmission : ℝ
  /-- The fixed-carrier path phase between the reference planes. -/
  carrierPathPhase : Real.Angle

/-- Physical parameter validity for the reduced fixed-carrier model.

The amplitude factor is nonnegative because a sign can be absorbed into the phase, and it is at
most one so the visible modeled channels do not gain amplitude. The phase is unrestricted.
-/
def Parameters.IsValid (p : Parameters) : Prop :=
  0 ≤ p.amplitudeTransmission ∧ p.amplitudeTransmission ≤ 1

/-- The unit-modulus fixed-carrier phase factor `exp (-I * φ)`.

The negative sign follows Physlib's positive-time realization convention. This factor is a
point-frequency phase, not a time delay.
-/
def carrierPhaseFactor (phase : Real.Angle) : ℂ :=
  ((-phase).toCircle : ℂ)

/-- The common complex amplitude-transmission coefficient `a * exp (-I * φ)`. -/
def transmissionCoefficient (p : Parameters) : ℂ :=
  (p.amplitudeTransmission : ℂ) * carrierPhaseFactor p.carrierPathPhase

/-- The same-mode scalar transmission transform `t I`. -/
def transmission (p : Parameters) (ι : Type u) : ModeTransform ι ι := by
  classical
  exact transmissionCoefficient p • 1

/-- The scalar transmission transform multiplies every modal amplitude by its coefficient. -/
lemma transmission_toLinearMap_apply [Fintype ι] [DecidableEq ι] (p : Parameters)
    (amplitude : ModeAmplitude ι) :
    (transmission p ι).toLinearMap amplitude = transmissionCoefficient p • amplitude := by
  classical
  have hTransmission : transmission p ι =
      transmissionCoefficient p • (1 : ModeTransform ι ι) := by
    ext output input
    by_cases h : output = input <;> simp [transmission, h]
  rw [hTransmission]
  simp only [ModeTransform.toLinearMap, Matrix.toEuclideanLin,
    map_smul, Matrix.toLpLin_one, LinearMap.smul_apply, LinearMap.id_apply]

/-! ## B. Independent behavioral specification -/

/-- The independent fixed-carrier matched-propagation behavior.

It is defined from the two directional scalar transmission laws, not from the scattering matrix.
-/
def behavior [Fintype ι] [DecidableEq ι] (p : Parameters) :
    TwoPortScatteringBehavior ι ι :=
  ReflectionlessTwoPort.behavior (transmission p ι) (transmission p ι)

/-- Behavior membership is exactly the two declared directional propagation equations. -/
@[simp]
lemma mem_behavior_iff [Fintype ι] [DecidableEq ι] (p : Parameters)
    (incident : ModeAmplitude (Incident ι ⊕ Incident ι))
    (outgoing : ModeAmplitude (Outgoing ι ⊕ Outgoing ι)) :
    (incident, outgoing) ∈ behavior p ↔
      outgoing =
        (ModeAmplitude.reindex Outgoing.channelEquiv.symm
          (transmissionCoefficient p •
            ModeAmplitude.reindex Incident.channelEquiv incident.restrictInr)).directSum
        (ModeAmplitude.reindex Outgoing.channelEquiv.symm
          (transmissionCoefficient p •
            ModeAmplitude.reindex Incident.channelEquiv incident.restrictInl)) := by
  rw [behavior, ReflectionlessTwoPort.mem_behavior_iff]
  simp only [transmission_toLinearMap_apply]

/-! ## C. Scattering realization -/

/-- The zero-reflection scattering realization of fixed-carrier matched propagation. -/
def scattering (p : Parameters) (ι : Type u) : ScatteringMatrix (ι ⊕ ι) :=
  ReflectionlessTwoPort.scattering (transmission p ι) (transmission p ι)

/-- The realized scattering matrix crosses the two incident sides and applies the common
transmission coefficient. -/
lemma scattering_toLinearMap_apply [Fintype ι] [DecidableEq ι] (p : Parameters)
    (left right : ModeAmplitude ι) :
    (scattering p ι).toModeTransform.toLinearMap (left.directSum right) =
      (transmissionCoefficient p • right).directSum
        (transmissionCoefficient p • left) := by
  rw [scattering, ReflectionlessTwoPort.scattering_toLinearMap_apply,
    transmission_toLinearMap_apply, transmission_toLinearMap_apply]

/-- The typed two-port scattering adapter obeys the two explicit directional propagation laws. -/
lemma scattering_toTwoPortScatteringTransform_toLinearMap_apply
    [Fintype ι] [DecidableEq ι] (p : Parameters)
    (incident : ModeAmplitude (Incident ι ⊕ Incident ι)) :
    (scattering p ι).toTwoPortScatteringTransform.toLinearMap incident =
      (ModeAmplitude.reindex Outgoing.channelEquiv.symm
        (transmissionCoefficient p •
          ModeAmplitude.reindex Incident.channelEquiv incident.restrictInr)).directSum
      (ModeAmplitude.reindex Outgoing.channelEquiv.symm
        (transmissionCoefficient p •
          ModeAmplitude.reindex Incident.channelEquiv incident.restrictInl)) := by
  rw [scattering,
    ReflectionlessTwoPort.scattering_toTwoPortScatteringTransform_toLinearMap_apply]
  simp only [ReflectionlessTwoPort.outputMap_apply, transmission_toLinearMap_apply]

/-- The scattering matrix realizes the independently specified fixed-carrier behavior exactly. -/
lemma scattering_realizes_behavior [Fintype ι] [DecidableEq ι] (p : Parameters) :
    (scattering p ι).toTwoPortScatteringBehavior = behavior p := by
  exact ReflectionlessTwoPort.scattering_realizes_behavior
    (transmission p ι) (transmission p ι)

end MatchedPropagation

end

end Optics
