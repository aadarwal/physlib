/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module
public import Physlib.Optics.Systems.Microring.ObservablesPower

/-!
# SysCon'15 source bridges for microring transfer formulas

## i. Overview

This file records the SysCon'15 parameter and port dictionary needed to compare Physlib's
explicit microring network with the source statements catalogued at `HOL-CORPUS.md:226-274` in
the parity audit checkout. SysCon's drop model uses `(phi, x_r, k1, k2, u1, u2)`.

SysCon Def. 9 has the same two half arcs and the same `-I * k` cross phase as Physlib
(`HOL-CORPUS.md:244-247` and
`Physlib/Optics/Components/DirectionalCoupler.lean:68-70`). Its bridge therefore changes only
names and port order.

The source writes rejection ratios as `10 log` without an audited logarithm base
(`HOL-CORPUS.md:246-249`). Results below keep the base as data, then separately identify the
base-ten and natural-log readings. No unverified base is silently selected.

Exact parity with SysCon Thm. 6 is withheld. The corpus survey records that theorem only as a
closed form and transcribes no expression (`HOL-CORPUS.md:248`). A previously recorded
transcription of uncertain provenance instead used the denominator
`(1-u1*u2*x_r)^2 + 4*k1*k2*exp(-phi)*sin(phi/2)^2`. At the exact rational fixture
`u1=u2=4/5`, `k1=k2=3/5`, `x_r=9/16`, and `phi=pi`,
`sourceBridgeRegression_disputedDenominator_ne_amplitudeDenominator` proves that this candidate
is `256/625 + (36/25)*exp(-pi)`, whereas the norm-square denominator is `1156/625`. No
available source reading classifies the discrepancy as a paper error, script error, or
transcription error.

The amplitude-derived denominator is proved here from Thm. 5 and yields Thm. 7's power ratio
when evaluated according to Def. 11. Agreement of those two independently transcribed source
results is evidence for that denominator, not a classification of the unverified Thm. 6
statement.

## ii. Key results

- `sysConDropTransfer_eq_dropTransfer`: the SysCon drop formula and the S2 amplitude.
- `sysConDropTransfer_eq_n5Response`: the source formula and proof-gated N5 response entry.
- `sysConDropPower_eq_n5ResponsePower`: Def. 10 and squared norm of that N5 response entry.
- `sysConDropPower_eq_amplitudePowerDenominator`: Def. 10 derived from Thm. 5.
- `sysConRejectionRatioInBase_eq_closedForm`: Def. 11 and Thm. 7 for an explicit log base.
- `sysConRejectionClosedForm_base_ten`: the base-ten interpretation of SysCon Thm. 7.

## iii. Table of contents

- C. SysCon'15 drop response and power
- D. Log-base-explicit rejection ratios

## iv. References and non-claims

SysCon Defs. 9--11 and Thms. 5--7 are summarized at `HOL-CORPUS.md:244-249`.

The source predicates store their transfer formulas; this file does not recast them as component
derivations. It also does not assert that every source record maps to N7-valid components.
Physical response meaning on the Physlib side remains gated by N5 well-posedness and N7
validity. No reciprocity, omitted-loss completeness, time-domain causality, bandwidth,
dispersion, or measurement-validation claim is made. SysCon contains no formal
through-response result (`HOL-CORPUS.md:251-269`).

`sysConDropResponseSeries` is a total Mathlib `tsum`; it has feedback-series or N5 response
meaning only under `SysConParameters.IsContractive` and the stated attenuation gate. The
SysCon transfer quotients and their norm-square powers are also totalized at zero denominator.
Their algebraic identities remain meaningful there, but an N5 response claim requires the
displayed nonzero-denominator or contraction gate. Exact printed-Thm.-6 parity and the source's
unaudited logarithm base are not claimed.
-/
@[expose] public section

namespace Optics

noncomputable section

namespace MicroringSourceBridge
/-! ## C. SysCon'15 drop response and power -/

/-- The six real SysCon'15 drop-response parameters from `HOL-CORPUS.md:244-249`. -/
structure SysConParameters where
  /-- Source round-trip phase `phi`. -/
  phase : ℝ
  /-- Source scalar `x_r`, mapped below to Physlib's round-trip field attenuation. -/
  fieldAttenuation : ℝ
  /-- Source first cross amplitude `k1`. -/
  inputCrossAmplitude : ℝ
  /-- Source second cross amplitude `k2`. -/
  dropCrossAmplitude : ℝ
  /-- Source first through amplitude `u1`. -/
  inputThroughAmplitude : ℝ
  /-- Source second through amplitude `u2`. -/
  dropThroughAmplitude : ℝ

/-- The SysCon dictionary into Physlib's add-drop parameters.

Def. 9 uses the same `sqrt(x_r)` per half arc, `phi/2` per half phase, and `-j*k` cross gauge;
see `HOL-CORPUS.md:244-247`. Mapping `x_r` to a round-trip field attenuation is Physlib's
inference from those two half-arc factors, not a source classification of `x_r` as field or power.
-/
def SysConParameters.toAddDrop (p : SysConParameters) : AddDrop.Parameters where
  inputThroughAmplitude := p.inputThroughAmplitude
  inputCrossAmplitude := p.inputCrossAmplitude
  dropThroughAmplitude := p.dropThroughAmplitude
  dropCrossAmplitude := p.dropCrossAmplitude
  fieldAttenuation := p.fieldAttenuation
  roundTripPhase := p.phase

/-- The SysCon dictionary changes names only and preserves all six scalar values. -/
lemma SysConParameters.toAddDrop_data (p : SysConParameters) :
    p.toAddDrop.inputThroughAmplitude = p.inputThroughAmplitude ∧
      p.toAddDrop.inputCrossAmplitude = p.inputCrossAmplitude ∧
      p.toAddDrop.dropThroughAmplitude = p.dropThroughAmplitude ∧
      p.toAddDrop.dropCrossAmplitude = p.dropCrossAmplitude ∧
      p.toAddDrop.fieldAttenuation = p.fieldAttenuation ∧
      p.toAddDrop.roundTripPhase = p.phase :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- SysCon Def. 9's repeated half-arc factor `exp(-j*phi/2)*sqrt(x_r)`. -/
def SysConParameters.halfArcCoefficient (p : SysConParameters) : ℂ :=
  MatchedPropagation.carrierPhaseFactor (((p.phase / 2 : ℝ)) : Real.Angle) *
    Real.sqrt p.fieldAttenuation

/-- SysCon's real circulation magnitude before its unit-modulus phase factor. -/
def SysConParameters.realLoopGain (p : SysConParameters) : ℝ :=
  p.inputThroughAmplitude * p.dropThroughAmplitude * p.fieldAttenuation

/-- SysCon's complete circulation factor `u1*u2*exp(-j*phi)*x_r`. -/
def SysConParameters.loopGain (p : SysConParameters) : ℂ :=
  (p.inputThroughAmplitude : ℂ) * (p.dropThroughAmplitude : ℂ) *
    MatchedPropagation.carrierPhaseFactor ((p.phase : ℝ) : Real.Angle) *
      p.fieldAttenuation

/-- SysCon Thm. 5's source contraction hypothesis `norm(x_r*u1*u2) < 1`.

All three factors are real in Def. 9, so the scalar norm is the real absolute value.
-/
def SysConParameters.IsContractive (p : SysConParameters) : Prop :=
  |p.realLoopGain| < 1

/-- The source contraction gate is the complex geometric-series gate for the phased loop gain. -/
lemma SysConParameters.IsContractive.norm_loopGain_lt_one {p : SysConParameters}
    (hp : p.IsContractive) : ‖p.loopGain‖ < 1 := by
  rw [SysConParameters.IsContractive, SysConParameters.realLoopGain] at hp
  simpa [SysConParameters.loopGain, MatchedPropagation.carrierPhaseFactor,
    norm_mul, abs_mul, mul_comm, mul_left_comm, mul_assoc] using hp

/-- SysCon Thm. 5's displayed feedback denominator (`HOL-CORPUS.md:247`). -/
def SysConParameters.denominator (p : SysConParameters) : ℂ :=
  1 - p.loopGain

/-- The nonzero-denominator gate required to interpret the SysCon quotient as an N5 response. -/
def SysConParameters.HasNonzeroDenominator (p : SysConParameters) : Prop :=
  p.denominator ≠ 0

/-- SysCon Thm. 5's closed-form drop amplitude (`HOL-CORPUS.md:247`). -/
def sysConDropTransfer (p : SysConParameters) : ℂ :=
  -((p.inputCrossAmplitude : ℂ) * (p.dropCrossAmplitude : ℂ) *
      MatchedPropagation.carrierPhaseFactor (((p.phase / 2 : ℝ)) : Real.Angle) *
        Real.sqrt p.fieldAttenuation) / p.denominator

/-- SysCon Def. 9 expanded as its totalized multiple-circulation scalar series.

The object is a Mathlib `tsum` at every parameter value. It has the source feedback-series meaning
only under `SysConParameters.IsContractive`.
-/
def sysConDropResponseSeries (p : SysConParameters) : ℂ :=
  (-Complex.I * p.inputCrossAmplitude) * p.halfArcCoefficient *
    (∑' circulation : ℕ, p.loopGain ^ circulation) *
      (-Complex.I * p.dropCrossAmplitude)

/-- Under the exact source contraction gate, the Def. 9 series is summable. -/
lemma sysConDropResponseSeries_summable (p : SysConParameters)
    (hContractive : p.IsContractive) :
    Summable (fun circulation : ℕ => p.loopGain ^ circulation) :=
  summable_geometric_of_norm_lt_one hContractive.norm_loopGain_lt_one

/-- SysCon Thm. 5: the convergent Def. 9 series equals its displayed quotient. -/
theorem sysConDropResponseSeries_eq_transfer (p : SysConParameters)
    (_hAttenuation : 0 < p.fieldAttenuation) (hContractive : p.IsContractive) :
    sysConDropResponseSeries p = sysConDropTransfer p := by
  rw [sysConDropResponseSeries, sysConDropTransfer,
    tsum_geometric_of_norm_lt_one hContractive.norm_loopGain_lt_one]
  simp only [SysConParameters.halfArcCoefficient,
    SysConParameters.denominator]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Nonnegative `x_r` makes the mapped first arc exactly the SysCon half-arc factor. -/
lemma SysConParameters.toAddDrop_firstArcCoefficient (p : SysConParameters) :
    p.toAddDrop.firstArcCoefficient =
      (Real.sqrt p.fieldAttenuation : ℂ) *
        MatchedPropagation.carrierPhaseFactor (((p.phase / 2 : ℝ)) : Real.Angle) := by
  rfl

/-- Nonnegative `x_r` makes the mapped round trip exactly the SysCon loop field factor. -/
lemma SysConParameters.toAddDrop_roundTripCoefficient (p : SysConParameters)
    (hAttenuation : 0 ≤ p.fieldAttenuation) :
    p.toAddDrop.roundTripCoefficient =
      (p.fieldAttenuation : ℂ) *
        MatchedPropagation.carrierPhaseFactor ((p.phase : ℝ) : Real.Angle) := by
  exact p.toAddDrop.roundTripCoefficient_eq_fieldAttenuation hAttenuation

/-- Under nonnegative `x_r`, the SysCon and Physlib feedback denominators coincide. -/
lemma SysConParameters.toAddDrop_denominator (p : SysConParameters)
    (hAttenuation : 0 ≤ p.fieldAttenuation) :
    p.toAddDrop.denominator = p.denominator := by
  rw [AddDrop.Parameters.denominator, AddDrop.Parameters.loopGain,
    p.toAddDrop_roundTripCoefficient hAttenuation]
  simp only [SysConParameters.toAddDrop, SysConParameters.denominator,
    SysConParameters.loopGain]
  ring

/-- Under nonnegative attenuation, the mapped N5 loop gain is the SysCon phased loop gain. -/
lemma SysConParameters.toAddDrop_loopGain (p : SysConParameters)
    (hAttenuation : 0 ≤ p.fieldAttenuation) :
    p.toAddDrop.loopGain = p.loopGain := by
  rw [AddDrop.Parameters.loopGain, p.toAddDrop_roundTripCoefficient hAttenuation]
  simp only [SysConParameters.toAddDrop, SysConParameters.loopGain]
  ring

/-- The exact SysCon source contraction gate implies the mapped S2 contraction gate. -/
lemma SysConParameters.IsContractive.toAddDrop {p : SysConParameters}
    (hContractive : p.IsContractive) (hAttenuation : 0 ≤ p.fieldAttenuation) :
    p.toAddDrop.IsContractive := by
  rw [AddDrop.Parameters.IsContractive, p.toAddDrop_loopGain hAttenuation]
  exact hContractive.norm_loopGain_lt_one

/-- Under nonnegative `x_r`, the SysCon and Physlib solve gates coincide. -/
lemma SysConParameters.hasNonzeroDenominator_iff (p : SysConParameters)
    (hAttenuation : 0 ≤ p.fieldAttenuation) :
    p.HasNonzeroDenominator ↔ p.toAddDrop.HasNonzeroDenominator := by
  rw [SysConParameters.HasNonzeroDenominator, AddDrop.Parameters.HasNonzeroDenominator,
    p.toAddDrop_denominator hAttenuation]

/-- SysCon Thm. 5's closed form is exactly the S2 add-drop amplitude under the name dictionary. -/
theorem sysConDropTransfer_eq_dropTransfer (p : SysConParameters)
    (hAttenuation : 0 ≤ p.fieldAttenuation) :
    sysConDropTransfer p = AddDrop.dropTransfer p.toAddDrop := by
  rw [AddDrop.dropTransfer_eq_standard, sysConDropTransfer,
    AddDrop.standardDropTransfer, p.toAddDrop_denominator hAttenuation,
    p.toAddDrop_firstArcCoefficient]
  simp only [SysConParameters.toAddDrop]
  ring

/-- SysCon Thm. 5's amplitude is the proof-gated N5 input-to-drop response entry. -/
theorem sysConDropTransfer_eq_n5Response (p : SysConParameters)
    (hAttenuation : 0 ≤ p.fieldAttenuation)
    (hDenominator : p.HasNonzeroDenominator) :
    sysConDropTransfer p =
      (AddDrop.netlist p.toAddDrop).responseTransform
        (AddDrop.isWellPosed_of_hasNonzeroDenominator p.toAddDrop
          ((p.hasNonzeroDenominator_iff hAttenuation).mp hDenominator))
        (Outgoing.mk (AddDrop.dropChannel p.toAddDrop))
        (Incident.mk (AddDrop.inputChannel p.toAddDrop)) := by
  have hMapped := (p.hasNonzeroDenominator_iff hAttenuation).mp hDenominator
  have hResponse := AddDrop.responseTransform_entry_drop_input p.toAddDrop hMapped
  rw [sysConDropTransfer_eq_dropTransfer p hAttenuation]
  exact hResponse.symm

/-- SysCon Def. 9 and Thm. 5 agree with the proof-gated N5 response on the source domain. -/
theorem sysConDropResponseSeries_eq_n5Response (p : SysConParameters)
    (hAttenuation : 0 < p.fieldAttenuation) (hContractive : p.IsContractive) :
    sysConDropResponseSeries p =
      (AddDrop.netlist p.toAddDrop).responseTransform
        (AddDrop.isWellPosed_of_hasNonzeroDenominator p.toAddDrop
          (hContractive.toAddDrop hAttenuation.le).hasNonzeroDenominator)
        (Outgoing.mk (AddDrop.dropChannel p.toAddDrop))
        (Incident.mk (AddDrop.inputChannel p.toAddDrop)) := by
  rw [sysConDropResponseSeries_eq_transfer p hAttenuation hContractive]
  have hMapped := (hContractive.toAddDrop hAttenuation.le).hasNonzeroDenominator
  have hSource := (p.hasNonzeroDenominator_iff hAttenuation.le).mpr hMapped
  exact sysConDropTransfer_eq_n5Response p hAttenuation.le hSource

/-- SysCon Def. 10's power is squared complex norm of its drop response
(`HOL-CORPUS.md:245`). -/
def sysConDropPower (p : SysConParameters) : ℝ :=
  Complex.normSq (sysConDropTransfer p)

/-- SysCon Def. 10 is the squared norm of the proof-gated N5 input-to-drop response entry. -/
theorem sysConDropPower_eq_n5ResponsePower (p : SysConParameters)
    (hAttenuation : 0 ≤ p.fieldAttenuation)
    (hDenominator : p.HasNonzeroDenominator) :
    sysConDropPower p =
      Complex.normSq
        ((AddDrop.netlist p.toAddDrop).responseTransform
          (AddDrop.isWellPosed_of_hasNonzeroDenominator p.toAddDrop
            ((p.hasNonzeroDenominator_iff hAttenuation).mp hDenominator))
          (Outgoing.mk (AddDrop.dropChannel p.toAddDrop))
          (Incident.mk (AddDrop.inputChannel p.toAddDrop))) := by
  rw [sysConDropPower, sysConDropTransfer_eq_n5Response p hAttenuation hDenominator]

/-- SysCon Def. 10 is exactly Physlib's drop power under the parameter dictionary. -/
theorem sysConDropPower_eq_dropPower (p : SysConParameters)
    (hAttenuation : 0 ≤ p.fieldAttenuation) :
    sysConDropPower p = AddDrop.dropPower p.toAddDrop := by
  rw [sysConDropPower, AddDrop.dropPower,
    sysConDropTransfer_eq_dropTransfer p hAttenuation]

/-- The algebraically correct real closed form obtained from SysCon Thm. 5. -/
def sysConAnalyticDropPower (p : SysConParameters) : ℝ :=
  (p.inputCrossAmplitude * p.dropCrossAmplitude) ^ 2 * p.fieldAttenuation /
    (1 + (p.inputThroughAmplitude * p.dropThroughAmplitude *
      p.fieldAttenuation) ^ 2 -
        2 * p.inputThroughAmplitude * p.dropThroughAmplitude *
          p.fieldAttenuation * Real.cos p.phase)

/-- The power denominator obtained directly by norm-squaring SysCon Thm. 5. -/
def sysConAmplitudePowerDenominator (p : SysConParameters) : ℝ :=
  (1 - p.realLoopGain) ^ 2 +
    4 * p.realLoopGain * Real.sin (p.phase / 2) ^ 2

/-- A previously recorded Thm. 6 denominator whose provenance is presently uncertain.

`HOL-CORPUS.md:248` does not transcribe a Thm. 6 expression. This definition exists only to state
and test the discrepancy; it is not asserted to be the paper's or the HOL Light script's formula.
-/
def sysConDisputedPowerDenominator (p : SysConParameters) : ℝ :=
  (1 - p.realLoopGain) ^ 2 +
    4 * p.inputCrossAmplitude * p.dropCrossAmplitude * Real.exp (-p.phase) *
      Real.sin (p.phase / 2) ^ 2

/-- The quotient formed with the provenance-uncertain denominator candidate.

This totalized comparison object has no claimed source or physical-response meaning.
-/
def sysConDisputedDropPower (p : SysConParameters) : ℝ :=
  (p.inputCrossAmplitude * p.dropCrossAmplitude) ^ 2 * p.fieldAttenuation /
    sysConDisputedPowerDenominator p

/-- The half-angle and cosine forms of the amplitude-derived denominator agree exactly. -/
lemma sysConAmplitudePowerDenominator_eq_cosineForm (p : SysConParameters) :
    sysConAmplitudePowerDenominator p =
      1 + p.realLoopGain ^ 2 - 2 * p.realLoopGain * Real.cos p.phase := by
  rw [show p.phase = 2 * (p.phase / 2) by ring, Real.cos_two_mul_eq_one_sub]
  rw [sysConAmplitudePowerDenominator]
  ring

/-- The SysCon amplitude has the analytic real power form on the nonnegative-attenuation domain. -/
theorem sysConDropPower_eq_analytic (p : SysConParameters)
    (hAttenuation : 0 ≤ p.fieldAttenuation) :
    sysConDropPower p = sysConAnalyticDropPower p := by
  rw [sysConDropPower_eq_dropPower p hAttenuation,
    AddDrop.dropPower_eq_closedForm p.toAddDrop hAttenuation]
  simp only [AddDrop.Parameters.dropPowerNumerator,
    AddDrop.Parameters.powerDenominator, SysConParameters.toAddDrop,
    sysConAnalyticDropPower]
  ring

/-- The norm-square power bridge can equivalently use the source-style half-angle denominator. -/
theorem sysConDropPower_eq_amplitudePowerDenominator (p : SysConParameters)
    (hAttenuation : 0 ≤ p.fieldAttenuation) :
    sysConDropPower p =
      (p.inputCrossAmplitude * p.dropCrossAmplitude) ^ 2 * p.fieldAttenuation /
        sysConAmplitudePowerDenominator p := by
  rw [sysConDropPower_eq_analytic p hAttenuation, sysConAnalyticDropPower,
    sysConAmplitudePowerDenominator_eq_cosineForm]
  simp only [SysConParameters.realLoopGain]
  ring

/-! ## D. Log-base-explicit rejection ratios -/

/-- Ten times a logarithm in an explicit base, applied to a power ratio. -/
def powerRatioInBase (base numerator denominator : ℝ) : ℝ :=
  10 * Real.logb base (numerator / denominator)

/-- At base ten, the explicit-base convention is Physlib's power-ratio decibel convention. -/
lemma powerRatioInBase_ten (numerator denominator : ℝ) :
    powerRatioInBase 10 numerator denominator =
      AddDrop.powerRatioDB numerator denominator := rfl

/-- At base `exp(1)`, the explicit-base convention is ten times the natural logarithm. -/
lemma powerRatioInBase_exp_one (numerator denominator : ℝ) :
    powerRatioInBase (Real.exp 1) numerator denominator =
      10 * Real.log (numerator / denominator) := by
  rw [powerRatioInBase, Real.logb]
  simp

/-- SysCon Thm. 7's closed rejection-ratio argument with an explicit log base
(`HOL-CORPUS.md:246-249`). -/
def sysConRejectionClosedForm (base : ℝ) (p : SysConParameters) : ℝ :=
  10 * Real.logb base
    (((1 + p.inputThroughAmplitude * p.dropThroughAmplitude *
      p.fieldAttenuation) ^ 2) /
      ((1 - p.inputThroughAmplitude * p.dropThroughAmplitude *
        p.fieldAttenuation) ^ 2))

/-- SysCon Def. 11's on-resonance point uses the printed phase `2*pi`. -/
def SysConParameters.atResonance (p : SysConParameters) : SysConParameters :=
  { p with phase := 2 * Real.pi }

/-- SysCon Def. 11's off-resonance point uses the printed phase `pi`. -/
def SysConParameters.atAntiresonance (p : SysConParameters) : SysConParameters :=
  { p with phase := Real.pi }

/-- SysCon Def. 11 with the previously unaudited logarithm base made explicit. -/
def sysConRejectionRatioInBase (base : ℝ) (p : SysConParameters) : ℝ :=
  powerRatioInBase base (sysConDropPower p.atResonance)
    (sysConDropPower p.atAntiresonance)

/-- The SysCon named resonance has the exact amplitude-derived drop power. -/
lemma sysConDropPower_atResonance (p : SysConParameters)
    (hAttenuation : 0 ≤ p.fieldAttenuation) :
    sysConDropPower p.atResonance =
      (p.inputCrossAmplitude * p.dropCrossAmplitude) ^ 2 * p.fieldAttenuation /
        (1 - p.realLoopGain) ^ 2 := by
  rw [sysConDropPower_eq_analytic p.atResonance
    (by simpa [SysConParameters.atResonance] using hAttenuation)]
  simp [sysConAnalyticDropPower, SysConParameters.atResonance,
    SysConParameters.realLoopGain, Real.cos_two_pi]
  ring

/-- The SysCon named antiresonance has the exact amplitude-derived drop power. -/
lemma sysConDropPower_atAntiresonance (p : SysConParameters)
    (hAttenuation : 0 ≤ p.fieldAttenuation) :
    sysConDropPower p.atAntiresonance =
      (p.inputCrossAmplitude * p.dropCrossAmplitude) ^ 2 * p.fieldAttenuation /
        (1 + p.realLoopGain) ^ 2 := by
  rw [sysConDropPower_eq_analytic p.atAntiresonance
    (by simpa [SysConParameters.atAntiresonance] using hAttenuation)]
  simp [sysConAnalyticDropPower, SysConParameters.atAntiresonance,
    SysConParameters.realLoopGain, Real.cos_pi]
  ring

/-- On the source domain, the SysCon named resonance power is strictly positive. -/
lemma sysConDropPower_atResonance_pos (p : SysConParameters)
    (hAttenuation : 0 < p.fieldAttenuation)
    (hInputCross : p.inputCrossAmplitude ≠ 0)
    (hDropCross : p.dropCrossAmplitude ≠ 0)
    (hContractive : p.IsContractive) :
    0 < sysConDropPower p.atResonance := by
  rw [sysConDropPower_atResonance p hAttenuation.le]
  have hLoop : -1 < p.realLoopGain ∧ p.realLoopGain < 1 :=
    abs_lt.mp (show |p.realLoopGain| < 1 from hContractive)
  apply div_pos
  · exact mul_pos (sq_pos_of_ne_zero (mul_ne_zero hInputCross hDropCross)) hAttenuation
  · exact sq_pos_of_pos (sub_pos.mpr hLoop.2)

/-- On the source domain, the SysCon named antiresonance power is strictly positive. -/
lemma sysConDropPower_atAntiresonance_pos (p : SysConParameters)
    (hAttenuation : 0 < p.fieldAttenuation)
    (hInputCross : p.inputCrossAmplitude ≠ 0)
    (hDropCross : p.dropCrossAmplitude ≠ 0)
    (hContractive : p.IsContractive) :
    0 < sysConDropPower p.atAntiresonance := by
  rw [sysConDropPower_atAntiresonance p hAttenuation.le]
  have hLoop : -1 < p.realLoopGain ∧ p.realLoopGain < 1 :=
    abs_lt.mp (show |p.realLoopGain| < 1 from hContractive)
  apply div_pos
  · exact mul_pos (sq_pos_of_ne_zero (mul_ne_zero hInputCross hDropCross)) hAttenuation
  · exact sq_pos_of_pos (by linarith [hLoop.1])

/-- The two positive source powers have SysCon Thm. 7's cancelled denominator ratio. -/
lemma sysCon_namedDropPower_ratio (p : SysConParameters)
    (hAttenuation : 0 < p.fieldAttenuation)
    (hInputCross : p.inputCrossAmplitude ≠ 0)
    (hDropCross : p.dropCrossAmplitude ≠ 0)
    (hContractive : p.IsContractive) :
    sysConDropPower p.atResonance / sysConDropPower p.atAntiresonance =
      (1 + p.realLoopGain) ^ 2 / (1 - p.realLoopGain) ^ 2 := by
  rw [sysConDropPower_atResonance p hAttenuation.le,
    sysConDropPower_atAntiresonance p hAttenuation.le]
  have hLoop : -1 < p.realLoopGain ∧ p.realLoopGain < 1 :=
    abs_lt.mp (show |p.realLoopGain| < 1 from hContractive)
  have hNumerator :
      (p.inputCrossAmplitude * p.dropCrossAmplitude) ^ 2 *
        p.fieldAttenuation ≠ 0 := by
    exact ne_of_gt
      (mul_pos (sq_pos_of_ne_zero (mul_ne_zero hInputCross hDropCross)) hAttenuation)
  have hResonance : (1 - p.realLoopGain) ^ 2 ≠ 0 := by
    exact ne_of_gt (sq_pos_of_pos (sub_pos.mpr hLoop.2))
  have hAntiresonance : (1 + p.realLoopGain) ^ 2 ≠ 0 := by
    exact ne_of_gt (sq_pos_of_pos (by linarith [hLoop.1]))
  field_simp

/-- SysCon Def. 11 equals Thm. 7 for every explicit logarithm base greater than one. -/
theorem sysConRejectionRatioInBase_eq_closedForm (base : ℝ) (p : SysConParameters)
    (_hBase : 1 < base) (hAttenuation : 0 < p.fieldAttenuation)
    (hInputCross : p.inputCrossAmplitude ≠ 0)
    (hDropCross : p.dropCrossAmplitude ≠ 0)
    (hContractive : p.IsContractive) :
    sysConRejectionRatioInBase base p = sysConRejectionClosedForm base p := by
  rw [sysConRejectionRatioInBase, powerRatioInBase, sysConRejectionClosedForm,
    sysCon_namedDropPower_ratio p hAttenuation hInputCross hDropCross hContractive]
  simp only [SysConParameters.realLoopGain]

/-- The base-ten reading of SysCon Thm. 7 is Physlib's drop rejection ratio. -/
lemma sysConRejectionClosedForm_base_ten (p : SysConParameters)
    (hAttenuation : 0 < p.fieldAttenuation)
    (hInputCross : p.inputCrossAmplitude ≠ 0)
    (hDropCross : p.dropCrossAmplitude ≠ 0)
    (hResonanceDenominator : p.toAddDrop.atResonance.HasNonzeroDenominator)
    (hAntiresonanceDenominator : p.toAddDrop.atAntiresonance.HasNonzeroDenominator) :
    sysConRejectionClosedForm 10 p = AddDrop.dropRejectionRatioDB p.toAddDrop := by
  rw [sysConRejectionClosedForm,
    AddDrop.dropRejectionRatioDB_eq_denominatorRatio p.toAddDrop hAttenuation
      hInputCross hDropCross hResonanceDenominator hAntiresonanceDenominator]
  rfl

/-- The base-ten reading of SysCon Def. 11 is Physlib's drop rejection ratio. -/
lemma sysConRejectionRatioInBase_ten_eq_dropRejectionRatioDB
    (p : SysConParameters) (hAttenuation : 0 < p.fieldAttenuation)
    (hInputCross : p.inputCrossAmplitude ≠ 0)
    (hDropCross : p.dropCrossAmplitude ≠ 0)
    (hContractive : p.IsContractive)
    (hResonanceDenominator : p.toAddDrop.atResonance.HasNonzeroDenominator)
    (hAntiresonanceDenominator : p.toAddDrop.atAntiresonance.HasNonzeroDenominator) :
    sysConRejectionRatioInBase 10 p = AddDrop.dropRejectionRatioDB p.toAddDrop := by
  rw [sysConRejectionRatioInBase_eq_closedForm 10 p (by norm_num) hAttenuation
    hInputCross hDropCross hContractive]
  exact sysConRejectionClosedForm_base_ten p hAttenuation hInputCross hDropCross
    hResonanceDenominator hAntiresonanceDenominator

/-- The natural-log reading of SysCon Thm. 7 is the same positive ratio measured with `ln`. -/
lemma sysConRejectionClosedForm_exp_one (p : SysConParameters) :
    sysConRejectionClosedForm (Real.exp 1) p =
      10 * Real.log
        (((1 + p.inputThroughAmplitude * p.dropThroughAmplitude *
          p.fieldAttenuation) ^ 2) /
          ((1 - p.inputThroughAmplitude * p.dropThroughAmplitude *
            p.fieldAttenuation) ^ 2)) := by
  rw [sysConRejectionClosedForm, Real.logb]
  simp

/-- The natural-log reading of SysCon Def. 11 is ten times `ln` of Thm. 7's positive ratio. -/
lemma sysConRejectionRatioInBase_exp_one_eq_naturalLog
    (p : SysConParameters) (hAttenuation : 0 < p.fieldAttenuation)
    (hInputCross : p.inputCrossAmplitude ≠ 0)
    (hDropCross : p.dropCrossAmplitude ≠ 0)
    (hContractive : p.IsContractive) :
    sysConRejectionRatioInBase (Real.exp 1) p =
      10 * Real.log
        (((1 + p.inputThroughAmplitude * p.dropThroughAmplitude *
          p.fieldAttenuation) ^ 2) /
          ((1 - p.inputThroughAmplitude * p.dropThroughAmplitude *
            p.fieldAttenuation) ^ 2)) := by
  rw [sysConRejectionRatioInBase_eq_closedForm (Real.exp 1) p
      ((Real.one_lt_exp_iff).2 zero_lt_one) hAttenuation hInputCross hDropCross hContractive,
    sysConRejectionClosedForm_exp_one]

end MicroringSourceBridge

end

end Optics
