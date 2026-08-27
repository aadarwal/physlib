/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Network.Coherency
public import Physlib.Optics.Systems.DCDR.NominalChain

/-!
# Second-order coherency observables of the DCDR

## i. Overview

This module specializes N6c coherency transport to the proof-gated two-channel coherent DCDR
netlist. On the nonzero-denominator gate, the complete N5 response sends the nominal-right input
to the nominal-left output by `transfer p.reverse` and the nominal-left input to the
nominal-right output by `transfer p`. The two reflection entries vanish. The resulting formulas
identify rank-one coherent channel powers, diagonal second-order illumination, the two-channel
trace, decorrelated sums, and the explicit coherent interference term.

Here an "incoherent input" is SECOND-ORDER ILLUMINATION DATA: a positive-semidefinite coherency
matrix whose declared off-diagonal correlations vanish, or a sum whose two contributions are
declared mutually decorrelated. It is not FMICS'15's separately printed incoherent coefficient
model. No result identifies that printed model with the coherent N7 DCDR netlist.

## ii. Key results

- `DCDR.responseCoherency_rankOne_channelPowers`: both coherent output-channel powers.
- `DCDR.responseCoherency_diagonal_channelPowers`: exact diagonal-input transport.
- `DCDR.responseCoherency_trace_twoChannels`: the complete two-channel trace.
- `DCDR.responseCoherency_source_trace`: the source-only coherent trace.
- `DCDR.responseCoherency_decorrelated_channelPower`: decorrelated power addition.
- `DCDR.responseCoherency_source_crossTerm`: the explicit same-channel interference term.

## iii. Table of contents

- A. Two-channel enumeration
- B. Rank-one coherent response
- C. Diagonal and general second-order response
- D. Trace and interference formulas

## iv. References

All channel powers and traces are normalized-modal second-order quantities. This module makes no
claim of physical resonance, power flux, electromagnetic energy, reciprocity, physical time
reversal, physical reference planes, coherent--incoherent equivalence, causality or Maxwell
time-domain meaning, physical-frequency meaning, or HOL-script semantics. N6b reciprocity remains
blocked on its separate convention data.

The generic congruence `Gamma_out = H * Gamma_in * H^H`, rank-one construction, diagonal data,
and cross-term identity are from `Physlib/Optics/Network/Coherency.lean`. The complete DCDR N5
coordinates are derived from the forward and reverse N7 equations in
`Physlib/Optics/Systems/DCDR/NominalChain.lean`.
-/

@[expose] public section

namespace Optics.DCDR

open Matrix
open scoped ComplexConjugate

noncomputable section

/-- The DCDR coherency layer uses the same finite external family as generic N6c transport. -/
local instance dcdrCoherencyExternalChannelFintype (p : Parameters) :
    Fintype (netlist p).ExternalChannel :=
  (netlist p).coherencyExternalChannelFintype

/-!

## A. Two-channel enumeration

-/

/-- A real sum over incident DCDR endpoints is the sum of its nominal-left and nominal-right
values. -/
lemma sum_externalIncident (p : Parameters)
    (value : (netlist p).ExternalIncident -> Real) :
    (∑ endpoint, value endpoint) =
      value (Incident.mk (inputChannel p)) +
        value (Incident.mk (outputChannel p)) := by
  classical
  let endpointEquiv : Fin 2 ≃ (netlist p).ExternalIncident :=
    (externalChannelEquiv p).trans Incident.channelEquiv.symm
  rw [← Fintype.sum_equiv endpointEquiv
    (fun index => value (endpointEquiv index)) value (fun _ => rfl)]
  simp [endpointEquiv, externalChannelEquiv, externalChannelOfFin, Fin.sum_univ_two]

/-- A real sum over outgoing DCDR endpoints is the sum of its nominal-left and nominal-right
values. -/
lemma sum_externalOutgoing (p : Parameters)
    (value : (netlist p).ExternalOutgoing -> Real) :
    (∑ endpoint, value endpoint) =
      value (Outgoing.mk (inputChannel p)) +
        value (Outgoing.mk (outputChannel p)) := by
  classical
  let endpointEquiv : Fin 2 ≃ (netlist p).ExternalOutgoing :=
    (externalChannelEquiv p).trans Outgoing.channelEquiv.symm
  rw [← Fintype.sum_equiv endpointEquiv
    (fun index => value (endpointEquiv index)) value (fun _ => rfl)]
  simp [endpointEquiv, externalChannelEquiv, externalChannelOfFin, Fin.sum_univ_two]

/-!

## B. Rank-one coherent response

-/

/-- The rank-one coherent response has the exact two nominal channel powers.

The first component is the nominal-left output and the second is the nominal-right output. -/
lemma responseCoherency_rankOne_channelPowers (p : Parameters)
    (hDenominator : p.HasNonzeroDenominator)
    (input : ModeAmplitude (netlist p).ExternalIncident) :
    let hWellPosed := isWellPosed_of_hasNonzeroDenominator p hDenominator
    ((netlist p).responseCoherency hWellPosed
        (CoherencyMatrix.ofAmplitude input)).channelPower
          (Outgoing.mk (inputChannel p)) =
        Complex.normSq
          (transfer p.reverse * input (Incident.mk (outputChannel p))) ∧
      ((netlist p).responseCoherency hWellPosed
        (CoherencyMatrix.ofAmplitude input)).channelPower
          (Outgoing.mk (outputChannel p)) =
        Complex.normSq
          (transfer p * input (Incident.mk (inputChannel p))) := by
  let hWellPosed := isWellPosed_of_hasNonzeroDenominator p hDenominator
  have hCoordinates := response_nominal_reference_coordinates p hDenominator input
  dsimp only
  simp only [FlatNetlist.responseCoherency]
  constructor
  · rw [CoherencyMatrix.channelPower_map_ofAmplitude]
    exact congrArg Complex.normSq hCoordinates.1
  · rw [CoherencyMatrix.channelPower_map_ofAmplitude]
    exact congrArg Complex.normSq hCoordinates.2

/-- A coherent amplitude incident only from the source side has output power
`normSq (transfer p * amplitude)` at the nominal-right endpoint. -/
lemma responseCoherency_source_channelPower (p : Parameters)
    (hDenominator : p.HasNonzeroDenominator) (amplitude : Complex) :
    ((netlist p).responseCoherency
      (isWellPosed_of_hasNonzeroDenominator p hDenominator)
      (CoherencyMatrix.ofAmplitude (inputAmplitude p amplitude))).channelPower
        (Outgoing.mk (outputChannel p)) =
      Complex.normSq (transfer p * amplitude) := by
  simpa using (responseCoherency_rankOne_channelPowers p hDenominator
    (inputAmplitude p amplitude)).2

/-!

## C. Diagonal and general second-order response

-/

/-- Diagonal second-order illumination has the exact two nominal output powers.

The left output sees only the declared right-input power, and the right output sees only the
declared left-input power. There is no cross term because the supplied input coherency is
diagonal. -/
lemma responseCoherency_diagonal_channelPowers (p : Parameters)
    (hDenominator : p.HasNonzeroDenominator)
    (powers : (netlist p).ExternalIncident -> Real)
    (hPowers : ∀ endpoint, 0 ≤ powers endpoint) :
    let hWellPosed := isWellPosed_of_hasNonzeroDenominator p hDenominator
    ((netlist p).responseCoherency hWellPosed
        (CoherencyMatrix.ofChannelPowers powers hPowers)).channelPower
          (Outgoing.mk (inputChannel p)) =
        powers (Incident.mk (outputChannel p)) *
          Complex.normSq (transfer p.reverse) ∧
      ((netlist p).responseCoherency hWellPosed
        (CoherencyMatrix.ofChannelPowers powers hPowers)).channelPower
          (Outgoing.mk (outputChannel p)) =
        powers (Incident.mk (inputChannel p)) * Complex.normSq (transfer p) := by
  let hWellPosed := isWellPosed_of_hasNonzeroDenominator p hDenominator
  dsimp only
  simp only [FlatNetlist.responseCoherency]
  constructor
  · rw [CoherencyMatrix.channelPower_map_ofChannelPowers,
      sum_externalIncident]
    rw [responseTransform_entry_nominalLeft_nominalLeft p hDenominator,
      responseTransform_entry_nominalLeft_nominalRight p hDenominator]
    simp
  · rw [CoherencyMatrix.channelPower_map_ofChannelPowers,
      sum_externalIncident]
    rw [responseTransform_entry_nominalRight_nominalLeft p hDenominator,
      responseTransform_entry_nominalRight_nominalRight p hDenominator]
    simp

/-- Every entry of the proof-gated DCDR output coherency is the explicit N6c double sum. -/
lemma responseCoherency_entry (p : Parameters)
    (hDenominator : p.HasNonzeroDenominator)
    (input : CoherencyMatrix (netlist p).ExternalIncident)
    (row column : (netlist p).ExternalOutgoing) :
    let hWellPosed := isWellPosed_of_hasNonzeroDenominator p hDenominator
    ((netlist p).responseCoherency hWellPosed input).toMatrix row column =
      ∑ second, ∑ first,
        (netlist p).responseTransform hWellPosed row first *
          input.toMatrix first second *
            star ((netlist p).responseTransform hWellPosed column second) := by
  let hWellPosed := isWellPosed_of_hasNonzeroDenominator p hDenominator
  dsimp only
  exact CoherencyMatrix.map_toMatrix_apply input
    ((netlist p).responseTransform hWellPosed) row column

/-!

## D. Trace and interference formulas

-/

/-- The DCDR output trace is exactly the sum of its two named output-channel powers. -/
lemma responseCoherency_trace_twoChannels (p : Parameters)
    (hDenominator : p.HasNonzeroDenominator)
    (input : CoherencyMatrix (netlist p).ExternalIncident) :
    let hWellPosed := isWellPosed_of_hasNonzeroDenominator p hDenominator
    ((netlist p).responseCoherency hWellPosed input).trace =
      ((netlist p).responseCoherency hWellPosed input).channelPower
          (Outgoing.mk (inputChannel p)) +
        ((netlist p).responseCoherency hWellPosed input).channelPower
          (Outgoing.mk (outputChannel p)) := by
  let hWellPosed := isWellPosed_of_hasNonzeroDenominator p hDenominator
  dsimp only
  rw [CoherencyMatrix.trace_eq_sum_channelPower]
  exact sum_externalOutgoing p _

/-- A source-only coherent input has trace `normSq (transfer p * amplitude)`. -/
lemma responseCoherency_source_trace (p : Parameters)
    (hDenominator : p.HasNonzeroDenominator) (amplitude : Complex) :
    ((netlist p).responseCoherency
      (isWellPosed_of_hasNonzeroDenominator p hDenominator)
      (CoherencyMatrix.ofAmplitude (inputAmplitude p amplitude))).trace =
        Complex.normSq (transfer p * amplitude) := by
  rw [responseCoherency_trace_twoChannels p hDenominator]
  rcases responseCoherency_rankOne_channelPowers p hDenominator
    (inputAmplitude p amplitude) with ⟨hLeft, hRight⟩
  rw [hLeft, hRight]
  simp

/-- Mutually decorrelated DCDR inputs have exactly additive power at every output channel. -/
lemma responseCoherency_decorrelated_channelPower (p : Parameters)
    (hDenominator : p.HasNonzeroDenominator)
    (first second : CoherencyMatrix (netlist p).ExternalIncident)
    (channel : (netlist p).ExternalOutgoing) :
    ((netlist p).responseCoherency
      (isWellPosed_of_hasNonzeroDenominator p hDenominator)
      (first.incoherentSum second)).channelPower channel =
        ((netlist p).responseCoherency
          (isWellPosed_of_hasNonzeroDenominator p hDenominator) first).channelPower channel +
        ((netlist p).responseCoherency
          (isWellPosed_of_hasNonzeroDenominator p hDenominator) second).channelPower channel := by
  simp only [FlatNetlist.responseCoherency]
  exact CoherencyMatrix.channelPower_map_incoherentSum first second _ channel

/-- The source-side coherent-minus-decorrelated output power is the explicit interference term.

Both amplitudes occupy the same incident channel. The right side retains their phase-sensitive
cross term; no cross term has been deleted from the coherent calculation. -/
lemma responseCoherency_source_crossTerm (p : Parameters)
    (hDenominator : p.HasNonzeroDenominator) (first second : Complex) :
    ((netlist p).responseCoherency
        (isWellPosed_of_hasNonzeroDenominator p hDenominator)
        (CoherencyMatrix.ofAmplitude
          (inputAmplitude p first + inputAmplitude p second))).channelPower
          (Outgoing.mk (outputChannel p)) -
      ((netlist p).responseCoherency
        (isWellPosed_of_hasNonzeroDenominator p hDenominator)
        ((CoherencyMatrix.ofAmplitude (inputAmplitude p first)).incoherentSum
          (CoherencyMatrix.ofAmplitude (inputAmplitude p second)))).channelPower
            (Outgoing.mk (outputChannel p)) =
      2 * ((transfer p * first) * star (transfer p * second)).re := by
  let hWellPosed := isWellPosed_of_hasNonzeroDenominator p hDenominator
  let transform := (netlist p).responseTransform hWellPosed
  have hCross := CoherencyMatrix.channelPower_map_ofAmplitude_add_sub_incoherentSum
    (inputAmplitude p first) (inputAmplitude p second) transform
      (Outgoing.mk (outputChannel p))
  have hFirst := (response_nominal_reference_coordinates p hDenominator
    (inputAmplitude p first)).2
  have hSecond := (response_nominal_reference_coordinates p hDenominator
    (inputAmplitude p second)).2
  have hFirst' :
      transform.toLinearMap (inputAmplitude p first) (Outgoing.mk (outputChannel p)) =
        transfer p * first := by
    simpa [transform, hWellPosed] using hFirst
  have hSecond' :
      transform.toLinearMap (inputAmplitude p second) (Outgoing.mk (outputChannel p)) =
        transfer p * second := by
    simpa [transform, hWellPosed] using hSecond
  change ((CoherencyMatrix.ofAmplitude
      (inputAmplitude p first + inputAmplitude p second)).map transform).channelPower
        (Outgoing.mk (outputChannel p)) -
    (((CoherencyMatrix.ofAmplitude (inputAmplitude p first)).incoherentSum
      (CoherencyMatrix.ofAmplitude (inputAmplitude p second))).map transform).channelPower
        (Outgoing.mk (outputChannel p)) = _
  rw [hCross, hFirst', hSecond']

end

end Optics.DCDR
