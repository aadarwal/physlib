/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Systems.DCDR.Coherency
public import Physlib.Optics.Systems.DCDR.NominalChainRegression

/-!
# Exact DCDR coherency regressions

## i. Overview

At the accepted stable point `z = I`, hence formal delay `q = -I`, the independently expanded
DCDR response is the reflectionless matrix with both transmission entries `-(7/8) * I`. This
file writes that matrix on `Fin 2` and expands its second-order action directly from matrix
multiplication.

Two equal-and-opposite unit contributions occupy the same incident channel. Their coherent sum
has output power zero, while the supplied decorrelated second-order sum has output power `49/32`.
The explicit coherent-minus-decorrelated cross term is `-49/32`, so deleting it or conflating the
two illumination models makes the fixture fail. A separate input with relative phase `I` gives
the nonreal output coherency entry `(49/64) * I`; replacing the conjugate transpose by an ordinary
transpose flips its sign.

The numeric anchors unfold `CoherencyMatrix.map`, outer products, both matrix products, and the
two-element sums. They do not use any lemma from `DCDR.Coherency` or the generic derived
coherency formulas. Those production lemmas occur only in a final agreement statement paired
with the independent values.

## ii. Key results

- `DCDR.coherencyRegression_coherent_channelPower`: coherent cancellation gives zero.
- `DCDR.coherencyRegression_decorrelated_channelPower`: decorrelated power is `49/32`.
- `DCDR.coherencyRegression_crossTerm`: the retained cross term is `-49/32`.
- `DCDR.coherencyRegression_models_differ`: the two illumination models cannot be conflated.
- `DCDR.coherencyRegression_nonreal_offDiagonal`: the nonreal sign anchor is `(49/64) * I`.
- `DCDR.coherencyRegression_production_agreement`: proof-gated N6c matches the raw anchors.

## iii. Table of contents

- A. Stable raw response matrix
- B. Equal-and-opposite same-channel inputs
- C. Independent coherent and decorrelated anchors
- D. Nonreal congruence-orientation anchor
- E. Production agreement

## iv. References

The scalar and all four fixed response entries are independently derived from the raw N7
equations in `Physlib/Optics/Systems/DCDR/NominalChainRegression.lean`. Generic N6c definitions
are in `Physlib/Optics/Network/Coherency.lean`.

The word decorrelated refers only to supplied second-order illumination data. It is not the
separately printed FMICS'15 incoherent coefficient model. These regressions make no physical
resonance, power-flux, electromagnetic-energy, reciprocity, time-reversal, reference-plane,
coherent--incoherent-equivalence, causality, physical-frequency, or HOL-script claim. N6b remains
blocked on separate convention data.
-/

@[expose] public section

namespace Optics.DCDR

open Matrix
open scoped ComplexConjugate

noncomputable section

/-- The regression uses the same finite external family as production N6c transport. -/
local instance coherencyRegressionExternalChannelFintype (p : Parameters) :
    Fintype (netlist p).ExternalChannel :=
  (netlist p).coherencyExternalChannelFintype

/-!

## A. Stable raw response matrix

-/

/-- The independently audited stable transmission at `z = I`, in nominal left/right order. -/
def coherencyRegressionTransform : ModeTransform (Fin 2) (Fin 2) :=
  ![![0, -(7 / 8) * Complex.I], ![-(7 / 8) * Complex.I, 0]]

/-- The raw two-vector matrix agrees entrywise with the proof-gated response derived from N7.

This is an agreement statement only. None of the second-order numeric anchors below uses it. -/
lemma coherencyRegressionTransform_matches_response :
    let hWellPosed := isWellPosed_of_hasNonzeroDenominator zChainRegressionParameters
      zChainRegression_hasNonzeroDenominator
    (netlist zChainRegressionParameters).responseTransform hWellPosed
          (Outgoing.mk (inputChannel zChainRegressionParameters))
          (Incident.mk (inputChannel zChainRegressionParameters)) =
        coherencyRegressionTransform 0 0 ∧
      (netlist zChainRegressionParameters).responseTransform hWellPosed
          (Outgoing.mk (inputChannel zChainRegressionParameters))
          (Incident.mk (outputChannel zChainRegressionParameters)) =
        coherencyRegressionTransform 0 1 ∧
      (netlist zChainRegressionParameters).responseTransform hWellPosed
          (Outgoing.mk (outputChannel zChainRegressionParameters))
          (Incident.mk (inputChannel zChainRegressionParameters)) =
        coherencyRegressionTransform 1 0 ∧
      (netlist zChainRegressionParameters).responseTransform hWellPosed
          (Outgoing.mk (outputChannel zChainRegressionParameters))
          (Incident.mk (outputChannel zChainRegressionParameters)) =
        coherencyRegressionTransform 1 1 := by
  dsimp only
  exact ⟨by simpa [coherencyRegressionTransform] using
      zChainRegression_response_left_left,
    by simpa [coherencyRegressionTransform] using zChainRegression_response_left_right,
    by simpa [coherencyRegressionTransform] using zChainRegression_response_right_left,
    by simpa [coherencyRegressionTransform] using zChainRegression_response_right_right⟩

/-!

## B. Equal-and-opposite same-channel inputs

-/

/-- A unit contribution in the nominal-left incident channel. -/
def coherencyRegressionFirst : ModeAmplitude (Fin 2) :=
  WithLp.toLp 2 ![1, 0]

/-- The equal-and-opposite contribution in the same nominal-left incident channel. -/
def coherencyRegressionSecond : ModeAmplitude (Fin 2) :=
  WithLp.toLp 2 ![-1, 0]

/-- The two same-channel contributions cancel as coherent amplitudes. -/
lemma coherencyRegression_amplitudes_add :
    coherencyRegressionFirst + coherencyRegressionSecond = 0 := by
  apply WithLp.ofLp_injective 2
  funext channel
  fin_cases channel <;>
    norm_num [coherencyRegressionFirst, coherencyRegressionSecond]

/-!

## C. Independent coherent and decorrelated anchors

The following anchors unfold both matrix products and both `Fin 2` sums. They do not use
`DCDR.responseCoherency_rankOne_channelPowers`,
`DCDR.responseCoherency_decorrelated_channelPower`, or
`DCDR.responseCoherency_source_crossTerm`.

-/

/-- Primitive expansion gives coherent output power zero after amplitude cancellation. -/
lemma coherencyRegression_coherent_channelPower :
    ((CoherencyMatrix.ofAmplitude
        (coherencyRegressionFirst + coherencyRegressionSecond)).map
      coherencyRegressionTransform).channelPower 1 = 0 := by
  rw [coherencyRegression_amplitudes_add, CoherencyMatrix.channelPower,
    CoherencyMatrix.map_toMatrix, CoherencyMatrix.ofAmplitude_toMatrix]
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  norm_num [coherencyRegressionTransform, Matrix.vecMulVec,
    Matrix.conjTranspose, Matrix.transpose, Matrix.map, Matrix.of_apply]

/-- Primitive expansion gives decorrelated output power `49/32`. -/
lemma coherencyRegression_decorrelated_channelPower :
    (((CoherencyMatrix.ofAmplitude coherencyRegressionFirst).incoherentSum
        (CoherencyMatrix.ofAmplitude coherencyRegressionSecond)).map
      coherencyRegressionTransform).channelPower 1 = 49 / 32 := by
  rw [CoherencyMatrix.channelPower, CoherencyMatrix.map_toMatrix,
    CoherencyMatrix.incoherentSum_toMatrix]
  simp only [CoherencyMatrix.ofAmplitude_toMatrix, Matrix.mul_apply, Fin.sum_univ_two]
  norm_num [coherencyRegressionTransform, coherencyRegressionFirst,
    coherencyRegressionSecond, Matrix.vecMulVec, Matrix.conjTranspose,
    Matrix.transpose, Matrix.map, Matrix.of_apply, Complex.ext_iff,
    map_div₀, map_ofNat]

/-- Primitive amplitude action gives the exact retained cross term `-49/32`. -/
lemma coherencyRegression_crossTerm :
    2 * (coherencyRegressionTransform.toLinearMap coherencyRegressionFirst 1 *
      star (coherencyRegressionTransform.toLinearMap coherencyRegressionSecond 1)).re =
        -(49 / 32) := by
  simp only [ModeTransform.toLinearMap, Matrix.toLpLin_apply, Matrix.mulVec,
    dotProduct, Fin.sum_univ_two]
  norm_num [coherencyRegressionTransform, coherencyRegressionFirst,
    coherencyRegressionSecond, RCLike.star_def, Complex.ext_iff]

/-- The coherent-minus-decorrelated difference is exactly the nonzero cross term. -/
lemma coherencyRegression_coherent_sub_decorrelated :
    ((CoherencyMatrix.ofAmplitude
          (coherencyRegressionFirst + coherencyRegressionSecond)).map
        coherencyRegressionTransform).channelPower 1 -
      (((CoherencyMatrix.ofAmplitude coherencyRegressionFirst).incoherentSum
          (CoherencyMatrix.ofAmplitude coherencyRegressionSecond)).map
        coherencyRegressionTransform).channelPower 1 = -(49 / 32) := by
  rw [coherencyRegression_coherent_channelPower,
    coherencyRegression_decorrelated_channelPower]
  norm_num

/-- Hostile negative: coherent cancellation and decorrelated addition are unequal on the same
fixture, so conflating the illumination models or dropping the cross term is rejected. -/
lemma coherencyRegression_models_differ :
    ((CoherencyMatrix.ofAmplitude
          (coherencyRegressionFirst + coherencyRegressionSecond)).map
        coherencyRegressionTransform).channelPower 1 ≠
      (((CoherencyMatrix.ofAmplitude coherencyRegressionFirst).incoherentSum
          (CoherencyMatrix.ofAmplitude coherencyRegressionSecond)).map
        coherencyRegressionTransform).channelPower 1 := by
  rw [coherencyRegression_coherent_channelPower,
    coherencyRegression_decorrelated_channelPower]
  norm_num

/-!

## D. Nonreal congruence-orientation anchor

-/

/-- A two-channel coherent amplitude with relative phase `I`. -/
def coherencyRegressionNonrealAmplitude : ModeAmplitude (Fin 2) :=
  WithLp.toLp 2 ![1, Complex.I]

/-- Direct `H * Gamma * H^H` expansion gives the positive nonreal off-diagonal sign. -/
lemma coherencyRegression_nonreal_offDiagonal :
    ((CoherencyMatrix.ofAmplitude coherencyRegressionNonrealAmplitude).map
      coherencyRegressionTransform).toMatrix 0 1 = (49 / 64) * Complex.I := by
  rw [CoherencyMatrix.map_toMatrix, CoherencyMatrix.ofAmplitude_toMatrix]
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  norm_num [coherencyRegressionTransform, coherencyRegressionNonrealAmplitude,
    Matrix.vecMulVec, Matrix.conjTranspose, Matrix.transpose, Matrix.map,
    Matrix.of_apply, Complex.ext_iff, map_div₀, map_ofNat]

/-- Replacing the conjugate transpose by an ordinary transpose flips the nonreal anchor. -/
lemma coherencyRegression_unstarred_offDiagonal :
    (coherencyRegressionTransform *
      (CoherencyMatrix.ofAmplitude coherencyRegressionNonrealAmplitude).toMatrix *
        coherencyRegressionTransform.transpose) 0 1 = -(49 / 64) * Complex.I := by
  rw [CoherencyMatrix.ofAmplitude_toMatrix]
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  norm_num [coherencyRegressionTransform, coherencyRegressionNonrealAmplitude,
    Matrix.vecMulVec, Matrix.transpose, Matrix.of_apply, Complex.ext_iff]

/-- Hostile negative: the ordinary-transpose convention is rejected by the same nonreal entry. -/
lemma coherencyRegression_conjugation_is_loadBearing :
    ((CoherencyMatrix.ofAmplitude coherencyRegressionNonrealAmplitude).map
        coherencyRegressionTransform).toMatrix 0 1 ≠
      (coherencyRegressionTransform *
        (CoherencyMatrix.ofAmplitude coherencyRegressionNonrealAmplitude).toMatrix *
          coherencyRegressionTransform.transpose) 0 1 := by
  rw [coherencyRegression_nonreal_offDiagonal,
    coherencyRegression_unstarred_offDiagonal]
  intro hEqual
  have hImaginary := congrArg Complex.im hEqual
  norm_num at hImaginary

/-!

## E. Production agreement

-/

/-- The proof-gated DCDR coherency formulas agree with the independently expanded stable values.

The first conjunct is the independent raw anchor. The remaining conjuncts invoke production N6c
only after that value and the raw response matrix have been pinned separately. -/
lemma coherencyRegression_production_agreement :
    (((CoherencyMatrix.ofAmplitude coherencyRegressionFirst).incoherentSum
        (CoherencyMatrix.ofAmplitude coherencyRegressionSecond)).map
      coherencyRegressionTransform).channelPower 1 = 49 / 32 ∧
    ((netlist zChainRegressionParameters).responseCoherency
      (isWellPosed_of_hasNonzeroDenominator zChainRegressionParameters
        zChainRegression_hasNonzeroDenominator)
      (CoherencyMatrix.ofAmplitude
        (inputAmplitude zChainRegressionParameters 1))).channelPower
          (Outgoing.mk (outputChannel zChainRegressionParameters)) = 49 / 64 ∧
    ((netlist zChainRegressionParameters).responseCoherency
      (isWellPosed_of_hasNonzeroDenominator zChainRegressionParameters
        zChainRegression_hasNonzeroDenominator)
      (CoherencyMatrix.ofAmplitude
        (inputAmplitude zChainRegressionParameters 1))).trace = 49 / 64 ∧
    2 * ((transfer zChainRegressionParameters * 1) *
      star (transfer zChainRegressionParameters * (-1))).re = -(49 / 32) := by
  refine ⟨coherencyRegression_decorrelated_channelPower, ?_, ?_, ?_⟩
  · rw [responseCoherency_source_channelPower zChainRegressionParameters
        zChainRegression_hasNonzeroDenominator,
      zChainRegression_forward_transfer]
    norm_num [Complex.normSq]
  · rw [responseCoherency_source_trace zChainRegressionParameters
        zChainRegression_hasNonzeroDenominator,
      zChainRegression_forward_transfer]
    norm_num [Complex.normSq]
  · rw [zChainRegression_forward_transfer]
    norm_num [RCLike.star_def, Complex.ext_iff]

end

end Optics.DCDR
