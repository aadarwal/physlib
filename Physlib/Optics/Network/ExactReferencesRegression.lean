/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Network.ConservationRegression
public import Physlib.Optics.Network.ExactReferences

/-!
# Exact N6 reference manifest

## i. Overview

This file packages the five hand-transcribed N6 validation quantities as Gaussian-rational values
with kernel-checked semantic certificates. The response certificate reaches the public proof-gated
network response. The two power, cross-entry, and coherency certificates reach the corresponding
public regression declarations used by the validation statement snapshot.

Every certificate unfolds a fixed finite exact value and closes with `norm_num`. A bare `decide`
was attempted on a derived rational matrix expression and failed inside rational normalization,
while unfolded `norm_num` closed; this is why later family adapters must retain the same proof
contract. The hostile coherency sentinel unfolds the table value itself and rejects the transposed
off-diagonal entry, whose imaginary sign is flipped.

## ii. Key results

- `Optics.n6ResponseExactReference`: the exact N6 external response certificate.
- `Optics.n6ColumnAPowerExactReference`: the first exact unit-column-power certificate.
- `Optics.n6ColumnBPowerExactReference`: the second exact unit-column-power certificate.
- `Optics.n6CrossExactReference`: the two exact reciprocal cross entries.
- `Optics.n6CoherencyExactReference`: the exact asymmetric coherency matrix.
- `Optics.n6ExactReferences`: the ordered five-row transport table.

## iii. Table of contents

- A. Response reference
- B. Scalar power references
- C. Cross-entry and coherency references
- D. Manifest and hostile sentinel

## iv. References

The JSON emitter is transport; each sound theorem is the certificate; a buggy emitter is caught by
exact regeneration, never by trusting it.

this slice covers the FIVE hand-typed N6 quantities (Q(i) circuit tier); the circuit-tier fence is
83 rows (43 Q + 40 Q(i)), the field fence is 93, the contract population is 112 - never conflate
the three; the 19-row transcendental/algebraic residual stays on its current leg by name.

No claim is made beyond the N6 pilot. In particular, this is not a generic exact-response solver,
floating-point evaluator, validation parser, or circuit-family coverage theorem.

-/

@[expose] public section

namespace Optics

noncomputable section

/-- Local enumeration of channels for each component in the proof-gated N6 fixture. -/
local instance conservationExactLocalChannelFintype (component : Bool) :
    Fintype (conservationRegressionComponents.portFamily component).Channel := by
  change Fintype (Σ _ : Bool, Unit)
  infer_instance

/-- Local channel equality for each component in the proof-gated N6 fixture. -/
local instance conservationExactLocalChannelDecidableEq (component : Bool) :
    DecidableEq (conservationRegressionComponents.portFamily component).Channel :=
  Classical.decEq _

/-- Local enumeration of every channel in the proof-gated N6 fixture. -/
local instance conservationExactChannelFintype : Fintype conservationRegression.Channel := by
  change Fintype (Σ _ : (Σ _ : Bool, Bool), Unit)
  infer_instance

/-- Local channel equality for the proof-gated N6 fixture. -/
local instance conservationExactChannelDecidableEq :
    DecidableEq conservationRegression.Channel := Classical.decEq _

/-- Local enumeration of connected channels in the proof-gated N6 fixture. -/
local instance conservationExactConnectedChannelFintype :
    Fintype conservationRegression.ConnectedChannel := by
  change Fintype (Σ _ : Unit, Unit ⊕ Unit)
  infer_instance

/-- Local connected-channel equality for the proof-gated N6 fixture. -/
local instance conservationExactConnectedChannelDecidableEq :
    DecidableEq conservationRegression.ConnectedChannel := Classical.decEq _

/-- Local enumeration of exposed channels in the proof-gated N6 fixture. -/
local instance conservationExactExternalChannelFintype :
    Fintype conservationRegression.ExternalChannel := by
  classical
  infer_instance

/-!

## A. Response reference

-/

/-- External outgoing channels in the N6 statement-snapshot order. -/
def n6ResponseOutput : Fin 2 → conservationRegression.ExternalOutgoing :=
  ![Outgoing.mk conservationRegressionExternalA, Outgoing.mk conservationRegressionExternalB]

/-- External incident channels in the N6 statement-snapshot order. -/
def n6ResponseInput : Fin 2 → conservationRegression.ExternalIncident :=
  ![Incident.mk conservationRegressionExternalA, Incident.mk conservationRegressionExternalB]

/-- The public proof-gated N6 response, reindexed by the emitted two-channel order. -/
def n6ResponseSemantic : Matrix (Fin 2) (Fin 2) ℂ := fun row column ↦
  conservationRegression.responseTransform conservationRegression_isWellPosed
    (n6ResponseOutput row) (n6ResponseInput column)

/-- The exact Gaussian-rational N6 response `[[0, i], [i, 0]]`. -/
def n6ResponseExactValue : Matrix (Fin 2) (Fin 2) GaussianRational :=
  ![![0, GaussianRational.I], ![GaussianRational.I, 0]]

/-- The emitted exact response embeds to the public proof-gated N6 response. -/
lemma n6ResponseExactReference_sound :
    n6ResponseExactValue.map GaussianRational.toComplex = n6ResponseSemantic := by
  ext row column
  change GaussianRational.toComplex (n6ResponseExactValue row column) =
    conservationRegression.responseTransform conservationRegression_isWellPosed
      (n6ResponseOutput row) (n6ResponseInput column)
  rw [conservationRegression_responseTransform_eq]
  fin_cases row <;> fin_cases column <;>
    norm_num [n6ResponseExactValue, n6ResponseOutput, n6ResponseInput,
      conservationRegressionResponse, GaussianRational.I]

/-- Proof-carrying exact reference for comparison row `N6-NET-RESPONSE`. -/
def n6ResponseExactReference : ExactMatrixReference 2 2 n6ResponseSemantic where
  rowId := "N6-NET-RESPONSE"
  leanDeclaration := "Optics.conservationRegression_responseTransform_eq"
  proofDeclaration := "Optics.n6ResponseExactReference_sound"
  exactField := .gaussianRational
  value := n6ResponseExactValue
  sound := n6ResponseExactReference_sound

/-!

## B. Scalar power references

-/

/-- The first displayed N6 response-column power, embedded in `ℂ` for transport. -/
def n6ColumnAPowerSemantic : ℂ :=
  ((Complex.normSq (conservationRegressionResponse
        (Outgoing.mk conservationRegressionExternalA)
        (Incident.mk conservationRegressionExternalA)) +
      Complex.normSq (conservationRegressionResponse
        (Outgoing.mk conservationRegressionExternalB)
        (Incident.mk conservationRegressionExternalA)) : ℝ) : ℂ)

/-- The first N6 column-power exact value. -/
def n6ColumnAPowerExactValue : GaussianRational := 1

/-- The emitted first column power embeds to the public N6 column-power expression. -/
lemma n6ColumnAPowerExactReference_sound :
    GaussianRational.toComplex n6ColumnAPowerExactValue = n6ColumnAPowerSemantic := by
  rw [n6ColumnAPowerSemantic, conservationRegressionResponse_column_a_power]
  norm_num [n6ColumnAPowerExactValue, QuadraticAlgebra.re_one,
    QuadraticAlgebra.im_one]

/-- Proof-carrying exact reference for comparison row `N6-NET-COL-A`. -/
def n6ColumnAPowerExactReference : ExactScalarReference n6ColumnAPowerSemantic where
  rowId := "N6-NET-COL-A"
  leanDeclaration := "Optics.conservationRegressionResponse_column_a_power"
  proofDeclaration := "Optics.n6ColumnAPowerExactReference_sound"
  exactField := .rational
  value := n6ColumnAPowerExactValue
  sound := n6ColumnAPowerExactReference_sound

/-- The second displayed N6 response-column power, embedded in `ℂ` for transport. -/
def n6ColumnBPowerSemantic : ℂ :=
  ((Complex.normSq (conservationRegressionResponse
        (Outgoing.mk conservationRegressionExternalA)
        (Incident.mk conservationRegressionExternalB)) +
      Complex.normSq (conservationRegressionResponse
        (Outgoing.mk conservationRegressionExternalB)
        (Incident.mk conservationRegressionExternalB)) : ℝ) : ℂ)

/-- The second N6 column-power exact value. -/
def n6ColumnBPowerExactValue : GaussianRational := 1

/-- The emitted second column power embeds to the public N6 column-power expression. -/
lemma n6ColumnBPowerExactReference_sound :
    GaussianRational.toComplex n6ColumnBPowerExactValue = n6ColumnBPowerSemantic := by
  rw [n6ColumnBPowerSemantic, conservationRegressionResponse_column_b_power]
  norm_num [n6ColumnBPowerExactValue, QuadraticAlgebra.re_one,
    QuadraticAlgebra.im_one]

/-- Proof-carrying exact reference for comparison row `N6-NET-COL-B`. -/
def n6ColumnBPowerExactReference : ExactScalarReference n6ColumnBPowerSemantic where
  rowId := "N6-NET-COL-B"
  leanDeclaration := "Optics.conservationRegressionResponse_column_b_power"
  proofDeclaration := "Optics.n6ColumnBPowerExactReference_sound"
  exactField := .rational
  value := n6ColumnBPowerExactValue
  sound := n6ColumnBPowerExactReference_sound

/-!

## C. Cross-entry and coherency references

-/

/-- The two public reciprocal cross-entry expressions, stored as a two-by-one matrix. -/
def n6CrossSemantic : Matrix (Fin 2) (Fin 1) ℂ :=
  ![![conservationRegressionResponse (Outgoing.mk conservationRegressionExternalA)
        (Incident.mk conservationRegressionExternalB)],
    ![conservationRegressionResponse (Outgoing.mk conservationRegressionExternalB)
        (Incident.mk conservationRegressionExternalA)]]

/-- The two exact reciprocal cross entries. -/
def n6CrossExactValue : Matrix (Fin 2) (Fin 1) GaussianRational :=
  ![![GaussianRational.I], ![GaussianRational.I]]

/-- The emitted cross entries embed to the two public N6 cross-entry expressions. -/
lemma n6CrossExactReference_sound :
    n6CrossExactValue.map GaussianRational.toComplex = n6CrossSemantic := by
  rcases conservationRegressionResponse_cross_entries with ⟨hFirst, hSecond⟩
  ext row column
  change GaussianRational.toComplex (n6CrossExactValue row column) =
    n6CrossSemantic row column
  fin_cases row <;> fin_cases column <;>
    norm_num [n6CrossExactValue, n6CrossSemantic, hFirst, hSecond,
      GaussianRational.I]

/-- Proof-carrying exact reference for comparison row `N6-NET-CROSS`. -/
def n6CrossExactReference : ExactMatrixReference 2 1 n6CrossSemantic where
  rowId := "N6-NET-CROSS"
  leanDeclaration := "Optics.conservationRegressionResponse_cross_entries"
  proofDeclaration := "Optics.n6CrossExactReference_sound"
  exactField := .gaussianRational
  value := n6CrossExactValue
  sound := n6CrossExactReference_sound

/-- The public asymmetric N6 coherency expression, entry by entry. -/
def n6CoherencySemantic : Matrix (Fin 2) (Fin 2) ℂ := fun row column ↦
  ((CoherencyMatrix.ofChannelPowers conservationCoherencyRegressionPowers
      conservationCoherencyRegressionPowers_nonneg).map
    conservationCoherencyRegressionTransform).toMatrix row column

/-- The exact transported coherency matrix `[[3, 2-2i], [2+2i, 6]]`. -/
def n6CoherencyExactValue : Matrix (Fin 2) (Fin 2) GaussianRational :=
  ![![GaussianRational.ofParts 3 0, GaussianRational.ofParts 2 (-2)],
    ![GaussianRational.ofParts 2 2, GaussianRational.ofParts 6 0]]

/-- The emitted coherency matrix embeds to the public N6 coherency expression. -/
lemma n6CoherencyExactReference_sound :
    n6CoherencyExactValue.map GaussianRational.toComplex = n6CoherencySemantic := by
  ext row column
  change GaussianRational.toComplex (n6CoherencyExactValue row column) =
    n6CoherencySemantic row column
  rw [n6CoherencySemantic, conservationCoherencyRegression_diagonal_map_apply]
  fin_cases row <;> fin_cases column <;>
    norm_num [n6CoherencyExactValue, GaussianRational.ofParts, sub_eq_add_neg]

/-- Proof-carrying exact reference for comparison row `N6-COHERENCY`. -/
def n6CoherencyExactReference : ExactMatrixReference 2 2 n6CoherencySemantic where
  rowId := "N6-COHERENCY"
  leanDeclaration := "Optics.conservationCoherencyRegression_diagonal_map_apply"
  proofDeclaration := "Optics.n6CoherencyExactReference_sound"
  exactField := .gaussianRational
  value := n6CoherencyExactValue
  sound := n6CoherencyExactReference_sound

end

/-!

## D. Manifest and hostile sentinel

-/

/-- The ordered validation statement snapshot for the five N6 quantities. -/
def n6ExactReferenceStatementSnapshot : List String :=
  ["Optics.conservationRegression_responseTransform_eq",
    "Optics.conservationRegressionResponse_column_a_power",
    "Optics.conservationRegressionResponse_column_b_power",
    "Optics.conservationRegressionResponse_cross_entries",
    "Optics.conservationCoherencyRegression_diagonal_map_apply"]

/-- The five certified N6 references in validation transport order. -/
def n6ExactReferences : List ExactReference :=
  [ExactReference.ofMatrixValue "N6-NET-RESPONSE"
      "Optics.conservationRegression_responseTransform_eq"
      "Optics.n6ResponseExactReference_sound" .gaussianRational n6ResponseExactValue,
    ExactReference.ofScalarValue "N6-NET-COL-A"
      "Optics.conservationRegressionResponse_column_a_power"
      "Optics.n6ColumnAPowerExactReference_sound" .rational n6ColumnAPowerExactValue,
    ExactReference.ofScalarValue "N6-NET-COL-B"
      "Optics.conservationRegressionResponse_column_b_power"
      "Optics.n6ColumnBPowerExactReference_sound" .rational n6ColumnBPowerExactValue,
    ExactReference.ofMatrixValue "N6-NET-CROSS"
      "Optics.conservationRegressionResponse_cross_entries"
      "Optics.n6CrossExactReference_sound" .gaussianRational n6CrossExactValue,
    ExactReference.ofMatrixValue "N6-COHERENCY"
      "Optics.conservationCoherencyRegression_diagonal_map_apply"
      "Optics.n6CoherencyExactReference_sound" .gaussianRational n6CoherencyExactValue]

/-- The executable table is exactly the transport projection of the five certificates. -/
lemma n6ExactReferences_eq_certificates :
    n6ExactReferences =
      [n6ResponseExactReference.toReference,
        n6ColumnAPowerExactReference.toReference,
        n6ColumnBPowerExactReference.toReference,
        n6CrossExactReference.toReference,
        n6CoherencyExactReference.toReference] := by
  rfl

/-- The transport table contains five distinct comparison-contract row identifiers. -/
lemma n6ExactReferences_rowIds_nodup :
    (n6ExactReferences.map ExactReference.rowId).Nodup := by
  simp [n6ExactReferences, ExactReference.ofMatrixValue,
    ExactReference.ofScalarValue]

/-- The emitted semantic declaration names match the validation statement snapshot. -/
lemma n6ExactReferences_declarations_eq_snapshot :
    n6ExactReferences.map ExactReference.leanDeclaration =
      n6ExactReferenceStatementSnapshot := by
  rfl

/-- The coherency entry rejects both transposition and its resulting imaginary-sign flip.

This proof expands only the table certificate and its exact Gaussian-rational primitives. It does
not use any sound theorem or semantic coherency declaration. -/
lemma n6CoherencyExactReference_rejects_transposed_sign :
    (n6ExactReferences[4]).values[1] = GaussianRational.ofParts 2 (-2) ∧
      (n6ExactReferences[4]).values[1] ≠ GaussianRational.ofParts 2 2 := by
  norm_num [n6ExactReferences, ExactReference.ofMatrixValue,
    n6CoherencyExactValue, GaussianRational.ofParts, QuadraticAlgebra.ext_iff,
    List.finRange_succ]

end Optics
