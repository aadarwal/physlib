/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Lean.Data.Json
public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.List.FinRange
public import Mathlib.Data.Matrix.Basic

/-!
# Proof-carrying exact references for optical networks

## i. Overview

This file supplies an executable Gaussian-rational carrier and certificate types for exact circuit
references. A certificate stores transport metadata and an exact value while indexing the type by
the semantic expression it certifies. Its `sound` field is a kernel-checked equality after embedding
the exact value in `ℂ`.

The proof contract is deliberately explicit. A bare `decide` was attempted on a derived rational
matrix expression and failed inside rational normalization, while unfolded `norm_num` closed the
same equality. Family adapters should therefore expose their finite formulas and use `norm_num`,
not assume that bare decision reduction will normalize derived rational matrices.

The JSON emitter is transport; each sound theorem is the certificate; a buggy emitter is caught by
exact regeneration, never by trusting it. A computational family table is joined to the scalar and
matrix certificate conversions by a kernel-checked equality.

## ii. Key results

- `Optics.GaussianRational`: the computable exact field `ℚ(i)`.
- `Optics.GaussianRational.toComplex`: the embedding sending the generator to `Complex.I`.
- `Optics.ExactScalarReference`: a proof-carrying scalar reference.
- `Optics.ExactMatrixReference`: a proof-carrying finite matrix reference.
- `Optics.ExactReference.manifestJson`: deterministic canonical JSON transport.

## iii. Table of contents

- A. Gaussian-rational carrier
- B. Proof-carrying references
- C. Canonical JSON transport

## iv. References

The carrier is Mathlib's `QuadraticAlgebra` structure
(`Mathlib/Algebra/QuadraticAlgebra/Defs.lean:38` at `db584cd6`). The embedding uses
`QuadraticAlgebra.lift` (`Mathlib/Algebra/QuadraticAlgebra/Basic.lean:106`), and the executable
inverse and field instances are declared at lines 401 and 406 of that file at the same ref.

this slice covers the FIVE hand-typed N6 quantities (Q(i) circuit tier); the circuit-tier fence is
83 rows (43 Q + 40 Q(i)), the field fence is 93, the contract population is 112 - never conflate
the three; the 19-row transcendental/algebraic residual stays on its current leg by name.

No floating-point evaluator, generic matrix solver, circuit semantics, validation parser, or claim
beyond the N6 pilot is introduced here.

-/

@[expose] public section

namespace Optics

open Lean

/-!

## A. Gaussian-rational carrier

-/

/-- Gaussian rationals, represented as the quadratic algebra `ℚ[i]` with `i² = -1`. -/
abbrev GaussianRational := QuadraticAlgebra ℚ (-1) 0

namespace GaussianRational

/-- No rational square is negative one, supplying the constructive field gate for `ℚ[i]`. -/
instance noRationalRoot : Fact (∀ r : ℚ, r ^ 2 ≠ (-1 : ℚ) + 0 * r) :=
  ⟨fun r h ↦ by nlinarith [sq_nonneg r]⟩

/-- The distinguished Gaussian-rational generator `i`. -/
def I : GaussianRational := ⟨0, 1⟩

/-- Construct a Gaussian rational from its real and imaginary rational parts. -/
def ofParts (re im : ℚ) : GaussianRational := ⟨re, im⟩

/-- The Gaussian-rational embedding into `ℂ`, sending the generator to `Complex.I`. -/
noncomputable def toComplex : GaussianRational →+* ℂ :=
  (QuadraticAlgebra.lift (R := ℚ) (a := (-1 : ℚ)) (b := 0)
    ⟨Complex.I, by norm_num [Complex.I_mul_I]⟩).toRingHom

/-- The complex embedding reads the two stored rational coordinates literally. -/
@[simp]
lemma toComplex_apply (value : GaussianRational) :
    toComplex value = (value.re : ℂ) + (value.im : ℂ) * Complex.I := by
  simp [toComplex, QuadraticAlgebra.lift_apply_apply, Algebra.smul_def]

/-- Embedding the Gaussian-rational generator gives the complex imaginary unit. -/
lemma toComplex_I : toComplex I = Complex.I := by
  norm_num [I]

/-- Embedding explicit rational coordinates gives the corresponding complex number. -/
lemma toComplex_ofParts (re im : ℚ) :
    toComplex (ofParts re im) = (re : ℂ) + (im : ℂ) * Complex.I := by
  norm_num [ofParts]

end GaussianRational

/-!

## B. Proof-carrying references

-/

/-- The smallest exact field needed by a transported reference value. -/
inductive ExactReferenceField where
  /-- A rational value. -/
  | rational
  /-- A Gaussian-rational value. -/
  | gaussianRational
  deriving DecidableEq

/-- A scalar exact reference indexed by the semantic complex expression it certifies. -/
structure ExactScalarReference (semantic : ℂ) where
  /-- Stable comparison-contract row identifier. -/
  rowId : String
  /-- Public Lean declaration whose semantic expression is represented. -/
  leanDeclaration : String
  /-- Public kernel-checked equality declaration certifying the exact value. -/
  proofDeclaration : String
  /-- Smallest exact field containing the value. -/
  exactField : ExactReferenceField
  /-- Exact Gaussian-rational transport value. -/
  value : GaussianRational
  /-- The exact value embeds to the indexed semantic expression. -/
  sound : GaussianRational.toComplex value = semantic

/-- A matrix exact reference indexed by its dimensions and semantic complex matrix. -/
structure ExactMatrixReference (rows columns : ℕ)
    (semantic : Matrix (Fin rows) (Fin columns) ℂ) where
  /-- Stable comparison-contract row identifier. -/
  rowId : String
  /-- Public Lean declaration whose semantic expression is represented. -/
  leanDeclaration : String
  /-- Public kernel-checked equality declaration certifying the exact matrix. -/
  proofDeclaration : String
  /-- Smallest exact field containing every entry. -/
  exactField : ExactReferenceField
  /-- Exact matrix in row-major index order. -/
  value : Matrix (Fin rows) (Fin columns) GaussianRational
  /-- Entrywise embedding gives the indexed semantic matrix. -/
  sound : value.map GaussianRational.toComplex = semantic

/-- Whether an encoded reference is scalar or matrix-valued. -/
inductive ExactReferenceKind where
  /-- A scalar payload. -/
  | scalar
  /-- A row-major matrix payload. -/
  | matrix
  deriving DecidableEq

/-- Serializable data obtained only through a proof-carrying reference constructor. -/
structure ExactReference where
  /-- Stable comparison-contract row identifier. -/
  rowId : String
  /-- Public Lean semantic declaration. -/
  leanDeclaration : String
  /-- Public Lean certificate declaration. -/
  proofDeclaration : String
  /-- Smallest exact field containing the payload. -/
  exactField : ExactReferenceField
  /-- Scalar or matrix payload tag. -/
  kind : ExactReferenceKind
  /-- Empty for scalars and `[rows, columns]` for matrices. -/
  shape : List ℕ
  /-- One scalar or a flattened row-major matrix. -/
  values : List GaussianRational

/-- Build the serializable payload of an exact scalar value. -/
def ExactReference.ofScalarValue (rowId leanDeclaration proofDeclaration : String)
    (exactField : ExactReferenceField) (value : GaussianRational) : ExactReference :=
  .mk rowId leanDeclaration proofDeclaration exactField .scalar [] [value]

/-- Build the serializable row-major payload of an exact matrix value. -/
def ExactReference.ofMatrixValue {rows columns : ℕ}
    (rowId leanDeclaration proofDeclaration : String) (exactField : ExactReferenceField)
    (value : Matrix (Fin rows) (Fin columns) GaussianRational) : ExactReference :=
  .mk rowId leanDeclaration proofDeclaration exactField .matrix [rows, columns]
    ((List.finRange rows).flatMap fun row ↦
      (List.finRange columns).map fun column ↦ value row column)

/-- Erase a scalar certificate to its serializable transport payload. -/
def ExactScalarReference.toReference {semantic : ℂ}
    (reference : ExactScalarReference semantic) : ExactReference :=
  ExactReference.ofScalarValue reference.rowId reference.leanDeclaration
    reference.proofDeclaration reference.exactField reference.value

/-- Erase a matrix certificate to a row-major serializable transport payload. -/
def ExactMatrixReference.toReference {rows columns : ℕ}
    {semantic : Matrix (Fin rows) (Fin columns) ℂ}
    (reference : ExactMatrixReference rows columns semantic) : ExactReference :=
  ExactReference.ofMatrixValue reference.rowId reference.leanDeclaration
    reference.proofDeclaration reference.exactField reference.value

/-!

## C. Canonical JSON transport

-/

/-- Canonical field label used by the exact-reference JSON schema. -/
def ExactReferenceField.jsonLabel : ExactReferenceField → String
  | .rational => "Q"
  | .gaussianRational => "Q(i)"

/-- Encode a normalized rational as a signed numerator and positive denominator. -/
def rationalJson (value : ℚ) : Json :=
  Json.mkObj [("num", (value.num : Json)), ("den", (value.den : Json))]

/-- Encode a Gaussian rational as canonical real and imaginary rational pairs. -/
def GaussianRational.toJson (value : GaussianRational) : Json :=
  Json.mkObj [("re", rationalJson value.re), ("im", rationalJson value.im)]

/-- Encode the scalar or row-major value payload of an exact reference. -/
def ExactReference.valueJson (reference : ExactReference) : Json :=
  match reference.kind, reference.values with
  | .scalar, [value] => GaussianRational.toJson value
  | .matrix, values => .arr (values.map GaussianRational.toJson).toArray
  | _, _ => .null

/-- Encode one exact reference using the canonical transport schema. -/
def ExactReference.toJson (reference : ExactReference) : Json :=
  Json.mkObj
    [("row_id", reference.rowId),
      ("lean_declaration", reference.leanDeclaration),
      ("proof_declaration", reference.proofDeclaration),
      ("field", reference.exactField.jsonLabel),
      ("shape", .arr (reference.shape.map fun value ↦ (value : Json)).toArray),
      ("value", reference.valueJson)]

/-- Encode a complete exact-reference manifest at a named Physlib commit. -/
def ExactReference.manifestJson (physlibRef : String)
    (references : List ExactReference) : Json :=
  Json.mkObj
    [("schema_version", (1 : Json)),
      ("physlib_ref", physlibRef),
      ("references", .arr (references.map ExactReference.toJson).toArray)]

/-- Render a manifest deterministically and terminate it with one newline. -/
def ExactReference.manifestString (physlibRef : String)
    (references : List ExactReference) : String :=
  (ExactReference.manifestJson physlibRef references).pretty ++ "\n"

end Optics
