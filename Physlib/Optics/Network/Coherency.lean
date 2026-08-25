/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Mathlib.Analysis.Matrix.PosDef
public import Physlib.Optics.Network.Conservation
public import Physlib.Optics.Polarization.Coherency

/-!
# Coherent and incoherent network observables

## i. Overview

A complex mode amplitude describes a fully coherent field. Partially coherent and mutually
uncorrelated illumination is second-order data, so this file states network observables through
the positive-semidefinite coherency matrices of `Physlib/Optics/Polarization/Coherency.lean`
rather than by deleting phase-sensitive cross terms from amplitudes.

For a well-posed netlist with external response `H`, the transported coherency is
`Γ_out = H * Γ_in * Hᴴ`, which is `CoherencyMatrix.map` at
`Physlib/Optics/Polarization/Coherency.lean:113`. Channel powers are the diagonal entries of
`Γ_out` and total power is its trace, both in the same normalized modal convention used by
`Physlib/Optics/Network/Conservation.lean`.

The cross-term theorem is stated as a pair. For a coherent superposition of two amplitudes the
output channel power carries the explicit interference term `2 * (u i * star (v i)).re`; for the
decorrelated superposition, whose second-order data is the sum of the two coherency matrices, the
same channel power is exactly additive. The interference term is therefore proved to be exactly
the difference between the two models rather than dropped.

## ii. Scope and non-claims

Coherency data is not redefined here: `CoherencyMatrix`, `CoherencyMatrix.map`,
`CoherencyMatrix.trace`, and the self-adjoint congruence
`Matrix.selfAdjointCongruence` are used as given.

`CoherencyMatrix.ofAmplitude` is rank-one second-order data, so it models a fully coherent field
and nothing else. `CoherencyMatrix.incoherentSum` is the second-order data of two mutually
uncorrelated contributions; calling it incoherent is a modelling statement about the input, not a
theorem, and every result that uses it states it as a hypothesis on the supplied data.

All powers are `ModeAmplitude.power`, normalized modal power. No spectral density, temporal
coherence function, bandwidth, detector model, or ergodicity assumption is introduced: a coherency
matrix here is a fixed second-order datum at one frequency, not a time average that has been
proved to exist.

## iii. Key definitions and results

- `CoherencyMatrix.ofAmplitude`: rank-one coherency data of a coherent mode amplitude.
- `CoherencyMatrix.channelPower`: the per-channel power observable, a diagonal entry.
- `CoherencyMatrix.trace_eq_sum_channelPower`: total power is the sum of channel powers.
- `CoherencyMatrix.map_ofAmplitude`: coherent transport agrees with amplitude transport.
- `CoherencyMatrix.incoherentSum`: the second-order data of decorrelated contributions.
- `CoherencyMatrix.channelPower_map_incoherentSum`: decorrelated channel powers are additive.
- `CoherencyMatrix.channelPower_map_ofAmplitude_add`: coherent channel power with its explicit
  interference term.
- `CoherencyMatrix.channelPower_map_sub_channelPower_map_incoherentSum`: the interference term is
  exactly the coherent-minus-decorrelated difference.
- `CoherencyMatrix.trace_map_le_of_isPassive` and
  `CoherencyMatrix.trace_map_of_isPowerPreserving`: passivity and conservation of transport.
- `FlatNetlist.responseCoherency` and its passivity, conservation, and coherent-input laws.

## iv. Table of contents

- A. Second-order data of a mode amplitude
- B. Coherency transport by a mode transform
- C. Decorrelated superposition
- D. The interference cross term
- E. Passivity and conservation of coherency transport
- F. Network response coherency

-/

@[expose] public section

namespace Optics

open Matrix
open scoped ComplexConjugate ComplexOrder

noncomputable section

universe u v w x

/-!

## A. Second-order data of a mode amplitude

-/

namespace CoherencyMatrix

/-- The rank-one coherency data of a fully coherent mode amplitude.

Its entries are `a i * star (a j)`, so every relative phase of the amplitude is retained. This
construction models a coherent field only; partially coherent light is not of this form. -/
def ofAmplitude {ι : Type*} [Finite ι] (amplitude : ModeAmplitude ι) : CoherencyMatrix ι where
  toMatrix := Matrix.vecMulVec (WithLp.ofLp amplitude) (star (WithLp.ofLp amplitude))
  posSemidef := Matrix.posSemidef_vecMulVec_self_star _

/-- Coherent second-order data is the amplitude outer product. -/
@[simp]
lemma ofAmplitude_toMatrix {ι : Type*} [Finite ι] (amplitude : ModeAmplitude ι) :
    (ofAmplitude amplitude).toMatrix =
      Matrix.vecMulVec (WithLp.ofLp amplitude) (star (WithLp.ofLp amplitude)) := rfl

/-- A coherent coherency entry is the corresponding amplitude outer-product entry. -/
@[simp]
lemma ofAmplitude_apply {ι : Type*} [Finite ι] (amplitude : ModeAmplitude ι) (row column : ι) :
    (ofAmplitude amplitude).toMatrix row column =
      amplitude row * star (amplitude column) := rfl

/-- The normalized modal power carried by one channel, read off the coherency diagonal. -/
def channelPower {ι : Type*} (coherency : CoherencyMatrix ι) (channel : ι) : ℝ :=
  (coherency.toMatrix channel channel).re

/-- Channel power is nonnegative. -/
lemma channelPower_nonneg {ι : Type*} (coherency : CoherencyMatrix ι) (channel : ι) :
    0 ≤ coherency.channelPower channel :=
  coherency.diagonal_re_nonneg channel

/-- Total coherency power is the sum of the channel powers. -/
lemma trace_eq_sum_channelPower {ι : Type*} [Fintype ι] (coherency : CoherencyMatrix ι) :
    coherency.trace = ∑ channel : ι, coherency.channelPower channel := by
  simp only [CoherencyMatrix.trace, channelPower, Matrix.trace, Matrix.diag_apply,
    Complex.re_sum]

/-- The channel powers of coherent data are the squared amplitude moduli. -/
@[simp]
lemma ofAmplitude_channelPower {ι : Type*} [Finite ι] (amplitude : ModeAmplitude ι)
    (channel : ι) :
    (ofAmplitude amplitude).channelPower channel = Complex.normSq (amplitude channel) := by
  simp only [channelPower, ofAmplitude_apply, RCLike.star_def, Complex.mul_conj,
    Complex.ofReal_re]

/-- The total power of coherent data is the modal power of its amplitude. -/
@[simp]
lemma ofAmplitude_trace {ι : Type*} [Fintype ι] (amplitude : ModeAmplitude ι) :
    (ofAmplitude amplitude).trace = amplitude.power := by
  rw [trace_eq_sum_channelPower, ModeAmplitude.power_eq_sum_normSq]
  exact Finset.sum_congr rfl fun channel _ => ofAmplitude_channelPower amplitude channel

/-!

## B. Coherency transport by a mode transform

-/

/-- Transporting coherent data through a mode transform agrees with transporting the amplitude.

This is the statement that `Γ ↦ T Γ Tᴴ` restricts on rank-one data to the ordinary amplitude
action, so the coherent model is a special case of the second-order model rather than a rival to
it. -/
lemma map_ofAmplitude {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (amplitude : ModeAmplitude ι) (transform : ModeTransform ι κ) :
    (ofAmplitude amplitude).map transform =
      ofAmplitude (transform.toLinearMap amplitude) := by
  apply CoherencyMatrix.ext
  show transform *
      Matrix.vecMulVec (WithLp.ofLp amplitude) (star (WithLp.ofLp amplitude)) * transformᴴ =
    Matrix.vecMulVec (Matrix.mulVec transform (WithLp.ofLp amplitude))
      (star (Matrix.mulVec transform (WithLp.ofLp amplitude)))
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, ← Matrix.star_mulVec]

/-- The channel powers of transported coherent data are the transported amplitude moduli. -/
lemma channelPower_map_ofAmplitude {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (amplitude : ModeAmplitude ι) (transform : ModeTransform ι κ) (channel : κ) :
    ((ofAmplitude amplitude).map transform).channelPower channel =
      Complex.normSq (transform.toLinearMap amplitude channel) := by
  rw [map_ofAmplitude, ofAmplitude_channelPower]

/-!

## C. Decorrelated superposition

-/

/-- The second-order data of two mutually uncorrelated contributions.

Adding coherency matrices is the decorrelation model: the cross correlations between the two
contributions are taken to vanish. This is a hypothesis about the supplied illumination, never a
theorem about two amplitudes. -/
def incoherentSum {ι : Type*} [Fintype ι] (first second : CoherencyMatrix ι) :
    CoherencyMatrix ι where
  toMatrix := first.toMatrix + second.toMatrix
  posSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
      (first.isHermitian.add second.isHermitian) fun vector => ?_
    rw [Matrix.add_mulVec, dotProduct_add]
    exact add_nonneg (first.posSemidef.dotProduct_mulVec_nonneg vector)
      (second.posSemidef.dotProduct_mulVec_nonneg vector)

/-- Decorrelated second-order data is the sum of the two coherency matrices. -/
@[simp]
lemma incoherentSum_toMatrix {ι : Type*} [Fintype ι] (first second : CoherencyMatrix ι) :
    (first.incoherentSum second).toMatrix = first.toMatrix + second.toMatrix := rfl

/-- Decorrelated channel powers add. -/
@[simp]
lemma incoherentSum_channelPower {ι : Type*} [Fintype ι] (first second : CoherencyMatrix ι)
    (channel : ι) :
    (first.incoherentSum second).channelPower channel =
      first.channelPower channel + second.channelPower channel := by
  simp only [channelPower, incoherentSum_toMatrix, Matrix.add_apply, Complex.add_re]

/-- Decorrelated total powers add. -/
@[simp]
lemma incoherentSum_trace {ι : Type*} [Fintype ι] (first second : CoherencyMatrix ι) :
    (first.incoherentSum second).trace = first.trace + second.trace := by
  simp only [trace_eq_sum_channelPower, incoherentSum_channelPower, Finset.sum_add_distrib]

/-- Transport is additive on decorrelated second-order data. -/
lemma map_incoherentSum {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (first second : CoherencyMatrix ι) (transform : ModeTransform ι κ) :
    (first.incoherentSum second).map transform =
      (first.map transform).incoherentSum (second.map transform) := by
  apply CoherencyMatrix.ext
  show transform * (first.toMatrix + second.toMatrix) * transformᴴ =
    transform * first.toMatrix * transformᴴ + transform * second.toMatrix * transformᴴ
  rw [Matrix.mul_add, Matrix.add_mul]

/-!

## D. The interference cross term

-/

/-- Decorrelated inputs have exactly additive output channel powers.

No interference term appears, and none was deleted: the decorrelation hypothesis is carried by the
supplied second-order data. -/
lemma channelPower_map_incoherentSum {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (first second : CoherencyMatrix ι) (transform : ModeTransform ι κ) (channel : κ) :
    ((first.incoherentSum second).map transform).channelPower channel =
      ((first.map transform).channelPower channel) +
        ((second.map transform).channelPower channel) := by
  rw [map_incoherentSum, incoherentSum_channelPower]

/-- Decorrelated inputs have exactly additive total output power. -/
lemma trace_map_incoherentSum {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (first second : CoherencyMatrix ι) (transform : ModeTransform ι κ) :
    ((first.incoherentSum second).map transform).trace =
      (first.map transform).trace + (second.map transform).trace := by
  rw [map_incoherentSum, incoherentSum_trace]

/-- A coherent superposition of two amplitudes carries the explicit interference term
`2 * (u channel * star (v channel)).re` in every output channel power. -/
lemma channelPower_map_ofAmplitude_add {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (first second : ModeAmplitude ι) (transform : ModeTransform ι κ) (channel : κ) :
    ((ofAmplitude (first + second)).map transform).channelPower channel =
      Complex.normSq (transform.toLinearMap first channel) +
          Complex.normSq (transform.toLinearMap second channel) +
        2 * (transform.toLinearMap first channel *
          star (transform.toLinearMap second channel)).re := by
  rw [channelPower_map_ofAmplitude, map_add]
  exact Complex.normSq_add _ _

/-- The interference term is exactly the coherent-minus-decorrelated difference in every output
channel.

This makes the cross term a proved quantity rather than a modelling convenience: it vanishes
exactly when the supplied second-order data is the decorrelated sum. -/
lemma channelPower_map_ofAmplitude_add_sub_incoherentSum
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (first second : ModeAmplitude ι) (transform : ModeTransform ι κ) (channel : κ) :
    ((ofAmplitude (first + second)).map transform).channelPower channel -
        (((ofAmplitude first).incoherentSum (ofAmplitude second)).map transform).channelPower
          channel =
      2 * (transform.toLinearMap first channel *
        star (transform.toLinearMap second channel)).re := by
  rw [channelPower_map_ofAmplitude_add, channelPower_map_incoherentSum,
    channelPower_map_ofAmplitude, channelPower_map_ofAmplitude]
  ring

/-!

## E. Passivity and conservation of coherency transport

-/

/-- The trace of a product of positive-semidefinite matrices is nonnegative.

The proof diagonalizes the right factor and uses that congruence preserves positive
semidefiniteness, so every diagonal weight and every eigenvalue in the resulting sum is
nonnegative. -/
lemma trace_mul_nonneg_of_posSemidef {ι : Type*} [Fintype ι] [DecidableEq ι]
    {left right : Matrix ι ι ℂ} (hLeft : left.PosSemidef) (hRight : right.PosSemidef) :
    0 ≤ (left * right).trace := by
  classical
  have hCongruence :
      ((hRight.1.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ * left *
        (hRight.1.eigenvectorUnitary : Matrix ι ι ℂ)).PosSemidef := by
    simpa only [Matrix.conjTranspose_conjTranspose] using
      hLeft.conjTranspose_mul_mul_same (hRight.1.eigenvectorUnitary : Matrix ι ι ℂ)
  have hRightEq :
      right = (hRight.1.eigenvectorUnitary : Matrix ι ι ℂ) *
          Matrix.diagonal (fun index : ι => ((hRight.1.eigenvalues index : ℝ) : ℂ)) *
            (hRight.1.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ := by
    conv_lhs => rw [hRight.1.spectral_theorem]
    rfl
  have hReassociate :
      left * ((hRight.1.eigenvectorUnitary : Matrix ι ι ℂ) *
          Matrix.diagonal (fun index : ι => ((hRight.1.eigenvalues index : ℝ) : ℂ)) *
            (hRight.1.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ) =
        left * (hRight.1.eigenvectorUnitary : Matrix ι ι ℂ) *
            Matrix.diagonal (fun index : ι => ((hRight.1.eigenvalues index : ℝ) : ℂ)) *
          (hRight.1.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ := by
    simp only [Matrix.mul_assoc]
  have hCycle :
      (hRight.1.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ *
          (left * (hRight.1.eigenvectorUnitary : Matrix ι ι ℂ) *
            Matrix.diagonal (fun index : ι => ((hRight.1.eigenvalues index : ℝ) : ℂ))) =
        (hRight.1.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ * left *
            (hRight.1.eigenvectorUnitary : Matrix ι ι ℂ) *
          Matrix.diagonal (fun index : ι => ((hRight.1.eigenvalues index : ℝ) : ℂ)) := by
    simp only [Matrix.mul_assoc]
  rw [hRightEq, hReassociate, Matrix.trace_mul_comm, hCycle]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_diagonal]
  refine Finset.sum_nonneg fun index _ => ?_
  refine mul_nonneg hCongruence.diag_nonneg ?_
  exact Complex.nonneg_iff.mpr ⟨by simpa using hRight.eigenvalues_nonneg index, by simp⟩

/-- Coherency transport through a passive mode transform never increases total power. -/
lemma trace_map_le_of_isPassive {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (coherency : CoherencyMatrix ι) {transform : ModeTransform ι κ}
    (hTransform : transform.IsPassive) :
    (coherency.map transform).trace ≤ coherency.trace := by
  classical
  have hDefect : ((1 : ModeTransform ι ι) - transformᴴ * transform).PosSemidef :=
    (ModeTransform.isPassive_iff_posSemidef_one_sub_conjTranspose_mul_self transform).mp
      hTransform
  have hNonneg :
      0 ≤ (coherency.toMatrix * ((1 : ModeTransform ι ι) - transformᴴ * transform)).trace :=
    trace_mul_nonneg_of_posSemidef coherency.posSemidef hDefect
  have hExpand :
      (coherency.toMatrix * ((1 : ModeTransform ι ι) - transformᴴ * transform)).trace =
        Matrix.trace coherency.toMatrix -
          Matrix.trace (transform * coherency.toMatrix * transformᴴ) := by
    rw [Matrix.mul_sub, Matrix.trace_sub, Matrix.mul_one]
    congr 1
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
  rw [hExpand] at hNonneg
  have hReal := (Complex.nonneg_iff.mp hNonneg).1
  rw [Complex.sub_re] at hReal
  change 0 ≤ (Matrix.trace coherency.toMatrix).re -
    (Matrix.trace (transform * coherency.toMatrix * transformᴴ)).re at hReal
  exact sub_nonneg.mp hReal

/-- Coherency transport through a power-preserving mode transform conserves total power. -/
lemma trace_map_of_isPowerPreserving {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (coherency : CoherencyMatrix ι) {transform : ModeTransform ι κ}
    (hTransform : transform.IsPowerPreserving) :
    (coherency.map transform).trace = coherency.trace := by
  classical
  have hIsometry : transformᴴ * transform = 1 :=
    (ModeTransform.isPowerPreserving_iff_conjTranspose_mul_self transform).mp hTransform
  have hTrace :
      Matrix.trace (transform * coherency.toMatrix * transformᴴ) =
        Matrix.trace coherency.toMatrix := by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hIsometry, Matrix.one_mul]
  change (Matrix.trace (transform * coherency.toMatrix * transformᴴ)).re = _
  rw [hTrace]
  rfl

end CoherencyMatrix

/-!

## F. Network response coherency

-/

namespace FlatNetlist

variable (netlist : FlatNetlist.{u, v, w, x})

section Finite

variable [Fintype netlist.Channel] [Fintype netlist.ConnectedChannel]

/-- Classical equality on aggregate channels, kept local to finite coherency statements. -/
local instance coherencyChannelDecidableEq : DecidableEq netlist.Channel := Classical.decEq _

/-- Classical equality on connected channels, kept local to finite coherency statements. -/
local instance coherencyConnectedChannelDecidableEq :
    DecidableEq netlist.ConnectedChannel := Classical.decEq _

/-- The external complement of the finite aggregate and connected channel families is finite. -/
local instance coherencyExternalChannelFintype : Fintype netlist.ExternalChannel := by
  classical
  infer_instance

/-- Classical equality on the external channels exposed by the netlist. -/
local instance coherencyExternalChannelDecidableEq :
    DecidableEq netlist.ExternalChannel := Classical.decEq _

/-- The transported second-order data `Γ_out = H * Γ_in * Hᴴ` of a well-posed network. -/
def responseCoherency (hWellPosed : netlist.IsWellPosed)
    (input : CoherencyMatrix netlist.ExternalIncident) :
    CoherencyMatrix netlist.ExternalOutgoing :=
  input.map (netlist.responseTransform hWellPosed)

/-- Network coherency transport is congruence by the external response. -/
@[simp]
lemma responseCoherency_toMatrix (hWellPosed : netlist.IsWellPosed)
    (input : CoherencyMatrix netlist.ExternalIncident) :
    (netlist.responseCoherency hWellPosed input).toMatrix =
      netlist.responseTransform hWellPosed * input.toMatrix *
        (netlist.responseTransform hWellPosed)ᴴ := rfl

/-- Network coherency transport is the self-adjoint congruence of the external response. -/
lemma responseCoherency_toSelfAdjoint (hWellPosed : netlist.IsWellPosed)
    (input : CoherencyMatrix netlist.ExternalIncident) :
    (netlist.responseCoherency hWellPosed input).toSelfAdjoint =
      Matrix.selfAdjointCongruence (netlist.responseTransform hWellPosed)
        input.toSelfAdjoint :=
  CoherencyMatrix.map_toSelfAdjoint _ _

/-- A coherent input is transported to the coherent data of the transported amplitude. -/
lemma responseCoherency_ofAmplitude (hWellPosed : netlist.IsWellPosed)
    (input : ModeAmplitude netlist.ExternalIncident) :
    netlist.responseCoherency hWellPosed (CoherencyMatrix.ofAmplitude input) =
      CoherencyMatrix.ofAmplitude
        ((netlist.responseTransform hWellPosed).toLinearMap input) :=
  CoherencyMatrix.map_ofAmplitude input (netlist.responseTransform hWellPosed)

/-- Total output power is the sum of the external channel powers. -/
lemma responseCoherency_trace_eq_sum_channelPower (hWellPosed : netlist.IsWellPosed)
    (input : CoherencyMatrix netlist.ExternalIncident) :
    (netlist.responseCoherency hWellPosed input).trace =
      ∑ channel : netlist.ExternalOutgoing,
        (netlist.responseCoherency hWellPosed input).channelPower channel :=
  CoherencyMatrix.trace_eq_sum_channelPower _

/-- Coherency transport through a well-posed passive network never increases total power. -/
lemma responseCoherency_trace_le_of_isPassive
    (hWellPosed : netlist.IsWellPosed)
    (hScattering : netlist.scatteringTransform.IsPassive)
    (input : CoherencyMatrix netlist.ExternalIncident) :
    (netlist.responseCoherency hWellPosed input).trace ≤ input.trace :=
  CoherencyMatrix.trace_map_le_of_isPassive input
    (netlist.responseTransform_isPassive hWellPosed hScattering)

/-- Coherency transport through a well-posed lossless network conserves total power. -/
lemma responseCoherency_trace_of_isPowerPreserving
    (hWellPosed : netlist.IsWellPosed)
    (hScattering : netlist.scatteringTransform.IsPowerPreserving)
    (input : CoherencyMatrix netlist.ExternalIncident) :
    (netlist.responseCoherency hWellPosed input).trace = input.trace :=
  CoherencyMatrix.trace_map_of_isPowerPreserving input
    (netlist.responseTransform_isPowerPreserving hWellPosed hScattering)

/-- Second-order power conservation stated directly from component unitarity. -/
lemma responseCoherency_trace_of_components_isLossless
    [Fintype netlist.components.Component] [DecidableEq netlist.components.Component]
    [∀ component, Fintype (netlist.components.portFamily component).Channel]
    [∀ component, DecidableEq (netlist.components.portFamily component).Channel]
    (hWellPosed : netlist.IsWellPosed)
    (hComponents : ∀ component : netlist.components.Component,
      (netlist.components.scattering component).IsLossless)
    (input : CoherencyMatrix netlist.ExternalIncident) :
    (netlist.responseCoherency hWellPosed input).trace = input.trace :=
  netlist.responseCoherency_trace_of_isPowerPreserving hWellPosed
    (netlist.scatteringTransform_isPowerPreserving_of_components_isLossless hComponents) input

/-- Decorrelated network inputs have exactly additive output power. -/
lemma responseCoherency_trace_incoherentSum (hWellPosed : netlist.IsWellPosed)
    (first second : CoherencyMatrix netlist.ExternalIncident) :
    (netlist.responseCoherency hWellPosed (first.incoherentSum second)).trace =
      (netlist.responseCoherency hWellPosed first).trace +
        (netlist.responseCoherency hWellPosed second).trace :=
  CoherencyMatrix.trace_map_incoherentSum first second _

end Finite

end FlatNetlist

end

end Optics
