/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Components.PolarizationScatteringPhysical
public import Physlib.Optics.Components.Retarder.WavePlate
public import Physlib.Optics.Interfaces.PlanarDielectric.FresnelScatteringPhysical
public import Physlib.Optics.Interfaces.PlanarDielectric.JonesBoundaryRegression

/-!
# Regression for polarization and interface physical-port packaging

## i. Overview

This Phase 9b regression combines a Jones quarter-wave plate with an s/p Fresnel interface in a
mixed finite `ScatteringComponentFamily`. The raw inputs `(5, 6)` and
`((1, 2), (3, 4))` produce `(5, -6I)` and `((11/5, -2/5), (7/5, 24/5))`.
Those values are expanded from the registered primitive matrices before the physical-port
packages are unfolded.

A hostile interface swaps only the negative-side s/p output fiber, forcing `7/5` instead of
`11/5` on the same mixed input. This sentinel can fail under side, mode-fiber, component-index,
or aggregate-channel reindex errors.

## ii. Key results

- `physicalPortSuite9b_polarization_raw_action`: primitive quarter-wave-plate action.
- `physicalPortSuite9b_interface_raw_action`: primitive full-vector s/p interface action.
- `physicalPortSuite9b_indexed_action`: exact dependent block action.
- `physicalPortSuite9b_aggregate_action`: exact mixed polarization/interface output.
- `physicalPortSuite9b_hostile_action_ne`: a negative-side s/p swap changes the output.

## iii. Table of contents

- A. Primitive polarization and interface actions
- B. Mixed component family
- C. Hostile polarization-fiber swap

## iv. References

All coefficients are algebraic sentinels and modal-amplitude bookkeeping, not electromagnetic
power. No reciprocity, time reversal, reverse-incidence Maxwell law, modal completeness,
propagation, causality, dispersion, material, coating, or physical realization is asserted.
The polarization fixture uses Physlib's positive-time phase convention. The interface fixture
uses the fork-declared full-vector p sign and the registered negative-side/positive-side kernel
order; it does not assert typed reciprocity or reference-plane laws.
-/

@[expose] public section

namespace Optics

noncomputable section

open Electromagnetism

/-- The negative-side fixture medium has wave admittance four. -/
def physicalPortSuite9bNegativeMedium : HomogeneousIsotropicMedium where
  ε := 16
  μ := 1
  ε_pos := by norm_num
  μ_pos := by norm_num

/-- The positive-side fixture medium has wave admittance one. -/
def physicalPortSuite9bPositiveMedium : HomogeneousIsotropicMedium where
  ε := 1
  μ := 1
  ε_pos := by norm_num
  μ_pos := by norm_num

/-- The negative-side fixture wave admittance is exactly four. -/
lemma physicalPortSuite9b_negative_waveImpedance_inv :
    physicalPortSuite9bNegativeMedium.waveImpedance⁻¹ = 4 := by
  have hSqrt : Real.sqrt (1 / 16 : ℝ) = 1 / 4 := by
    rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
  norm_num [HomogeneousIsotropicMedium.waveImpedance,
    physicalPortSuite9bNegativeMedium, hSqrt]

/-- The positive-side fixture wave admittance is exactly one. -/
lemma physicalPortSuite9b_positive_waveImpedance_inv :
    physicalPortSuite9bPositiveMedium.waveImpedance⁻¹ = 1 := by
  norm_num [HomogeneousIsotropicMedium.waveImpedance,
    physicalPortSuite9bPositiveMedium]

/-- The rational interface fixture reuses an established oriented plane with distinct media. -/
def physicalPortSuite9bInterface : PlanarDielectricInterface where
  plane := jonesBoundaryRegressionPlane
  negativeMedium := physicalPortSuite9bNegativeMedium
  positiveMedium := physicalPortSuite9bPositiveMedium

/-- The fixture pins the flux factor and all four full-vector Fresnel coefficients. -/
lemma physicalPortSuite9b_fresnel_values :
    physicalPortSuite9bInterface.fresnelTransmissionFluxFactor 1 1 = 1 / 4 ∧
      physicalPortSuite9bInterface.sFresnelReflectionCoefficient 1 1 = 3 / 5 ∧
      physicalPortSuite9bInterface.sFresnelTransmissionCoefficient 1 1 = 8 / 5 ∧
      physicalPortSuite9bInterface.pFresnelReflectionCoefficient 1 1 = -3 / 5 ∧
      physicalPortSuite9bInterface.pFresnelTransmissionCoefficient 1 1 = 8 / 5 := by
  norm_num [PlanarDielectricInterface.fresnelTransmissionFluxFactor,
    PlanarDielectricInterface.sFresnelReflectionCoefficient,
    PlanarDielectricInterface.sFresnelTransmissionCoefficient,
    PlanarDielectricInterface.pFresnelReflectionCoefficient,
    PlanarDielectricInterface.pFresnelTransmissionCoefficient,
    PlanarDielectricInterface.sFresnelDenominator,
    PlanarDielectricInterface.pFresnelDenominator,
    physicalPortSuite9bInterface, physicalPortSuite9b_negative_waveImpedance_inv,
    physicalPortSuite9b_positive_waveImpedance_inv]

/-- Flux normalization converts the fixture's electric transmission `8/5` to `4/5`. -/
lemma physicalPortSuite9b_normalized_transmission :
    PlanarDielectricInterface.powerNormalizedFresnelTransmissionCoefficient
      (1 / 4) (8 / 5) = 4 / 5 := by
  have hSqrt : Real.sqrt (1 / 4 : ℝ) = 1 / 2 := by
    rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
  norm_num [PlanarDielectricInterface.powerNormalizedFresnelTransmissionCoefficient,
    hSqrt]

/-- The positive-quarter-wave-plate raw input has distinct nonzero Jones coordinates. -/
def physicalPortSuite9bPolarizationRawInput : ModeAmplitude (Fin 2) :=
  WithLp.toLp 2 ![5, 6]

/-- The exact positive-time quarter-wave-plate raw output is `(5, -6I)`. -/
def physicalPortSuite9bPolarizationRawOutput : ModeAmplitude (Fin 2) :=
  WithLp.toLp 2 ![5, -6 * Complex.I]

/-- Primitive Jones matrix multiplication gives the positive-time quarter-wave-plate output. -/
lemma physicalPortSuite9b_polarization_raw_action :
    (JonesMatrix.quarterWavePlate 0).entries.toEuclideanLin
        physicalPortSuite9bPolarizationRawInput =
      physicalPortSuite9bPolarizationRawOutput := by
  rw [JonesMatrix.quarterWavePlate, JonesMatrix.linearRetarder_zero_axis_entries,
    JonesMatrix.linearRetarderPhase_pi_div_two]
  apply WithLp.ofLp_injective 2
  funext output
  fin_cases output <;>
    simp [physicalPortSuite9bPolarizationRawInput,
      physicalPortSuite9bPolarizationRawOutput, Matrix.toLpLin_apply]

/-- The raw interface input is nonzero in both sides of both polarization blocks. -/
def physicalPortSuite9bInterfaceRawInput : ModeAmplitude (Fin 2 ⊕ Fin 2) :=
  ModeAmplitude.directSum (WithLp.toLp 2 ![1, 2]) (WithLp.toLp 2 ![3, 4])

/-- The exact raw interface output retains all four independently checked coordinates. -/
def physicalPortSuite9bInterfaceRawOutput : ModeAmplitude (Fin 2 ⊕ Fin 2) :=
  ModeAmplitude.directSum (WithLp.toLp 2 ![11 / 5, -2 / 5])
    (WithLp.toLp 2 ![7 / 5, 24 / 5])

/-- The registered s kernel is the exact rational primitive matrix at the fixture. -/
lemma physicalPortSuite9b_s_kernel :
    (physicalPortSuite9bInterface.sFresnelScatteringKernel 1 1).toModeTransform =
      !![(3 / 5 : ℂ), (4 / 5 : ℂ); (4 / 5 : ℂ), (-3 / 5 : ℂ)] := by
  rcases physicalPortSuite9b_fresnel_values with ⟨hFactor, hRS, hTS, _, _⟩
  have hNormalized :
      PlanarDielectricInterface.powerNormalizedFresnelTransmissionCoefficient
          (physicalPortSuite9bInterface.fresnelTransmissionFluxFactor 1 1)
          (physicalPortSuite9bInterface.sFresnelTransmissionCoefficient 1 1) =
        4 / 5 := by
    rw [hFactor, hTS, physicalPortSuite9b_normalized_transmission]
  ext output input
  fin_cases output <;> fin_cases input <;>
    simp [PlanarDielectricInterface.sFresnelScatteringKernel,
      PlanarDielectricInterface.scalarFresnelScatteringKernel, hRS, hNormalized]
  all_goals norm_num

/-- The registered p kernel pins the fork-declared full-vector reflection sign. -/
lemma physicalPortSuite9b_p_kernel :
    (physicalPortSuite9bInterface.pFresnelScatteringKernel 1 1).toModeTransform =
      !![(-3 / 5 : ℂ), (4 / 5 : ℂ); (4 / 5 : ℂ), (3 / 5 : ℂ)] := by
  rcases physicalPortSuite9b_fresnel_values with ⟨hFactor, _, _, hRP, hTP⟩
  have hNormalized :
      PlanarDielectricInterface.powerNormalizedFresnelTransmissionCoefficient
          (physicalPortSuite9bInterface.fresnelTransmissionFluxFactor 1 1)
          (physicalPortSuite9bInterface.pFresnelTransmissionCoefficient 1 1) =
        4 / 5 := by
    rw [hFactor, hTP, physicalPortSuite9b_normalized_transmission]
  ext output input
  fin_cases output <;> fin_cases input <;>
    simp [PlanarDielectricInterface.pFresnelScatteringKernel,
      PlanarDielectricInterface.scalarFresnelScatteringKernel, hRP, hNormalized]
  all_goals norm_num

/-- Primitive block-matrix multiplication gives all four exact polarized-interface outputs. -/
lemma physicalPortSuite9b_interface_raw_action :
    ((physicalPortSuite9bInterface.sFresnelScatteringKernel 1 1).toModeTransform.directSum
      (physicalPortSuite9bInterface.pFresnelScatteringKernel 1 1).toModeTransform).toLinearMap
        physicalPortSuite9bInterfaceRawInput =
      physicalPortSuite9bInterfaceRawOutput := by
  rw [physicalPortSuite9b_s_kernel, physicalPortSuite9b_p_kernel]
  apply WithLp.ofLp_injective 2
  funext output
  rcases output with output | output <;> fin_cases output <;>
    simp [ModeTransform.directSum, physicalPortSuite9bInterfaceRawInput,
      physicalPortSuite9bInterfaceRawOutput, ModeTransform.toLinearMap,
      Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
      Fin.sum_univ_two]
  <;> ring

/-!
## B. Mixed component family
-/

/-- The Jones input transported to its owned aperture channels. -/
def physicalPortSuite9bPolarizationLocalInput :
    ModeAmplitude JonesMatrix.portFamily.Channel :=
  ModeAmplitude.reindex JonesMatrix.channelEquiv
    physicalPortSuite9bPolarizationRawInput

/-- The Jones output transported to its owned aperture channels. -/
def physicalPortSuite9bPolarizationLocalOutput :
    ModeAmplitude JonesMatrix.portFamily.Channel :=
  ModeAmplitude.reindex JonesMatrix.channelEquiv
    physicalPortSuite9bPolarizationRawOutput

/-- The physical Jones adapter has the independently expanded primitive action. -/
lemma physicalPortSuite9b_polarization_local_action :
    (JonesMatrix.physicalScattering
      (JonesMatrix.quarterWavePlate 0)).toModeTransform.toLinearMap
        physicalPortSuite9bPolarizationLocalInput =
      physicalPortSuite9bPolarizationLocalOutput := by
  rw [JonesMatrix.physicalScattering, ScatteringMatrix.toModeTransform_reindex,
    ModeTransform.toLinearMap_reindex_eq, physicalPortSuite9bPolarizationLocalInput,
    ModeAmplitude.reindex_symm_reindex]
  change ModeAmplitude.reindex JonesMatrix.channelEquiv
      ((JonesMatrix.quarterWavePlate 0).entries.toEuclideanLin
        physicalPortSuite9bPolarizationRawInput) = _
  rw [physicalPortSuite9b_polarization_raw_action]
  rfl

/-- The interface input transported to its owned side/polarization channels. -/
def physicalPortSuite9bInterfaceLocalInput :
    ModeAmplitude PlanarDielectricInterface.portFamily.Channel :=
  ModeAmplitude.reindex PlanarDielectricInterface.channelEquiv
    physicalPortSuite9bInterfaceRawInput

/-- The interface output transported to its owned side/polarization channels. -/
def physicalPortSuite9bInterfaceLocalOutput :
    ModeAmplitude PlanarDielectricInterface.portFamily.Channel :=
  ModeAmplitude.reindex PlanarDielectricInterface.channelEquiv
    physicalPortSuite9bInterfaceRawOutput

/-- The physical interface adapter has the independently expanded primitive action. -/
lemma physicalPortSuite9b_interface_local_action :
    (physicalPortSuite9bInterface.physicalScattering 1 1).toModeTransform.toLinearMap
        physicalPortSuite9bInterfaceLocalInput =
      physicalPortSuite9bInterfaceLocalOutput := by
  rw [PlanarDielectricInterface.physicalScattering,
    ScatteringMatrix.toModeTransform_reindex, ModeTransform.toLinearMap_reindex_eq,
    physicalPortSuite9bInterfaceLocalInput, ModeAmplitude.reindex_symm_reindex]
  change ModeAmplitude.reindex PlanarDielectricInterface.channelEquiv
      (((physicalPortSuite9bInterface.sFresnelScatteringKernel 1 1).toModeTransform.directSum
        (physicalPortSuite9bInterface.pFresnelScatteringKernel 1 1).toModeTransform).toLinearMap
          physicalPortSuite9bInterfaceRawInput) = _
  rw [physicalPortSuite9b_interface_raw_action]
  rfl

/-- The separate Phase 9b component labels. -/
inductive PhysicalPortSuite9bComponent
  | polarization
  | interface
  deriving DecidableEq

/-- The two Phase 9b component labels form a finite family. -/
instance : Fintype PhysicalPortSuite9bComponent where
  elems := {PhysicalPortSuite9bComponent.polarization,
    PhysicalPortSuite9bComponent.interface}
  complete component := by
    cases component <;> simp

/-- The owned port family selected by each Phase 9b component. -/
def physicalPortSuite9bPortFamily : PhysicalPortSuite9bComponent → PortModeFamily
  | .polarization => JonesMatrix.portFamily
  | .interface => PlanarDielectricInterface.portFamily

/-- The owned scattering law selected by each Phase 9b component. -/
def physicalPortSuite9bScattering :
    (component : PhysicalPortSuite9bComponent) →
      ScatteringMatrix (physicalPortSuite9bPortFamily component).Channel
  | .polarization => JonesMatrix.physicalScattering (JonesMatrix.quarterWavePlate 0)
  | .interface => physicalPortSuite9bInterface.physicalScattering 1 1

/-- The mixed Phase 9b polarization/interface component family. -/
abbrev physicalPortSuite9bFamily : ScatteringComponentFamily where
  Component := PhysicalPortSuite9bComponent
  portFamily := physicalPortSuite9bPortFamily
  scattering := physicalPortSuite9bScattering

/-- Every Phase 9b local channel family is finite. -/
local instance physicalPortSuite9bLocalChannelFintype
    (component : PhysicalPortSuite9bComponent) :
    Fintype (physicalPortSuite9bFamily.portFamily component).Channel := by
  cases component
  · change Fintype JonesMatrix.portFamily.Channel
    infer_instance
  · change Fintype PlanarDielectricInterface.portFamily.Channel
    infer_instance

/-- Every Phase 9b local channel family has decidable equality. -/
local instance physicalPortSuite9bLocalChannelDecidableEq
    (component : PhysicalPortSuite9bComponent) :
    DecidableEq (physicalPortSuite9bFamily.portFamily component).Channel := by
  cases component
  · change DecidableEq JonesMatrix.portFamily.Channel
    infer_instance
  · change DecidableEq PlanarDielectricInterface.portFamily.Channel
    infer_instance

/-- The indexed Phase 9b channels have decidable equality. -/
local instance physicalPortSuite9bIndexedChannelDecidableEq :
    DecidableEq physicalPortSuite9bFamily.IndexedChannel :=
  Classical.decEq _

/-- The aggregate Phase 9b channels are finite by indexed reassociation. -/
local instance physicalPortSuite9bAggregateChannelFintype :
    Fintype physicalPortSuite9bFamily.aggregatePortModeFamily.Channel :=
  Fintype.ofEquiv physicalPortSuite9bFamily.IndexedChannel
    physicalPortSuite9bFamily.channelEquiv

/-- The aggregate Phase 9b channels have decidable equality in indexed coordinates. -/
local instance physicalPortSuite9bAggregateChannelDecidableEq :
    DecidableEq physicalPortSuite9bFamily.aggregatePortModeFamily.Channel :=
  physicalPortSuite9bFamily.channelEquiv.symm.decidableEq

/-- The nonzero mixed input in component-indexed owned-channel coordinates. -/
def physicalPortSuite9bIndexedInput :
    ModeAmplitude physicalPortSuite9bFamily.IndexedChannel :=
  WithLp.toLp 2 fun
    | ⟨.polarization, ⟨JonesMatrix.Port.aperture, coordinate⟩⟩ =>
        physicalPortSuite9bPolarizationRawInput coordinate
    | ⟨.interface, ⟨port, mode⟩⟩ =>
        physicalPortSuite9bInterfaceRawInput
          (PlanarDielectricInterface.channelEquiv.symm ⟨port, mode⟩)

/-- The exact mixed output in component-indexed owned-channel coordinates. -/
def physicalPortSuite9bIndexedOutput :
    ModeAmplitude physicalPortSuite9bFamily.IndexedChannel :=
  WithLp.toLp 2 fun
    | ⟨.polarization, ⟨JonesMatrix.Port.aperture, coordinate⟩⟩ =>
        physicalPortSuite9bPolarizationRawOutput coordinate
    | ⟨.interface, ⟨port, mode⟩⟩ =>
        physicalPortSuite9bInterfaceRawOutput
          (PlanarDielectricInterface.channelEquiv.symm ⟨port, mode⟩)

/-- Restricting the mixed input recovers the owned Jones local input. -/
lemma physicalPortSuite9bIndexedInput_restrict_polarization :
    physicalPortSuite9bIndexedInput.restrictEmbedding
        (Function.Embedding.sigmaMk PhysicalPortSuite9bComponent.polarization) =
      physicalPortSuite9bPolarizationLocalInput := by
  apply WithLp.ofLp_injective 2
  funext channel
  rcases channel with ⟨port, coordinate⟩
  cases port
  rfl

/-- Restricting the mixed input recovers the owned interface local input. -/
lemma physicalPortSuite9bIndexedInput_restrict_interface :
    physicalPortSuite9bIndexedInput.restrictEmbedding
        (Function.Embedding.sigmaMk PhysicalPortSuite9bComponent.interface) =
      physicalPortSuite9bInterfaceLocalInput := by
  apply WithLp.ofLp_injective 2
  funext channel
  rcases channel with ⟨port, mode⟩
  cases port <;> cases mode <;> rfl

/-- Primitive local actions give the exact mixed dependent block-diagonal output. -/
lemma physicalPortSuite9b_indexed_action :
    physicalPortSuite9bFamily.indexedScatteringMatrix.toModeTransform.toLinearMap
        physicalPortSuite9bIndexedInput =
      physicalPortSuite9bIndexedOutput := by
  apply WithLp.ofLp_injective 2
  funext output
  change ModeTransform.toLinearMap
      (Matrix.blockDiagonal' fun selected =>
        (physicalPortSuite9bScattering selected).toModeTransform)
      physicalPortSuite9bIndexedInput output = _
  rcases output with ⟨component, channel⟩
  have hBlock := ModeTransform.blockDiagonal'_apply
    (fun selected => (physicalPortSuite9bScattering selected).toModeTransform)
    physicalPortSuite9bIndexedInput component channel
  calc
    _ = (physicalPortSuite9bScattering component).toModeTransform.toLinearMap
        (physicalPortSuite9bIndexedInput.restrictEmbedding
          (Function.Embedding.sigmaMk component)) channel := hBlock
    _ = _ := by
      cases component
      · rw [physicalPortSuite9bIndexedInput_restrict_polarization,
          physicalPortSuite9b_polarization_local_action]
        rcases channel with ⟨port, coordinate⟩
        cases port
        rfl
      · rw [physicalPortSuite9bIndexedInput_restrict_interface,
          physicalPortSuite9b_interface_local_action]
        rcases channel with ⟨port, mode⟩
        cases port <;> cases mode <;> rfl

/-- The mixed input in aggregate component-owned physical-channel coordinates. -/
def physicalPortSuite9bAggregateInput :
    ModeAmplitude physicalPortSuite9bFamily.aggregatePortModeFamily.Channel :=
  ModeAmplitude.reindex physicalPortSuite9bFamily.channelEquiv
    physicalPortSuite9bIndexedInput

/-- The exact mixed output in aggregate component-owned physical-channel coordinates. -/
def physicalPortSuite9bAggregateOutput :
    ModeAmplitude physicalPortSuite9bFamily.aggregatePortModeFamily.Channel :=
  ModeAmplitude.reindex physicalPortSuite9bFamily.channelEquiv
    physicalPortSuite9bIndexedOutput

/-- The mixed family's aggregate action is the independently expanded six-channel output. -/
lemma physicalPortSuite9b_aggregate_action :
    physicalPortSuite9bFamily.assembledScatteringMatrix.toModeTransform.toLinearMap
        physicalPortSuite9bAggregateInput =
      physicalPortSuite9bAggregateOutput := by
  rw [ScatteringComponentFamily.assembledScatteringMatrix,
    ScatteringMatrix.toModeTransform_reindex, ModeTransform.toLinearMap_reindex_eq,
    physicalPortSuite9bAggregateInput, ModeAmplitude.reindex_symm_reindex,
    physicalPortSuite9b_indexed_action]
  rfl

/-!
## C. Hostile polarization-fiber swap
-/

/-- Swap only the s/p mode fiber at the negative-side interface port. -/
def physicalPortSuite9bInterfaceNegativePolarizationSwap :
    PlanarDielectricInterface.portFamily.Channel ≃
      PlanarDielectricInterface.portFamily.Channel where
  toFun
    | ⟨PlanarDielectricInterface.Port.negativeSide,
        PlanarDielectricInterface.PolarizationMode.s⟩ =>
      ⟨PlanarDielectricInterface.Port.negativeSide,
        PlanarDielectricInterface.PolarizationMode.p⟩
    | ⟨PlanarDielectricInterface.Port.negativeSide,
        PlanarDielectricInterface.PolarizationMode.p⟩ =>
      ⟨PlanarDielectricInterface.Port.negativeSide,
        PlanarDielectricInterface.PolarizationMode.s⟩
    | ⟨PlanarDielectricInterface.Port.positiveSide, mode⟩ =>
      ⟨PlanarDielectricInterface.Port.positiveSide, mode⟩
  invFun
    | ⟨PlanarDielectricInterface.Port.negativeSide,
        PlanarDielectricInterface.PolarizationMode.s⟩ =>
      ⟨PlanarDielectricInterface.Port.negativeSide,
        PlanarDielectricInterface.PolarizationMode.p⟩
    | ⟨PlanarDielectricInterface.Port.negativeSide,
        PlanarDielectricInterface.PolarizationMode.p⟩ =>
      ⟨PlanarDielectricInterface.Port.negativeSide,
        PlanarDielectricInterface.PolarizationMode.s⟩
    | ⟨PlanarDielectricInterface.Port.positiveSide, mode⟩ =>
      ⟨PlanarDielectricInterface.Port.positiveSide, mode⟩
  left_inv := by
    rintro ⟨port, mode⟩
    cases port <;> cases mode <;> rfl
  right_inv := by
    rintro ⟨port, mode⟩
    cases port <;> cases mode <;> rfl

/-- The hostile interface law swaps only physical output rows at the negative side. -/
def physicalPortSuite9bHostileInterfaceScattering :
    ScatteringMatrix PlanarDielectricInterface.portFamily.Channel where
  toModeTransform :=
    ModeTransform.reindex (Equiv.refl _)
      physicalPortSuite9bInterfaceNegativePolarizationSwap
      (physicalPortSuite9bInterface.physicalScattering 1 1).toModeTransform

/-- The hostile interface output is the positive output with one side's s/p fiber swapped. -/
def physicalPortSuite9bHostileInterfaceLocalOutput :
    ModeAmplitude PlanarDielectricInterface.portFamily.Channel :=
  ModeAmplitude.reindex physicalPortSuite9bInterfaceNegativePolarizationSwap
    physicalPortSuite9bInterfaceLocalOutput

/-- Direct row relabeling forces the hostile fiber-swapped local output. -/
lemma physicalPortSuite9b_hostile_interface_local_action :
    physicalPortSuite9bHostileInterfaceScattering.toModeTransform.toLinearMap
        physicalPortSuite9bInterfaceLocalInput =
      physicalPortSuite9bHostileInterfaceLocalOutput := by
  rw [physicalPortSuite9bHostileInterfaceScattering,
    ModeTransform.toLinearMap_reindex_eq]
  have hInput :
      ModeAmplitude.reindex (Equiv.refl _).symm
          physicalPortSuite9bInterfaceLocalInput =
        physicalPortSuite9bInterfaceLocalInput := by
    apply WithLp.ofLp_injective 2
    funext channel
    rfl
  rw [hInput, physicalPortSuite9b_interface_local_action]
  rfl

/-- The hostile mixed family changes only the interface output fiber assignment. -/
def physicalPortSuite9bHostileScattering :
    (component : PhysicalPortSuite9bComponent) →
      ScatteringMatrix (physicalPortSuite9bPortFamily component).Channel
  | .polarization => JonesMatrix.physicalScattering (JonesMatrix.quarterWavePlate 0)
  | .interface => physicalPortSuite9bHostileInterfaceScattering

/-- The hostile Phase 9b family has the same owned ports and one swapped output fiber. -/
abbrev physicalPortSuite9bHostileFamily : ScatteringComponentFamily where
  Component := PhysicalPortSuite9bComponent
  portFamily := physicalPortSuite9bPortFamily
  scattering := physicalPortSuite9bHostileScattering

/-- The negative-side s channel in indexed component coordinates. -/
abbrev physicalPortSuite9bInterfaceNegativeSIndexed :
    physicalPortSuite9bFamily.IndexedChannel :=
  ⟨PhysicalPortSuite9bComponent.interface,
    ⟨PlanarDielectricInterface.Port.negativeSide,
      PlanarDielectricInterface.PolarizationMode.s⟩⟩

/-- The correct indexed action gives `11/5` at negative-side s. -/
lemma physicalPortSuite9b_indexed_negative_s_value :
    physicalPortSuite9bFamily.indexedScatteringMatrix.toModeTransform.toLinearMap
        physicalPortSuite9bIndexedInput
      physicalPortSuite9bInterfaceNegativeSIndexed = 11 / 5 := by
  rw [physicalPortSuite9b_indexed_action]
  change physicalPortSuite9bInterfaceRawOutput
      (PlanarDielectricInterface.channelEquiv.symm
        ⟨PlanarDielectricInterface.Port.negativeSide,
          PlanarDielectricInterface.PolarizationMode.s⟩) = _
  have hChannel :
      PlanarDielectricInterface.channelEquiv.symm
          ⟨PlanarDielectricInterface.Port.negativeSide,
            PlanarDielectricInterface.PolarizationMode.s⟩ =
        Sum.inl 0 := by
    rfl
  rw [hChannel]
  rfl

/-- The hostile family instead gives the p value `7/5` at negative-side s. -/
lemma physicalPortSuite9b_hostile_indexed_negative_s_value :
    physicalPortSuite9bHostileFamily.indexedScatteringMatrix.toModeTransform.toLinearMap
      physicalPortSuite9bIndexedInput
        physicalPortSuite9bInterfaceNegativeSIndexed = 7 / 5 := by
  unfold physicalPortSuite9bInterfaceNegativeSIndexed
  change ModeTransform.toLinearMap
      (Matrix.blockDiagonal' fun selected =>
        (physicalPortSuite9bHostileScattering selected).toModeTransform)
      physicalPortSuite9bIndexedInput
        ⟨PhysicalPortSuite9bComponent.interface,
          ⟨PlanarDielectricInterface.Port.negativeSide,
            PlanarDielectricInterface.PolarizationMode.s⟩⟩ = _
  have hBlock := ModeTransform.blockDiagonal'_apply
    (fun selected => (physicalPortSuite9bHostileScattering selected).toModeTransform)
    physicalPortSuite9bIndexedInput PhysicalPortSuite9bComponent.interface
      ⟨PlanarDielectricInterface.Port.negativeSide,
        PlanarDielectricInterface.PolarizationMode.s⟩
  calc
    _ = (physicalPortSuite9bHostileScattering
          PhysicalPortSuite9bComponent.interface).toModeTransform.toLinearMap
        (physicalPortSuite9bIndexedInput.restrictEmbedding
          (Function.Embedding.sigmaMk PhysicalPortSuite9bComponent.interface))
        ⟨PlanarDielectricInterface.Port.negativeSide,
          PlanarDielectricInterface.PolarizationMode.s⟩ := hBlock
    _ = _ := by
      rw [physicalPortSuite9bIndexedInput_restrict_interface,
        physicalPortSuite9b_hostile_interface_local_action]
      change physicalPortSuite9bInterfaceRawOutput
          (PlanarDielectricInterface.channelEquiv.symm
            (physicalPortSuite9bInterfaceNegativePolarizationSwap.symm
              ⟨PlanarDielectricInterface.Port.negativeSide,
                PlanarDielectricInterface.PolarizationMode.s⟩)) = _
      have hSwap :
          physicalPortSuite9bInterfaceNegativePolarizationSwap.symm
              ⟨PlanarDielectricInterface.Port.negativeSide,
                PlanarDielectricInterface.PolarizationMode.s⟩ =
            ⟨PlanarDielectricInterface.Port.negativeSide,
              PlanarDielectricInterface.PolarizationMode.p⟩ := by
        rfl
      have hChannel :
          PlanarDielectricInterface.channelEquiv.symm
              ⟨PlanarDielectricInterface.Port.negativeSide,
                PlanarDielectricInterface.PolarizationMode.p⟩ =
            Sum.inr 0 := by
        rfl
      rw [hSwap, hChannel]
      rfl

/-- Swapping one owned side's polarization fiber changes the mixed-family output. -/
lemma physicalPortSuite9b_hostile_action_ne :
    physicalPortSuite9bHostileFamily.indexedScatteringMatrix.toModeTransform.toLinearMap
        physicalPortSuite9bIndexedInput
        physicalPortSuite9bInterfaceNegativeSIndexed ≠
      physicalPortSuite9bFamily.indexedScatteringMatrix.toModeTransform.toLinearMap
        physicalPortSuite9bIndexedInput
        physicalPortSuite9bInterfaceNegativeSIndexed := by
  rw [physicalPortSuite9b_hostile_indexed_negative_s_value,
    physicalPortSuite9b_indexed_negative_s_value]
  norm_num

end

end Optics

