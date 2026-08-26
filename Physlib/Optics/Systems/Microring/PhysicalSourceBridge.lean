/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Systems.Microring.PhysicalRealization
public import Physlib.Optics.Systems.Microring.SourceBridge

/-!
# Source consequences of the physical microring realization

## i. Overview

This file composes the source-neutral physical realization with the audited DATE'14, SysCon'15,
and SFG-TR'14 dictionaries. It introduces no second source parameter records. The existing records
and their reduced parameter maps are defined in
`Physlib/Optics/Systems/Microring/SourceBridgeDate.lean:64-428`,
`Physlib/Optics/Systems/Microring/SourceBridgeSysCon.lean:84-119`, and
`Physlib/Optics/Systems/Microring/SourceBridgeSfg.lean:52-82`.

`DateParameters.toPhysicalAddDrop` maps DATE's physical source record to physical coupling and
propagation data. Conversely, `addDropPhysicalToSysConParameters` expresses physical data in the
existing reduced SysCon dictionary. The latter is a declared interpretation of SysCon's `x_r`:
the source uses `sqrt(x_r)` on each half arc but does not classify `x_r` as a field or power
quantity, as recorded at
`Physlib/Optics/Systems/Microring/SourceBridgeSysCon.lean:95-108`.

The DATE two-port chain matrix is obtained from the physical N7 arm mixer under the N7 amplitude
normalization `r ^ 2 + t ^ 2 = 1` and source pivot gate `t != 0`. The DATE four-port chain matrix
is obtained from the physical two-coupler, two-half-arc N5 response under the exact source
unitarity, ring-denominator, and forward-pivot gates. Thus both source matrices are consequences
of component responses in backward-first chain coordinates, rather than defining fields of a
formula container.

DATE's forward/through comparison uses the algebraic channel-sign gauge at
`Physlib/Optics/Systems/Microring/SourceBridgeDate.lean:457-466`; no physical reference-plane
provenance is inferred for that source sign. The physical drop amplitude uses the N7 cross gauge
and the symmetric half-arc reference plane at
`Physlib/Optics/Components/DirectionalCoupler.lean:68-77` and
`Physlib/Optics/Systems/Microring/AddDropNetwork.lean:117-181`. It is therefore gauge- and
reference-plane-dependent. The corresponding chain matrices are totalized at zero pivots, while
their component-response meanings below are gated.

The SysCon and SFG results below are direct compositions with their merged source bridges. The
SysCon quotient needs the ring solve gate, its series meaning additionally needs the source
contraction gate, and the SFG comparison needs its explicit principal-square-root branch match.
This file does not resolve SysCon's unaudited log base or the withheld printed Thm. 6 expression.

No dispersion, bending-loss, material, thermal, nonlinear, bandwidth, causality, group-delay,
omitted-loss-channel, or measurement-validation claim is made. Coupling amplitudes are free N7
parameters; no coupling-length model is supplied. Power means normalized modal power, not
electromagnetic power before the finite, common-frequency, Maxwell-qualified, pairwise-integrable,
mutually flux-orthogonal, unit-normalized bridge at
`Physlib/Optics/HarmonicFlux/PropagatingModePower.lean:16-22,60-93`.

## ii. Key results

- `DateParameters.toPhysicalAddDrop_toParameters`: equality with the audited source dictionary.
- `dateTwoPortChainMatrix_eq_gauged_physicalCouplerChain`: DATE Thm. 1 from the physical N7 mixer.
- `dateForwardTransfer_eq_physicalResponse`: DATE's forward field from the physical N5 response.
- `dateBackwardTransfer_eq_physicalResponse`: DATE's backward field from the physical N5 response.
- `dateFourPortChainMatrix_eq_reindexed_physicalResponse`: DATE Thm. 2 from the physical N5 ring.
- `sysConDropTransfer_eq_physicalResponse`: SysCon Thm. 5 from the physical N5 response.
- `sysConDropResponseSeries_eq_physicalResponse`: SysCon Def. 9 on its contraction domain.
- `sysConDropPower_eq_physicalResponsePower`: SysCon Def. 10 from the physical N5 response.
- `sfgAddDropTransfer_eq_physicalResponse`: SFG-TR Thm. 7 from the physical N5 response.

## iii. Table of contents

- A. Existing DATE parameters mapped to physical data
- B. DATE two-port matrix from the physical N7 coupler
- C. DATE four-port scattering from the physical N5 ring
- D. DATE transfer and chain consequences
- E. Physical data in the existing SysCon dictionary
- F. SFG-TR transfer from the physical N5 ring

## iv. References

DATE'14 Def. 3 and Thms. 1--2 are catalogued at `HOL-CORPUS.md:194-198`. SysCon'15 Defs. 9--11
and Thms. 5--7 are catalogued at `HOL-CORPUS.md:244-249`; SFG-TR'14 Def. 35 and Thm. 7 are at
`HOL-CORPUS.md:345-346`. The source formulas, dictionaries, conventions, gates, and non-claims are
proved or recorded in the three imported `SourceBridge` modules cited above.
-/

@[expose] public section

namespace Optics

noncomputable section

namespace MicroringSourceBridge

open Microring

/-! ## A. Existing DATE parameters mapped to physical data -/

/-- The DATE amplitudes at
`Physlib/Optics/Systems/Microring/SourceBridgeDate.lean:64-118` as physical N7 fields. -/
def DateParameters.toPhysicalCoupling (p : DateParameters) : CouplingParameters where
  throughAmplitude := p.reflectivity
  crossAmplitude := p.transmissivity

/-- The DATE data at
`Physlib/Optics/Systems/Microring/SourceBridgeDate.lean:64-89` as physical propagation data. -/
def DateParameters.toPhysicalPropagation (p : DateParameters) : PhysicalParameters where
  pathLength := p.couplingLength
  powerAttenuationCoefficient := p.powerAttenuation
  effectiveIndex := p.effectiveIndex
  wavelength := p.wavelength

/-- The DATE dictionary at
`Physlib/Optics/Systems/Microring/SourceBridgeDate.lean:410-428` as a physical two-bus ring. -/
def DateParameters.toPhysicalAddDrop (p : DateParameters) : AddDropPhysicalParameters where
  inputCoupling := p.toPhysicalCoupling
  dropCoupling := p.toPhysicalCoupling
  propagation := p.toPhysicalPropagation

/-- The physical DATE map retains the attenuation definition at
`Physlib/Optics/Systems/Microring/SourceBridgeDate.lean:82-89`. -/
lemma DateParameters.toPhysicalPropagation_fieldAttenuation (p : DateParameters) :
    p.toPhysicalPropagation.fieldAttenuation.value = p.fieldAttenuation := rfl

/-- The physical phase lift is DATE's formula at
`Physlib/Optics/Systems/Microring/SourceBridgeDate.lean:79-80`. -/
lemma DateParameters.toPhysicalPropagation_roundTripPhaseLift (p : DateParameters) :
    p.toPhysicalPropagation.roundTripPhaseLift = p.roundTripPhase := by
  rw [Microring.PhysicalParameters.roundTripPhaseLift,
    Microring.PhysicalParameters.propagationConstant,
    DateParameters.toPhysicalPropagation, DateParameters.roundTripPhase]
  ring

/-- Mapping DATE physically gives the audited dictionary at
`Physlib/Optics/Systems/Microring/SourceBridgeDate.lean:410-428`. -/
lemma DateParameters.toPhysicalAddDrop_toParameters (p : DateParameters) :
    p.toPhysicalAddDrop.toParameters = p.toAddDrop := by
  unfold DateParameters.toPhysicalAddDrop AddDropPhysicalParameters.toParameters
  rw [p.toPhysicalPropagation_roundTripPhaseLift]
  rfl

/-- Nonnegative source amplitudes and propagation data make the physical DATE map valid. -/
lemma DateParameters.toPhysicalAddDrop_isValid (p : DateParameters)
    (hUnitary : p.IsUnitary) (hReflectivity : 0 ≤ p.reflectivity)
    (hTransmissivity : 0 ≤ p.transmissivity) (hLength : 0 ≤ p.couplingLength)
    (hAttenuation : 0 ≤ p.powerAttenuation) (hIndex : 0 ≤ p.effectiveIndex)
    (hWavelength : 0 < p.wavelength) : p.toPhysicalAddDrop.IsValid := by
  exact ⟨⟨hReflectivity, hTransmissivity, hUnitary⟩,
    ⟨hReflectivity, hTransmissivity, hUnitary⟩,
    hLength, hAttenuation, hIndex, hWavelength⟩

/-- The DATE solve gate transports to the physically parameterized S2 ring. -/
lemma DateParameters.toPhysicalAddDrop_hasNonzeroDenominator (p : DateParameters)
    (hDenominator : p.HasNonzeroDenominator) :
    p.toPhysicalAddDrop.toParameters.HasNonzeroDenominator := by
  rw [p.toPhysicalAddDrop_toParameters]
  exact (p.hasNonzeroDenominator_iff).mp hDenominator

/-! ## B. DATE two-port matrix from the physical N7 coupler -/

/-- The DATE N7 arm mixer is definitionally the physical coupling arm mixer. -/
lemma DateParameters.toPhysicalCoupling_toTwoPortScattering (p : DateParameters) :
    p.toPhysicalCoupling.toTwoPortScattering = p.couplerScattering := rfl

/-- The source gate `t != 0` makes the physical N7 arm-mixer pivot bijective. -/
lemma DateParameters.toPhysicalCoupling_hasBijectiveRightToLeftTransmission
    (p : DateParameters) (hTransmissivity : p.transmissivity ≠ 0) :
    p.toPhysicalCoupling.toTwoPortScattering.HasBijectiveRightToLeftTransmission := by
  rw [p.toPhysicalCoupling_toTwoPortScattering]
  exact p.couplerScattering_hasBijectiveRightToLeftTransmission hTransmissivity

/-- DATE Thm. 1 is the physical N7 chain conversion up to the algebraic sign gauge at
`Physlib/Optics/Systems/Microring/SourceBridgeDate.lean:295-307`. -/
lemma dateTwoPortChainMatrix_eq_gauged_physicalCouplerChain (p : DateParameters)
    (hUnitary : p.IsUnitary) (hTransmissivity : p.transmissivity ≠ 0) :
    dateTwoPortChainMatrix p =
      dateChainGauge *
          p.toPhysicalCoupling.toTwoPortScattering.toBackwardFirstChainTransform
            (p.toPhysicalCoupling_hasBijectiveRightToLeftTransmission hTransmissivity) *
        dateChainGauge := by
  have hTransport :
      ∀ (first second : TwoPortScatteringTransform Unit Unit)
        (hEqual : first = second)
        (hFirst : first.HasBijectiveRightToLeftTransmission)
        (hSecond : second.HasBijectiveRightToLeftTransmission),
        first.toBackwardFirstChainTransform hFirst =
          second.toBackwardFirstChainTransform hSecond := by
    intro first second hEqual hFirst hSecond
    subst second
    rw [Subsingleton.elim hFirst hSecond]
  calc
    dateTwoPortChainMatrix p = dateChainGauge *
        p.couplerScattering.toBackwardFirstChainTransform
          (p.couplerScattering_hasBijectiveRightToLeftTransmission hTransmissivity) *
        dateChainGauge :=
      dateTwoPortChainMatrix_eq_gauged_n7Chain p hUnitary hTransmissivity
    _ = dateChainGauge *
        p.toPhysicalCoupling.toTwoPortScattering.toBackwardFirstChainTransform
          (p.toPhysicalCoupling_hasBijectiveRightToLeftTransmission hTransmissivity) *
        dateChainGauge := by
      rw [hTransport _ _ p.toPhysicalCoupling_toTwoPortScattering _ _]

/-! ## C. DATE four-port scattering from the physical N5 ring -/

/-- The DATE-ordered, gauge-adapted two-sided scattering view of the physical N5 ring response.

Rows are source `(c,b)` and columns are source `(a,d)`, with the gauges defined at
`Physlib/Optics/Systems/Microring/SourceBridgeDate.lean:457-466`.
-/
def datePhysicalN5FourPortScattering (p : DateParameters)
    (hDenominator : p.toPhysicalAddDrop.toParameters.HasNonzeroDenominator) :
    TwoPortScatteringTransform Unit Unit
  | Sum.inl _, Sum.inl _ =>
      (addDropTopology p.toPhysicalAddDrop).responseTransform
        (AddDrop.isWellPosed_of_hasNonzeroDenominator
          p.toPhysicalAddDrop.toParameters hDenominator)
        (Outgoing.mk (addDropDropChannel p.toPhysicalAddDrop))
        (Incident.mk (addDropInputChannel p.toPhysicalAddDrop))
  | Sum.inl _, Sum.inr _ => dateAddGauge
      ((addDropTopology p.toPhysicalAddDrop).responseTransform
        (AddDrop.isWellPosed_of_hasNonzeroDenominator
          p.toPhysicalAddDrop.toParameters hDenominator)
        (Outgoing.mk (addDropDropChannel p.toPhysicalAddDrop))
        (Incident.mk (addDropAddChannel p.toPhysicalAddDrop)))
  | Sum.inr _, Sum.inl _ => dateThroughGauge
      ((addDropTopology p.toPhysicalAddDrop).responseTransform
        (AddDrop.isWellPosed_of_hasNonzeroDenominator
          p.toPhysicalAddDrop.toParameters hDenominator)
        (Outgoing.mk (addDropThroughChannel p.toPhysicalAddDrop))
        (Incident.mk (addDropInputChannel p.toPhysicalAddDrop)))
  | Sum.inr _, Sum.inr _ => dateThroughGauge (dateAddGauge
      ((addDropTopology p.toPhysicalAddDrop).responseTransform
        (AddDrop.isWellPosed_of_hasNonzeroDenominator
          p.toPhysicalAddDrop.toParameters hDenominator)
        (Outgoing.mk (addDropThroughChannel p.toPhysicalAddDrop))
        (Incident.mk (addDropAddChannel p.toPhysicalAddDrop))))

/-- The physical DATE response agrees with the existing source-dictionary N5 response. -/
lemma datePhysicalN5FourPortScattering_eq_n5Response (p : DateParameters)
    (hDenominator : p.HasNonzeroDenominator) :
    datePhysicalN5FourPortScattering p
        (p.toPhysicalAddDrop_hasNonzeroDenominator hDenominator) =
      dateN5FourPortScattering p ((p.hasNonzeroDenominator_iff).mp hDenominator) := by
  let hPhysical := AddDrop.isWellPosed_of_hasNonzeroDenominator
    p.toPhysicalAddDrop.toParameters
      (p.toPhysicalAddDrop_hasNonzeroDenominator hDenominator)
  let hSource := AddDrop.isWellPosed_of_hasNonzeroDenominator p.toAddDrop
    ((p.hasNonzeroDenominator_iff).mp hDenominator)
  have hTransport :
      ∀ (q r : AddDrop.Parameters) (hqr : q = r)
        (hq : (AddDrop.netlist q).IsWellPosed) (hr : (AddDrop.netlist r).IsWellPosed)
        (output input : (s : AddDrop.Parameters) → (AddDrop.netlist s).ExternalChannel),
        (AddDrop.netlist q).responseTransform hq (Outgoing.mk (output q))
            (Incident.mk (input q)) =
          (AddDrop.netlist r).responseTransform hr (Outgoing.mk (output r))
            (Incident.mk (input r)) := by
    intro q r hqr hq hr output input
    subst r
    rw [Subsingleton.elim hq hr]
  ext (output | output) (input | input) <;>
    rcases output with ⟨⟨⟩⟩ <;>
    rcases input with ⟨⟨⟩⟩
  · exact hTransport _ _ p.toPhysicalAddDrop_toParameters hPhysical hSource
      AddDrop.dropChannel AddDrop.inputChannel
  · exact congrArg dateAddGauge
      (hTransport _ _ p.toPhysicalAddDrop_toParameters hPhysical hSource
        AddDrop.dropChannel AddDrop.addChannel)
  · exact congrArg dateThroughGauge
      (hTransport _ _ p.toPhysicalAddDrop_toParameters hPhysical hSource
        AddDrop.throughChannel AddDrop.inputChannel)
  · exact congrArg (fun value => dateThroughGauge (dateAddGauge value))
      (hTransport _ _ p.toPhysicalAddDrop_toParameters hPhysical hSource
        AddDrop.throughChannel AddDrop.addChannel)

/-- The physical DATE response is exactly the DATE source scattering matrix. -/
lemma datePhysicalN5FourPortScattering_eq_source (p : DateParameters)
    (hUnitary : p.IsUnitary) (hDenominator : p.HasNonzeroDenominator) :
    datePhysicalN5FourPortScattering p
        (p.toPhysicalAddDrop_hasNonzeroDenominator hDenominator) =
      dateSourceFourPortScattering p := by
  rw [datePhysicalN5FourPortScattering_eq_n5Response p hDenominator]
  exact dateN5FourPortScattering_eq_source p hUnitary
    ((p.hasNonzeroDenominator_iff).mp hDenominator)

/-- A nonzero DATE forward field makes the physical four-port response pivot bijective. -/
lemma datePhysicalN5FourPortScattering_hasBijectiveRightToLeftTransmission
    (p : DateParameters) (hUnitary : p.IsUnitary)
    (hDenominator : p.HasNonzeroDenominator) (hForward : dateForwardTransfer p ≠ 0) :
    TwoPortScatteringTransform.HasBijectiveRightToLeftTransmission
      (datePhysicalN5FourPortScattering p
        (p.toPhysicalAddDrop_hasNonzeroDenominator hDenominator)) := by
  rw [datePhysicalN5FourPortScattering_eq_source p hUnitary hDenominator]
  exact dateSourceFourPortScattering_hasBijectiveRightToLeftTransmission p hForward

/-! ## D. DATE transfer and chain consequences -/

/-- DATE's forward field is the sign-gauged through entry of the physical N5 ring response. -/
lemma dateForwardTransfer_eq_physicalResponse (p : DateParameters)
    (hUnitary : p.IsUnitary) (hDenominator : p.HasNonzeroDenominator) :
    dateForwardTransfer p = dateThroughGauge
      ((addDropTopology p.toPhysicalAddDrop).responseTransform
        (AddDrop.isWellPosed_of_hasNonzeroDenominator p.toPhysicalAddDrop.toParameters
          (p.toPhysicalAddDrop_hasNonzeroDenominator hDenominator))
        (Outgoing.mk (addDropThroughChannel p.toPhysicalAddDrop))
        (Incident.mk (addDropInputChannel p.toPhysicalAddDrop))) := by
  have hScattering :=
    datePhysicalN5FourPortScattering_eq_source p hUnitary hDenominator
  have hEntry := congrFun (congrFun hScattering
    (Sum.inr (Outgoing.mk ()))) (Sum.inl (Incident.mk ()))
  exact hEntry.symm

/-- DATE's backward field is the drop entry of the physical N5 ring response. -/
lemma dateBackwardTransfer_eq_physicalResponse (p : DateParameters)
    (hDenominator : p.HasNonzeroDenominator) :
    dateBackwardTransfer p =
      (addDropTopology p.toPhysicalAddDrop).responseTransform
        (AddDrop.isWellPosed_of_hasNonzeroDenominator p.toPhysicalAddDrop.toParameters
          (p.toPhysicalAddDrop_hasNonzeroDenominator hDenominator))
        (Outgoing.mk (addDropDropChannel p.toPhysicalAddDrop))
        (Incident.mk (addDropInputChannel p.toPhysicalAddDrop)) := by
  have hScattering := datePhysicalN5FourPortScattering_eq_n5Response p hDenominator
  have hEntry := congrFun (congrFun hScattering
    (Sum.inl (Outgoing.mk ()))) (Sum.inl (Incident.mk ()))
  exact (dateBackwardTransfer_eq_n5Response p hDenominator).trans hEntry.symm

/-- DATE Thm. 2, catalogued at `HOL-CORPUS.md:198`, is the physical N5 chain conversion. -/
lemma datePhysicalFourPortChainTransform_eq (p : DateParameters)
    (hUnitary : p.IsUnitary) (hDenominator : p.HasNonzeroDenominator)
    (hForward : dateForwardTransfer p ≠ 0) :
    (datePhysicalN5FourPortScattering p
      (p.toPhysicalAddDrop_hasNonzeroDenominator hDenominator)).toBackwardFirstChainTransform
        (datePhysicalN5FourPortScattering_hasBijectiveRightToLeftTransmission p hUnitary
          hDenominator hForward) =
      dateFourPortBackwardFirstChainMatrix p := by
  have hScattering := datePhysicalN5FourPortScattering_eq_source p hUnitary hDenominator
  calc
    _ = (dateSourceFourPortScattering p).toBackwardFirstChainTransform
        (dateSourceFourPortScattering_hasBijectiveRightToLeftTransmission p hForward) := by
      apply ModeTransform.toBehavior_injective
      rw [TwoPortScatteringTransform.toBehavior_toBackwardFirstChainTransform,
        TwoPortScatteringTransform.toBehavior_toBackwardFirstChainTransform,
        hScattering]
    _ = dateFourPortBackwardFirstChainMatrix p :=
      dateSourceFourPortChainTransform_eq p hForward

/-- DATE Thm. 2's source-order matrix at
`Physlib/Optics/Systems/Microring/SourceBridgeDate.lean:588-619` is the reindexed physical N5
chain response. -/
lemma dateFourPortChainMatrix_eq_reindexed_physicalResponse (p : DateParameters)
    (hUnitary : p.IsUnitary) (hDenominator : p.HasNonzeroDenominator)
    (hForward : dateForwardTransfer p ≠ 0) :
    dateFourPortChainMatrix p =
      fun output input =>
        (datePhysicalN5FourPortScattering p
          (p.toPhysicalAddDrop_hasNonzeroDenominator hDenominator)).toBackwardFirstChainTransform
              (datePhysicalN5FourPortScattering_hasBijectiveRightToLeftTransmission p hUnitary
                hDenominator hForward)
              (dateBackwardFirstFinEquiv output) (dateBackwardFirstFinEquiv input) := by
  rw [datePhysicalFourPortChainTransform_eq p hUnitary hDenominator hForward]
  exact (dateFourPortBackwardFirstChainMatrix_reindex p).symm

/-! ## E. Physical data in the existing SysCon dictionary -/

/-- Physical add-drop data expressed in the existing SysCon'15 parameter record.

The map selects SysCon's `x_r` to be the physically derived round-trip field attenuation. This is
the interpretation documented at
`Physlib/Optics/Systems/Microring/SourceBridgeSysCon.lean:95-108`, not a source-side
classification of `x_r`.
-/
def addDropPhysicalToSysConParameters (p : AddDropPhysicalParameters) :
    SysConParameters where
  phase := p.propagation.roundTripPhaseLift
  fieldAttenuation := p.propagation.fieldAttenuation.value
  inputCrossAmplitude := p.inputCoupling.crossAmplitude
  dropCrossAmplitude := p.dropCoupling.crossAmplitude
  inputThroughAmplitude := p.inputCoupling.throughAmplitude
  dropThroughAmplitude := p.dropCoupling.throughAmplitude

/-- Mapping physical data through the existing SysCon dictionary recovers its S2 parameters. -/
lemma addDropPhysicalToSysConParameters_toAddDrop (p : AddDropPhysicalParameters) :
    (addDropPhysicalToSysConParameters p).toAddDrop = p.toParameters := rfl

/-- The physical attenuation map lies in SysCon's strictly positive source domain. -/
lemma addDropPhysicalToSysConParameters_fieldAttenuation_pos
    (p : AddDropPhysicalParameters) :
    0 < (addDropPhysicalToSysConParameters p).fieldAttenuation :=
  p.propagation.fieldAttenuation_pos

/-- The physical S2 solve gate transports to the existing SysCon quotient gate. -/
lemma addDropPhysicalToSysConParameters_hasNonzeroDenominator
    (p : AddDropPhysicalParameters) (hDenominator : p.toParameters.HasNonzeroDenominator) :
    (addDropPhysicalToSysConParameters p).HasNonzeroDenominator := by
  apply ((addDropPhysicalToSysConParameters p).hasNonzeroDenominator_iff
    (addDropPhysicalToSysConParameters_fieldAttenuation_pos p).le).mpr
  rwa [addDropPhysicalToSysConParameters_toAddDrop]

/-- The SysCon source contraction gate transports to the physical S2 parameter map. -/
lemma addDropPhysicalToSysConParameters_isContractive_toParameters
    (p : AddDropPhysicalParameters)
    (hContractive : (addDropPhysicalToSysConParameters p).IsContractive) :
    p.toParameters.IsContractive := by
  have hMapped := hContractive.toAddDrop
    (addDropPhysicalToSysConParameters_fieldAttenuation_pos p).le
  rwa [addDropPhysicalToSysConParameters_toAddDrop] at hMapped

/-- SysCon Thm. 5 at `HOL-CORPUS.md:247` is the physical N5 input-to-drop response. -/
lemma sysConDropTransfer_eq_physicalResponse (p : AddDropPhysicalParameters)
    (hDenominator : p.toParameters.HasNonzeroDenominator) :
    sysConDropTransfer (addDropPhysicalToSysConParameters p) =
      (addDropTopology p).responseTransform
        (AddDrop.isWellPosed_of_hasNonzeroDenominator p.toParameters hDenominator)
        (Outgoing.mk (addDropDropChannel p))
        (Incident.mk (addDropInputChannel p)) := by
  have hSource := sysConDropTransfer_eq_n5Response
    (addDropPhysicalToSysConParameters p)
    (addDropPhysicalToSysConParameters_fieldAttenuation_pos p).le
      (addDropPhysicalToSysConParameters_hasNonzeroDenominator p hDenominator)
  simpa only [addDropTopology, addDropDropChannel, addDropInputChannel,
    addDropPhysicalToSysConParameters_toAddDrop] using hSource

/-- SysCon Def. 9 at `HOL-CORPUS.md:244` is the physical response on its contraction domain. -/
lemma sysConDropResponseSeries_eq_physicalResponse (p : AddDropPhysicalParameters)
    (hContractive : (addDropPhysicalToSysConParameters p).IsContractive) :
    sysConDropResponseSeries (addDropPhysicalToSysConParameters p) =
      (addDropTopology p).responseTransform
        (AddDrop.isWellPosed_of_hasNonzeroDenominator p.toParameters
          (addDropPhysicalToSysConParameters_isContractive_toParameters
            p hContractive).hasNonzeroDenominator)
        (Outgoing.mk (addDropDropChannel p))
        (Incident.mk (addDropInputChannel p)) := by
  rw [sysConDropResponseSeries_eq_transfer _
    (addDropPhysicalToSysConParameters_fieldAttenuation_pos p) hContractive]
  exact sysConDropTransfer_eq_physicalResponse p
    (addDropPhysicalToSysConParameters_isContractive_toParameters
      p hContractive).hasNonzeroDenominator

/-- SysCon Def. 10 at `HOL-CORPUS.md:245` is normalized modal power of the physical response.

This is not electromagnetic power before the finite, common-frequency, Maxwell-qualified,
pairwise-integrable, mutually flux-orthogonal, unit-normalized bridge at
`Physlib/Optics/HarmonicFlux/PropagatingModePower.lean:16-22,60-93`.
-/
lemma sysConDropPower_eq_physicalResponsePower (p : AddDropPhysicalParameters)
    (hDenominator : p.toParameters.HasNonzeroDenominator) :
    sysConDropPower (addDropPhysicalToSysConParameters p) = Complex.normSq
      ((addDropTopology p).responseTransform
        (AddDrop.isWellPosed_of_hasNonzeroDenominator p.toParameters hDenominator)
        (Outgoing.mk (addDropDropChannel p))
        (Incident.mk (addDropInputChannel p))) := by
  rw [sysConDropPower, sysConDropTransfer_eq_physicalResponse p hDenominator]

/-! ## F. SFG-TR transfer from the physical N5 ring -/

/-- SFG-TR Thm. 7 at `HOL-CORPUS.md:346` is the physical response under its branch gate. -/
lemma sfgAddDropTransfer_eq_physicalResponse (p : AddDropPhysicalParameters)
    (hSqrt : Complex.sqrt p.toParameters.roundTripCoefficient =
      p.toParameters.firstArcCoefficient)
    (hDenominator : p.toParameters.HasNonzeroDenominator) :
    sfgAddDropTransfer (SfgParameters.ofAddDrop p.toParameters) =
      (addDropTopology p).responseTransform
        (AddDrop.isWellPosed_of_hasNonzeroDenominator p.toParameters hDenominator)
        (Outgoing.mk (addDropDropChannel p))
        (Incident.mk (addDropInputChannel p)) := by
  exact sfgAddDropTransfer_eq_n5Response p.toParameters hSqrt hDenominator

end MicroringSourceBridge

end

end Optics
