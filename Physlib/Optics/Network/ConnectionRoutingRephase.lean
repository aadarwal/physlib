/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Mode.Rephase
public import Physlib.Optics.Network.ExternalChannel

/-!
# Matched-gauge covariance of optical connection routing

## i. Overview

A channel-end gauge independently changes the incident and outgoing coordinates on an ambient
optical boundary. Ideal unit-gain routing is unchanged precisely when the incident phase at every
routed mate equals the outgoing phase at its source channel. This file records that exact
mate-matching condition and lifts it from connected routing to ambient partial routing, external
boundary exposure, readout, and incident assembly.

## ii. Key results

- `ChannelEndGauge`: independent incident and outgoing unit-phase coordinate gauges.
- `PortConnectionFamily.IsMatchedGauge`: the exact phase matching law across every routed mate.
- `PortConnectionFamily.idealRouting_rephase_eq_iff`: connected unit routing is unchanged exactly
  for matched gauges.
- `PortConnectionFamily.partialRouting_rephase_eq_iff`: the same characterization for ambient
  zero-extended routing.
- `PortConnectionFamily.incidentAssembly_rephase`: matched rephasing commutes with assembly of
  internal routing and the external incident drive.

## iii. Table of contents

- A. Channel-end gauges
- B. Exact connected-routing criterion
- C. Ambient routing covariance
- D. External boundary covariance
- E. Incident-assembly covariance

## iv. References

This is the open `goal.md` item at lines 1920--1921 of commit `57c866bc`:
"matched-gauge covariance of connection routing under channel-end rephasing; arbitrary independent
endpoint rephasings do not leave a unit-gain wire unchanged;" It targets ledger row N-07.

Rephasing here is a passive coordinate change. No physical reference-plane displacement,
time-reversal convention, reciprocity, propagation, passivity, losslessness, or electromagnetic
power claim is made. The exact iff results explicitly prevent arbitrary independent endpoint
phases from being treated as an invariant unit-gain wire.
-/

@[expose] public section

namespace Optics

noncomputable section

universe u v w

/-!
## A. Channel-end gauges
-/

/-- Independent incident and outgoing unit-phase coordinates on one channel family. -/
structure ChannelEndGauge (channel : Type u) where
  /-- The phase used for incident channel-end coordinates. -/
  incident : ModePhaseGauge (Incident channel)
  /-- The phase used for outgoing channel-end coordinates. -/
  outgoing : ModePhaseGauge (Outgoing channel)

namespace ChannelEndGauge

/-- Restrict an ambient channel-end gauge along a channel embedding. -/
def pullback {small : Type v} {large : Type u} (embedding : small ↪ large)
    (gauge : ChannelEndGauge large) : ChannelEndGauge small where
  incident endpoint := gauge.incident (Incident.mk (embedding endpoint.channel))
  outgoing endpoint := gauge.outgoing (Outgoing.mk (embedding endpoint.channel))

/-- The incident part of a pulled-back gauge is evaluation at the embedded channel. -/
@[simp]
lemma pullback_incident_apply {small : Type v} {large : Type u}
    (embedding : small ↪ large) (gauge : ChannelEndGauge large)
    (channel : small) :
    (gauge.pullback embedding).incident (Incident.mk channel) =
      gauge.incident (Incident.mk (embedding channel)) := rfl

/-- The outgoing part of a pulled-back gauge is evaluation at the embedded channel. -/
@[simp]
lemma pullback_outgoing_apply {small : Type v} {large : Type u}
    (embedding : small ↪ large) (gauge : ChannelEndGauge large)
    (channel : small) :
    (gauge.pullback embedding).outgoing (Outgoing.mk channel) =
      gauge.outgoing (Outgoing.mk (embedding channel)) := rfl

end ChannelEndGauge

namespace PortConnectionFamily

variable {P : PortModeFamily.{u, v}} {index : Type w}
variable (family : PortConnectionFamily P index)

/-- The ambient gauge restricted to a connection family's connected channels. -/
def connectedGauge (gauge : ChannelEndGauge P.Channel) :
    ChannelEndGauge family.Channel :=
  gauge.pullback family.channelEmbedding

/-- The ambient gauge restricted to the structurally external channel complement. -/
def externalGauge (gauge : ChannelEndGauge P.Channel) :
    ChannelEndGauge family.ExternalChannel :=
  gauge.pullback family.externalChannelEmbedding

/-- A channel-end gauge is matched when each routed incident mate has the same phase as its
outgoing source coordinate. -/
def IsMatchedGauge (gauge : ChannelEndGauge P.Channel) : Prop :=
  ∀ channel,
    gauge.incident
        (Incident.mk (family.channelEmbedding (family.mateEquiv channel))) =
      gauge.outgoing (Outgoing.mk (family.channelEmbedding channel))

/-!
## B. Exact connected-routing criterion
-/

/-- Rephased connected unit routing equals the original routing exactly when every source phase
matches the incident phase at its mate. -/
lemma idealRouting_rephase_eq_iff [DecidableEq family.Channel]
    (gauge : ChannelEndGauge P.Channel) :
    family.idealRouting.rephase
        (family.connectedGauge gauge).outgoing
        (family.connectedGauge gauge).incident =
      family.idealRouting ↔
        family.IsMatchedGauge gauge := by
  constructor
  · intro hRouting channel
    have hEntry := congrArg
      (fun transform => transform
        (Incident.mk (family.mateEquiv channel)) (Outgoing.mk channel)) hRouting
    simp only [ModeTransform.rephase_apply, family.idealRouting_entry_mate,
      mul_one] at hEntry
    change
      (gauge.incident
          (Incident.mk (family.channelEmbedding (family.mateEquiv channel))) : ℂ) *
          (gauge.outgoing
            (Outgoing.mk (family.channelEmbedding channel)) : ℂ)⁻¹ = 1 at hEntry
    apply Subtype.ext
    calc
      (gauge.incident
            (Incident.mk (family.channelEmbedding (family.mateEquiv channel))) : ℂ) =
          ((gauge.incident
              (Incident.mk (family.channelEmbedding (family.mateEquiv channel))) : ℂ) *
            (gauge.outgoing
              (Outgoing.mk (family.channelEmbedding channel)) : ℂ)⁻¹) *
            (gauge.outgoing
              (Outgoing.mk (family.channelEmbedding channel)) : ℂ) := by
                field_simp [Circle.coe_ne_zero]
      _ = 1 *
          (gauge.outgoing
            (Outgoing.mk (family.channelEmbedding channel)) : ℂ) := by
              rw [hEntry]
      _ = (gauge.outgoing
          (Outgoing.mk (family.channelEmbedding channel)) : ℂ) := one_mul _
  · intro hMatched
    ext output input
    rcases output with ⟨output⟩
    rcases input with ⟨input⟩
    rw [ModeTransform.rephase_apply]
    by_cases hOutput : output = family.mateEquiv input
    · subst output
      rw [family.idealRouting_entry_mate]
      change
        (gauge.incident
            (Incident.mk (family.channelEmbedding (family.mateEquiv input))) : ℂ) *
            1 *
            (gauge.outgoing
              (Outgoing.mk (family.channelEmbedding input)) : ℂ)⁻¹ = 1
      rw [hMatched input]
      field_simp [Circle.coe_ne_zero]
    · rw [family.idealRouting_entry, if_neg hOutput]
      simp

/-- A matched gauge leaves connected unit routing literally unchanged. -/
lemma idealRouting_rephase_eq [DecidableEq family.Channel]
    (gauge : ChannelEndGauge P.Channel) (hMatched : family.IsMatchedGauge gauge) :
    family.idealRouting.rephase
        (family.connectedGauge gauge).outgoing
        (family.connectedGauge gauge).incident =
      family.idealRouting :=
  (family.idealRouting_rephase_eq_iff gauge).2 hMatched

/-!
## C. Ambient routing covariance
-/

/-- A matched ambient gauge leaves the zero-extended partial-routing transform unchanged. -/
lemma partialRouting_rephase_eq [Fintype family.Channel]
    [DecidableEq family.Channel] [DecidableEq P.Channel]
    (gauge : ChannelEndGauge P.Channel) (hMatched : family.IsMatchedGauge gauge) :
    family.partialRouting.rephase gauge.outgoing gauge.incident =
      family.partialRouting := by
  ext incident outgoing
  rcases incident with ⟨incident⟩
  rcases outgoing with ⟨outgoing⟩
  rw [ModeTransform.rephase_apply]
  by_cases hOutgoing : outgoing ∈ Set.range family.channelEmbedding
  · rcases hOutgoing with ⟨channel, rfl⟩
    rw [family.partialRouting_entry_connected_column]
    by_cases hIncident :
        incident = family.channelEmbedding (family.mateEquiv channel)
    · subst incident
      rw [if_pos rfl]
      rw [hMatched channel]
      field_simp [Circle.coe_ne_zero]
    · rw [if_neg hIncident]
      simp
  · rw [family.partialRouting_entry_of_outgoing_not_mem_range outgoing hOutgoing]
    simp

/-- Ambient partial routing is unchanged exactly for mate-matched endpoint phases. -/
lemma partialRouting_rephase_eq_iff [Fintype family.Channel]
    [DecidableEq family.Channel] [DecidableEq P.Channel]
    (gauge : ChannelEndGauge P.Channel) :
    family.partialRouting.rephase gauge.outgoing gauge.incident =
      family.partialRouting ↔
        family.IsMatchedGauge gauge := by
  constructor
  · intro hRouting channel
    have hEntry := congrArg
      (fun transform => transform
        (Incident.mk
          (family.channelEmbedding (family.mateEquiv channel)))
        (Outgoing.mk (family.channelEmbedding channel))) hRouting
    simp only [ModeTransform.rephase_apply, family.partialRouting_entry_mate,
      mul_one] at hEntry
    change
      (gauge.incident
          (Incident.mk (family.channelEmbedding (family.mateEquiv channel))) : ℂ) *
          (gauge.outgoing
            (Outgoing.mk (family.channelEmbedding channel)) : ℂ)⁻¹ = 1 at hEntry
    apply Subtype.ext
    calc
      (gauge.incident
            (Incident.mk (family.channelEmbedding (family.mateEquiv channel))) : ℂ) =
          ((gauge.incident
              (Incident.mk (family.channelEmbedding (family.mateEquiv channel))) : ℂ) *
            (gauge.outgoing
              (Outgoing.mk (family.channelEmbedding channel)) : ℂ)⁻¹) *
            (gauge.outgoing
              (Outgoing.mk (family.channelEmbedding channel)) : ℂ) := by
                field_simp [Circle.coe_ne_zero]
      _ = 1 *
          (gauge.outgoing
            (Outgoing.mk (family.channelEmbedding channel)) : ℂ) := by
              rw [hEntry]
      _ = (gauge.outgoing
          (Outgoing.mk (family.channelEmbedding channel)) : ℂ) := one_mul _
  · exact family.partialRouting_rephase_eq gauge

/-- Matched partial routing sends rephased outgoing amplitudes to the rephasing of the original
routed incident amplitude. -/
lemma partialRouting_apply_rephase [Fintype family.Channel]
    [DecidableEq family.Channel] [Fintype P.Channel] [DecidableEq P.Channel]
    (gauge : ChannelEndGauge P.Channel) (hMatched : family.IsMatchedGauge gauge)
    (outgoing : ModeAmplitude (Outgoing P.Channel)) :
    family.partialRouting.toLinearMap
        (ModeAmplitude.rephase gauge.outgoing outgoing) =
      ModeAmplitude.rephase gauge.incident
        (family.partialRouting.toLinearMap outgoing) := by
  have hCovariance := ModeTransform.toLinearMap_rephase_apply
    gauge.outgoing gauge.incident family.partialRouting outgoing
  rw [family.partialRouting_rephase_eq gauge hMatched] at hCovariance
  exact hCovariance

/-!
## D. External boundary covariance
-/

/-- External incident injection is unchanged when its input gauge is the restriction of the
ambient incident gauge. -/
lemma externalIncidentInjection_rephase_eq [DecidableEq P.Channel]
    (gauge : ChannelEndGauge P.Channel) :
    family.externalIncidentInjection.rephase
        (family.externalGauge gauge).incident gauge.incident =
      family.externalIncidentInjection := by
  ext ambient external
  rcases ambient with ⟨ambient⟩
  rcases external with ⟨external⟩
  rw [ModeTransform.rephase_apply]
  by_cases hChannel : ambient = external.1
  · subst ambient
    rw [family.externalIncidentInjection_entry_external]
    change
      (gauge.incident (Incident.mk external.1) : ℂ) * 1 *
          (gauge.incident (Incident.mk external.1) : ℂ)⁻¹ = 1
    field_simp [Circle.coe_ne_zero]
  · rw [family.externalIncidentInjection_entry_of_ne ambient external hChannel]
    simp

/-- External outgoing readout is unchanged when its output gauge is the restriction of the
ambient outgoing gauge. -/
lemma externalOutgoingReadout_rephase_eq [DecidableEq P.Channel]
    (gauge : ChannelEndGauge P.Channel) :
    family.externalOutgoingReadout.rephase gauge.outgoing
        (family.externalGauge gauge).outgoing =
      family.externalOutgoingReadout := by
  ext external ambient
  rcases external with ⟨external⟩
  rcases ambient with ⟨ambient⟩
  rw [ModeTransform.rephase_apply]
  by_cases hChannel : ambient = external.1
  · subst ambient
    rw [family.externalOutgoingReadout_entry_external]
    change
      (gauge.outgoing (Outgoing.mk external.1) : ℂ) * 1 *
          (gauge.outgoing (Outgoing.mk external.1) : ℂ)⁻¹ = 1
    field_simp [Circle.coe_ne_zero]
  · rw [family.externalOutgoingReadout_entry_of_ne external ambient hChannel]
    simp

/-- External readout sends a rephased ambient outgoing amplitude to the corresponding rephased
external output. -/
lemma externalOutgoingReadout_apply_rephase [Fintype P.Channel]
    [DecidableEq P.Channel] [Fintype family.ExternalChannel]
    (gauge : ChannelEndGauge P.Channel)
    (outgoing : ModeAmplitude (Outgoing P.Channel)) :
    family.externalOutgoingReadout.toLinearMap
        (ModeAmplitude.rephase gauge.outgoing outgoing) =
      ModeAmplitude.rephase (family.externalGauge gauge).outgoing
        (family.externalOutgoingReadout.toLinearMap outgoing) := by
  have hCovariance := ModeTransform.toLinearMap_rephase_apply
    gauge.outgoing (family.externalGauge gauge).outgoing
      family.externalOutgoingReadout outgoing
  rw [family.externalOutgoingReadout_rephase_eq gauge] at hCovariance
  exact hCovariance

/-!
## E. Incident-assembly covariance
-/

/-- Matched rephasing commutes with assembly of routed outgoing data and external incident data.
-/
lemma incidentAssembly_rephase [Fintype family.Channel]
    [DecidableEq family.Channel] [Fintype family.ExternalChannel]
    [Fintype P.Channel] [DecidableEq P.Channel]
    (gauge : ChannelEndGauge P.Channel) (hMatched : family.IsMatchedGauge gauge)
    (outgoing : ModeAmplitude (Outgoing P.Channel))
    (external : ModeAmplitude (Incident family.ExternalChannel)) :
    family.incidentAssembly
        (ModeAmplitude.rephase gauge.outgoing outgoing)
        (ModeAmplitude.rephase (family.externalGauge gauge).incident external) =
      ModeAmplitude.rephase gauge.incident
        (family.incidentAssembly outgoing external) := by
  apply WithLp.ofLp_injective 2
  funext endpoint
  rcases endpoint with ⟨channel⟩
  by_cases hConnected : channel ∈ Set.range family.channelEmbedding
  · rcases hConnected with ⟨connected, rfl⟩
    rw [family.incidentAssembly_apply_connected_channel,
      ModeAmplitude.rephase_apply,
      ModeAmplitude.rephase_apply,
      family.incidentAssembly_apply_connected_channel]
    have hPhase := hMatched (family.mateEquiv connected)
    rw [family.mateEquiv_apply_apply] at hPhase
    exact congrArg
      (fun phase : Circle => (phase : ℂ) *
        outgoing
          (Outgoing.mk
            (family.channelEmbedding (family.mateEquiv connected)))) hPhase.symm
  · let externalChannel : family.ExternalChannel := ⟨channel, hConnected⟩
    change family.incidentAssembly
          (ModeAmplitude.rephase gauge.outgoing outgoing)
          (ModeAmplitude.rephase (family.externalGauge gauge).incident external)
          (Incident.mk externalChannel.1) =
        ModeAmplitude.rephase gauge.incident
          (family.incidentAssembly outgoing external)
          (Incident.mk externalChannel.1)
    rw [family.incidentAssembly_apply_external,
      ModeAmplitude.rephase_apply,
      ModeAmplitude.rephase_apply,
      family.incidentAssembly_apply_external]
    rfl

end PortConnectionFamily

end

end Optics
