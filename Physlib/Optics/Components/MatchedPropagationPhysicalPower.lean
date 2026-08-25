/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Components.MatchedPropagationPhysical
public import Physlib.Optics.Components.MatchedPropagationPower

/-!
# Modal power for physical-port matched propagation

## i. Overview

This file transports the exact normalized-modal-power law and the passive/lossless classifications
of `MatchedPropagation` to its component-owned physical-port presentation. The specification-level
result remains primary: every physical behavior member has output power equal to `a²` times input
power. Scattering classifications then follow through coordinate invariance.

These are still normalized finite-mode statements. Physical port ownership does not supply an
electromagnetic normalization, material-loss model, impedance derivation, reciprocity convention,
or completeness theorem for omitted channels.

## ii. Key results

- `MatchedPropagation.physicalBehavior_output_power`: physical specification-level power scaling.
- `MatchedPropagation.physicalScattering_isPassive`: valid parameters imply modal passivity.
- `MatchedPropagation.physicalScattering_isLossless`: unit amplitude implies modal losslessness.

## iii. Table of contents

- A. Physical behavior power
- B. Physical scattering classification

## iv. References

These coordinate-transport results are Physlib-original and source-neutral.
-/

@[expose] public section

namespace Optics

noncomputable section

universe u

namespace MatchedPropagation

/-!

## A. Physical behavior power

-/

/-- Every state in the independent physical behavior has output power equal to `a²` times its
incident power. -/
lemma physicalBehavior_output_power [Fintype ι] [DecidableEq ι] (p : Parameters)
    {incident : ModeAmplitude (Incident ((portFamily ι).Channel))}
    {outgoing : ModeAmplitude (Outgoing ((portFamily ι).Channel))}
    (hMember : (incident, outgoing) ∈ physicalBehavior p) :
    outgoing.power = p.amplitudeTransmission ^ 2 * incident.power := by
  have hRaw := (mem_physicalBehavior_iff p incident outgoing).mp hMember
  have hPower := behavior_output_power p hRaw
  simpa only [ModeAmplitude.power_reindex] using hPower

/-!

## B. Physical scattering classification

-/

/-- Valid fixed-carrier parameters make the physical-port scattering law passive in normalized
modal power. -/
lemma physicalScattering_isPassive [Fintype ι] [DecidableEq ι] (p : Parameters)
    (hp : p.IsValid) : (physicalScattering p ι).toModeTransform.IsPassive := by
  change ((scattering p ι).toModeTransform.reindex
    (channelEquiv ι) (channelEquiv ι)).IsPassive
  exact (ModeTransform.isPassive_reindex_iff
    (channelEquiv ι) (channelEquiv ι) (scattering p ι).toModeTransform).mpr
      (scattering_isPassive p hp)

/-- Unit amplitude transmission makes the physical-port scattering law lossless in normalized
modal power. -/
lemma physicalScattering_isLossless [Fintype ι] [DecidableEq ι] (p : Parameters)
    (hUnit : p.amplitudeTransmission = 1) :
    (physicalScattering p ι).IsLossless := by
  exact (ScatteringMatrix.isLossless_reindex_iff
    (channelEquiv ι) (scattering p ι)).mpr (scattering_isLossless p hUnit)

end MatchedPropagation

end

end Optics
