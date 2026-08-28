/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

/-
Reconnaissance elaboration probe — R3 width-2 cascade, optical interleaver.

Tests R3's central claim and its own biggest residue: that the cascade combinators are
polymorphic in the channel family and nothing fixes the width to one, so the interleaver
instantiates at W := Unit ⊕ Unit with no reindex and no bespoke module.

`W` is spelled as an `abbrev` deliberately — R3 predicted that an opaque `def` would break
`Fintype`/`DecidableEq` instance resolution. That prediction is tested separately in
ReconProbeR3Def.lean.

Elaboration-only. Cited declarations, all at pin cfaeef36:
  DirectionalCoupler.behavior        Components/DirectionalCoupler.lean:109
  MatchedPropagation.transmission    Components/MatchedPropagation.lean:108
  ModeTransform.directSum            Mode/Basic.lean:344
  ReflectionlessTwoPort.behavior     Components/ReflectionlessTwoPort.lean:109
  TwoPortScatteringBehavior.redhefferSeries  Network/TwoPortSeries.lean:74
  BackwardFirstTwoPortBehavior.seriesFold    Network/TwoPortChainFold.lean:69
-/

public import Physlib.Optics.Network.TwoPortChainFold
public import Physlib.Optics.Network.TwoPortSeries
public import Physlib.Optics.Components.DirectionalCoupler
public import Physlib.Optics.Components.MatchedPropagation
public import Physlib.Optics.Components.ReflectionlessTwoPort

@[expose] public section

namespace Optics.CitableR3

open Optics

noncomputable section

/-- The two-waveguide channel family. `abbrev`, per R3's hazard note. -/
abbrev W := Unit ⊕ Unit

/-- Step 1 — coupler stage at `ι := Unit`; each side is already two channels wide. -/
def stageCoupler (p : DirectionalCoupler.Parameters) : TwoPortScatteringBehavior W W :=
  DirectionalCoupler.behavior (ι := Unit) p

/-- Step 2 — the asymmetric arm pair: two DIFFERENT scalar propagations, direct-summed.
This is the step R3 expected to be the obstruction and reported was not. -/
def arm (upper lower : MatchedPropagation.Parameters) : ModeTransform W W :=
  ModeTransform.directSum (MatchedPropagation.transmission upper Unit)
    (MatchedPropagation.transmission lower Unit)

/-- Step 3 — wrap the arm pair as a reflectionless two-port. -/
def stageDelay (upper lower : MatchedPropagation.Parameters) : TwoPortScatteringBehavior W W :=
  ReflectionlessTwoPort.behavior (arm upper lower) (arm upper lower)

/-- Step 4a — two stages composed by the Redheffer series at width two. -/
def twoStages (p : DirectionalCoupler.Parameters)
    (upper lower : MatchedPropagation.Parameters) : TwoPortScatteringBehavior W W :=
  TwoPortScatteringBehavior.redhefferSeries (stageCoupler p) (stageDelay upper lower)

/-- Step 4b — N stages by `seriesFold`, generic in the list, at width two. -/
def lattice (stages : List (BackwardFirstTwoPortBehavior W W)) :
    BackwardFirstTwoPortBehavior W W :=
  BackwardFirstTwoPortBehavior.seriesFold stages

end

end Optics.CitableR3
