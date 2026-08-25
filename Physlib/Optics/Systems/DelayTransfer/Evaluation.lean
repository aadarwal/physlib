/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.Optics.Network.ParameterizedResponse
public import Physlib.Optics.Systems.DelayTransfer.Basic

/-!
# Evaluation of rational-delay optical networks

## i. Overview

`RationalComponentFamily` stores every local scattering entry as a `RationalModel` in a declared
finite family of formal delays. Its conversion to `ParameterizedComponentFamily` evaluates those
models pointwise. Component validity is the conjunction of the independently stored physical
model predicate and nonvanishing of every retained rational denominator.

Entry regularity and network solvability are independent gates. Regular component entries need
not make the feedback operator invertible. Conversely, an algebraically well-posed evaluated
network can lie outside `responseDomain` because a removable retained denominator excludes that
presentation point.

`RationalNetlist` adds parameter-independent N5F wiring. Its `solveDomain` and `responseDomain`
are abbreviations of the N5F domains, not a second elimination procedure. The central commutation
lemma is a direct specialization of
`ParameterizedNetlist.mem_compileBehavior_iff_unguardedResponse` from
`Physlib/Optics/Network/ParameterizedResponse.lean:583`: on the pointwise algebraic solve domain,
evaluating the formal delays, compiling, and eliminating gives the compiled relational behavior.

`laplace` and `reciprocalZ` are N5F reparameterizations. Consequently their solve and response
domains are exact preimages, and their proof-gated responses are the original rational-delay
response evaluated at `q_i = exp (-s * τ_i)` or `q = z⁻¹`.

## ii. Key definitions and results

- `RationalComponentFamily`: component scattering entries presented as rational delay models.
- `RationalComponentFamily.toParameterizedComponentFamily`: pointwise N5F component family.
- `RationalNetlist`: rational components with parameter-independent typed wiring.
- `RationalNetlist.toParameterizedNetlist`: the inherited N5F network.
- `RationalNetlist.mem_compileBehavior_iff_unguardedResponse`: N-10 on formal delay tuples.
- `RationalNetlist.laplace`: substitution by `q_i = exp (-s * τ_i)`.
- `RationalNetlist.response_laplace`: proof-gated response commutes with that substitution.
- `RationalNetlist.reciprocalZ`: substitution by `q = z⁻¹`.

## iii. Table of contents

- A. Rational component families
- B. Rational netlists and inherited domains
- C. N5F evaluation commutation
- D. Laplace and reciprocal-z reparameterization

## iv. References and non-claims

The domain split is inherited from
`Physlib/Optics/Network/ParameterizedResponse.lean:441-468`: `solveDomain` is algebraic
well-posedness, while `responseDomain` additionally contains every stored component-validity
claim. Outside `solveDomain`, N5F's total inverse is meaningless; on
`solveDomain \ responseDomain` it is algebraic but not a physical response.

Delay variables remain formal. This file does not assert rational dependence on physical
frequency, does not identify candidate singularities with transfer-function poles, and makes no
causality, stability, resonance, group-delay, or dispersion claim. No elimination argument is
reproved here. In particular, symbolic rational elimination of the external response is future
work; this module only evaluates retained component presentations pointwise into N5F.
-/

@[expose] public section

namespace Optics.DelayTransfer

noncomputable section

universe u v w x

/-!

## A. Rational component families

-/

set_option linter.checkUnivs false in
/-- Optical component laws whose scattering entries are rational in `n` formal delays. -/
structure RationalComponentFamily (n : ℕ) where
  /-- The type indexing component instances. -/
  Component : Type u
  /-- The parameter-independent physical-port family of each component. -/
  portFamily : Component → PortModeFamily.{v, w}
  /-- The rational model of every local scattering entry. -/
  entryModel :
    (component : Component) →
      (portFamily component).Channel →
        (portFamily component).Channel → RationalModel n
  /-- The independently stored physical-model validity predicate. -/
  ModelValidAt : Component → DelayTuple n → Prop

namespace RationalComponentFamily

variable {n : ℕ} (family : RationalComponentFamily.{u, v, w} n)

/-- Every retained entry denominator of a component is nonzero at one delay assignment. -/
def EntriesRegularAt (component : family.Component) (value : DelayTuple n) : Prop :=
  ∀ output input, value ∈ (family.entryModel component output input).evaluationDomain

/-- Pointwise validity combines the stored model predicate with rational regularity. -/
def IsValidAt (component : family.Component) (value : DelayTuple n) : Prop :=
  family.ModelValidAt component value ∧ family.EntriesRegularAt component value

/-- The evaluated scattering matrix of one component at a formal-delay assignment. -/
def scattering (value : DelayTuple n) (component : family.Component) :
    ScatteringMatrix (family.portFamily component).Channel where
  toModeTransform := fun output input => (family.entryModel component output input).eval value

/-- The N5F component family obtained by pointwise rational evaluation. -/
def toParameterizedComponentFamily : ParameterizedComponentFamily (DelayTuple n) where
  Component := family.Component
  portFamily := family.portFamily
  scattering := family.scattering
  IsValidAt := family.IsValidAt

/-- Pointwise scattering selects exactly the retained rational entry model. -/
lemma toParameterizedComponentFamily_scattering_apply (value : DelayTuple n)
    (component : family.Component)
    (output input : (family.portFamily component).Channel) :
    (family.toParameterizedComponentFamily.scattering value component).toModeTransform
        output input = (family.entryModel component output input).eval value := rfl

/-- N5F component validity is stored physical validity plus entrywise denominator regularity. -/
lemma toParameterizedComponentFamily_isValidAt_iff (component : family.Component)
    (value : DelayTuple n) :
    family.toParameterizedComponentFamily.IsValidAt component value ↔
      family.ModelValidAt component value ∧
        ∀ output input,
          value ∈ (family.entryModel component output input).evaluationDomain := Iff.rfl

end RationalComponentFamily

/-!

## B. Rational netlists and inherited domains

-/

set_option linter.checkUnivs false in
/-- A rational-delay component family equipped with parameter-independent N5F wiring. -/
structure RationalNetlist (n : ℕ) where
  /-- The rational local component laws. -/
  components : RationalComponentFamily.{u, v, w} n
  /-- The type indexing internal physical connections. -/
  Connection : Type x
  /-- The proof-carrying wiring on the aggregate component boundary. -/
  connections : PortConnectionFamily
    components.toParameterizedComponentFamily.aggregatePortModeFamily Connection

namespace RationalNetlist

variable {n : ℕ} (netlist : RationalNetlist.{u, v, w, x} n)

/-- The N5F netlist underlying a rational-delay network. -/
def toParameterizedNetlist : ParameterizedNetlist (DelayTuple n) where
  components := netlist.components.toParameterizedComponentFamily
  Connection := netlist.Connection
  connections := netlist.connections

/-- The aggregate channel type inherited from N5F. -/
abbrev Channel := netlist.toParameterizedNetlist.Channel

/-- The connected-channel family inherited from N5F. -/
abbrev ConnectedChannel := netlist.toParameterizedNetlist.ConnectedChannel

/-- The external channel type inherited from N5F. -/
abbrev ExternalChannel := netlist.toParameterizedNetlist.ExternalChannel

/-- The external incident coordinate type inherited from N5F. -/
abbrev ExternalIncident := netlist.toParameterizedNetlist.ExternalIncident

/-- The external outgoing coordinate type inherited from N5F. -/
abbrev ExternalOutgoing := netlist.toParameterizedNetlist.ExternalOutgoing

/-- Pointwise compilation is exactly N5F compilation of the evaluated component laws. -/
abbrev compile (value : DelayTuple n) := netlist.toParameterizedNetlist.compile value

section Finite

variable [Fintype netlist.Channel] [Fintype netlist.ConnectedChannel]

/-- Classical equality on aggregate rational-netlist channels. -/
local instance rationalChannelDecidableEq : DecidableEq netlist.Channel := Classical.decEq _

/-- Classical equality on connected rational-netlist channels. -/
local instance rationalConnectedChannelDecidableEq :
    DecidableEq netlist.ConnectedChannel := Classical.decEq _

/-- External channels of the finite rational netlist are finite. -/
local instance rationalExternalChannelFintype : Fintype netlist.ExternalChannel := by
  classical
  infer_instance

/-- Classical equality on external rational-netlist channels. -/
local instance rationalExternalChannelDecidableEq :
    DecidableEq netlist.ExternalChannel := Classical.decEq _

/-- Pointwise compilation retains finite aggregate channels. -/
local instance rationalCompileChannelFintype (value : DelayTuple n) :
    Fintype (netlist.compile value).Channel :=
  inferInstanceAs (Fintype netlist.Channel)

/-- Pointwise compilation retains finite connected channels. -/
local instance rationalCompileConnectedChannelFintype (value : DelayTuple n) :
    Fintype (netlist.compile value).ConnectedChannel :=
  inferInstanceAs (Fintype netlist.ConnectedChannel)

/-- Classical equality on pointwise compiled aggregate channels. -/
local instance rationalCompileChannelDecidableEq (value : DelayTuple n) :
    DecidableEq (netlist.compile value).Channel := Classical.decEq _

/-- Classical equality on pointwise compiled connected channels. -/
local instance rationalCompileConnectedChannelDecidableEq (value : DelayTuple n) :
    DecidableEq (netlist.compile value).ConnectedChannel := Classical.decEq _

/-- The algebraic solve domain inherited unchanged from N5F. -/
abbrev solveDomain : Set (DelayTuple n) := netlist.toParameterizedNetlist.solveDomain

/-- The physical response domain inherited unchanged from N5F. -/
abbrev responseDomain : Set (DelayTuple n) := netlist.toParameterizedNetlist.responseDomain

/-!

## C. N5F evaluation commutation

-/

/-- On the pointwise solve domain, rational-delay evaluation, compilation, and N5 elimination
agree with the compiled singular-safe relational behavior. -/
lemma mem_compileBehavior_iff_unguardedResponse {value : DelayTuple n}
    (hSolve : value ∈ netlist.solveDomain)
    (input : ModeAmplitude netlist.ExternalIncident)
    (output : ModeAmplitude netlist.ExternalOutgoing) :
    (input, output) ∈ (netlist.compile value).behavior ↔
      output =
        (netlist.toParameterizedNetlist.unguardedResponse value).toLinearMap input :=
  netlist.toParameterizedNetlist.mem_compileBehavior_iff_unguardedResponse
    hSolve input output

/-- On the physical response domain, rational-delay evaluation gives the proof-gated N5F
response. -/
lemma mem_compileBehavior_iff_response {value : DelayTuple n}
    (hValue : value ∈ netlist.responseDomain)
    (input : ModeAmplitude netlist.ExternalIncident)
    (output : ModeAmplitude netlist.ExternalOutgoing) :
    (input, output) ∈ (netlist.compile value).behavior ↔
      output =
        (netlist.toParameterizedNetlist.response hValue).toLinearMap input :=
  netlist.toParameterizedNetlist.mem_compileBehavior_iff_response hValue input output

/-!

## D. Laplace and reciprocal-z reparameterization

-/

/-- The N5F family obtained by substituting `q_i = exp (-s * τ_i)`. -/
def laplace (delays : Fin n → ℝ) : ParameterizedNetlist ℂ :=
  netlist.toParameterizedNetlist.reparameterize (laplaceEvaluation delays)

/-- Laplace reparameterization retains finite aggregate channels. -/
local instance laplaceChannelFintype (delays : Fin n → ℝ) :
    Fintype (netlist.laplace delays).Channel :=
  inferInstanceAs (Fintype netlist.Channel)

/-- Laplace reparameterization retains finite connected channels. -/
local instance laplaceConnectedChannelFintype (delays : Fin n → ℝ) :
    Fintype (netlist.laplace delays).ConnectedChannel :=
  inferInstanceAs (Fintype netlist.ConnectedChannel)

/-- Classical equality on Laplace-reparameterized aggregate channels. -/
local instance laplaceChannelDecidableEq (delays : Fin n → ℝ) :
    DecidableEq (netlist.laplace delays).Channel := Classical.decEq _

/-- Classical equality on Laplace-reparameterized connected channels. -/
local instance laplaceConnectedChannelDecidableEq (delays : Fin n → ℝ) :
    DecidableEq (netlist.laplace delays).ConnectedChannel := Classical.decEq _

/-- Laplace reparameterization retains finite external channels. -/
local instance laplaceExternalChannelFintype (delays : Fin n → ℝ) :
    Fintype (netlist.laplace delays).ExternalChannel :=
  inferInstanceAs (Fintype netlist.ExternalChannel)

/-- Pointwise Laplace compilation retains finite aggregate channels. -/
local instance laplaceCompileChannelFintype (delays : Fin n → ℝ) (s : ℂ) :
    Fintype ((netlist.laplace delays).compile s).Channel :=
  inferInstanceAs (Fintype netlist.Channel)

/-- Pointwise Laplace compilation retains finite connected channels. -/
local instance laplaceCompileConnectedChannelFintype (delays : Fin n → ℝ) (s : ℂ) :
    Fintype ((netlist.laplace delays).compile s).ConnectedChannel :=
  inferInstanceAs (Fintype netlist.ConnectedChannel)

/-- Classical equality on pointwise compiled Laplace channels. -/
local instance laplaceCompileChannelDecidableEq (delays : Fin n → ℝ) (s : ℂ) :
    DecidableEq ((netlist.laplace delays).compile s).Channel := Classical.decEq _

/-- Classical equality on pointwise compiled Laplace connected channels. -/
local instance laplaceCompileConnectedChannelDecidableEq
    (delays : Fin n → ℝ) (s : ℂ) :
    DecidableEq ((netlist.laplace delays).compile s).ConnectedChannel := Classical.decEq _

/-- The Laplace solve domain is the exact preimage of the formal-delay solve domain. -/
lemma solveDomain_laplace (delays : Fin n → ℝ) :
    (netlist.laplace delays).solveDomain =
      laplaceEvaluation delays ⁻¹' netlist.solveDomain :=
  netlist.toParameterizedNetlist.solveDomain_reparameterize (laplaceEvaluation delays)

/-- The Laplace response domain is the exact preimage of the formal-delay response domain. -/
lemma responseDomain_laplace (delays : Fin n → ℝ) :
    (netlist.laplace delays).responseDomain =
      laplaceEvaluation delays ⁻¹' netlist.responseDomain :=
  netlist.toParameterizedNetlist.responseDomain_reparameterize (laplaceEvaluation delays)

/-- The algebraic total-inverse formula commutes definitionally with Laplace substitution. -/
lemma unguardedResponse_laplace (delays : Fin n → ℝ) (s : ℂ) :
    (netlist.laplace delays).unguardedResponse s =
      netlist.toParameterizedNetlist.unguardedResponse (laplaceEvaluation delays s) := rfl

/-- On the Laplace solve domain, direct pointwise compilation agrees with formal-delay response
evaluation at `q_i = exp (-s * τ_i)`. -/
lemma mem_compileBehavior_laplace_iff_unguardedResponse
    (delays : Fin n → ℝ) {s : ℂ}
    (hSolve : s ∈ (netlist.laplace delays).solveDomain)
    (input : ModeAmplitude netlist.ExternalIncident)
    (output : ModeAmplitude netlist.ExternalOutgoing) :
    (input, output) ∈ ((netlist.laplace delays).compile s).behavior ↔
      output =
        (netlist.toParameterizedNetlist.unguardedResponse
          (laplaceEvaluation delays s)).toLinearMap input := by
  have hDelaySolve : laplaceEvaluation delays s ∈ netlist.solveDomain := by
    rw [netlist.solveDomain_laplace delays] at hSolve
    exact hSolve
  change (input, output) ∈
      (netlist.compile (laplaceEvaluation delays s)).behavior ↔ _
  exact netlist.mem_compileBehavior_iff_unguardedResponse hDelaySolve input output

/-- The proof-gated Laplace response is formal-delay response evaluated at the exponential
substitution. -/
lemma response_laplace (delays : Fin n → ℝ) {s : ℂ}
    (hLaplace : s ∈ (netlist.laplace delays).responseDomain)
    (hDelay : laplaceEvaluation delays s ∈ netlist.responseDomain) :
    (netlist.laplace delays).response hLaplace =
      netlist.toParameterizedNetlist.response hDelay :=
  netlist.toParameterizedNetlist.response_reparameterize
    (laplaceEvaluation delays) hLaplace hDelay

/-- The one-delay N5F family obtained by substituting `q = z⁻¹`. -/
def reciprocalZ (oneDelayNetlist : RationalNetlist.{u, v, w, x} 1) :
    ParameterizedNetlist ℂ :=
  oneDelayNetlist.toParameterizedNetlist.reparameterize zInverseEvaluation

/-- Reciprocal-z reparameterization retains finite aggregate channels. -/
local instance reciprocalZChannelFintype
    (oneDelayNetlist : RationalNetlist.{u, v, w, x} 1)
    [Fintype oneDelayNetlist.Channel] :
    Fintype oneDelayNetlist.reciprocalZ.Channel :=
  inferInstanceAs (Fintype oneDelayNetlist.Channel)

/-- Reciprocal-z reparameterization retains finite connected channels. -/
local instance reciprocalZConnectedChannelFintype
    (oneDelayNetlist : RationalNetlist.{u, v, w, x} 1)
    [Fintype oneDelayNetlist.ConnectedChannel] :
    Fintype oneDelayNetlist.reciprocalZ.ConnectedChannel :=
  inferInstanceAs (Fintype oneDelayNetlist.ConnectedChannel)

/-- Classical equality on reciprocal-z aggregate channels. -/
local instance reciprocalZChannelDecidableEq
    (oneDelayNetlist : RationalNetlist.{u, v, w, x} 1) :
    DecidableEq oneDelayNetlist.reciprocalZ.Channel := Classical.decEq _

/-- Classical equality on reciprocal-z connected channels. -/
local instance reciprocalZConnectedChannelDecidableEq
    (oneDelayNetlist : RationalNetlist.{u, v, w, x} 1) :
    DecidableEq oneDelayNetlist.reciprocalZ.ConnectedChannel := Classical.decEq _

/-- Reciprocal-z reparameterization retains finite external channels. -/
local instance reciprocalZExternalChannelFintype
    (oneDelayNetlist : RationalNetlist.{u, v, w, x} 1)
    [Fintype oneDelayNetlist.Channel] [Fintype oneDelayNetlist.ConnectedChannel] :
    Fintype oneDelayNetlist.reciprocalZ.ExternalChannel := by
  change Fintype oneDelayNetlist.ExternalChannel
  classical
  infer_instance

/-- The reciprocal-z solve domain is the exact preimage of the formal-delay solve domain. -/
lemma solveDomain_reciprocalZ (netlist : RationalNetlist.{u, v, w, x} 1)
    [Fintype netlist.Channel] [Fintype netlist.ConnectedChannel] :
    netlist.reciprocalZ.solveDomain = zInverseEvaluation ⁻¹' netlist.solveDomain :=
  netlist.toParameterizedNetlist.solveDomain_reparameterize zInverseEvaluation

/-- Proof-gated response commutes with the selected `q = z⁻¹` substitution. -/
lemma response_reciprocalZ (netlist : RationalNetlist.{u, v, w, x} 1)
    [Fintype netlist.Channel] [Fintype netlist.ConnectedChannel]
    {z : ℂ} (hZ : z ∈ netlist.reciprocalZ.responseDomain)
    (hDelay : zInverseEvaluation z ∈ netlist.responseDomain) :
    netlist.reciprocalZ.response hZ =
      netlist.toParameterizedNetlist.response hDelay :=
  netlist.toParameterizedNetlist.response_reparameterize zInverseEvaluation hZ hDelay

end Finite

end RationalNetlist

end

end Optics.DelayTransfer
