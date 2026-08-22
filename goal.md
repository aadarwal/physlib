# Physlib Optics: long-running formal-photonics goal

This is the fork-only execution plan for building a connected Optics library in Physlib. It is a
living engineering document, not a proposed upstream API and not a substitute for the human-owned
review obligations in `AI-POLICY.md`. The public scope contract is
`Physlib/Optics/API-map.yaml`; unresolved upstream, licensing, and human-certification work belongs
in `tbd.md`. This file should normally be omitted from focused upstream pull requests.

## A. Mission

Build a reusable Lean optics stack that can formally model an optical system from its physical
assumptions, compose the system from verified components, and prove its requested behavior. The
stack should eventually match the useful system-analysis capabilities demonstrated by the
Concordia HOL developments while improving their connection between abstraction levels.

The central end-to-end result is:

1. start with a real monochromatic electromagnetic plane wave;
2. derive its phasor, Jones, coherency, and Stokes representations;
3. propagate it through polarization elements and a planar dielectric interface;
4. prove Malus' law, reflection, Snell's law, Fresnel amplitudes, and energy-flux balance;
5. reuse the same modal and component semantics in finite photonic networks;
6. derive transfer functions, powers, resonance properties, and rejection ratios for
   interferometers and microring systems; and
7. provide the ray-transfer, imaging, Gaussian-beam, and resonator analyses needed for functional
   parity with the broader HOL Light optics work.

The goal is not a collection of isolated formulas. A result counts only when its assumptions and
objects are connected to the preceding layer, or when the file explicitly states that it is an
abstract model awaiting a named bridge theorem.

### A.1. First release checkpoint: Optics v0.1

Before claiming broad HOL parity, deliver one connected vertical slice. Optics v0.1 accepts a real
monochromatic plane wave, obtains its raw Jones, coherency, and Stokes data, applies an ideal
polarizer and retarder, sends it to a planar lossless dielectric interface, and proves Malus'
law, reflection, Snell's law, Fresnel amplitudes, and normal energy-flux balance. Every observable
must commute through the relevant raw-field, irradiance, and power-normalized-mode bridges.

The finite-network track proceeds in parallel because it is the foundation for the integrated-
photonics baseline, but it is not allowed to weaken or delay the physical v0.1 bridge chain. A
stand-alone Jones calculation, a stored Fresnel matrix, or a microring formula is not v0.1.

## B. What “HOL-equivalent” means

“Equivalent” means equivalent verification capability, not a transliteration of HOL Light source
or an attempt to preserve its internal encodings. The target has two main baselines.

### B.1. Integrated-photonics baseline

The SysCon and related signal-processing work demonstrates:

- physical behavior predicates for photonic components;
- complex transfer-matrix models derived from those behaviors;
- series, summing, pickoff, and feedback block-diagram calculations;
- causal difference equations and a Z-transform with a region of convergence;
- closed-form microring transfer amplitude, output power, and rejection ratio;
- signal-flow graphs and Mason-style calculations in the follow-on work; and
- reuse of these foundations for families of coupled resonators.

Physlib reaches this baseline when the corresponding results are obtained from typed components
and a common network semantics, with every division, inverse, infinite sum, and stability statement
carrying its real nondegeneracy or convergence hypotheses.

### B.2. Geometrical- and quasi-optics baseline

The broader HOL Light development demonstrates:

- valid optical interfaces, components, ordered systems, rays, and beams;
- ray behavior in free space and at plane, spherical, reflecting, and phase-conjugating interfaces;
- component and whole-system ray-transfer matrices;
- composition of arbitrary finite optical systems;
- cardinal points and imaging laws;
- Gaussian-beam parameters and the complex ABCD law;
- lenses, mirrors, cavities, and resonator-stability criteria; and
- representative instrument and resonator case studies.

Physlib reaches this baseline when it can state and prove the same classes of system properties
using native geometry, matrices, and analysis, even if its types and proof decomposition differ.

### B.3. The stronger Physlib criterion

For each capability, completion requires all of the following:

- **Model coverage:** the relevant physical objects and parameter-validity predicates exist.
- **Law coverage:** the component or propagation law is stated with explicit hypotheses.
- **Composition coverage:** arbitrary finite systems can reuse the law without restating it.
- **Calculation coverage:** an important closed form follows from the compositional semantics.
- **Observable coverage:** amplitude results are connected to power, flux, stability, or another
  physically meaningful specification.
- **Bridge coverage:** adjacent abstractions agree by a theorem, or the missing bridge is explicitly
  named and the stronger physical interpretation is withheld.
- **Regression coverage:** canonical examples are proved from the public API.

A tuple of parameters plus a formula does not meet this criterion. A proof that merely unfolds a
formula assumed in the definition also does not meet it.

## C. Ownership and import layering

The intended dependency direction is:

```text
Mathlib / SpaceAndTime / WaveEquation
        |
        | geometry, complex algebra, analysis, Fourier theory
        v
Electromagnetism
        |
        | real fields, Maxwell equations, constitutive data, energy flux,
        | boundary laws, field-level plane waves
        v
Optics
        |
        | phasors, polarization, rays, finite modes, observables,
        | components and interfaces
        v
Optical systems
        |
        | imaging, ABCD systems, interferometers, resonators,
        | transfer functions, diffraction and Fourier optics
        v
QuantumInfo-owned bridge
        |
        | finite-mode bosonic lifts and quantum observables
```

Ownership rules:

- General complex, matrix, graph, topology, integration, and Fourier results belong in Mathlib or
  an existing mathematical Physlib namespace.
- Real electromagnetic fields remain foundational. Optics adds fixed-frequency reduced
  representations and proves how they reconstruct the real fields; it does not introduce a second
  competing Maxwell theory.
- Constitutive laws, electromagnetic energy density and flux, and field boundary laws belong in
  `Physlib/Electromagnetism`.
- Phasors, Jones/Stokes/Mueller data, optical components, rays, interfaces, observables, and
  finite-mode system semantics belong in `Physlib/Optics`.
- A quantum-optics lift should import Optics from `QuantumInfo`; Optics must not import
  `QuantumInfo` merely to obtain qubit state wrappers.
- Reflective scattering networks and one-way cascades remain different operations. Ordinary matrix
  multiplication is a cascade law, not a feedback-interconnection law.

## D. Current foundation

### D.1. Present in the fork

- [x] `Physlib/Optics/API-map.yaml` records the domain boundary and long-term requirements.
- [x] `Optics.ModeAmplitude` is `EuclideanSpace ℂ ι` with modal power equal to its squared `L²`
  norm and component, scaling, positivity, and inner-product lemmas.
- [x] `Optics.ModeTransform` is a rectangular complex matrix with power-preserving and passive
  semantics and cascade closure.
- [x] Matrix isometry implies modal power preservation.
- [x] `Optics.ScatteringMatrix` wraps a square transform without inheriting multiplication;
  unitarity implies power preservation and passivity under the stated normalization.
- [x] Power preservation is equivalent to `Tᴴ * T = 1`, passivity is equivalent to positivity of
  the defect `1 - Tᴴ * T`, and square power preservation is equivalent to unitarity.
- [x] Fixed-carrier phasors, distinct raw-field `JonesVector` and `JonesMatrix` wrappers,
  amplitude-phase realization, squared Jones intensity, global-phase invariance, and matrix action
  are present without importing Electromagnetism or identifying raw fields with normalized modes.
- [x] The explicit three-dimensional `harmonicWaveX` solution has a named positive-frequency,
  positive-first-coordinate Jones frame with complete electric- and magnetic-field realization and
  a direct `B = c⁻¹ k̂ × E` theorem, without a static-background, gauge, or power claim.
- [x] Generic positive-semidefinite `CoherencyMatrix` data supplies Hermiticity, real nonnegative
  diagonal and trace results, `A * C * Aᴴ` transport, cascade compatibility, and combined
  mode-polarization specializations without assuming Jones purity.
- [x] Jones outer-product coherency embeds coherent polarization into the general coherency type,
  with rank-at-most-one, determinant-zero, trace-intensity, unit-phase, and Jones-action laws.
- [x] `tbd.md` records the human, source-license, upstream-design, and validation gates.

### D.2. Relevant upstream foundations

- `Electromagnetism.Vacuum.HarmonicWave` supplies an explicit real harmonic Maxwell solution in
  free space. In three spatial dimensions its two transverse electric components are
  `E₀ i * cos (k * c * t - k * x₀ + φ i)` when `k ≠ 0`.
- `Electromagnetism.Vacuum.IsPlaneWave` supplies the existing real plane-wave predicate.
- `Electromagnetism.ThreeDimension.MaxwellEquations` proves pointwise differential vacuum Maxwell
  equations, but explicitly does not yet supply material constitutive laws, integral laws, or
  boundary conditions.
- `ClassicalMechanics.WaveEquation` supplies real plane waves and harmonic-wave infrastructure.
- `SpaceAndTime.Space` supplies Euclidean geometry, derivatives, volume integration, and cross
  products, but not yet the complete oriented-surface and trace API needed for generic interface
  derivations.
- Mathlib supplies complex Euclidean spaces, adjoints, positive-semidefinite matrices, matrix
  inversion under determinant hypotheses, Schur complements, power/Laurent series, rational
  functions, and finite graph infrastructure. Exact reuse should be audited per work package.

### D.3. Not yet present

- [ ] Stokes, Poincare, and Mueller APIs;
- [ ] polarizers, retarders, Malus' law, and wave-plate calculations;
- [ ] material media, Poynting flux, boundary laws, Snell, Fresnel, and total internal reflection;
- [ ] typed ports, behaviors, wiring, and well-posed network elimination;
- [ ] reusable beam splitters, couplers, delays, mirrors, interferometers, and microrings;
- [ ] difference-equation, Z-transform, transfer-function, signal-flow, and Mason layers; and
- [ ] ray, imaging, Gaussian-beam, and resonator libraries.

## E. Non-negotiable modeling invariants

1. **No logical shortcuts.** No `axiom`, `sorry`, `Lean.ofReduceBool`, `True` placeholders,
   conclusion-as-hypothesis tricks, or vacuous existential results.
2. **No hidden static field.** A generic plane-wave profile can contain a constant background.
   Phasor transversality must use the explicit harmonic solution or a zero-static-component,
   zero-mean, nonzero-frequency, or equivalent hypothesis.
3. **One convention registry.** Every file that depends on phase, handedness, port direction,
   reference plane, or matrix row/column order must point to a single documented convention.
4. **No inverse without invertibility.** Mathlib's matrix inverse is a total operation. Every
   physical use must carry `IsUnit M.det`, `M.det ≠ 0`, a proved inverse, or an equivalent unique
   solvability hypothesis.
5. **No feedback by multiplication.** For a reflective device, `S₂ * S₁` is not in general the
   connected scattering matrix. Interconnection is defined by internal signal equations and
   elimination.
6. **No physical power claim before normalization.** `ModeAmplitude.power` is modal power under a
   declared convention. It becomes electromagnetic power only after a Poynting-flux normalization
   theorem.
7. **No mixed state disguised as a Jones vector.** Jones vectors describe coherent pure
   polarization. Partially polarized light enters through positive-semidefinite coherency data.
8. **No frequency-domain ambiguity.** Physical angular frequency, Laplace frequency, discrete
   Z-transform variable, and the delay variable `q = exp (-s * τ) = z⁻¹` are distinct concepts.
9. **No false rationality claim.** A circuit may be rational in a formal delay variable while not
   being rational in physical frequency because propagation constants and material data can be
   dispersive.
10. **No source-code copying without license confirmation.** External HOL scripts are architecture
    and theorem-selection references until a human confirms their licenses. Implementations are
    independently written against Lean and Mathlib APIs.
11. **No import cycle.** Electromagnetism never imports Optics; the bridge theorem importing both
    lives in Optics. QuantumInfo imports Optics, not conversely.
12. **One coherent concept per upstream PR.** The long-running branch may integrate many commits,
    but every candidate upstream branch remains small, reviewable, and independently meaningful.

## F. Dependency graph

```text
polarization
  Mathlib --> P1a Jones foundations
  Mathlib --> P2a general coherency
  Mathlib --> P3a neutral Hermitian basis
  P1a --> P1b harmonic bridge, P2b pure coherency, P5a Malus, P6a retarder core
  P2a --> P2b pure coherency, P3b Stokes cone
  P3a --> P3b Stokes cone
  P2b + P3b --> P3c Poincare classification
  P1a + P2a + P3a + P3b --> P4 deterministic Mueller
  P5a + E3b --> P5b physical Malus bridge
  P1b + P2b + P3b/P4 + P5a/P5b + P6a + E3b --> P6b connected polarization chain

electromagnetic v0.1
  E1 media/macroscopic Maxwell --> E2 material waves, E3a real energy/Poynting, E4 boundary laws
  O1 + P1a + E2 + E3a --> E3b harmonic-flux and mode-normalization bridge
  E2 + E4 --> E5 reflection/Snell/TIR
  E3b + E5 --> E6 Fresnel amplitudes/flux
  P1b + P2b + P3b/P4 + P5b/P6b + E3b/E6 --> Optics v0.1

finite networks and integrated photonics
  O1 mode core --> O2/N1 modal completion --> N2a ports/routing
  O1 mode core --> N3 relational behaviors
  O2/N1 + N2a + N3 --> N4 flat relational semantics --> N5 well-posed elimination
  N4 --> relational N5H flattening; N5 --> functional N5H subsystem packaging
  N2a + O2/N1 --> N7 behavior-specified components
  N5 + N7 --> N5F parameterized response domains
  N2a + N5 --> N6a conservation
  N2b reciprocity metadata + N6a --> N6b reciprocity
  N5/N5F + N6a + N7 --> S1--S4 systems
  Mathlib analysis --> S5 Z-transform
  N5 + finite graph API --> S6 Mason
  N5H + S1--S6 --> S7 HOL case suite

ray and beam parity
  E1/E5 --> R1 physical/paraxial rays --> R2 systems --> R3 imaging --> R4 Gaussian beams
  R4 --> R5 resonators
```

P1a, P2a, P3a, O2/N1, N3, E1, and the mathematical audit for S5 are independent starting fronts.
P2a/P3a do not wait for P1b; P5a/P6a core Jones calculations do not wait for Stokes, although P6b's
comparison chain does. E1--E6 is the deepest physical prerequisite chain and must not be bypassed by
assuming Fresnel coefficients. R1--R5 is a later functional-parity track; it should reuse E-track
medium and interface data where that does not force a false equivalence between exact wave optics
and the paraxial approximation.

## G. Intended Lean representations

The names below are design targets, not frozen API promises. Each feature branch must first check
current Mathlib and Physlib declarations and choose the least duplicative representation.

### G.1. Phasors and polarization

```lean
abbrev Phasor := ℂ

def Phasor.realize (z : Phasor) (carrierPhase : ℝ) : ℝ :=
  (z * Complex.exp (carrierPhase * Complex.I)).re

structure JonesVector where
  val : EuclideanSpace ℂ (Fin 2)

structure JonesMatrix where
  val : Matrix (Fin 2) (Fin 2) ℂ

structure CoherencyMatrix (ι : Type*) where
  toMatrix : Matrix ι ι ℂ
  posSemidef : toMatrix.PosSemidef

abbrev StokesIndex := Fin 1 ⊕ Fin 3
abbrev StokesVector := EuclideanSpace ℝ StokesIndex
```

The first bridge uses the convention `Re (z * exp (I * carrierPhase))`. For amplitudes `E₀` and
phases `φ`, the Jones component is `E₀ i * exp (I * φ i)`. The bridge must prove equality with the
existing `harmonicWaveX` electric-field components, not merely define a parallel signal. Jones
foundations and this Electromagnetism bridge are separate modules and separate PR concepts.

This first bridge is deliberately basis-specific: the wave propagates along coordinate `0`, its
longitudinal electric component is zero, and the Jones entries reconstruct spatial components `1`
and `2`. The underlying potential only needs `k ≠ 0`, but the first physical polarization bridge
uses positive wavenumber/frequency and represents propagation direction separately; otherwise the
meaning of right/left circular polarization reverses with the sign of temporal frequency. It does
not need nonzero transverse amplitudes. Signed amplitude/phase coordinates are non-unique, so no
inverse or injectivity theorem is claimed without first choosing a normalized amplitude convention.
The bridge module belongs in Optics because it imports both layers; Electromagnetism must remain
independent of Optics.

`JonesVector` is intentionally a distinct wrapper rather than an abbreviation for
`ModeAmplitude (Fin 2)`. Its entries are raw transverse electric-field phasors. Its squared norm is
an electric-amplitude-squared or Jones-intensity parameter; for a vacuum plane wave the mean flux
density has an additional impedance factor, and total power also needs an area or normalized mode
profile. Only a proved normalization map may turn this data into a power-normalized
`ModeAmplitude`. Likewise, a Jones matrix is not silently a `ModeTransform`; their agreement under
a common medium/mode normalization is a bridge theorem.

Neither wrapper receives a blanket coercion to `EuclideanSpace` or `Matrix`. Such a coercion would
make raw Jones data silently usable wherever `ModeAmplitude` or `ModeTransform` is expected and
would defeat the type boundary. Use explicit value projections for algebra internal to the Jones
API and named physical-normalization maps at the boundary.

Jones data alone does not reconstruct an electromagnetic potential. Given the medium, carrier,
propagation direction, transverse frame, and phase origin, it reconstructs the electric field and
the compatible magnetic field. Recovering a potential would additionally require a gauge choice.

Pure coherency is the outer product

```text
C(J) i j = J i * conj (J j).
```

General coherency data is defined before the pure Jones construction. It bundles only an indexed
complex matrix and `Matrix.PosSemidef`; finite and decidable index assumptions belong on operations,
not in the structure. The predicate already supplies Hermiticity in the selected complex setting,
so the wrapper does not store a redundant Hermitian proof. The polarization specialization uses
`Fin 2`; multimode polarization uses a combined index such as `ι × Fin 2` so that cross-port and
cross-mode coherence is not discarded by a collection of unrelated per-port `2 x 2` matrices.

The expected proof spine reuses `Matrix.posSemidef_vecMulVec_self_star`,
`Matrix.PosSemidef.isHermitian`, `Matrix.trace_vecMulVec`, `Matrix.mul_vecMulVec`,
`Matrix.vecMulVec_mul`, `Matrix.conjTranspose_vecMulVec`,
`Matrix.PosSemidef.mul_mul_conjTranspose_same`, `Matrix.det_vecMulVec`, and
`Matrix.rank_vecMulVec_le` after confirming their current signatures and importing the relevant
matrix files directly. Jones vectors themselves are never quotiented: coherent networks still need
their global phase. A quotient or equivalence relation is used only to state the pure
polarization-state classification theorem. Invariance under a scalar phase always includes the
unit-modulus hypothesis.

The `Fin 1 ⊕ Fin 3` index separates total intensity from the three polarization coordinates and can
be reindexed to conventional `Fin 4` data. The Optics Stokes basis must be local even if existing
Pauli-matrix results provide proof help. If generic Pauli/self-adjoint algebra currently lives under
Relativity, extract it to a neutral mathematical module rather than importing Relativity into
Optics. The existing Pauli coefficient convention is a half-trace coefficient; a Stokes definition
based on it therefore needs the audited factor of two. Existing Pauli-coordinate order is not the
conventional Stokes order: for horizontal/vertical coordinates the intended map is
`S₀ = 2*c₀`, `S₁ = 2*c₃`, `S₂ = 2*c₁`, and `S₃ = ±2*c₂`. The final sign depends on the exponential
and handedness convention and is frozen only after right- and left-circular Jones vectors have
named realization theorems that a human checks.

Define an explicit Stokes intensity coordinate and a three-dimensional polarization projection.
The physical cone condition is `‖S.polarization‖ ≤ S.intensity`, not a bound on the full
four-dimensional Euclidean norm. The linear reconstruction
`(1/2) • ∑ μ, S μ • σ μ` exists for every real coordinate vector; it is positive semidefinite
exactly under the cone condition. The public physical-Stokes type should therefore bundle that
condition rather than pretend every `StokesVector` is physical.

### G.2. Finite-mode components and networks

Keep the existing conventions:

```text
ModeAmplitude ι        = EuclideanSpace ℂ ι
ModeTransform ι κ      = Matrix κ ι ℂ
b                      = S a
```

A network should distinguish incident and outgoing channel spaces at the type level. A candidate
design has a finite port type, a finite mode family over ports, orientation wrappers, and a
connection object whose well-formedness proves compatible one-to-one matching. The existing
`ScatteringMatrix ι` uses a common coordinate label for physically distinct incident and outgoing
spaces. The network layer can retain that component API by lifting its matrix along canonical
equivalences into `Incident ι` and `Outgoing ι`; it must not silently identify those wrappers.
Relabeling a port or channel should be an equivalence, not an unchecked integer rewrite.

An implicit linear behavior is a submodule or predicate on paired input/output amplitudes. It must
exist independently of invertibility. A functional transform embeds as its graph; series and
parallel composition are relational operations. This is necessary for ideal constraints and for
components whose useful transfer orientation can become singular.

Let `A_in` and `A_out` be the assembled incident and outgoing spaces. For the first finite
scattering network, use a typed wiring transform `C : A_out -> A_in`, input exposure
`E_in : U -> A_in`, and output exposure `E_out : Y -> A_out`. The equations are

```text
b = S a
a = C b + E_in u
y = E_outᴴ b.
```

They imply

```text
(I - C S) a = E_in u
y = E_outᴴ S (I - C S)⁻¹ E_in u
```

only when the internal equation is well posed. Define well-posedness first as unique solvability
for every external input. Prove its finite-dimensional equivalence to invertibility of `I - C*S`;
then derive the inverse formula as a `ModeTransform U Y`. Call it a `ScatteringMatrix` only after
declaring the input/output channel pairing, square equivalence, and completeness identities needed
for incident and outgoing coordinates of the same external ports. A contraction bound may prove
convergence of a multiple-round-trip series, but it is sufficient rather than necessary for
algebraic well-posedness. The construction must state matrix shapes and prove exposure isometries,
internal/external disjointness, and channel completeness. General readout and direct-feedthrough
matrices can be layered on later; they should not obscure the physically selected-channel theorem
required by the first API.

A concrete first netlist design to test is:

- `PortModeFamily`, with a port type and finite mode family over each port;
- `Channel := Σ p, Mode p`;
- `LinearBehavior ι κ := Submodule ℂ (ModeAmplitude ι × ModeAmplitude κ)`;
- a finite component family with a scattering matrix on each component's channels; and
- a flat netlist whose channel equivalence partitions internal and external channels, with internal
  wiring represented by a fixed-point-free involution together with its lifts from outgoing to
  incident endpoint wrappers and proofs of mode compatibility.

Use local classical decidability where possible instead of storing public `DecidableEq` fields.
The wiring model is one-to-one: splitters, combiners, and terminations are physical components, not
multi-links hidden in the connection relation. Preserve the order `I - C*S`, not `I - S*C`, because
rows are outgoing, columns incident, `b = S*a`, and `a = C*b + E_in*u`.

### G.3. Frequency, delays, recurrences, and transfer functions

- A fixed-frequency component is a matrix at one frequency.
- A frequency response is a function from a deliberately chosen frequency parameter type to fixed-
  frequency components.
- Network well-posedness is pointwise in that parameter; the public response domain records the
  frequencies at which the internal operator is invertible.
- A propagation delay at Laplace frequency `s` has factor `exp (-s * τ)`.
- On the imaginary axis, the nondispersive harmonic response is obtained by `s = I * ω`, after the
  sign convention is reconciled with the phasor layer.
- Algebraic circuit calculations use an explicit delay symbol `q`; where appropriate, represent
  rational results by Mathlib's rational-function API. Rational-network theorems require component
  entries rational in finitely many declared delay variables.
- A unilateral Z-transform is an analytic sum of a causal sequence and therefore carries a region
  of convergence. Its delay theorem must encode zero extension and initial conditions correctly.
- A formal power-series model can prove coefficient recurrences without analytic convergence, but
  it is not silently identified with the analytic Z-transform.

### G.4. Material fields and interfaces

The first material model should be intentionally narrow: homogeneous, isotropic, linear,
nonconducting, nondispersive media with positive scalar permittivity and permeability. It should
derive wave speed and impedance. Refractive index must say whether it is absolute, relative to
vacuum, or relative between two media. Constitutive equations alone are not material Maxwell
equations: Electromagnetism also needs a macroscopic Maxwell predicate in terms of `D`, `H`, and
free sources, plus source-free and superposition lemmas.

The first interface stack is explicitly three-dimensional, because cross products, `s`/`p`
polarization, and the Poynting vector are used. It must connect the existing magnetic
matrix/vector representation to `H = B / μ` under the isotropic-medium assumptions.

Field-level energy definitions belong in Electromagnetism:

```text
instantaneous Poynting vector  S = E x H
time-averaged harmonic flux   <S> = (1/2) Re (Ephasor x conj Hphasor)
```

The real field definitions and Poynting laws belong in Electromagnetism. Complex harmonic
averaging and the Jones/mode normalization bridges live in Optics modules that import the required
electromagnetic results. The factor, sign, and use of `B` versus `H` must be derived under the
chosen conventions. A normalization theorem integrates or evaluates the appropriate normal flux,
includes impedance and area/mode-profile factors, and only then identifies it with
`ModeAmplitude.power` for a declared power-normalized propagating mode.

For coherent superpositions, use the Hermitian signed-power pairing, not a one-sided complex
Poynting product. With interface normal `n` and phasor fields `F` and `G`, the target convention is

```text
⟨F, G⟩_P = (1/4) ∫ n · (E_F × conj(H_G) + conj(E_G) × H_F).
```

Its self-pairing must be proved equal to real time-averaged normal flux. Only after proving modal
orthogonality, unit normalization, and the incoming/outgoing signs may the separate positive
coordinate norms be identified with `ModeAmplitude.power`.

A planar interface contains a point and oriented unit normal. The initial exact-wave slice may use
pointwise tangential boundary predicates for smooth explicit plane waves, but the final physical
claim requires an Electromagnetism theorem deriving those predicates from Maxwell's integral laws
and explicit absence of free surface charge/current; bound polarization charge may remain in a
material description. Fresnel coefficients are conclusions of the boundary system, never fields
stored in the interface definition.

The incident plus reflected total field and the transmitted total field must be assembled on their
respective half-spaces at a common frequency before traces are compared. `s` and `p` require either
oblique incidence or an independently selected tangential frame at normal incidence. Total
internal reflection requires a complex wavevector and a chosen outgoing/decaying square-root
branch; an evanescent field is not an ordinary positive-power propagating mode. Converting Fresnel
field amplitudes to a multiport scattering matrix uses square-root normal-admittance factors. Its
ordinary power-unitarity theorem is restricted to the regime where every retained propagating
channel has strictly positive normal admittance. Grazing/critical channels have singular
normalization, and a TIR evanescent transmitted field is not placed in that ordinary positive-power
port set; those regimes use a reduced propagating-channel set or a later generalized flux pairing.

The Fresnel convention must orient `s` and `p` bases separately for incident, reflected, and
transmitted directions and state whether `r_p` and `t_p` multiply full electric-vector amplitudes
or tangential components. No coefficient theorem or field-to-scattering bridge is named until the
choice and its induced signs and admittance factors are explicit.

### G.5. Rays, paraxial systems, and Gaussian beams

Keep three notions separate:

- a physical ray with a point and unit propagation direction;
- a paraxial meridional coordinate such as height and reduced angle/slope; and
- a Gaussian beam with wavelength and a complex beam parameter in its physically valid domain.

An ordered optical system is a list or composable structure of valid components. Its system matrix
is a fold in the documented propagation order. Free propagation, refraction, thin lenses, and
mirrors receive explicit parameter-validity predicates. The ray-transfer and ABCD laws are proved
by induction from component behavior. Gaussian-beam validity should make the nonzero denominator
and positive-imaginary-domain facts available rather than asking every application to recover them.

## H. Milestones and work packages

Each work package is intended to become one focused branch or a short stack of branches. A package
is complete only after its exit theorem(s), tests, documentation, API-map update, and validation
gate pass.

### H.0. Foundations already started

#### O0. Domain roadmap — complete

- `Physlib/Optics/Basic.lean` states ownership.
- `Physlib/Optics/API-map.yaml` records the long-term contract.
- `tbd.md` separates fork progress from upstream-readiness obligations.

#### O1. Power-normalized finite modes — complete

- mode amplitudes, modal power, transforms, passivity, power preservation, and wrapped scattering
  matrices;
- cascade closure and the forward implication from matrix isometry to power preservation.

#### O2. Complete the modal algebra — active

- [x] characterize power preservation by `Tᴴ * T = I`;
- [x] characterize passivity by a positive-semidefinite defect matrix;
- [x] specialize square power preservation to unitarity;
- add finite direct-sum/parallel composition and preservation lemmas; and
- add reindexing/rephasing invariance before reciprocity.

Exit: the modal predicates can be used bidirectionally by later component and network proofs.

### H.1. Polarization milestone

#### P1a. Jones and scalar-phasor foundations — complete

Candidate location: `Physlib/Optics/Polarization/Basic.lean`.

Deliverables:

- fixed-carrier phasor realization with a documented sign convention;
- a distinct raw-electric-field `JonesVector` and `JonesMatrix`, without importing
  Electromagnetism or identifying either with the power-normalized mode API;
- construction of a Jones vector from two real amplitudes and phases;
- componentwise realization and squared Jones amplitude/intensity;
- proof that realization gives `E₀ i * cos (carrierPhase + φ i)`;
- Jones-matrix action, identity, composition, and squared-norm lemmas; and
- unit-modulus global-phase invariance where an observable forgets phase.

Exit: Jones calculations have a small field-amplitude API whose units and normalization claims are
honest and which can be reviewed without importing the electromagnetic stack.

#### P1b. Harmonic electromagnetic bridge — complete

Candidate location: `Physlib/Optics/Polarization/HarmonicWave.lean`.

Deliverables:

- vector and component bridge theorems to the transverse electric field of the existing explicit
  `harmonicWaveX` construction for `d = 2` and positive `k`, with propagation direction represented
  separately from positive carrier frequency;
- explicit medium (vacuum in the first bridge), carrier, propagation direction, transverse frame,
  and phase-origin data;
- longitudinal-electric-field and compatible magnetic-field results needed to identify the whole
  field solution covered by the theorem; and
- an explicit statement that the bridge covers the purely harmonic field and does not absorb an
  arbitrary static background or determine a potential without an additional gauge choice.

Exit: the existing real Maxwell field solution, but not an unqualified potential, is reconstructed
from Jones data under named geometric and carrier assumptions.

#### P2a. General coherency data — complete

Candidate location: `Physlib/Optics/Polarization/Coherency.lean`.

Deliverables:

- a generic indexed wrapper containing only a complex matrix and `Matrix.PosSemidef`;
- Hermiticity, nonnegative diagonal, trace, and conjugation-map lemmas, with finiteness and
  decidable-equality assumptions placed on operations rather than stored in the wrapper;
- specialization to `Fin 2` and to multimode indices such as `ι × Fin 2`, retaining cross-mode
  coherences; and
- direct imports only of the positive-semidefinite and trace APIs needed by this package; determinant
  and rank imports enter P2b where the pure outer-product proofs actually use them.

Exit: partially polarized states have a general positive-semidefinite representation independent
of Jones purity and independent of Electromagnetism.

#### P2b. Pure coherency embedding — complete

Deliverables:

- outer-product coherency of a Jones vector;
- Hermiticity, positive semidefiniteness, rank at most one, determinant zero, and trace/squared-
  amplitude identity;
- invariance under multiplication of the Jones vector by a unit-modulus scalar;
- the transformation law `C(J') = M * C(J) * Mᴴ` when `J' = M J`; and
- a proof that every pure construction inhabits the general coherency type.

Exit: coherent and partially polarized states are represented without conflation.

#### P3a. Neutral Hermitian/Pauli coordinates

Candidate location: an existing neutral matrix module, or a new neutral mathematical module only
if the audit proves one is necessary.

Deliverables:

- the Hermitian `2 x 2` basis, half-trace coordinate extraction, and reconstruction theorem;
- reality, linearity, and basis-orthogonality lemmas; and
- extraction of reusable algebra from a physics namespace rather than introducing an
  Optics-to-Relativity dependency, with the neutral module itself importing no Relativity file and
  the existing Relativity Pauli API re-exporting or delegating to it so current downstream imports
  and public names are preserved.

#### P3b. Stokes coordinates and the physical cone

Candidate location: `Physlib/Optics/Polarization/Stokes.lean`.

Deliverables:

- the audited Stokes reordering/factors relative to P3a and the convention-dependent `S₃` sign;
- reality of all coordinates, explicit intensity, and three-dimensional polarization projection;
- linear reconstruction for every raw real Stokes vector;
- positive semidefiniteness exactly when intensity is nonnegative and polarization norm is at most
  intensity; and
- a physical-Stokes subtype bundling that cone condition rather than an unconditional inverse into
  coherency data.

#### P3c. Poincare classification

Candidate location: `Physlib/Optics/Polarization/Poincare.lean`.

Deliverables:

- the closed-Poincare-ball theorem for normalized nonzero physical coherency;
- sphere equality for rank-one states and a strict interior theorem for a precisely stated mixed
  class such as rank two or positive definite;
- canonical horizontal, vertical, diagonal, antidiagonal, right-circular, and left-circular cases;
- explicit handling of the zero-intensity case; and
- the pure-state correspondence stated for unit-intensity Jones vectors modulo the `U(1)` action,
  not for arbitrary nonzero Jones vectors modulo phase alone.

Exit: normalized physical coherency matrices correspond to the closed ball and pure unit-intensity
Jones states modulo unit phase correspond to the sphere.

Jones matrices induce deterministic coherency and Mueller maps but do not describe depolarizers.
A later general depolarizing layer needs positive, and where physically appropriate completely
positive, maps on coherency data; it must not be smuggled into the Jones API.

#### P4. Deterministic Mueller action

Candidate location: `Physlib/Optics/Polarization/Mueller.lean`.

Deliverables:

- the real `4 x 4` Mueller matrix induced by a Jones matrix through coherency conjugation;
- reality of its entries and the theorem that Stokes coordinates commute with the Jones/coherency
  transformation;
- identity and composition laws;
- invariance under multiplication of the Jones matrix by a unit-modulus global scalar phase;
- intensity and Poincare-sphere consequences for unitary Jones matrices; and
- explicit documentation that this is deterministic nondepolarizing optics, not the most general
  real Stokes-space transformation.

Exit: Jones, coherency, Stokes, and deterministic Mueller calculations are four proved views of the
same transformation.

#### P5a. Jones polarizer and Malus core

Candidate locations: `Components/Polarizer.lean` and a small shared Jones-component file if needed.

Deliverables:

- normalized linear-polarization vectors at arbitrary axes;
- ideal linear-polarizer Jones matrices as rank-one projections;
- self-adjointness, idempotence, contraction for squared Jones intensity, axis transmission, and
  orthogonal extinction;
- sequential-polarizer amplitude and squared-Jones-intensity laws;
- Malus' law for a linearly polarized input, with the input/output axis angle made explicit.

Exit: a linearly polarized input sent through an arbitrary ideal linear polarizer has transmitted
Jones intensity `I * cos²(delta)` without making a physical-power claim.

#### P5b. Physical Malus bridge

Candidate location: the Optics normalization bridge beside E3b, not the Jones core file.

Deliverables:

- translate P5a's squared-Jones-intensity theorem to irradiance for the plane-wave family covered
  by E3b; and
- translate it to `ModeAmplitude.power` only for the proved flux-normalized mode family.

Exit: physical Malus power is a corollary of P5a plus E3b rather than a second intensity definition.

#### P6a. Retarder and wave-plate core

Candidate location: `Components/Retarder.lean`.

Deliverables:

- rotated ideal retarder at arbitrary fast-axis angle and retardance;
- unitarity and squared-Jones-intensity preservation without depending on Stokes theory;
- quarter-wave and half-wave specializations;
- proved Jones actions on the canonical linear, circular, and selected elliptical states.

Exit: retarder and wave-plate calculations are complete in raw Jones coordinates without waiting
for Stokes or the electromagnetic bridge.

#### P6b. Cross-representation polarization chain

Deliverables:

- agreement of P6a Jones actions with the P2b/P3b coherency and Stokes descriptions;
- induced P4 Mueller calculations;
- a connected example starting at P1b's `harmonicWaveX` bridge and passing through a P5a polarizer
  and P6a wave plate; and
- raw Jones, coherency, Stokes, Mueller, field-realization, irradiance, and normalized-power
  observables, using P5b/E3b only where physical power is claimed.

Exit: the connected polarization chain has all four reduced descriptions and its physical
observables agree through named bridge theorems.

### H.2. Electromagnetic-interface milestone

#### E1. Homogeneous isotropic media

Owner: Electromagnetism.

- positive scalar permittivity and permeability with explicit linear, homogeneous, isotropic,
  nonconducting, nondispersive scope;
- `D = ε E`, `B = μ H`, wave speed, wave impedance, and refractive-index conventions;
- a macroscopic Maxwell predicate using `E`, `D`, `B`, `H`, free charge, and free current, rather
  than treating the constitutive equations as Maxwell's equations;
- source-free specialization and linear-superposition lemmas;
- positivity and nonzero lemmas needed by divisions and square roots; and
- vacuum as a specialization or proved bridge to `FreeSpace`.

Exit: medium parameters are sufficient to state material plane waves and interface coefficients
without ad hoc real tuples, and the governing equations distinguish free from bound sources.

#### E2. Material monochromatic plane waves

- real three-dimensional electric, displacement, magnetic-induction, and magnetic fields in a
  homogeneous medium, including the existing representation bridge and `H = B / μ`;
- dispersion relation, transversality under explicit harmonic hypotheses, and `E`/`H` relation;
- Maxwell-equation satisfaction;
- an Optics-owned complex-harmonic/phasor representation importing the real field theorem;
- polarization-basis decomposition into `s` and `p` modes for oblique incidence, with an
  independently chosen tangent frame for normal incidence; and
- a complex-wavevector representation and outgoing/decaying branch for evanescent fields.

Exit: incident, reflected, transmitted, and evanescent candidate fields share one field API.

#### E3a. Electromagnetic energy and Poynting flux

Owner: Electromagnetism.

- instantaneous energy density and Poynting vector;
- Poynting theorem in the available smooth source-free setting;
- real-field vacuum energy conservation; and
- material energy conservation only from E1's time-independent nondispersive constitutive laws.

Exit: electromagnetic energy flow exists independently of Jones or finite-mode conventions.

#### E3b. Harmonic flux and Optics normalization

Owner: Optics, importing E3a.

- harmonic time average and complex-phasor formula with the factor and sign derived from the
  adopted convention;
- normal flux density of a propagating plane wave, including impedance;
- zero normal average flux for the evanescent transmitted wave where appropriate;
- an aperture or normalized transverse-mode-profile integral when total power is claimed;
- the Hermitian signed-power flux pairing for finite mode families, with its self-pairing equal to
  real time-averaged normal flux, mutual flux orthogonality, normalization, and incident/outgoing
  sign conventions proved before extending a one-mode result to coherent superpositions; and
- explicit maps from raw Jones field amplitudes to irradiance and from a declared normalized field
  mode to `ModeAmplitude.power`.

Exit: “lossless” and “power balance” can be interpreted as electromagnetic statements for the
mode family covered by the theorem.

#### E4. Planar interface and boundary laws

- oriented affine plane, tangential projection, two half-spaces, and incident-side convention;
- total incident-plus-reflected and transmitted fields, their half-space restrictions/traces, and
  a common-frequency condition before boundary values are compared;
- tangential `E` and `H` and normal `D` and `B` boundary laws with free surface sources;
- zero-free-surface-charge/current specializations, without claiming bound polarization charge is
  absent; and
- derivation from integral Maxwell laws, or an explicitly tracked intermediate status if the first
  PR only packages the local boundary predicate.

Exit: boundary equations are physical theorems or clearly named hypotheses, never disguised
Fresnel formulas.

#### E5. Reflection, refraction, and total internal reflection

- phase matching along the entire plane;
- equality of frequency and tangential wave-vector components under necessary nonzero-amplitude
  assumptions;
- specular reflection and Snell's law;
- existence/uniqueness of a propagating transmitted direction below the critical angle;
- critical-angle and total-internal-reflection characterization; and
- evanescent transmitted wave with a complex wavevector and its outgoing/decaying square-root
  branch convention, kept distinct from an ordinary positive-power propagating mode.

Exit: the geometric laws follow from the field and boundary setup.

#### E6. Fresnel amplitudes and flux balance

- `s`- and `p`-polarized reflection and transmission amplitudes derived by solving the boundary
  equations;
- normal-incidence specialization through a selected tangent frame;
- oriented incident/reflected/transmitted `s` and `p` bases and an explicit choice between full-
  vector and tangential-amplitude coefficient conventions;
- Brewster-angle results with the exact magnetic/nonmagnetic and positivity hypotheses needed for
  existence;
- total-internal-reflection modulus and phase results;
- the power transmission factor with the correct normal-admittance multiplier;
- `R + T = 1` for lossless propagating interfaces, proved using Poynting flux; and
- the Fresnel multiport matrix normalized by square roots of normal admittance, with unitarity
  proved in those power coordinates for strictly positive-admittance propagating channels rather
  than for raw electric-field amplitudes, grazing channels, or TIR evanescent fields.

Exit: the full Optics v0.1 example proves Jones/Stokes/component/interface results from connected
definitions.

### H.3. Typed finite-network milestone

#### N1. Modal algebra completion

Complete O2 before relying on converse characterizations or parallel closure.

#### N2a. Ports, channels, and convention-free routing

- a finite `PortModeFamily` and dependent flattened channel type `Σ p, Mode p`;
- distinct incident and outgoing channel-end types;
- compatible one-to-one connections, represented in the flat finite case by a fixed-point-free
  involution on internal channels;
- channel relabeling and rephasing; and
- power, passivity, and losslessness predicates that do not require choosing time-reversal data.

Exit: malformed direction or channel connections are unrepresentable or fail an explicit
well-formedness predicate before semantic analysis.

#### N2b. Reciprocity convention metadata

- time-reversed channel pairing;
- reference-plane and port-phase conventions;
- their transformation under relabeling and rephasing; and
- the precise reciprocity predicate induced by those choices.

Exit: reciprocity has a physical convention rather than an unexplained matrix-symmetry label. This
package remains blocked on the decision in section L; it does not block N2a--N6a.

#### N3. Implicit linear behaviors

- a relation/submodule for linear component behavior;
- embedding of `ModeTransform` as a graph;
- a membership characterization for the embedded graph;
- identity, series, and parallel behavior composition;
- rectangular summing, pickoff, splitter, and combiner behaviors, without pretending fan-out is a
  one-to-one wire;
- equivalence between relational and functional composition where a function exists; and
- no invertibility requirement merely to state a component.

Exit: transfer matrices are derived views of suitable behavior, not the only possible component
definition.

#### N4. Scattering netlists and equations

- disjoint-sum assembly of component incident and outgoing channel spaces;
- block-diagonal assembly of component scattering matrices;
- a routing transform `C : A_out → A_in`, an input exposure `E_in : U → A_in`, and an output
  exposure `E_out : Y → A_out`, each derived from typed endpoint selections;
- proofs of the exposure isometries and projection identities, and of routing/exposure
  disjointness and completeness;
- derivation of `b = S*a`, `a = C*b + E_in*u`, `y = E_outᴴ*b`, and
  `(I - C*S)*a = E_in*u`;
- a singular-safe `FlatNetlist.behavior` defined by existential internal amplitudes, together with
  a theorem that it equals relational composition of the assembled component behaviors; and
- invariance under internal-channel reordering.

Exit: network equations come from a typed netlist rather than being supplied independently.

#### N5. Well-posed elimination

- unique-solvability definition;
- equivalence with trivial homogeneous kernel, injectivity/surjectivity, determinant nonzero, and
  matrix invertibility in the finite complex case;
- external response transform `E_outᴴ * S * (I - C*S)⁻¹ * E_in`, with all domain and codomain
  shapes visible in its statement, and a separate scattering specialization only under an
  external input/output pairing and completeness theorem;
- agreement of that formula with the relational semantics;
- series cascade as a specialization; and
- Redheffer star products for declared matched block partitions, with the particular feedback
  block's invertibility hypothesis stated explicitly and reflective feedback kept distinct from
  one-way cascade.

Exit: the solver works whenever the finite network is uniquely solvable, without imposing a norm
contraction as a necessary condition.

The first eliminator should also prove exposed-single-component, two-component series,
nested-feedback, scalar-feedback, singular-loop, relabeling, and relation/matrix agreement
examples. Summing and pickoff are N3 rectangular behaviors; an N5 elimination example uses them
only after giving an explicit square component realization with the required extra channels and
honest gain/power hypotheses; an exact unit-gain fan-out is not silently called passive in
power-normalized coordinates. Otherwise those examples remain purely relational in N3. General
direct feedthrough can come later, but selected-channel readout is part of the first semantics.

#### N5F. Parameterized compilation and response domains

- frequency- or parameter-dependent component families with pointwise validity hypotheses;
- compilation of each parameter value to the fixed-frequency N4 equations;
- an algebraic solve domain where the N5 internal operator is invertible, and a physical response
  domain obtained by intersecting it with every component's parameter-validity domain;
- a response function on that domain, with evaluation commuting with compilation and elimination;
  and
- continuity, differentiability, or analyticity results only under corresponding hypotheses on
  component data and inverse-domain control.

Exit: spectral responses, resonance conditions, and free-spectral-range statements are derived
from the same network semantics at every frequency where the response is defined.

#### N5H. Hierarchical composition and flattening

- a hierarchical network whose child components may themselves be well-formed networks;
- a relational flattening operation preserving typed external ports, mode compatibility, and
  conventions, with no well-posedness assumption required merely to flatten;
- equality between hierarchical relational semantics and the semantics of the flattened netlist;
- functional packaging of a child as a scattering/response component only after that child's
  well-posedness and external-channel pairing have been proved; and
- associativity/invariance results needed to reuse a verified subsystem.

Exit: proofs scale by verified subsystem boundaries without changing the result obtained from the
fully flattened channel equations.

#### N6a. Conservation under interconnection

- internal connection power balance with no fan-out or duplicated channel;
- passivity closure assuming every component is passive and routing is a power-nonincreasing
  partial isometry with the stated exposure disjointness;
- losslessness of the complete external response assuming every component is lossless, internal
  routing is power preserving on the routed subspace, external channels are complete, and the
  network is well posed; and
- invariance of all physical predicates under relabeling/rephasing.

Exit: system-level conservation is a theorem from component properties and wiring validity.

#### N6b. Reciprocity under interconnection

- reciprocity closure using N2b's time-reversed channel pairing and reference-plane conventions;
- covariance under allowed relabeling and rephasing; and
- scattering-matrix symmetry only in the coordinates for which it has actually been proved.

Exit: reciprocity is available without blocking the convention-free conservation and system work.

#### N7. Reusable finite-mode components

- basic component definitions may start after N2a and the O2 direct-sum/reindexing support, before
  the general eliminator is complete;
- matched propagation delay and attenuation;
- mirror and termination;
- ideal directional coupler and beam splitter with explicit unitary parameter constraints;
- polarization components embedded into multimode channels;
- dielectric interface scattering connected to E6;
- an independent behavioral specification for every component, followed by a realization lemma
  proving that its matrix or relation satisfies that specification; and
- explicit passivity and losslessness proofs under each component's real parameter hypotheses,
  rather than merely storing or assuming those classifications.

Exit: every core component has orientation, an independent behavioral specification, a realization
lemma, parameter validity, and intensity/power classification suitable for automatic system
proofs. Reciprocity extensions are added only after N2b/N6b conventions are available.

### H.4. Integrated-photonic system milestone

#### S1. Mach-Zehnder interferometer

- depend on the N5 solver and the N6a/N7 conservation and component laws, rather than supplying an
  interferometer-specific transfer formula;
- construct it solely from two couplers and two arms;
- prove complex output amplitudes and both output powers;
- prove lossless power balance; and
- specialize to balanced, dark-port, and phase-sensing cases.

#### S2. All-pass and add-drop microring resonators

- depend on N5/N5F, N6a, and the proved N7 coupler/delay component laws;
- construct each ring as an explicit feedback network;
- derive through/drop transfer amplitudes from N5;
- state exact denominator/well-posedness conditions;
- prove the multiple-round-trip geometric series only under its convergence condition; and
- prove equality between the series and algebraic-elimination views where both apply.

#### S3. Ring observables

- derive observables from the S2 pointwise N5F response and the N6a/N7 normalization and conservation
  theorems;
- through/drop power responses;
- lossless power balance;
- resonance and antiresonance conditions;
- critical coupling and extinction conditions;
- rejection ratio with positive numerator/denominator and explicit log convention; and
- free spectral range under an explicit nondispersive or group-index hypothesis.

#### S4. Delay-variable transfer functions

- build on N5F's parameterized compilation and response domain;
- formal delay indeterminate `q` and evaluation map;
- rational transfer functions for finite-delay linear networks whose component entries are
  rational in the declared finite family of delay variables;
- proof that evaluating `q = exp (-s*τ)` agrees with the direct frequency response on the
  pointwise well-posed domain;
- singular internal operators as candidate poles, with actual poles identified only after ruling
  out input/output cancellation or hidden unreachable/unobservable singular modes; and
- no claim of rational dependence on physical frequency without the required model.

#### S5. Difference equations and Z-transform

- causal complex sequences with zero extension;
- finite convolution and linear recurrences with initial conditions;
- analytic unilateral Z-transform and region of convergence;
- linearity and correctly stated delay/advance laws;
- recurrence-to-transfer theorem under summability and initial-condition hypotheses;
- absolute-summability/BIBO stability results and their relation to poles and the region of
  convergence for the selected causal rational class; and
- connection between coefficient recurrences and the formal power-series view.

#### S6. Signal-flow graphs and Mason's rule

- finite directed weighted multigraph with distinguished input/output nodes and explicit edge
  identity, so parallel paths are not collapsed;
- topology independent of whether a symbolic or evaluated edge weight happens to be zero;
- node-equation semantics and adjacency matrix;
- paths, simple loops, touching, and pairwise non-touching loop families;
- graph determinant and cofactors;
- Mason gain formula under a nonzero graph determinant;
- equality with the corresponding entry of `(I - A)⁻¹`; and
- extraction from suitable scalar network models.

The ordinary commutative Mason formula is applied only after expanding a multimode network into
scalar channel nodes. Matrix-valued edge gains do not commute and require a different theorem; do
not claim the scalar formula for them.

#### S7. HOL-equivalence case suite

- one-port/all-pass and four-port/add-drop ring;
- coupled and double-coupled ring examples after the single-ring API stabilizes;
- transfer amplitude, spectral power, resonance, and rejection-ratio results;
- at least one difference-equation/Z-transform derivation; and
- at least one signal-flow/Mason derivation proved equal to network elimination.

Exit for H.4: the integrated-photonics results in the cited HOL program can be reproduced as
instances of a more general typed system API.

### H.5. Ray, imaging, Gaussian-beam, and resonator milestone

#### R1. Physical and paraxial rays

- physical ray, oriented interface incidence, reflection, and refraction;
- paraxial ray coordinate with the approximation stated as a model assumption or a proved limit;
- free-space and plane/spherical-interface behavior; and
- relationship to E5's exact geometric directions.

#### R2. Ray-transfer components and systems

- free propagation, refraction, thin/thick lenses, and plane/spherical mirrors;
- validity predicates and component matrices;
- arbitrary ordered system and matrix fold; and
- component, system, and composed-system ray-transfer theorems.

#### R3. Imaging and cardinal points

- imaging condition and transverse/angular magnification;
- principal, nodal, and focal points with nondegeneracy assumptions;
- thin-lens and lens-maker specializations; and
- a representative ophthalmic or telescope subsystem after source/model review.

#### R4. Gaussian beams and the complex ABCD law

- wavelength, waist, Rayleigh range, and complex `q` parameter;
- physically valid domain and free-propagation law;
- Gaussian solution of the paraxial wave/Helmholtz equation;
- ABCD transformation with denominator and domain proofs; and
- output waist and location formulas.

#### R5. Optical resonators

- round-trip system and fixed-ray/fixed-beam predicates;
- determinant-one trace criterion and its exact hypotheses;
- Fabry-Perot, ring, and selected phase-conjugate resonators; and
- agreement between ray-stability and Gaussian fixed-point views where applicable.

Exit for H.5: the principal ray- and Gaussian-optics theorem classes and representative system
analyses of the broader HOL work are available through reusable Physlib definitions.

### H.6. Later connected extensions

These are intentionally outside the first HOL-equivalence stopping point.

- Fourier optics: apertures, scalar diffraction, propagation kernels, lenses as Fourier
  transformers, and observable intensity.
- General surfaces and vector diffraction beyond planar interfaces.
- Dispersive, conducting, anisotropic, nonlinear, and lossy media.
- Waveguide eigenmodes, radiation continua, and non-power-orthogonal/evanescent modal pairings.
- QuantumInfo-owned finite-mode bosonic lifts, coherent states, photodetection observables, and
  quantum interferometers.

## I. Verification suite

Lean proofs are the primary tests. Numerical comparisons are useful model-validation evidence, but
they do not replace a theorem and must not be presented as kernel verification.

### I.1. Readiness before a system can be “tested”

A photonic example is verification-ready only after it has:

1. a typed physical/component model with parameter-validity conditions;
2. compositional semantics that produces its field, behavior, or network equations;
3. a well-posedness theorem or an explicit characterization of singular parameter values;
4. an observable derived from the solved state rather than inserted as an assumption;
5. a specification stated independently of the implementation formula; and
6. a theorem that the model satisfies that specification.

This distinction prevents a test from comparing a formula with the same formula hidden behind a
definition. For example, the microring transfer function is a test target only after the ring has
been built from couplers and delays and eliminated through N5.

### I.2. Test layers

- **Kernel theorem tests:** symbolic equalities, inequalities, conservation, existence,
  uniqueness, and cross-representation agreement. These are the authoritative verification.
- **API/elaboration tests:** canonical examples use only public declarations, ensuring that the
  abstraction is usable and does not depend on private proof details.
- **Construction tests:** invalid self-wiring, fan-out, direction mismatches, or incompatible mode
  families are rejected by types or by proved well-formedness checks.
- **Exact executable checks:** finite rational/algebraic special cases may be evaluated to catch
  indexing and assembly regressions, with a theorem relating the evaluator to the semantics.
- **Independent numerical cross-checks:** selected frequency sweeps may be compared with a separate
  reference implementation such as SAX after conventions and parameter units are mapped. These
  detect model-entry mistakes but are not proof evidence.
- **Performance regressions:** representative finite networks should elaborate and solve without
  accidental factorial behavior. Mason path enumeration is tested on small graphs; matrix
  elimination remains the scalable default.

Floating-point tolerance, sample range, reference revision, port ordering, and phase convention
must be recorded for every external numerical comparison. No sampled sweep can establish a
universal continuous-frequency property.

### I.3. Required symbolic regressions

| ID | Required regression theorem | What it detects |
|---|---|---|
| P-01 | Jones realization equals each `harmonicWaveX` transverse electric component | phase/cast/index mismatch |
| P-02 | squared Jones intensity equals the sum of squared real electric amplitudes | raw-field normalization mismatch |
| P-03 | pure coherency and Stokes data are invariant under unit-modulus global phase | missing phase hypothesis or incorrect conjugation |
| P-04 | canonical H/V/D/A/R/L states have the documented Stokes vectors | handedness and `S₃` sign errors |
| P-05 | normalized nonzero coherency lies in the Poincare ball, reaches its boundary exactly at rank one, and rank-two/positive-definite data is strictly interior | invalid mixed-state classification |
| P-06 | induced Mueller action agrees with Jones conjugation and composes correctly | basis/factor/conjugation mismatch |
| P-07 | extracting Stokes coordinates after reconstruction returns the original raw Stokes vector | wrong basis order or factor of two |
| P-08 | reconstructed coherency is PSD exactly for vectors in the physical Stokes cone | unsound physical-Stokes inverse |
| C-01 | ideal polarizer is self-adjoint, idempotent, and Jones-intensity nonincreasing | wrong projector/component law |
| C-02 | sequential ideal polarizers on a linear input prove Malus' law | overgeneralized input class or disconnected intensity |
| C-03 | quarter- and half-wave plates produce named canonical states and preserve Jones intensity | axis/retardance convention errors |
| E-01 | interface at normal incidence specializes consistently using a selected tangent frame | hidden `s`/`p` degeneracy or normal-direction errors |
| E-02 | reflection and Snell laws follow from phase matching | assumed rather than derived geometry |
| E-03 | Fresnel boundary equations imply the amplitude formulas | sign and impedance errors |
| E-04 | total internal reflection gives unit reflection modulus and evanescent transmission | branch/critical-angle errors |
| E-05 | lossless propagating interface satisfies normal-flux balance | missing admittance factor |
| E-06 | raw Jones intensity, irradiance, normalized mode power, and Fresnel S coordinates commute through the declared bridges | field/mode normalization conflation |
| E-07 | flux of a finite coherent mode superposition equals modal power under the proved flux-orthonormality hypotheses | missing cross terms or incident/outgoing sign error |
| N-01 | transform-as-behavior composition agrees with matrix cascade | relational orientation errors |
| N-02 | scalar feedback gives `X / (1 - X*Y)` exactly when the denominator is nonzero | misuse of total inverse |
| N-03 | typed lossless interconnection preserves complete external power | duplicated/dropped internal channel |
| N-04 | exposed component and two-component series reduce to the original component/cascade maps | exposure shape or block-assembly errors |
| N-05 | N3 summing/pickoff behaviors and a physically realized nested-feedback network agree with their relational equations | fan-out hidden in wiring or elimination-order errors |
| N-06 | a singular loop fails well-posedness and cannot use the inverse formula | total-inverse leakage |
| N-07 | relabeling/rephasing preserves semantics and relation/matrix solvers agree | index- or convention-dependent behavior |
| N-08 | hierarchical semantics equals flattened-netlist semantics | subsystem-boundary or port-lift errors |
| N-09 | external response is a transform and specializes to scattering only under paired complete ports | false square-port identification |
| N-10 | parameter evaluation commutes with compilation and N5 elimination on the well-posed domain | disconnected frequency-response model |
| N-11 | singular flat-netlist behavior still equals relational component composition | solver accidentally defines semantics |
| S-01 | balanced Mach-Zehnder outputs and power balance | coupler phase convention errors |
| S-02 | microring elimination and convergent round-trip series agree | feedback orientation errors |
| S-03 | microring transfer, power, resonance, and rejection specializations | hidden nondegeneracy assumptions |
| T-01 | Z-transform delay law records ROC and initial conditions | false signal-processing identity |
| T-02 | recurrence, rational transfer function, and network response agree | domain-model mismatch |
| G-01 | Mason gain equals the matrix-inverse transfer for representative graphs | path/loop enumeration errors |
| R-01 | arbitrary valid system transports a ray by the folded component matrix | multiplication-order errors |
| R-02 | cardinal-point formulas satisfy their behavioral specifications | formula-only definitions |
| R-03 | Gaussian beam satisfies the paraxial equation and ABCD law | unconnected beam algebra |
| R-04 | resonator trace criterion implies the fixed-point stability condition | missing determinant/domain assumptions |

For every named physical component, also prove zero/identity limits, parameter-boundary behavior,
and a dimensional or normalization sanity result where the current Physlib unit representation
allows it.

## J. Validation and review gates

### J.1. Per feature branch

- inspect Mathlib and Physlib for existing definitions before adding any declaration;
- keep proofs short and extract mathematically or physically meaningful intermediate lemmas;
- use numbered module sections, docstrings on every definition, and docstrings on important lemmas;
- add the module to `Physlib.lean` in sorted order when a new file is justified;
- run changed files with warnings treated as errors;
- run `git diff --check` and searches for forbidden placeholders;
- update only API-map requirements actually completed by declarations in the branch;
- obtain an independent statement/convention/API review; and
- commit atomically before integration.

### J.2. Per integration milestone

- `lake exe cache get`;
- `lake build`;
- `lake exe lint_all`, recording repository-baseline failures separately from new failures;
- API-map linter with every completed location resolved;
- `./scripts/lint-style.sh` after committing, because it reads committed state;
- import-order, file-import, forbidden-term, spelling, and warnings-as-errors checks;
- clean-checkout rebuild of each proposed upstream branch; and
- a human physics review of conventions, hypotheses, source claims, and interpretation.

### J.3. What a green build does and does not certify

A green build certifies that Lean accepted the formal statements from the imported foundations. It
does not certify that the statement models the intended device, that a phase convention matches the
laboratory convention, that all relevant loss channels were modeled, or that an external reference
was cited accurately. Those checks remain human obligations.

## K. Long-running session protocol

At the start of each goal session:

1. read `goal.md`, `tbd.md`, `Physlib/Optics/API-map.yaml`, `AGENTS.md`, `AI-POLICY.md`, and the
   review guidelines;
2. inspect the integration branch, open worktrees, upstream base, and outstanding agent reviews;
3. select the earliest unblocked work package on a critical path;
4. create a focused feature branch/worktree from the latest appropriate foundation;
5. record any new convention or architecture decision in this file before dependent APIs spread;
6. implement one coherent concept with its required physics-facing lemmas;
7. validate locally and request independent review of statements as well as proofs;
8. commit without modifying unrelated user work, merge into `optics/development`, and push only to
   the user's fork;
9. update the progress ledger and `tbd.md`; and
10. continue to the next unblocked package rather than stopping merely because one commit landed.

If a package is blocked by a missing general theorem, place that theorem in the correct parent API
and keep the Optics import direction clean. If it is blocked by a human convention, license, or
upstream ownership decision, record the exact decision needed and work on an independent package.

## L. Decision gates requiring explicit human confirmation

- [ ] Confirm the phasor time convention, positive-frequency convention, and resulting right/left
  circular and `S₃` sign.
- [ ] Confirm whether the first material-medium API should use current raw real field values or wait
  for a stronger dimensional-units refactor.
- [ ] Confirm the upstream home and intended generality of surface traces and integral Maxwell laws.
- [ ] Confirm whether the initial planar-interface PR may state local boundary laws as named
  hypotheses while their Maxwell-integral derivation is developed in a stacked Electromagnetism PR.
- [ ] Confirm the oriented incident/reflected/transmitted `s`/`p` bases and whether Fresnel `p`
  coefficients scale full electric-vector amplitudes or tangential components.
- [ ] Confirm time-reversal pairing and reference-plane conventions before N2b/N6b reciprocity is
  named; this does not block convention-free N2a/N6a work.
- [ ] Confirm the exact HOL source licenses before adapting any source implementation.
- [ ] Independently verify every bibliography item, URL, page range, and physics claim used in a PR.
- [ ] Conduct all maintainer/reviewer communication and certify every contributed line.

## M. Risk register

| Risk | Consequence | Mitigation |
|---|---|---|
| Phase, handedness, or port convention drifts between files | formulas are individually provable but mutually inconsistent | one convention registry plus canonical-state regressions |
| Raw Jones electric amplitudes are identified with power-normalized modes | missing impedance/profile factors and dimensionally false power claims | distinct types plus E3b irradiance and normalization bridges |
| Individually normalized field modes are assumed orthogonal in flux | coherent superposition power gains missing cross terms | E3b flux pairing plus mutual orthogonality and sign theorems |
| Jones vectors are used for partially polarized light | mathematically excludes intended states | general PSD coherency type and explicit pure embedding |
| Matrix inverse is used at a resonance/singularity | false physical transfer formula | well-posedness first; inverse only under determinant/unique-solution proof |
| Feedback is represented by ordinary matrix multiplication | wrong reflective-network semantics | wrapped scattering matrices and equation-based elimination |
| Incident/output exposure maps are collapsed to one untyped matrix | ill-shaped equations and silent port-identification errors | distinct channel wrappers, `E_in`/`E_out`, and projection/completeness proofs |
| A rectangular external response is called a scattering matrix | unproved identification of input and output ports | retain `ModeTransform U Y` until pairing and completeness specialize it |
| The inverse solver is used as the network's definition | singular but meaningful implicit behaviors disappear | define flat relational semantics before well-posed elimination |
| Unmodeled radiation/loss channels are called lossless | misleading unitary claim | complete-channel hypothesis and Poynting normalization theorem |
| Generic plane waves admit a static background | false transversality/phasor bridge | explicit harmonic or zero-static hypothesis |
| Fresnel coefficients are assumed in a component definition | circular “derivation” | solve boundary equations and separate abstract component from EM realization |
| Transmission power is treated as `normSq t` alone | incorrect oblique-interface balance | prove normal-admittance flux factor |
| Geometric series contraction is treated as necessary | excludes well-posed resonators | distinguish algebraic inversion from convergent round-trip expansion |
| Z-transform delay law ignores startup terms | false recurrence result | causal zero extension, ROC, and initial-condition hypotheses |
| Rationality in delay is confused with rationality in frequency | invalid dispersive model | typed variables and explicit evaluation map |
| Every internal singularity is labeled a transfer-function pole | false poles survive despite input/output cancellation or hidden modes | call them candidate poles until reachability/observability or no-cancellation is proved |
| `s`/`p` coordinates are used at normal incidence without a tangent-frame choice | undefined basis disguised as a canonical formula | require oblique incidence or carry an independently selected tangent frame |
| Signed wavenumber silently changes temporal frequency and circular handedness | inconsistent R/L and `S₃` results | positive carrier frequency with propagation direction represented separately |
| Fresnel `p` amplitudes mix tangential and full-vector conventions | sign and admittance factors disagree across layers | oriented per-wave bases and one explicit coefficient convention |
| A component is only a stored formula with a property label | formula-to-itself proofs provide no behavioral verification | independent behavior specification plus realization theorem |
| Reciprocity conventions block ordinary routing/conservation | unnecessary critical-path stall | isolate N2b/N6b from convention-free N2a/N6a |
| Ray, wave, and Gaussian models are silently identified | abstraction error | bridge theorems or explicit approximation assumptions |
| Mason's scalar formula is applied to matrix-valued gains | invalid reordering of noncommuting products | scalarize to channel nodes before graph extraction |
| Large foundational PRs become unreviewable | upstream rejection and fragile design | single-concept branches and small stacked API maps |
| External formalization license is unclear | provenance risk | independent implementation until human license confirmation |
| Global lint failures obscure regressions | false confidence or wasted debugging | reproduce against exact upstream base and record deltas |

## N. Progress ledger

Status values are `done`, `active`, `ready`, `blocked`, and `future`.
`Ready` means its declared prerequisites are already complete and the package can start from the
current integration base; a designed package whose prerequisite is merely active or ready remains
`blocked` for this ledger.

| Package | Status | Depends on | Completion evidence |
|---|---|---|---|
| O0 roadmap | done | upstream base | Optics API map and scope module |
| O1 mode core | done | Mathlib complex linear algebra | mode branch and integration build |
| O2 modal algebra | active | O1 | converse characterizations complete; parallel/reindex/rephase suite remains |
| P1a Jones foundations | done | complex algebra | scalar realization, raw Jones action, and intensity suite |
| P1b harmonic bridge | done | P1a, existing harmonic wave | named-frame electric/magnetic field reconstruction |
| P2a general coherency | done | Mathlib PSD audit | generic PSD wrapper and conjugation suite |
| P2b pure coherency | done | P1a, P2a | outer-product/rank/trace/phase/conjugation suite |
| P3a neutral Hermitian basis | ready | matrix API audit | coordinate extraction/reconstruction suite |
| P3b Stokes cone | blocked | P2a, P3a | physical-cone equivalence and canonical coordinates |
| P3c Poincare classification | blocked | P2b, P3b | ball/sphere/mixed-state suite |
| P4 deterministic Mueller | blocked | P1a, P2a, P3a, P3b | real induced action and composition suite |
| P5a Jones polarizer/Malus | ready | P1a | projection, intensity contraction, and linear-input Malus suite |
| P5b physical Malus bridge | blocked | P5a, E3b | irradiance and normalized-power Malus corollaries |
| P6a retarder core | ready | P1a | unitary Jones action and canonical-state suite |
| P6b polarization chain | blocked | P1b, P2b, P3b, P4, P5a/P5b, P6a, E3b | cross-representation connected example |
| E1 media/macroscopic Maxwell | ready | Electromagnetism/FreeSpace review | medium API, field predicate, and vacuum bridge |
| E2 material plane waves | blocked | E1 | real Maxwell field and Optics phasor theorems |
| E3a Poynting | blocked | E1 for material conservation | real vacuum/material energy and flux suite |
| E3b Optics normalization | blocked | O1, P1a, E2, E3a | harmonic flux, irradiance, and modal-power bridges |
| E4 boundary laws | blocked | E1, surface/integral design decision | Maxwell-to-local-boundary theorem |
| E5 reflection/Snell/TIR | blocked | E2, E4 | phase-matching geometry suite |
| E6 Fresnel/flux | blocked | E3b, E5 | amplitude, admittance-normalized scattering, and flux suite |
| N1 modal completion | active | O1 | remaining O2 parallel/reindex/rephase suite |
| N2a ports/routing | blocked | O2 reindex/direct-sum support | typed convention-free connection API |
| N2b reciprocity metadata | blocked | human convention decision | time-reversal/reference-plane API |
| N3 behaviors | ready | O1 | relational composition, rectangular fan-out, and graph equivalence |
| N4 network equations | blocked | N1/O2, N2a, N3 | flat relational semantics and shaped matrix equations |
| N5 elimination | blocked | N4 | unique-solvability/inverse/external-map suite |
| N5F parameterized compilation | blocked | N5, N7 parameterized components | pointwise response-domain theorem suite |
| N5H hierarchy/flattening | blocked | N4, N5 | hierarchy-to-flat semantic equality |
| N6a conservation | blocked | N2a, N5; E3b for physical meaning | passive/lossless composition closure suite |
| N6b reciprocity | blocked | N2b, N6a | convention-aware reciprocity closure suite |
| N7 components | blocked | N2a, O2; E6 only for interface specialization | specification, realization, passivity, and losslessness suite |
| S1 Mach-Zehnder | blocked | N5, N6a, N7 | transfer and power suite |
| S2/S3 microrings | blocked | N5, N5F, N6a, N7 | pointwise response and observable suite |
| S4 delay transfer | blocked | N5F, N7 | rational-delay evaluation and pole-domain suite |
| S5 Z-transform | ready | Mathlib analysis audit | recurrence/ROC suite |
| S6 Mason | blocked | N5, finite graph audit | combinatorial/matrix equivalence |
| S7 HOL integrated parity | blocked | N5H, S1--S6 | case-study index |
| R1--R5 ray/beam parity | future | E1/E5 plus focused ray API map | ray, imaging, ABCD, resonator suite |
| Fourier/quantum extensions | future | relevant classical layers | separate API maps and bridges |

## O. Overall completion checklist

The long-running goal is complete only when:

- [ ] the polarization milestone P1a--P6b, including every lettered subpackage, is complete;
- [ ] the electromagnetic-interface milestone E1--E6, including E3a/E3b, is complete;
- [ ] the typed finite-network milestone N1--N7, including N2a/N2b, N5F/N5H, and N6a/N6b, is
  complete;
- [ ] the integrated-photonics milestone S1--S7 reproduces the target HOL capability classes;
- [ ] the ray/beam milestone R1--R5 reproduces the target geometrical/quasi-optics capability
  classes;
- [ ] the cross-layer regression suite in section I passes from shared public definitions;
- [ ] every completed public requirement is accurately reflected in focused API maps;
- [ ] all builds and linters pass except independently reproduced and documented upstream-baseline
  failures;
- [ ] external-source licenses and bibliography are independently verified by the human author;
- [ ] the human author has reviewed and can explain every definition, theorem statement, proof, and
  physical convention; and
- [ ] upstream work has been split into reviewable single-concept PRs and discussed by the human
  author with maintainers.

## P. Research inputs to verify before upstream use

- U. Siddique, O. Hasan, and S. Tahar, [*Formal Modeling and Verification of Integrated Photonic
  Systems*](https://hvg.ece.concordia.ca/Publications/Conferences/SysCon-15.pdf), IEEE SysCon 2015.
- U. Siddique, S. M. Beillahi, and S. Tahar, [*On the Formal Analysis of Photonic Signal Processing
  Systems*](https://doi.org/10.1007/978-3-319-19458-5_11), FMICS 2015.
- S. Khan-Afshar et al., [*Formal Analysis of Optical Systems*](https://arxiv.org/abs/1403.3039),
  2014.
- M. U. Siddique, [*Formal Analysis of Geometrical Optics using Theorem
  Proving*](https://spectrum.library.concordia.ca/id/eprint/980766/1/SIDDIQUE_PhD_S2016.pdf), PhD
  thesis.
- [SAX](https://github.com/gdsfactory/sax), an Apache-2.0 frequency-domain S-parameter circuit
  simulator, as a modern netlist and component-model architecture reference; record an exact
  revision before adapting a specific implementation idea.
- J. Tooby-Smith, [*A Perspective on Interactive Theorem Provers in
  Physics*](https://pmc.ncbi.nlm.nih.gov/articles/PMC13322628/), for the broader formal-physics and
  sparse formal-optics literature context.
- The Physlib Zulip archive discussions on Optics, Maxwell equations, and vector calculus listed in
  `Physlib/Optics/API-map.yaml`.
- A standard optics reference selected and page-checked by the human author for polarization,
  Fresnel flux, resonators, and Gaussian beams.

These sources justify the capability selection and expose useful hidden assumptions. They do not
authorize copying external proof scripts, and all bibliographic and technical claims require the
human verification recorded in `tbd.md`.

## Q. Immediate queue for the next goal session

1. P1a, P1b, P2a, and P2b are complete, independently reviewed, validated, and integrated.
   Preserve their type boundary: raw Jones intensity is still neither irradiance nor modal power,
   the harmonic bridge reconstructs fields rather than a gauge potential, general coherency still
   carries no Jones-purity assumption, and zero Jones data has no polarization direction.
2. The O2 predicate characterizations are complete. Finish its direct-sum/parallel,
   reindexing, and rephasing suite before starting N2a typed ports/routing.
3. Audit and develop P3a's neutral Hermitian basis, then use it with P2a and P2b for the physical
   Stokes cone and Poincare classification without identifying mixed states with Jones vectors.
4. Start E1's medium and macroscopic-Maxwell layer independently so the new harmonic bridge can
   later acquire Poynting-flux normalization and meet the material-interface track.
5. P5a polarizers/Malus and P6a retarders are also unblocked, but keep them as separate component
   PR concepts and do not translate Jones intensity into physical power before E3b.
6. Audit E1 against the existing electromagnetic constant structures and prepare a focused
   medium API proposal. Do not merge E1 until its dimensional and ownership choices receive human
   confirmation.

The first session should not jump directly to a polarizer, microring formula, or Fresnel
coefficient. Those would be easy isolated calculations but would evade the dependency structure
this goal is intended to establish.
