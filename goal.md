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

### B.4. Separate parity claims

The project has three independently auditable completion claims. None implies either of the
others.

1. **Physical Optics v0.1 parity:** the connected electromagnetic, polarization, interface, and
   observable slice in section A.1.
2. **Integrated-photonics parity:** the component, chain, network, recurrence, Z-transform,
   signal-flow, microring, cascade, and lattice capabilities in sections H.3 and H.4.
3. **Extended HOL optical-suite parity:** the geometrical-, Gaussian-, and resonator-optics work in
   section H.5 and any later named case studies explicitly added to its parity ledger.

Integrated-photonics parity does not wait for the stronger Maxwell-to-boundary derivation in E4b;
physical v0.1 does. Conversely, a completed physical v0.1 does not establish the transfer-system,
Z-transform, or signal-flow capabilities of the integrated-photonics sources.

### B.5. Source-to-Lean parity ledger

Before any parity claim is made, `tbd.md` must point to a human-verified ledger whose mandatory rows
record:

- the primary source, definition or theorem number, and page;
- the target public Lean declaration and import path;
- the source and target port ordering, propagation direction, phase, attenuation, `z`/`q`, and dB
  conventions;
- every source hypothesis retained, strengthened, corrected, or deliberately rejected;
- the proof status and exact symbolic regression ID; and
- whether the result is a source-parity requirement, a stronger Physlib theorem, or contextual
  evidence only.

Parity means that every mandatory ledger row is proved through the named public APIs. Broad topic
coverage, a formula stored in a definition, or a numerical plot is not parity evidence.

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
- Dimension-generic complex-wavevector geometry, its complex-bilinear pairing needed by later
  dispersion laws, and phase/attenuation decay belong in
  `Physlib/ClassicalMechanics/WaveEquation`.
- Real electromagnetic fields remain foundational. Optics adds fixed-frequency reduced
  representations and proves how they reconstruct the real fields; it does not introduce a second
  competing Maxwell theory.
- Electromagnetism may use complex coefficients as calculation data when it constructs and proves
  laws about real fields, but it does not introduce competing phasor, Jones, coherency, or modal
  normalization state APIs.
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
- [x] Binary direct sums concatenate and recover disjoint mode-amplitude families, add their modal
  powers, act block-diagonally on transforms, and preserve power preservation, passivity, and
  scattering losslessness under independent parallel composition.
- [x] Equivalence-based relabeling and unit-complex coordinate rephasing act isometrically on mode
  amplitudes and covariantly on transforms and scattering matrices; preserve and reflect modal
  predicates; and commute with cascade and independent parallel composition. The rephasing API is
  explicitly a coordinate change, not a physical phase-shifting component or a reciprocity law.
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
- [x] Relativity-independent Pauli matrices and the real basis of self-adjoint `2 × 2` complex matrices
  live under Mathematics, with half-trace coefficients, a bundled real-linear equivalence,
  reconstruction and scalar-vector identities, and compatibility imports for the former
  Relativity API.
- [x] The neutral Pauli layer characterizes the positive-semidefinite cone by
  `pauliRadius A ≤ scalarCoeff A`, with determinant, Hermiticity, and zero-radius support lemmas and
  no eigenvalue-ordering assumption.
- [x] Raw Stokes coordinates are a real-linear reordering and doubling of the neutral Pauli
  coordinates; reconstruction, intensity, polarization norm, determinant, physical-cone, and
  coherency-equivalence laws are proved with the provisional third-coordinate sign but without
  assigning circular-polarization names.
- [x] Jones-derived Stokes data is defined through pure coherency, with arbitrary complex-scaling
  covariance, unit-phase invariance, all four component formulas, and normalized full-vector
  checks for the H/V/D/A and positive/negative-`I` quadrature coordinate states.
- [x] Unit-intensity physical Stokes data and unit-trace polarization coherency are each equivalent
  to the closed Poincare ball; its sphere is exactly the rank-one/determinant-zero boundary and its
  open interior is exactly the rank-two/positive-definite class. This cross-section excludes zero
  coherency without assigning it a polarization direction, while the unnormalized classification
  treats the zero-intensity cone apex separately.
- [x] Unit-intensity Jones vectors carry the actual `Circle` scaling action, and their orbit
  quotient is algebraically equivalent to the Poincare sphere through the existing
  Jones--coherency--Stokes chain. Exact phase fibers, rank-one coherency factorization, and the six
  canonical axes are proved without making a topological or physical-power claim.
- [x] Rectangular congruence on self-adjoint complex matrices is a neutral real-linear
  construction shared by Optics and the existing Relativity compatibility API. Jones matrices
  induce wrapped real Mueller matrices through that construction, with proved Jones/coherency/
  Stokes commuting squares, the audited Pauli trace formula, physical-cone preservation,
  identity/cascade/scalar laws, algebraic-unitary consequences, and sign-sensitive regressions.
- [x] Normalized linear Jones axes use `Real.Angle`; ideal linear polarizers are rank-one star
  projections with half-turn invariance, axis transmission, orthogonal extinction, exact
  squared-Jones-intensity contraction, coherent and intensity forms of Malus' law, canonical
  matrix regressions, coherency transport, and an exact Jones-induced arbitrary-Stokes action.
- [x] Ideal linear retarders use a reference-principal-axis spectral decomposition and the
  convention-locked relative phase `exp (-I * retardance)`; they have exact entry, determinant,
  composition, inverse, unitarity, eigenaxis, linear-input, and raw-intensity laws. Positive and
  negative quarter-wave plates and half-wave plates have canonical matrix and state regressions,
  including a normalized equal-amplitude relative-phase family whose zero-axis phase transforms
  by `relativePhase - retardance`, without circular-handedness or physical-power claims.
- [x] Retarder actions have exact pure-coherency and arbitrary raw-Stokes/Mueller descriptions,
  and ordered Jones composition now connects a linear polarizer followed by a retarder through
  exact Jones, pure-coherency, and induced Mueller results with a quarter-wave sign regression.
- [x] The existing pointwise, potential-derived three-dimensional Maxwell laws with free-space
  constants and allowed sources are available through ordinary imports, with their declarations
  and proofs unchanged and their scope recorded.
- [x] Homogeneous isotropic material data now separates the semantic `E`, `D`, `B`, and `H` roles;
  provides positive real permittivity and permeability, linear constitutive maps, wave speed,
  impedance, explicitly relative refractive indices, and their algebra; and embeds `FreeSpace`
  one way without promoting the legacy unconstrained `EMSystem`.
- [x] A differentiability-aware macroscopic Maxwell predicate now keeps free sources explicit and
  bound response inside `D` and `H`; supplies source-free and linear-superposition APIs; connects
  the field equations to a fixed medium's constitutive equations; and derives the canonical
  free-space instance one way from the existing potential-derived laws.
- [x] Direction-indexed oriented polarization frames now embed Jones data as complex spatial
  electric phasors, recover exact real quadratures and transverse fields, and construct
  positive-branch homogeneous-material plane waves with exact `E`/`B`/`H`, coherent phase-shift,
  and complete source-free Maxwell results. A fixed-vacuum regression proves full electric-field
  and magnetic-induction agreement with the existing potential-derived `harmonicWaveX`
  construction.
- [x] Non-normal incidence now selects the proof-bearing Jones order `(s, p)` with
  `s = normalize (n × k)` and `p = k × s`; a generic one-axis constructor keeps the tangent
  choice explicit at normal incidence. Exact coordinate regressions pin both the non-normal axes
  and the normal-incidence reversal of the derived `p` axis without assigning incoming/outgoing,
  Fresnel, irradiance, or power semantics.
- [x] WaveEquation now supplies dimension-generic complex wave vectors, their real
  phase/attenuation decomposition, the non-Hermitian complex-bilinear pairing needed by later
  dispersion laws, exact spatial-factor phase and decay laws, and proof-bearing positive-normal
  exponential decay. A
  coordinate regression pins `K = (waveNumber, 0, -I * decayRate)` without assigning an interface,
  square-root branch, transmitted/outgoing role, Maxwell solution, evanescent-wave role, or power.
- [x] Electromagnetism now supplies an off-shell complex-amplitude plane-wave carrier with
  independent positive real frequency, complex wave vector, and complex electric amplitude;
  complex-bilinear cross-product algebra; ordinary real `E`/`D`/`B`/`H` realizations through one
  shared spine; the Faraday-compatible candidate `B0 = omega^-1 (K x E0)`; separate electric
  transversality; structural magnetic transversality; exact positive-normal carrier and field
  decay; and constitutive satisfaction. It deliberately makes no dispersion, Maxwell, interface,
  outgoing, evanescent-role, irradiance, power, potential, or gauge claim.
- [x] Every existing real-quadrature `MonochromaticPlaneWave` now embeds exactly into that carrier:
  wave vector, frequency, complex electric amplitude, its exact nonzero-quadrature guard, carrier,
  transversality, magnetic amplitude, and all four ordinary real fields agree, without introducing
  a second hidden electromagnetic state or claiming equality of potentials, gauges, or power
  normalizations.
- [x] The complex carrier now has a separate calculus layer proving joint smoothness of the carrier
  and all ordinary real fields, exact temporal and coordinate carrier factors, and generic
  ordinary-real-field time and coordinate derivatives, divergence expressed through the
  complex-bilinear pairing, and curl identities through the shared realization spine. These
  results remain off shell and make no claim about Maxwell equations, interface roles,
  evanescent-wave roles, or power.
- [x] The complex carrier now has a separate algebraic material-dispersion layer defining the
  bilinear shell `K dot K = epsilon * mu * omega ^ 2`; decomposing it exactly into phase--attenuation
  orthogonality and the signed squared-norm law; proving the matched wave vector is nonzero and the
  exact transverse `K cross (K cross E0)` and `K cross B0` identities; and recovering the existing
  positive real branch exactly. It selects no square-root, propagation, or interface role.
- [x] The complex carrier now has a forward ordinary-real-field Maxwell layer with named exact
  `E`/`D`/`B`/`H` differential identities, structural magnetic Gauss and Faraday laws, electric
  Gauss under bilinear transversality, Ampere--Maxwell under transversality and the bilinear shell,
  and differentiability-aware source-free and fixed-medium endpoints. It permits zero electric
  amplitude and therefore makes no converse or characterization claim.
- [x] The complex carrier now has an honest converse layer. Two time samples recover complex
  amplitude equations from ordinary real fields; Gauss--electric forces bilinear transversality;
  Ampere--Maxwell forces the material shell when the electric amplitude is nonzero; the zero
  amplitude is proved to solve Maxwell off shell; and the nonzero family has an exact
  transversality-and-dispersion characterization. No propagation, interface, or power role follows.
- [x] Exact attenuating TE/TM data now regresses the complex-bilinear material shell independently
  of the forward theorem: `K = (5, 0, -4 I)` has bilinear square `9` but Hermitian squared norm
  `41`; the TM amplitude is bilinearly transverse but has Hermitian pairing `40`; and both exact
  magnetic amplitudes satisfy the signed `K cross B0 = -9 E0` relation by coordinate calculation.
- [x] Exact ordinary-real-field Maxwell regressions now realize that TE/TM data, verify both
  source-free endpoints and guarded characterizations, pin the TM quadrature sign at two phases,
  and falsify unguarded dispersion, one-phase amplitude recovery, Hermitian transversality, and
  three-laws-imply-four reasoning with zero-amplitude and complex-null fixtures. A concrete real
  embedding separately checks real/complex guarded-converse coherence on the embedded image.
- [x] `tbd.md` records the human, source-license, upstream-design, and validation gates.

### D.2. Relevant upstream foundations

- `Electromagnetism.Vacuum.HarmonicWave` supplies an explicit real harmonic Maxwell solution in
  free space. In three spatial dimensions its two transverse electric components are
  `E₀ i * cos (k * c * t - k * x₀ + φ i)` when `k ≠ 0`.
- `Electromagnetism.Vacuum.IsPlaneWave` supplies the existing real plane-wave predicate.
- `Electromagnetism.ThreeDimension.MaxwellEquations` contains pointwise differential Maxwell
  equations for potential-derived fields with free-space constants and allowed sources. E0 exposes
  those declarations through the public module surface; it does not supply material constitutive
  laws, integral laws, or boundary conditions.
- `Electromagnetism.Media.HomogeneousIsotropic` supplies E1a's narrow material constants,
  constitutive relations, wave parameters, and one-way `FreeSpace` specialization. Its raw-real
  fixed-unit convention and definitionally equal field-role abbreviations are explicit limitations.
- `Electromagnetism.ThreeDimension.MacroscopicMaxwellEquations` supplies E1b's unbundled four-field
  equations, joint differentiability hypotheses, named laws, superposition, source-free
  specialization, and fixed-medium connector.
- `Electromagnetism.ThreeDimension.MacroscopicMaxwellBridge` derives the canonical free-space
  macroscopic solution from E0's smooth potential-derived equations without claiming a converse.
- `Electromagnetism.ThreeDimension.MonochromaticPlaneWave.Basic` supplies E2a's medium-independent,
  off-shell real harmonic carrier with independent positive frequency and wave number, compatible
  `E` and `B` candidates, medium-supplied `D` and `H`, separate transversality, regularity, wave
  equations at phase velocity, and constitutive satisfaction without assuming Maxwell dispersion.
- `Electromagnetism.ThreeDimension.MonochromaticPlaneWave.Dispersion` supplies E2b's positive
  material branch, fixed-angular-frequency constructor, squared-dispersion equivalence, and exact
  on-shell `B/E` and `H/E` impedance relations.
- `Electromagnetism.ThreeDimension.MonochromaticPlaneWave.Maxwell` supplies exact differential
  field identities, the four individual source-free laws with their honest hypotheses, and the
  canonical homogeneous-medium solution.
- `Electromagnetism.ThreeDimension.MonochromaticPlaneWave.Converse` proves that Maxwell forces
  transversality and, under the necessary nonzero-electric-amplitude condition, positive-branch
  dispersion; it also gives the resulting nonzero-carrier characterization.
- `ClassicalMechanics.WaveEquation` supplies real plane waves and harmonic-wave infrastructure;
  `ClassicalMechanics.WaveEquation.ComplexWaveVector` supplies the generic complex-vector,
  bilinear-pairing, spatial-factor, and positive-normal decay foundation needed by the remaining
  E2 work.
- `Electromagnetism.ThreeDimension.MonochromaticPlaneWave.ComplexBasic` supplies the off-shell
  complex carrier, complex vector algebra, shared ordinary-real-field realization, compatible
  magnetic candidate, bilinear transversality, decay, and constitutive API.
- `Electromagnetism.ThreeDimension.MonochromaticPlaneWave.ComplexBridge` proves exact compatibility
  with the existing real-quadrature plane-wave carrier, nonzero-amplitude guard, transversality
  predicate, magnetic amplitude, and ordinary real `E`/`D`/`B`/`H` fields.
- `Electromagnetism.ThreeDimension.MonochromaticPlaneWave.ComplexCalculus` supplies joint
  regularity, exact `partial_t C = I omega C` and `partial_j C = -I K_j C` carrier laws, and the
  generic ordinary-real-field time, coordinate, divergence, and curl identities required by the
  remaining Maxwell layer.
- `Electromagnetism.ThreeDimension.MonochromaticPlaneWave.ComplexDispersion` supplies the
  complex-bilinear material shell, its exact phase--attenuation decomposition, nonzero-wave-vector
  and transverse on-shell algebra, the guarded converse from the magnetic-amplitude relation, and
  exact agreement with the existing real positive branch.
- `Electromagnetism.ThreeDimension.MonochromaticPlaneWave.ComplexDispersionRegression` supplies
  exact TE/TM decay data separating the bilinear square and transversality pairing from their
  Hermitian counterparts and directly checks both magnetic amplitudes and signed cross relations.
- `Electromagnetism.ThreeDimension.MonochromaticPlaneWave.ComplexMaxwell` specializes the shared
  calculus to the named ordinary real electromagnetic fields, proves the four source-free laws
  under their stated sufficient forward hypotheses, and supplies the canonical fixed-medium solution.
- `Electromagnetism.ThreeDimension.MonochromaticPlaneWave.ComplexConverse` uses exact zero and
  quarter-period carrier samples to prove that ordinary-real-field Maxwell satisfaction forces
  bilinear transversality and, for nonzero electric amplitude, material dispersion; it also proves
  the zero-amplitude degeneracy and the guarded characterization.
- `Electromagnetism.ThreeDimension.MonochromaticPlaneWave.ComplexMaxwellRegression` supplies the
  exact TE/TM ordinary real fields and Maxwell endpoints, the zero-amplitude, one-phase, and
  complex-null falsification fixtures, and a concrete embedded-real coherence check.
- `ClassicalMechanics.WaveEquation.VectorCalculus` and `SpaceAndTime.Space.CrossProduct` now supply
  the dimension-generic plane-wave divergence, three-dimensional plane-wave curl, Euclidean
  cross-product bilinearity, vector triple-product identities, and the inner product of two cross
  products needed by E2's Maxwell and incidence-frame proofs.
- `SpaceAndTime.Space` supplies Euclidean geometry, derivatives, volume integration, and cross
  products, but not yet the complete oriented-surface and trace API needed for generic interface
  derivations.
- Mathlib supplies complex Euclidean spaces, adjoints, positive-semidefinite matrices, matrix
  inversion under determinant hypotheses, Schur complements, power/Laurent series, rational
  functions, and finite graph infrastructure. Exact reuse should be audited per work package.

### D.3. Not yet present

- [ ] Maxwell-qualified evanescent and outgoing semantics for the constructed interface-oriented
  side-decaying carrier branch;
- [ ] the physical Malus power bridge and the polarization chain's field/irradiance continuation;
- [ ] Poynting flux, boundary laws, Snell, Fresnel, and total internal reflection;
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
  P2a --> P2b pure coherency, P3b-1 Stokes/coherency cone
  P3a --> P3b-0 neutral positive cone --> P3b-1 Stokes/coherency cone
  P2b + P3b-1 --> P3b-2 Jones--Stokes bridge
  P3b-1 + P3b-2 --> P3c Poincare classification
  P1a + P2a + P3a + P3b-1 --> P4 deterministic Mueller
  P5a + E3b --> P5b physical Malus bridge
  P2b + P3b-2/P4 + P6a --> P6b-1 reduced retarder representations
  P5a + P6b-1 --> P6b-2 connected reduced polarizer--retarder example
  P1b + P5b + P6b-2 + E3b --> P6b-3 physical polarization observables

electromagnetic v0.1
  E0 public Maxwell API --> E1 media/macroscopic Maxwell
  complex-wavevector geometry --> E2 complex carrier --> E2 exact real-wave bridge
  E2 complex carrier --> E2 complex calculus
  E2 complex carrier + E2 exact real-wave bridge --> E2 complex dispersion
  E2 complex calculus + E2 complex dispersion --> E2 complex Maxwell --> E2 complex converse
  E1 + E3s Space identity --> E3a real energy/Poynting
  E1 --> E2 material waves, E4a local boundary semantics
  O1 + P1a + E2 + E3a --> E3b harmonic-flux and mode-normalization bridge
  E2 + E4a primitive independent-frequency traces --> E5a conservation/fixed-frequency reduction
  E5a --> E5b reflection/Snell/TIR
  oriented surfaces/integral Maxwell + E4a --> E4b derived boundary laws
  E3b + E5b --> E6 Fresnel amplitudes/flux
  P1b + P2b + P3b-2/P4 + P5b/P6b + E3b/E4b/E6 --> Optics v0.1

finite networks and integrated photonics
  O1 mode core --> O2/N1 modal completion --> N2a ports/routing
  O1 mode core --> N3 relational behaviors
  N3 --> N3T two-port chain semantics
  O2/N1 + N2a + N3 --> N4 flat relational semantics --> N4C certified compiler
  N4 + N4C --> N5 well-posed elimination
  N4 --> relational N5H flattening; N5 --> functional N5H subsystem packaging
  N2a + O2/N1 --> N7 behavior-specified components
  N5 + N7 --> N5F parameterized response domains
  N2a + N5 --> N6a conservation
  N2b reciprocity metadata + N6a --> N6b reciprocity
  P2a + N5 + N6a --> N6c coherent/incoherent network observables
  N3T + N5/N5F + N6a + N7 --> S0--S4 systems
  Mathlib analysis --> S5 Z-transform
  N5 + finite graph API --> S6 Mason
  N5H + S0--S6 --> S7 HOL case suite and cross-semantics oracle

ray and beam foundations
  E1/E5b --> R1 physical/paraxial rays --> R2 systems --> R3 imaging --> R4 Gaussian beams
  R4 --> R5 resonators
```

P1a, P2a, P3a, O2/N1, N3, E1, and the mathematical audit for S5 are independent starting fronts.
P2a/P3a do not wait for P1b; P5a/P6a core Jones calculations do not wait for Stokes. P6b-1 likewise
does not wait for the electromagnetic normalization bridge, while P6b-3 does. E0--E6 is the deepest
physical prerequisite chain and must not be bypassed by assuming Fresnel coefficients. R1--R5 is a
later foundational track; it should reuse E-track medium and interface data where that does not
force a false equivalence between exact wave optics and the paraxial approximation.

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

The interface stack has two levels. Its primitive time-domain boundary problem gives the incident,
reflected, and transmitted candidates independent positive frequencies and wave vectors, assembles
the incident-plus-reflected and transmitted ordinary real fields on their respective half-spaces,
and compares traces for every boundary point and time. Harmonic-uniqueness and noncancellation
lemmas, with explicit nonzero hypotheses, must then derive frequency conservation and tangential
wave-vector conservation; neither fact may be stored in the premise of the theorem meant to prove
it. Only after those results may a reduced fixed-frequency boundary problem expose complex
amplitude equations for Snell and Fresnel calculations. The reduction theorem must state exactly
which non-null and phase-matching hypotheses make it equivalent to the primitive problem.

At either level, `s` and `p` require oblique incidence or an independently selected tangential
frame at normal incidence. Total internal reflection requires a complex wavevector and a chosen
outgoing/decaying square-root branch; an evanescent field is not an ordinary positive-power
propagating mode. Converting Fresnel field amplitudes to a multiport scattering matrix uses
square-root normal-admittance factors. Its ordinary power-unitarity theorem is restricted to the
regime where every retained propagating channel has strictly positive normal admittance.
Grazing/critical channels have singular normalization, and a TIR evanescent transmitted field is
not placed in that ordinary positive-power port set; those regimes use a reduced
propagating-channel set or a later generalized flux pairing.

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

#### O2. Complete the modal algebra — complete

- [x] characterize power preservation by `Tᴴ * T = I`;
- [x] characterize passivity by a positive-semidefinite defect matrix;
- [x] specialize square power preservation to unitarity;
- [x] add binary direct-sum/parallel composition and preservation lemmas; and
- [x] add reindexing/rephasing invariance before reciprocity.

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

#### P3a. Neutral Hermitian/Pauli coordinates — complete

Candidate location: an existing neutral matrix module, or a new neutral mathematical module only
if the audit proves one is necessary.

Deliverables:

- the Hermitian `2 x 2` basis, half-trace coordinate extraction, and reconstruction theorem;
- reality, linearity, and basis-orthogonality lemmas; and
- extraction of reusable algebra from a physics namespace rather than introducing an
  Optics-to-Relativity dependency, with the neutral module itself importing no Relativity file and
  the existing Relativity Pauli API re-exporting or delegating to it so current downstream imports
  and public names are preserved.

Completion evidence: `Physlib.Mathematics.PauliMatrices.Basic` and `.SelfAdjoint` own the neutral
matrix algebra and bundled real-linear coefficient equivalence; the former Relativity paths remain
public compatibility/extension modules, and a full downstream build preserves every pre-existing
declaration name.

#### P3b-0. Neutral positive Pauli cone — complete

Owner: Mathematics.

- Hermiticity of the Pauli-vector part;
- `det A = scalarCoeff A ^ 2 - pauliRadius A ^ 2`; and
- positive semidefiniteness exactly when `pauliRadius A ≤ scalarCoeff A`.

The proof must not assume an eigenvalue ordering. A robust construction derives the forward
inequality from trace and determinant nonnegativity and proves the converse from the Hermitian
square of `pauliRadius A * I + vectorPart A`, handling zero radius separately.

Exit: Optics can obtain the physical Stokes cone from reusable matrix mathematics rather than
placing a general positivity theorem in a polarization namespace.

Completion evidence: `Physlib.Mathematics.PauliMatrices.SelfAdjoint` proves Hermiticity of the
Pauli-vector part, the determinant/radius identity, the zero-radius vanishing lemma, positivity of
`pauliRadius A • 1 + vectorPart A`, and the exact positive-semidefinite cone criterion. The proof
uses trace and determinant nonnegativity in one direction and an explicit PSD decomposition in the
other, with the zero-radius case separated before inverse scaling.

#### P3b-1. Stokes coordinates and coherency cone — complete

Candidate location: `Physlib/Optics/Polarization/Stokes.lean`.

Deliverables:

- `StokesIndex := Fin 1 ⊕ Fin 3` and `StokesVector := EuclideanSpace ℝ StokesIndex`;
- an explicit signed/reordered real-linear equivalence from P3a coordinates, with the provisional
  Pauli-positive order `S₀ ↦ σ₀`, `S₁ ↦ σ₃`, `S₂ ↦ σ₁`, `S₃ ↦ σ₂`;
- the reconstruction
  `C(S) = 1/2 * (S₀ σ₀ + S₁ σ₃ + S₂ σ₁ + S₃ σ₂)`, or the version with the last sign negated if
  the human convention gate selects the opposite optical `S₃` convention;
- explicit intensity and three-dimensional polarization projection;
- `IsPhysical S := ‖S.polarization‖ ≤ S.intensity`, with nonnegative intensity proved rather than
  stored redundantly;
- positive semidefiniteness of the reconstructed self-adjoint matrix exactly for physical Stokes
  vectors; and
- a plain equivalence between `PolarizationCoherency` and the physical-Stokes subtype.

Every raw real Stokes vector reconstructs a self-adjoint matrix. Only a physical Stokes vector may
reconstruct a `PolarizationCoherency`; the physical cone is not a vector subspace and must not be
given a linear-equivalence or module API.

Completion evidence: `Physlib.Optics.Polarization.Stokes` supplies the explicit real-linear
Pauli/Stokes coordinate equivalence, all four basis-order/factor regressions, raw reconstruction and
round trips, the entrywise reconstruction matrix, intensity and polarization observables, the
determinant identity, the exact PSD/physical-cone criterion, and an ordinary equivalence between
`PolarizationCoherency` and `PhysicalStokesVector`. The algebraic convention is
`S₀ = 2c₀`, `S₁ = 2c₃`, `S₂ = 2c₁`, and `S₃ = 2c₂`; right/left circular naming remains withheld.

#### P3b-2. Jones--Stokes bridge — complete

Candidate location: `Physlib/Optics/Polarization/JonesStokes.lean`.

- define Jones-derived Stokes data through the already-proved pure coherency embedding;
- prove Stokes intensity equals Jones intensity;
- prove invariance under unit-modulus scaling and phase shift; and
- prove all four explicit Jones-component formulas, which are the mandatory order, factor,
  conjugation, and sign regressions.

For the provisional Pauli-positive `S₃`, the component formulas are
`S₀ = |E₀|² + |E₁|²`, `S₁ = |E₀|² - |E₁|²`,
`S₂ = 2 re (E₀ conj E₁)`, and `S₃ = -2 im (E₀ conj E₁)`.
Do not name right/left circular states until the observer and handedness convention is source-checked
by the human author.

Completion evidence: `Physlib.Optics.Polarization.JonesStokes` defines `JonesVector.stokes` only
through the P2b outer-product coherency and the P3b-1 coherency/Stokes equivalence. It proves
physicality, equality of Jones and Stokes intensity, covariance by `Complex.normSq z` under an
arbitrary common complex scale, invariance under unit-modulus scale and common phase, the exact
four component formulas above, and the cross-coherence reconstruction identity. Normalized
coordinate states in `Polarization.Basic` use equal amplitudes `sqrt 2 / 2`; full-vector checks give
H/V as `(1, ±1, 0, 0)`, D/A as `(1, 0, ±1, 0)`, and positive/negative-`I` quadrature as
`(1, 0, 0, ±1)`. The API deliberately assigns no right/left circular name.

#### P3c. Poincare classification — complete

Candidate locations: `Physlib/Optics/Polarization/Poincare.lean` and
`Physlib/Optics/Polarization/JonesPoincare.lean`.

Deliverables:

- the closed-Poincare-ball theorem for normalized nonzero physical coherency;
- sphere equality for rank-one states and a strict interior theorem for a precisely stated mixed
  class such as rank two or positive definite;
- canonical horizontal, vertical, diagonal, antidiagonal, and positive/negative-`I` quadrature
  cases, with right/left circular aliases deferred until the human convention check;
- explicit handling of the zero-intensity case; and
- the pure-state correspondence stated for unit-intensity Jones vectors modulo the `U(1)` action,
  not for arbitrary nonzero Jones vectors modulo phase alone.

Exit: normalized physical coherency matrices correspond to the closed ball and pure unit-intensity
Jones states modulo unit phase correspond to the sphere.

Completion evidence: `Physlib.Optics.Polarization.Poincare` defines the closed ball and proves exact
equivalences from unit-intensity physical Stokes data and unit-trace coherency data to it. The ball
center is therefore the unit-trace unpolarized state, not zero coherency. The same file proves that
the sphere is equivalent to determinant zero and rank one, that the open interior is equivalent to
positive definiteness and rank two, and that the unnormalized cone apex has trace and rank zero.
`Physlib.Optics.Polarization.JonesPoincare` defines the actual `Circle` action on unit Jones
vectors, proves exact coherency and sphere fibers, constructs a representative of every sphere
point, factors every unit-trace rank-one coherency through a unit Jones vector, and identifies the
orbit quotient algebraically with the sphere. Its H/V/D/A and positive/negative-`I` regressions fix
all three coordinate signs. It intentionally makes no topological equivalence or physical-power
claim.

Jones matrices induce deterministic coherency and Mueller maps but do not describe depolarizers.
A later general depolarizing layer needs positive, and where physically appropriate completely
positive, maps on coherency data; it must not be smuggled into the Jones API.

#### P4. Deterministic Mueller action — complete

Locations: `Physlib/Optics/Polarization/Mueller.lean` and
`Physlib/Optics/Polarization/Mueller/`.

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

Completion evidence: `Matrix.selfAdjointCongruence` supplies the rectangular neutral real-linear
map `C ↦ A C Aᴴ`, with identity, cascade, and arbitrary complex-scaling laws; the prior
`Lorentz.SL2C.toSelfAdjointMap'` remains a compatibility alias rather than becoming an Optics
dependency. `JonesMatrix.mueller` transports this map through `selfAdjointStokesEquiv` into a
wrapped real `4 × 4` carrier. The implementation proves both Jones/coherency commuting squares,
preservation of the entire physical Stokes cone, entry reality, and the exact half-trace formula in
audited Stokes order `(σ₀, σ₃, σ₁, σ₂)`. Identity, cascade, arbitrary-scalar, and unit-phase laws
are connected to the same construction. Algebraic Jones unitarity preserves raw Jones
intensity, coherency trace, raw Stokes intensity, the unpolarized axis, polarization norm, and
Poincare-sphere membership without claiming electromagnetic power or `SO(3)`. The algebraically
named `diag(1, I)` regression proves
`(S₀, S₁, S₂, S₃) ↦ (S₀, S₁, -S₃, S₂)` and connects the corresponding canonical Jones states.
The raw Mueller wrapper explicitly certifies neither physical admissibility nor Jones
inducibility, and no general depolarizing-map claim is made.

#### P5a. Jones polarizer and Malus core — complete

Locations: `Physlib/Optics/Polarization/Linear.lean`,
`Physlib/Optics/Polarization/LinearStokes.lean`, and
`Physlib/Optics/Components/Polarizer.lean` with its `Polarizer/` subtree.

Deliverables:

- normalized linear-polarization vectors at arbitrary axes;
- ideal linear-polarizer Jones matrices as rank-one projections;
- self-adjointness, idempotence, contraction for squared Jones intensity, axis transmission, and
  orthogonal extinction;
- sequential-polarizer amplitude and squared-Jones-intensity laws;
- Malus' law for a linearly polarized input, with the input/output axis angle made explicit; and
- coherency, Stokes, and induced Mueller formulas derived through the existing commuting squares.

Exit: a linearly polarized input sent through an arbitrary ideal linear polarizer has transmitted
Jones intensity equal to its actual input intensity times `cos²(delta)`, without making a
physical-power claim.

Completion evidence: `JonesVector.linearPolarization` uses `Real.Angle`, so full-turn duplication is
removed while the half-turn Jones sign and half-turn projector invariance are both explicit.
`JonesMatrix.linearPolarizer` is the outer product of that normalized axis with itself; it is
Hermitian, idempotent, a bundled star projection, exactly rank one, algebraically nonunitary, and
contractive for every raw Jones input by Cauchy--Schwarz. The coherent action retains the signed
angle-difference cosine, while the single-input and sequential-polarizer intensity results derive
the squared cosine from the existing `JonesVector.intensity`. Exact zero, `π / 2`, and `π / 4`
matrices, crossed-axis extinction, and the `π / 4` half-intensity result pin the conventions.
Coherency transport is proved through `JonesMatrix.act_coherency`. The induced Mueller matrix is
proved through the shared Pauli trace formula to be one half of the transmitted Stokes state's
outer product, yielding the arbitrary raw-Stokes output
`q (1, cos (2θ), sin (2θ), 0)` and the zero-polarization factor-of-two regression. No irradiance,
Poynting-flux, modal-power, or electromagnetic-passivity theorem is included; those remain P5b.

#### P5b. Physical Malus bridge

Candidate location: the Optics normalization bridge beside E3b, not the Jones core file.

Deliverables:

- translate P5a's squared-Jones-intensity theorem to irradiance for the plane-wave family covered
  by E3b; and
- translate it to `ModeAmplitude.power` only for the proved flux-normalized mode family.

Exit: physical Malus power is a corollary of P5a plus E3b rather than a second intensity definition.

#### P6a. Retarder and wave-plate core

Status: complete on the fork. Candidate export location: `Components/Retarder.lean`, with semantic
modules under `Components/Retarder/` and the supporting relative-phase Jones family under
`Polarization/RelativePhase.lean`.

Deliverables:

- [x] rotated ideal retarder at an arbitrary reference principal-axis angle and retardance;
- [x] phase-sign realization, determinant, composition, inverse, unitarity, and
  squared-Jones-intensity preservation without depending on Stokes theory;
- [x] positive and negative quarter-wave and half-wave specializations; and
- [x] proved Jones actions on canonical linear and algebraic quadrature states and on a selected
  normalized equal-amplitude relative-phase family, while deferring circular handedness.

Exit achieved: retarder and wave-plate calculations are complete in raw Jones coordinates without
waiting for Stokes or the electromagnetic bridge. P6b-1 now supplies the reduced coherency,
Stokes, and deterministic Mueller views. The omitted common propagation phase, fast/slow-axis
material naming, observer-oriented Poincare interpretation, irradiance, and modal-power
interpretations remain explicit later gates rather than implicit claims of the Jones core.

#### P6b. Cross-representation polarization chain

This umbrella is split so the reduced representation theorem is not falsely blocked by physical
power normalization, and the single-component retarder PR is not enlarged into a system example.

##### P6b-1. Reduced retarder representations

Status: complete on the fork. Export locations:
`Polarization/RelativePhaseStokes.lean`, `Components/Retarder/Coherency.lean`, and
`Components/Retarder/Mueller*.lean`.

Deliverables:

- [x] exact Stokes coordinates `(0, cos relativePhase, sin relativePhase)` for the normalized
  equal-amplitude Jones family;
- [x] exact pure-coherency outputs for arbitrary linear input and the zero-axis relative-phase
  family;
- [x] the explicit arbitrary-axis `3 x 3` polarization block and the induced block-diagonal
  deterministic Mueller matrix;
- [x] arbitrary raw-Stokes, Jones-derived Stokes, and coherency-derived Stokes action theorems; and
- [x] zero-axis and `pi / 4` quarter-wave sign regressions tied to the existing `diag(1, I)`
  deterministic Mueller oracle.

Exit achieved: P6a Jones actions agree exactly with coherency, Stokes, and deterministic Mueller
descriptions. The coordinate formula records the algebraic sign without claiming observer-based
handedness or electromagnetic power.

##### P6b-2. Connected reduced polarizer--retarder example

Status: complete on the fork. Export location: `Optics/Systems/PolarizerRetarder.lean`.

Deliverables:

- [x] use ordered `JonesMatrix.comp`, without a second system carrier, to pass an arbitrary Jones
  input first through a P5a polarizer and then through a P6a linear retarder;
- [x] derive the exact Jones output and the coherency of that same output through the shared
  Jones/coherency commuting law;
- [x] derive the arbitrary raw-Stokes action from induced Mueller composition and the two public
  component actions, with the generic Jones and coherency commuting squares remaining reusable;
  and
- [x] pin the cascade order, analyzer amplitude, and positive-quarter-wave sign on the canonical
  horizontal--`pi / 4` analyzer--zero-axis plate regression.

Exit achieved: one ordered system-level polarization chain has exact Jones, pure-coherency, raw
Stokes, and induced Mueller descriptions. Its scalar remains a raw Stokes coordinate and its
quadrature output remains algebraically named, without electromagnetic-power or handedness claims.

##### P6b-3. Physical polarization observables

Status: blocked on P5b and E3b.

Deliverables:

- a connected example starting at P1b's `harmonicWaveX` bridge and passing through a P5a polarizer
  and P6a wave plate; and
- field realization, irradiance, and normalized-power observables, using P5b/E3b before any
  physical-power claim.

Exit: the reduced connected chain is realized as electromagnetic fields and its physical
observables agree through named normalization bridge theorems.

### H.2. Electromagnetic-interface milestone

#### E0. Public three-dimensional Maxwell API — complete

Owner: Electromagnetism.

- [x] expose the existing `gaussLawElectric`, `gaussLawMagnetic`, `ampereLaw`, and `faradayLaw`
  declarations through the public module surface;
- [x] preserve their statements and proofs; and
- [x] confirm there are no present theorem-name consumers, compile the sole root importer, and
  smoke-test ordinary direct and root imports to show that this is an export repair rather than a
  second Maxwell theory.

Exit achieved: E1 and its vacuum bridge can reuse the already-proved differential laws through
an ordinary import of `Physlib.Electromagnetism.ThreeDimension.MaxwellEquations` or `Physlib`; the
namespace content from the first declaration onward is byte-for-byte unchanged from the E0 base.

#### E1. Homogeneous isotropic media — complete

Owner: Electromagnetism.

- [x] positive scalar permittivity and permeability with explicit linear, homogeneous, isotropic,
  nonconducting, nondispersive scope;
- [x] `D = ε E`, `B = μ H`, wave speed, wave impedance, and explicitly relative refractive-index
  conventions, with zero, addition, and scalar closure of the separate constitutive predicate;
- [x] a differentiability-aware macroscopic Maxwell predicate using `E`, `D`, `B`, `H`, free
  charge, and free current, rather
  than treating the constitutive equations as Maxwell's equations;
- [x] source-free specialization and linear-superposition lemmas;
- [x] positivity and nonzero lemmas needed by divisions and square roots;
- [x] one-way specialization of `FreeSpace` constants to the material data; and
- [x] one-way bridge from E0's potential-derived laws to the macroscopic predicate.

Exit achieved: medium parameters are sufficient to state material plane waves and interface
coefficients without ad hoc real tuples, and the governing equations distinguish free from bound
sources.

#### E2. Material monochromatic plane waves

- [x] an off-shell, purely harmonic real three-dimensional carrier with independent positive
  angular frequency and wave number, two electric quadratures, compatible `E` and `B` candidates,
  medium-supplied `D` and `H`, separate transversality, regularity, phase-velocity wave equations,
  and constitutive satisfaction;
- [x] positive-branch material dispersion, a canonical fixed-medium constructor, source-free
  Maxwell satisfaction under transversality and dispersion, the honest nonzero-amplitude
  converse, the nonzero-candidate characterization, and on-shell `E`/`B`/`H` relations;
- [x] an Optics-owned complex-harmonic/phasor representation importing the real field theorem and
  a fixed-vacuum regression against the existing representation bridge;
- [x] canonical `s = normalize (n × k)` and `p = k × s` full-vector polarization axes and
  Jones decomposition for non-normal incidence, including grazing geometry but no positive-power
  claim;
- [x] a polarization-frame constructor from an independently selected unit transverse axis for
  normal incidence, with an exact regression proving that reversing propagation preserves the
  selected `s` axis and negates the derived `p` axis;
- [x] a dimension-generic complex-wavevector representation with a complex-bilinear pairing,
  phase/attenuation decomposition, spatial-factor laws, and proof-bearing positive-normal
  exponential decay, including an exact coordinate sign regression;
- [x] an off-shell complex electromagnetic carrier with ordinary real `E`/`D`/`B`/`H`, compatible
  magnetic amplitude, bilinear electric transversality, structural magnetic transversality,
  positive-normal field decay, and constitutive satisfaction;
- [x] an exact bridge from every existing real-quadrature plane wave to the complex carrier,
  including carrier, the exact nonzero-amplitude guard, transversality, magnetic amplitude, and
  all four ordinary real fields;
- [x] generic complex-carrier joint regularity, exact carrier time and coordinate derivatives, and
  generic realized-field time and coordinate derivatives, divergence expressed through the
  complex-bilinear pairing, and curl identities through the shared ordinary-real-field realization
  spine;
- [x] bilinear material dispersion, its exact phase/attenuation decomposition, nonzero-wave-vector
  consequence, transverse on-shell cross-product algebra, and exact positive-real-branch bridge;
- [x] forward ordinary-real-field differential identities, the four source-free Maxwell laws under
  their stated sufficient forward hypotheses, and the differentiability-aware fixed-medium endpoint;
- [x] exact two-time recovery of the required complex amplitude equations, Maxwell-forced
  bilinear transversality, the guarded nonzero-amplitude dispersion converse and characterization,
  and the explicit zero-amplitude off-shell degeneracy; and
- [x] an exact attenuating `K = (5, 0, -4 I)` algebraic regression with TE/TM amplitudes,
  bilinear-versus-Hermitian distinctions, dispersion, magnetic amplitudes, and signed cross
  relations; and
- [x] exact ordinary-real-field TE/TM, zero-amplitude, one-phase, complex-null, and embedded-real
  guarded-converse regressions; and
- [x] an interface-oriented carrier branch with tangent phase, strictly positive normal
  attenuation, and exact positive-side decay under a negative transmitted normal radicand; and
- [ ] Maxwell-qualified evanescent-field and outgoing semantics for that carrier geometry.

Exit: incident, reflected, transmitted, and side-decaying candidate carriers share one field API;
the evanescent-field label remains conditional on the stated Maxwell semantics.

#### E3s. Cross-product divergence identity

Owner: SpaceAndTime.

- prove `div (E × H) = H · curl E - E · curl H` for three-dimensional fields;
- state only the differentiability hypotheses actually used by the derivative API; and
- keep the result independent of electromagnetic field aliases and constitutive laws.

Exit: E3a can derive energy balance from Maxwell equations without reproving general vector
calculus inside Electromagnetism.

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

#### E4a. Planar interface and local boundary semantics

- [x] dimension-generic oriented affine hyperplane geometry with signed normal coordinates,
  neutral positive and negative sides, open and closed half-spaces, tangential projection, a
  bundled tangent submodule and linear retraction, exact normal-vector characterization, and
  carrier parameterization;
- [x] a planar dielectric interface assigning medium 1 to the negative side, medium 2 to the
  positive side, and the stored normal from medium 1 toward medium 2;
- [x] a primitive time-domain boundary-data configuration whose incident-, reflected-, and
  transmitted-labelled off-shell candidates retain independent positive frequencies and complex
  wave vectors, with incident-plus-reflected negative-medium and transmitted positive-medium
  ordinary real pointwise plane traces for every boundary point and time;
- [x] tangential `E` and `H` and normal `D` and `B` boundary laws with free electric surface
  sources, using the negative-to-positive jump convention;
- [x] zero-free-surface-charge/current specializations, without claiming bound polarization
  charge is absent; and
- [x] clearly named sourceful and zero-free-surface-source local predicates connecting those traces
  to the generic boundary laws; every future conditional reflection, Snell, and Fresnel result must
  expose the appropriate predicate.

This initial exact-wave slice uses pointwise restrictions of globally defined fields. It does not
construct half-space-supported fields or analytic one-sided traces, establish genuine one-sided
illumination, or package on-shellness; those require later propagation-role and branch hypotheses
and E4b's analytic derivation.

Exit: the primitive independent-frequency ordinary-real pointwise boundary-data problem is stated
honestly from explicit local laws, at the same abstraction level as the audited HOL interface work.

#### E4b. Maxwell derivation of the boundary laws

Owner: SpaceAndTime and Electromagnetism.

- local domains, oriented surfaces, traces or restrictions, and the required regularity API;
- integral curl and divergence laws with orientation and boundary hypotheses;
- integral Maxwell equations with volume and surface sources; and
- derivation that E4a's tangential and normal boundary predicates hold under the corresponding
  thin-loop and pillbox limits.

Exit: the local laws used by E5a/E5b/E6 become physical theorems from Maxwell equations. Physical
Optics v0.1 requires this stronger exit; integrated-photonics work does not.

#### E5a. Conservation and fixed-frequency reduction

- [x] neutral finite exponential-character independence for complex-valued real-linear
  functionals, including finite-support uniqueness without topology or a common period;
- [x] positive-frequency harmonic uniqueness for ordinary real finite sums, with coefficients
  aggregated by exponent functional and each supported positive-frequency character separated
  from every conjugate negative-frequency character;
- [x] the zero-free-surface-charge three-wave joint tangential-`E`/normal-`D` equality, with
  arbitrary free surface current, and its exact independent-frequency boundary-character
  realization;
- [x] a two-law electric planar-boundary predicate projected from the full four-law boundary, with
  the zero-charge predicate proved exactly equivalent to equality of the actual joint
  tangential-`E`/normal-`D` field data rather than either magnetic law;
- [x] finite-support joint-electric harmonic uniqueness lifting neutral positive-rate scalar
  character independence coordinatewise to the tangential-`E`/normal-`D` calculation amplitude,
  with exact aggregation by exponent functional;
- [x] the single-wave boundary exponent on time paired with the hyperplane tangent submodule, with
  the unit-time probe recovering positive angular frequency, equality of exponent functionals
  separating angular frequency from complex-bilinear wave-vector pairing against every tangent
  displacement, and exact carrier factorization isolating the affine-point spatial factor;
- [x] joint electric trace calculation amplitudes containing tangential `E` and scalar normal `D`,
  proved zero exactly when the electric amplitude is zero using the medium's nonzero permittivity,
  referenced at the affine plane's stored point by the nonvanishing spatial carrier, and connected
  to the actual ordinary-real plane data by exact boundary-exponent factorization;
- [x] the exact signed three-wave joint electric coefficient map, aggregated by boundary exponent,
  with its vanishing proved exactly equivalent to the zero-charge electric boundary predicate and
  inherited in the forward direction by a full local boundary with arbitrary free surface current;
- [x] the oriented-hyperplane results converting vanishing against every tangent displacement into
  an explicit normal-vector multiple and characterizing equality of tangential projections by
  equality against every tangent probe;
- [x] dimension-generic complex-wave-vector normal--tangential decomposition, compatible with the
  phase/attenuation split, with equality of complex tangential projections characterized by all
  real-tangent complex-bilinear pairings and arbitrary complex normal shifts proved invisible;
- [x] guarded three-wave label matching from the zero-charge electric predicate under the exact
  nonzero negative-side coefficient at the incident boundary exponent, deriving
  transmitted/incident exponent equality, the disjunction that the reflected electric amplitude
  is zero or its exponent also matches, and referenced joint coefficient balance, with full local
  boundaries inheriting the result;
- [x] transmitted electric-amplitude nonvanishing from the electric predicate under the exact
  aggregate guard, together with explicit conservation corollaries decoding the matched exponents
  into frequency and tangent wave-vector pairing equality and exact complex tangential-projection
  equality under exactly the derived branches, with full local boundary wrappers;
- [x] a reduced fixed-frequency complex-amplitude boundary problem introduced only after those
  conservation results, split into reusable active-wave phase-matching and stored-point-referenced
  joint electric amplitude-balance predicates; and
- [x] a guarded equivalence relating its amplitude equations to the primitive two-law electric trace
  problem, with the non-null guard used only to derive label matching in the primitive-to-reduced
  direction and no claim of reconstructing either magnetic boundary law.

Exit: every later fixed-frequency electric-boundary calculation is connected to the
independent-frequency physical problem, and no conservation conclusion is hidden in its own
premises.

#### E5b. Reflection, refraction, and total internal reflection

- [x] branch-neutral complex hyperplane reflection: the complex-bilinear square decomposes into
  tangential and oriented-normal squares, reflection flips only the normal component, preserves
  the tangential projection and complex-bilinear square, is involutive, and exhausts the two
  possible normal roots at fixed tangential projection and square; the alternatives deliberately
  remain nonexclusive at zero complex normal component, including grazing real geometry; the
  complex normal component and reflection are decoded exactly into their real phase and
  attenuation normal components, with both signs negated by reflection, but carry no incident,
  outgoing, medium, or physical-root semantics;
- [x] the material-shell normal-root equation expressing the squared oriented complex normal
  component as the real material square minus the complex tangential bilinear square, without
  selecting a square root, interface side, or propagation role;
- [x] neutral real-radicand normal-root alternatives: an explicitly nonnegative real normal square
  gives the two real roots `±√c`, a zero square forces the unique zero root, and an explicitly
  nonpositive real normal square gives the two imaginary roots `±I * √(-c)`, without preferring a
  sign or assigning propagation, grazing, evanescence, outgoing, or power meaning;
- [x] strict side-relative attenuation direction and real-square root selection: phase direction
  forces a positive radicand, zero attenuation normal component, and the side-signed real root;
  attenuation direction forces a negative radicand, zero phase normal component, and the root
  `-I` times the side-signed square root, without asserting zero tangential attenuation or assigning
  a medium, interface wave role, evanescence, outgoing, energy-flow, or power meaning;
- [x] phase-matched interface consequences: the transmitted positive-medium normal-root equation
  in incident frequency and tangential data, the exact two-medium contrast of transmitted and
  incident squared normal components, and the guarded reflected alternative of zero electric
  amplitude, the same wave vector, or neutral hyperplane reflection; the continuation root remains
  explicit in this branch-neutral result;
- [x] transmitted real-radicand reduction: complex tangential projection decodes into separate
  real phase and attenuation projections; zero incident tangential attenuation, without requiring
  zero normal attenuation, makes the transmitted normal square equal the explicitly real candidate
  `ε₂ μ₂ ωᵢ² - ‖qᵢ,tan‖²`; the reduction assigns no sign, root, angle, critical, evanescent,
  side-decaying, outgoing, or power meaning;
- [x] transmitted normal-root application: phase matching transports zero incident tangential
  attenuation to the transmitted candidate; supplied positive-side phase direction forces a
  positive radicand, zero whole transmitted attenuation, and the `+√c` normal root; zero
  radicand forces the unique zero normal root and zero whole attenuation; supplied positive-side
  attenuation direction forces a negative radicand, zero phase normal component, and the
  `-I * √(-c)` normal root, without constructing a candidate or assigning angle, spatial-decay,
  evanescent, outgoing, TIR, irradiance, or power meaning;
- [x] neutral hyperplane-normal spatial scaling: displacement along the stored normal changes the
  spatial pairing by `u * K_normal` and the spatial factor by `exp (-I * u * K_normal)`; the root
  `K_normal = -I * α` gives the exact real factor `exp (-α * u)`, while the general norm law is
  `‖S (x + u n)‖ = exp (-a_normal * u) * ‖S x‖`; strict positive-side attenuation makes the
  spatial factor tend to zero without requiring zero tangential attenuation or zero phase normal
  component and without assigning a medium, interface, evanescent, outgoing, or power role;
- [x] transmitted carrier and real-field side scaling: electromagnetism lifts normal-displacement
  scaling to the complete complex carrier and to every ordinary real field constructed from it;
  the attenuation-directed transmitted root specializes the rate to `√(-c)` for the carrier and
  the ordinary `E` and `B` fields at every base point, with negative displacement giving the
  inverse growth direction and without asserting one-sided support, outgoing behavior, TIR,
  irradiance, or power;
- [x] strict side-relative phase direction for complex wave vectors and phase-directed reflected
  branch selection: incident phase into the positive side and guarded active reflected phase into
  the negative side exclude the continuation root and force neutral hyperplane reflection, without
  deriving either direction from a trace label or assigning group-velocity or power meaning;
- [x] side-relative phase-angle geometry and the angular law of reflection: neutral real vector
  reflection preserves tangential data, norm, and angle after exchanging sides; complex
  hyperplane reflection acts by that real reflection on phase and attenuation vectors; incident,
  reflected, and transmitted label angles use respectively the positive-, negative-, and
  positive-side normals; and the guarded active reflected branch has equal incident and reflected
  phase angles while retaining arbitrary dummy angle data at zero reflected electric amplitude;
  the result assigns no ray, group-velocity, energy-flux, outgoing, irradiance, or power meaning;
- [x] the phase Snell identity from tangential phase matching alone, together with the
  wave-speed and explicitly relative-refractive-index forms for incident and transmitted carriers
  under their respective material-dispersion hypotheses and zero whole attenuation; the common
  positive frequency is derived from the reduced boundary predicate and cancels explicitly, while
  no direction,
  branch-existence, critical-angle, ray, group-velocity, outgoing, Fresnel, irradiance, or power
  claim is made;
- [x] critical phase-angle threshold geometry: the strict slower-to-faster wave-speed contrast
  gives the reference-free threshold `v₁ / v₂ = n₂ / n₁` in `(0, 1)` and a proof-bearing critical
  phase angle in `(0, π / 2)`; primitive subcritical, critical, and supercritical incidence
  predicates classify the exact transmitted normal-radicand sign under incident dispersion and
  zero whole incident attenuation, while an explicit incident-angle range gives the corresponding
  angle ordering; the sine-critical predicate is unconditional, deliberately includes equal-speed
  grazing without an interior critical angle, and can represent the supplementary obtuse branch
  until that range is supplied; for an already supplied phase-matched candidate with incident and
  transmitted material dispersion and zero whole incident attenuation, the unique zero transmitted
  normal root gives zero transmitted attenuation and genuine transmitted phase tangency, without
  constructing a candidate or assigning outgoing, evanescent, TIR, irradiance, or power meaning;
- [x] existence and uniqueness of the positive real transmitted phase root below the critical
  sine threshold: a neutral normal-component replacement preserves complex tangential data; the
  canonical construction retains the incident tangential phase vector and uses `+√c` along the
  stored normal; under incident negative-medium dispersion and zero whole attenuation,
  sine-subcritical incidence is equivalent to unique existence of the positive-medium-shell,
  zero-attenuation, positive-phase-directed wave vector; an arbitrary-amplitude plane-wave family
  is unique only after its electric amplitude is fixed; and a supplied phase-matched,
  positive-medium-dispersive, positive-phase-directed transmitted candidate with zero incident
  tangential attenuation is identified with that family member, without calling phase direction
  outgoing or assigning ray, group-velocity, Maxwell, boundary-amplitude, irradiance, or power
  meaning;
- [x] existence and uniqueness of the positive-normal-decay transmitted branch above the critical
  sine threshold: the canonical normal component is `-I * √(-c)` and the phase is tangent while
  attenuation is a strictly positive multiple of the stored normal; under zero incident
  tangential attenuation, negative radicand is equivalent to unique existence of the exact common-
  tangent, positive-medium-shell, purely-normal-attenuation, positive-side-directed vector;
  incident negative-medium dispersion and zero whole attenuation specialize this to strict
  sine-supercritical incidence. The branch lifts to an arbitrary-amplitude carrier family that is
  unique after fixing the electric amplitude, and its spatial factor, complete carrier, ordinary
  electric field, and ordinary magnetic induction have exact `exp (-√(-c) * u)` scaling. The
  carrier is global and grows at negative depth. A supplied phase-matched, positive-medium-
  dispersive, attenuation-directed candidate with zero incident tangential attenuation is
  identified with the canonical family member. None of this supplies transversality, Maxwell,
  one-sided support, ray, group-velocity, energy-flow, outgoing, evanescent-field, TIR, Fresnel,
  irradiance, or power semantics;
- [ ] total-internal-reflection characterization from boundary amplitudes and flux; and
- [ ] Maxwell-qualified evanescent classification and any outgoing interpretation of the
  side-decaying complex transmitted branch, kept distinct from an ordinary positive-power
  propagating mode.

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

#### N1. Modal algebra completion — complete

O2 now supplies the converse characterizations, parallel closure, and convention-free coordinate
changes required by the network layer.

#### N2a. Ports, channels, and convention-free routing — ready

- a `PortModeFamily` with dependent flattened channel type `Σ p, Mode p`, with finiteness required
  only by finite operations;
- nominally distinct incident and outgoing channel-end types with explicit canonical equivalences
  and no coercion erasing the boundary;
- a typed connection between distinct ports carrying an explicit equivalence between their mode
  fibers;
- the local mate permutation, fixed-point-free involution, and global no-endpoint-reuse property
  derived from those typed connections rather than accepted as unstructured flat data;
- ideal unit-gain routing obtained by reindexing identity, with its endpoint action and power
  preservation proved;
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

#### N3T. Two-port chain semantics

- typed left/right travelling-wave variables and an independently stated two-port behavior;
- a chain-matrix view only when the behavior determines the required outputs;
- scattering-to-chain and chain-to-scattering conversions with the exact transmission-block
  invertibility hypotheses visible in their types or theorem statements;
- behavioral equivalence and round trips for both conversions;
- series connection as chain-matrix multiplication, proved from relational composition;
- agreement with N5 netlist elimination and Redheffer feedback wherever both are defined; and
- terminated-load reflection and transmission formulas.

Exit: the transfer/chain calculations used by the audited cascade and microring sources are
derived views of the same component behavior, not illicit multiplication of scattering matrices.

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

#### N4C. Certified finite-netlist compiler

- finite executable data for ports, directed channel endpoints, component incidences, and gains;
- decidable well-formedness checking for endpoint direction, mode compatibility, self-wiring,
  reuse, and fan-out;
- executable construction of `S`, `C`, `E_in`, and `E_out`;
- a soundness theorem equating compiled equations with N4's flat relational semantics;
- an algebraic backend over an appropriate field, with exact rational-function instantiation for
  finite-delay responses; and
- evaluation into `ℂ` away from every required denominator, proved to commute with compilation.

Exit: exact executable fixtures test an implementation that is proved correct with respect to the
kernel semantics; a noncomputable complex matrix inverse is not the sole oracle.

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

#### N6c. Coherent and incoherent network observables

- modal coherency transport `Γ_out = H * Γ_in * Hᴴ` for a well-posed response `H`;
- output powers from diagonal entries or trace, connected to N6a's normalization conventions;
- rank-one coherent inputs and diagonal incoherent inputs;
- the vanishing of interference cross terms under the stated decorrelation hypothesis; and
- passivity and conservation corollaries for coherency transport.

Exit: coherent and incoherent system claims are represented by explicit second-order data rather
than by silently deleting phase-sensitive cross terms from complex amplitudes.

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

#### S0. Physical microring realization

- ring parameters for through/cross amplitude coefficients, optical path length, field attenuation,
  effective index or propagation constant, and wavelength/frequency;
- validity predicates distinguishing field from power attenuation and amplitude from power
  coupling coefficients;
- one-bus/all-pass and two-bus/add-drop typed port topologies;
- an independent relation between internal and external travelling fields;
- realization from N7 couplers and propagation delays; and
- proofs that each realization satisfies its field relation and induces the source-level
  transfer/chain matrices under their actual nondegeneracy hypotheses.

Exit: microring formulas are consequences of a physically parameterized component realization,
not the defining fields of a formula container.

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

#### S4P. Poles, zeros, stability, and frequency response

- reduced rational responses and their evaluation domains;
- zeros and transfer-function poles after cancellation, distinct from candidate singularities of
  the internal network operator;
- degree and finiteness bounds;
- a reachability/observability or explicit no-cancellation criterion connecting internal
  singularities to actual poles;
- discrete-time Schur stability and BIBO equivalence only for a stated proper causal rational
  class;
- frequency response under the chosen `q = exp (-s * τ) = z⁻¹` convention; and
- group delay and dispersion through a local logarithmic derivative or another branch-audited
  construction, not an unqualified global complex argument.

Names must state literal mathematical content. In particular, source terminology that calls all
zeros inside the unit disk a “resonance condition” is not adopted without a separate physical
resonance theorem.

#### S5. Difference equations and Z-transform

- causal complex sequences with zero extension;
- finite convolution and linear recurrences with initial conditions;
- analytic unilateral Z-transform with conditional and absolute convergence regions kept
  distinct;
- linearity, causal right-delay, and left-shift laws with their startup terms;
- first differences, `z`-domain scaling, and any complex-differentiation law required by a
  mandatory source-ledger row;
- recurrence-to-transfer theorem under summability and initial-condition hypotheses;
- general IIR and frequency-response theorems, including the audited second-order low-pass
  regression;
- absolute-summability/BIBO stability results and their relation to poles and the region of
  convergence for the selected causal rational class; and
- connection between coefficient recurrences and the formal power-series view.

Inverse-transform uniqueness is not required for source parity unless a later mandatory ledger row
needs it.

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

The graph representation must support executable and proved-correct enumeration of simple forward
paths, elementary directed cycles modulo cyclic rotation, touching and pairwise non-touching loop
families, and parallel edges as distinct branches. A simple digraph that collapses parallel edges
does not meet this milestone.

The ordinary commutative Mason formula is applied only after expanding a multimode network into
scalar channel nodes. Matrix-valued edge gains do not commute and require a different theorem; do
not claim the scalar formula for them.

#### S7. HOL-equivalence case suite

- one-port/all-pass and four-port/add-drop ring;
- a source-mapped double-coupled double-ring example;
- transfer amplitude, spectral power, resonance, and rejection-ratio results;
- at least one difference-equation/Z-transform derivation; and
- at least one signal-flow/Mason derivation proved equal to network elimination; and
- for an eligible ring and the DCDR case, a cross-semantics theorem equating relational behavior,
  compiled elimination, chain response, feedback algebra, Mason gain, and recurrence/Z response on
  the intersection of their domains.

The cross-semantics theorem keeps three conditions distinct: algebraic feedback requires an
invertible internal operator; an infinite round-trip series requires contraction or summability;
and a Z-transform identity additionally requires causality and a stated convergence region.

#### S7D. DCDR parity suite

- the human-audited eight-node, eleven-edge topology with parallel edges retained;
- the transfer result by N5 elimination and independently by S6 Mason gain;
- active/passive, unit-delay, and multiple-delay specializations;
- coherent and incoherent interpretations through N6c;
- poles, zeros, and stability results; and
- an exact or interval-certified, human-audited version of the source's reported unstable passive
  parameter case.

#### S7C. Periodic cascade and lattice parity suite

- arbitrary heterogeneous microring cascades;
- an identical-`N` cascade as a chain-matrix power;
- a Sylvester/Chebyshev closed form with its actual determinant and trace-domain assumptions;
- terminated reflection and transmission;
- coupled and uncoupled row/column decompositions;
- the mandatory `M × N` lattice theorem; and
- the source-mapped add-drop and quadruple-ring cases.

Exit for H.4: the integrated-photonics results in the cited HOL program can be reproduced as
instances of a more general typed system API, and every mandatory row in the integrated-photonics
parity ledger is discharged by a public declaration and regression.

### H.5. Foundational ray, imaging, Gaussian-beam, and resonator milestone

#### R1. Physical and paraxial rays

- physical ray, oriented interface incidence, reflection, and refraction;
- paraxial ray coordinate with the approximation stated as a model assumption or a proved limit;
- free-space and plane/spherical-interface behavior; and
- relationship to E5b's exact geometric directions.

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

Exit for H.5: the principal reusable ray-, Gaussian-, and resonator-optics foundations and their
representative system analyses are available through Physlib definitions. This is not by itself a
claim of full extended-suite parity. Such a claim additionally requires mandatory ledger rows for
the selected source case studies, potentially including corrective-eye and thick-lens examples,
Gaussian intensity and output-waist formulas, arbitrary-`N` resonator unfolding, receiver and
fiber-rod-lens analyses, phase-conjugated rings, and any nonlinear-map or chaos results retained
after a separate scope and physics review.

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
| P-01 | framed material-Jones realization equals the complete `harmonicWaveX` electric field and magnetic induction | phase/cast/index/cross-product mismatch |
| P-02 | squared Jones intensity equals the sum of squared real electric amplitudes | raw-field normalization mismatch |
| P-03 | pure coherency and Stokes data are invariant under unit-modulus global phase | missing phase hypothesis or incorrect conjugation |
| P-04a | canonical H/V/D/A and algebraically named positive/negative-quadrature Jones states have the documented Stokes vectors | basis order, factor-of-two, conjugation, and `S₃` sign errors |
| P-04b | after the human convention gate, named R/L Jones states agree with reconstructed real-field rotation and their documented Stokes vectors | observer-direction and circular-handedness errors |
| P-05 | normalized nonzero coherency lies in the Poincare ball, reaches its boundary exactly at rank one, and rank-two/positive-definite data is strictly interior | invalid mixed-state classification |
| P-06 | induced Mueller action agrees with Jones conjugation and composes correctly | basis/factor/conjugation mismatch |
| P-07 | extracting Stokes coordinates after reconstruction returns the original raw Stokes vector | wrong basis order or factor of two |
| P-08 | reconstructed coherency is PSD exactly for vectors in the physical Stokes cone | unsound physical-Stokes inverse |
| C-01 | ideal polarizer is self-adjoint, idempotent, and Jones-intensity nonincreasing | wrong projector/component law |
| C-02 | sequential ideal polarizers on a linear input prove Malus' law | overgeneralized input class or disconnected intensity |
| C-03 | quarter- and half-wave plates produce named canonical states and preserve Jones intensity | axis/retardance convention errors |
| E-00 | `K = q - I * alpha * n` has bilinear square `norm q ^ 2 - alpha ^ 2`, and positive-normal displacement multiplies its spatial factor by `exp (-alpha * u)` | Hermitian/bilinear confusion or attenuation-sign error |
| E-00a | every existing real-quadrature `MonochromaticPlaneWave` embeds with exactly equal carrier, transversality predicate, magnetic amplitude, and ordinary real `E`/`B`; for every supplied homogeneous medium its `D`/`H` fields also agree | disconnected complex state or quadrature-sign error |
| E-00b | for `epsilon = mu = 3`, `omega = 1`, and `K = (5, 0, -4 I)`, exact TE and TM amplitudes satisfy bilinear dispersion/transversality and full real Maxwell with carrier `exp (-4 z) exp (I (t - 5 x))`, while the Hermitian norm square is `41`, not `9` | Hermitian/bilinear, attenuation, cross-order, constitutive, or quadrature-sign confusion |
| E-00c | zero electric amplitude satisfies the real Maxwell predicate for a deliberately dispersion-mismatched carrier, while every converse that derives dispersion requires a nonzero-amplitude hypothesis | silently invalid complex converse |
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
| H-01 | independently stated two- and four-port ring behaviors imply their chain matrices | formula stored as behavior or wrong travelling-wave orientation |
| H-02 | scattering/chain conversion round trips under the exact transmission-block hypotheses | illicit inverse or port-order error |
| H-03 | arbitrary cascade behavior equals the folded chain matrix | multiplication-order or behavior/matrix mismatch |
| H-04 | an identical-`N` cascade equals the corresponding matrix power | incorrect finite-fold specialization |
| H-05 | the Sylvester/Chebyshev cascade form holds with its determinant and trace-domain assumptions | overgeneralized closed form |
| H-06 | terminated-cascade reflection and transmission agree with relational termination | load-orientation or denominator error |
| B-01 | contraction feedback series converges to the algebraic inverse response | unjustified geometric series |
| B-02 | a noncontractive but invertible feedback example remains well posed | contraction treated as necessary |
| B-03 | the source-mapped nested feedback/sum/pickoff identity follows from common behavior semantics | block-algebra orientation error |
| S-01 | balanced Mach-Zehnder outputs and power balance | coupler phase convention errors |
| S-02 | microring elimination and convergent round-trip series agree | feedback orientation errors |
| S-03 | microring transfer, power, resonance, and rejection specializations | hidden nondegeneracy assumptions |
| S-04 | physical add-drop realization yields the exact transfer response | disconnected ring formula |
| S-05 | add-drop power and rejection ratio satisfy their positivity and logarithm domains | amplitude/power or dB-convention error |
| S-06 | the audited eight-node DCDR response agrees between elimination and Mason gain | graph topology or path/loop error |
| S-07 | DCDR pole/zero/stability theorems include the audited unstable parameter case | cancellation or strictness error |
| S-08 | the `M × N` lattice flattening agrees with its row/column decomposition | hierarchy or cascade-index error |
| T-01 | Z-transform delay law records ROC and initial conditions | false signal-processing identity |
| T-02 | recurrence, rational transfer function, and network response agree | domain-model mismatch |
| T-03 | conditional and absolute convergence regions are not identified | overstated ROC or BIBO theorem |
| T-04 | general IIR and audited second-order low-pass responses follow from recurrence semantics | formula-only Z-transform development |
| T-05 | the selected `q = z⁻¹` translation commutes with evaluation | reversed delay/frequency convention |
| G-01 | Mason gain equals the matrix-inverse transfer for representative graphs | path/loop enumeration errors |
| G-02 | distinct parallel branches remain distinct in compilation and Mason enumeration | digraph edge collapse |
| G-03 | self-loops, touching loops, and non-touching loop families have the audited gains/signs | cycle quotient or determinant error |
| G-04 | DCDR Mason response equals the independently compiled elimination response | same-formula circularity |
| X-01 | one ring and one DCDR satisfy the full relational/compiled/chain/feedback/Mason/Z cross-semantics equality on the common domain | abstraction layers disagree despite local proofs |
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
  circular and `S₃` sign, including whether the observer looks along propagation or into the beam.
- [ ] Confirm whether the first material-medium API should use current raw real field values or wait
  for a stronger dimensional-units refactor.
- [ ] Confirm the upstream home and intended generality of surface traces and integral Maxwell laws.
- [ ] Confirm whether the initial planar-interface PR may state local boundary laws as named
  hypotheses while their Maxwell-integral derivation is developed in a stacked Electromagnetism PR.
- [ ] Confirm the oriented incident/reflected/transmitted `s`/`p` bases and whether Fresnel `p`
  coefficients scale full electric-vector amplitudes or tangential components.
- [ ] Confirm time-reversal pairing and reference-plane conventions before N2b/N6b reciprocity is
  named; this does not block convention-free N2a/N6a work.
- [ ] Confirm chain-matrix port ordering, travelling-wave direction, and scattering-to-chain block
  convention before N3T source-parity names are fixed.
- [ ] Confirm that every ring model distinguishes field from power attenuation and amplitude from
  power coupling coefficients.
- [ ] Confirm the exact `z` versus `q = z⁻¹` convention, the sign in `exp (-s * τ)`, and every
  startup term before S4/S5 identities are named.
- [ ] Confirm the dB/logarithm convention and parentheses of every rejection-ratio formula.
- [ ] Confirm whether each stability condition is strict or non-strict and whether it concerns
  poles, zeros, an internal operator, BIBO behavior, or a source-specific named condition.
- [ ] Replace source decimal examples by human-audited exact data or certified intervals and record
  every source assumption that the Lean statement strengthens, corrects, or rejects.
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
| Scattering matrices are multiplied as source chain matrices | wrong two-port cascade semantics | N3T behavioral chain view and proved scattering/chain conversions |
| A numerical or noncomputable solver is treated as an executable verification oracle | fixtures can agree with an unverified compiler | N4C decidable compilation plus semantic soundness theorem |
| Incident/output exposure maps are collapsed to one untyped matrix | ill-shaped equations and silent port-identification errors | distinct channel wrappers, `E_in`/`E_out`, and projection/completeness proofs |
| A rectangular external response is called a scattering matrix | unproved identification of input and output ports | retain `ModeTransform U Y` until pairing and completeness specialize it |
| The inverse solver is used as the network's definition | singular but meaningful implicit behaviors disappear | define flat relational semantics before well-posed elimination |
| Unmodeled radiation/loss channels are called lossless | misleading unitary claim | complete-channel hypothesis and Poynting normalization theorem |
| Generic plane waves admit a static background | false transversality/phasor bridge | explicit harmonic or zero-static hypothesis |
| Fresnel coefficients are assumed in a component definition | circular “derivation” | solve boundary equations and separate abstract component from EM realization |
| Transmission power is treated as `normSq t` alone | incorrect oblique-interface balance | prove normal-admittance flux factor |
| Geometric series contraction is treated as necessary | excludes well-posed resonators | distinguish algebraic inversion from convergent round-trip expansion |
| Z-transform delay law ignores startup terms | false recurrence result | causal zero extension, ROC, and initial-condition hypotheses |
| Conditional convergence is called absolute convergence | false ROC, product, or BIBO conclusions | distinct convergence predicates and regression T-03 |
| Rationality in delay is confused with rationality in frequency | invalid dispersive model | typed variables and explicit evaluation map |
| Every internal singularity is labeled a transfer-function pole | false poles survive despite input/output cancellation or hidden modes | call them candidate poles until reachability/observability or no-cancellation is proved |
| `s`/`p` coordinates are used at normal incidence without a tangent-frame choice | undefined basis disguised as a canonical formula | require oblique incidence or carry an independently selected tangent frame |
| Signed wavenumber silently changes temporal frequency and circular handedness | inconsistent R/L and `S₃` results | positive carrier frequency with propagation direction represented separately |
| Fresnel `p` amplitudes mix tangential and full-vector conventions | sign and admittance factors disagree across layers | oriented per-wave bases and one explicit coefficient convention |
| A component is only a stored formula with a property label | formula-to-itself proofs provide no behavioral verification | independent behavior specification plus realization theorem |
| Field attenuation or coupling amplitude is used as a power fraction | squared-factor errors in ring observables | distinct parameter documentation, validity predicates, and S-05 |
| Incoherent power is modeled by deleting amplitude cross terms | phase-sensitive behavior is silently changed | N6c coherency transport and explicit decorrelation hypotheses |
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
| O2 modal algebra | done | O1 | predicate characterizations, binary parallel composition, relabeling, and rephasing suites |
| P1a Jones foundations | done | complex algebra | scalar realization, raw Jones action, and intensity suite |
| P1b harmonic bridge | done | P1a, existing harmonic wave | named-frame electric/magnetic field reconstruction |
| P2a general coherency | done | Mathlib PSD audit | generic PSD wrapper and conjugation suite |
| P2b pure coherency | done | P1a, P2a | outer-product/rank/trace/phase/conjugation suite |
| P3a neutral Hermitian basis | done | matrix API audit | neutral basis, bundled coordinate equivalence, compatibility wrappers, and full downstream build |
| P3b-0 neutral positive cone | done | P3a | determinant identity, PSD/radius criterion, and zero-radius-safe construction |
| P3b-1 Stokes/coherency cone | done | P2a, P3b-0 | raw linear reconstruction, exact PSD cone, coherency equivalence, and round-trip suite |
| P3b-2 Jones--Stokes bridge | done | P2b, P3b-1 | coherency-derived components, scaling/phase laws, and normalized canonical-state suite |
| P3c Poincare classification | done | P3b-1, P3b-2 | closed-ball, boundary/interior, exact phase-fiber, rank-one factorization, orbit-quotient, and canonical-axis suites |
| P4 deterministic Mueller | done | P1a, P2a, P3a, P3b-1 | transported real action, Pauli trace/reality, cone, algebra, unitary, and regression suites |
| P5a Jones polarizer/Malus | done | P1a, P2b, P3b-2, P4 | projection, contraction, coherent/intensity Malus, coherency, arbitrary-Stokes Mueller, and convention-regression suites |
| P5b physical Malus bridge | blocked | P5a, E3b | irradiance and normalized-power Malus corollaries |
| P6a retarder core | complete | P1a | unitary Jones action and canonical-state suite |
| P6b-1 retarder representations | complete | P2b, P3b-2, P4, P6a | relative-phase Stokes bridge, exact coherency outputs, arbitrary Mueller block/action, and sign regressions |
| P6b-2 reduced polarization chain | complete | P5a, P6b-1 | ordered polarizer--retarder exact Jones/coherency outputs, arbitrary raw-Stokes action, and connected QWP regression |
| P6b-3 physical observables | blocked | P1b, P5b, P6b-2, E3b | field realization, irradiance, and normalized-power agreement |
| E0 Maxwell public API | complete | existing three-dimensional Maxwell module | exported free-space-constant declarations and downstream build |
| E1 media/macroscopic Maxwell | complete | E0 | medium data, differentiability-aware field predicate, source-free/superposition API, and one-way vacuum bridge |
| E2 material plane waves | in progress | E1, plane-wave vector calculus | real carrier/dispersion/Maxwell/converse, oriented Jones/phasor frame, incidence frames, neutral complex-wavevector decay geometry, off-shell complex carrier, exact real-wave bridge, complex calculus, bilinear complex dispersion, forward/converse complex-carrier Maxwell, exact algebraic and ordinary-field falsification regressions, and interface-oriented side-decaying carrier geometry complete; Maxwell-qualified evanescent/outgoing semantics remain |
| E3s cross-product divergence | ready | Space derivative API review | reusable vector-calculus identity |
| E3a Poynting | blocked | E1, E3s for material conservation | real vacuum/material energy and flux suite |
| E3b Optics normalization | blocked | O1, P1a, E2, E3a | harmonic flux, irradiance, and modal-power bridges |
| E4a local boundary semantics | complete (pointwise explicit-wave slice) | E1, E2 | oriented geometry, medium assignment, signed boundary laws, an independent off-shell three-label configuration, side-medium pointwise traces, and sourceful/source-free local predicates; analytic half-space traces and Maxwell derivation remain E4b, while genuine propagation roles remain E5b |
| E4b derived boundary laws | blocked | E4a, oriented surfaces/integral Maxwell | Maxwell-to-local-boundary theorem |
| E5a conservation/reduction | done | E2, E4a | neutral harmonic uniqueness, real and complex hyperplane projection geometry, primitive independent-frequency electric traces, exact joint-data/character/coefficient equivalences, positive-rate harmonic noncancellation, guarded label matching, explicit frequency/tangential-projection conservation, a reusable fixed-frequency electric predicate, and its directionally guarded equivalence with the primitive two-law electric boundary |
| E5b reflection/Snell/TIR | in progress | E2, E5a | neutral reflection/two-root geometry, material normal-shell and direction-selected root APIs, guarded reflected-root selection and angular reflection, phase Snell laws, critical sine/angle and radicand-sign classification, and unique subcritical positive-phase and supercritical positive-normal-decay transmitted constructions with arbitrary-amplitude carrier lifts complete; Maxwell-qualified evanescent/outgoing semantics and flux-based TIR remain |
| E6 Fresnel/flux | blocked | E3b, E5b | amplitude, admittance-normalized scattering, and flux suite |
| N1 modal completion | done | O1 | completed O2 modal predicate, parallel, and coordinate-change API |
| N2a ports/routing | ready | O2 reindex/direct-sum support | typed convention-free connection API |
| N2b reciprocity metadata | blocked | human convention decision | time-reversal/reference-plane API |
| N3 behaviors | ready | O1 | relational composition, rectangular fan-out, and graph equivalence |
| N3T chain semantics | blocked | N3 | behavior-derived two-port transfer matrices and conversions |
| N4 network equations | blocked | N1/O2, N2a, N3 | flat relational semantics and shaped matrix equations |
| N4C certified compiler | blocked | N4 | executable assembly and semantic soundness |
| N5 elimination | blocked | N4, N4C | unique-solvability/inverse/external-map suite |
| N5F parameterized compilation | blocked | N5, N7 parameterized components | pointwise response-domain theorem suite |
| N5H hierarchy/flattening | blocked | N4, N5 | hierarchy-to-flat semantic equality |
| N6a conservation | blocked | N2a, N5; E3b for physical meaning | passive/lossless composition closure suite |
| N6b reciprocity | blocked | N2b, N6a | convention-aware reciprocity closure suite |
| N6c coherent/incoherent observables | blocked | P2a, N5, N6a | coherency transport and decorrelation suite |
| N7 components | blocked | N2a, O2; E6 only for interface specialization | specification, realization, passivity, and losslessness suite |
| S0 physical microrings | blocked | N3T, N7 | independent ring behavior and primitive realization |
| S1 Mach-Zehnder | blocked | N5, N6a, N7 | transfer and power suite |
| S2/S3 microrings | blocked | S0, N5, N5F, N6a, N7 | pointwise response and observable suite |
| S4 delay transfer | blocked | N5F, N7 | rational-delay evaluation and pole-domain suite |
| S4P poles/zeros/stability | blocked | S4, N5F | reduced response, cancellation, and stability suite |
| S5 Z-transform | ready | Mathlib analysis audit | recurrence/ROC suite |
| S6 Mason | blocked | N5, finite graph audit | combinatorial/matrix equivalence |
| S7 HOL integrated parity | blocked | N5H, S0--S6 | source ledger and cross-semantics suite |
| S7D DCDR parity | blocked | N4C, N5H, N6c, S4P--S6 | audited DCDR topology and observable suite |
| S7C cascade/lattice parity | blocked | N3T, N5H, S0, S4P | finite cascade and lattice suite |
| R1--R5 ray/beam foundations | future | E1/E5b plus focused ray API map | ray, imaging, ABCD, resonator suite |
| Fourier/quantum extensions | future | relevant classical layers | separate API maps and bridges |

## O. Overall completion checklist

The long-running goal is complete only when:

- [ ] the polarization milestone P1a--P6b, including every lettered subpackage, is complete;
- [ ] the electromagnetic-interface milestone E0--E6, including E3s/E3a/E3b and E4a/E4b, is
  complete;
- [ ] the typed finite-network milestone N1--N7, including N3T, N4C, N5F/N5H, and N6a/N6b/N6c,
  is complete;
- [ ] the integrated-photonics milestone S0--S7C reproduces every mandatory source-ledger row and
  includes the cross-semantics oracle;
- [ ] the ray/beam milestone R1--R5 is complete as a foundation, and any claim of extended HOL-suite
  parity additionally discharges its selected named case-study ledger;
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
- U. Siddique et al., [DATE 2014 integrated-optics system
  analysis](https://hvg.ece.concordia.ca/Publications/Conferences/DATE14.pdf), for finite cascades,
  matrix powers, terminated systems, and periodic lattice results.
- U. Siddique et al., [FMICS 2015 signal-flow
  analysis](https://hvg.ece.concordia.ca/Publications/Conferences/FMICS15_1.pdf), for directed
  signal-flow graphs, Mason gain, DCDR, poles, zeros, group delay, and dispersion.
- U. Siddique et al., [ITP 2014 Z-transform
  formalization](https://hvg.ece.concordia.ca/Publications/Conferences/ITP14-1.pdf), for unilateral
  transforms, regions of convergence, shifts, recurrence solutions, and IIR examples.
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

1. P1a, P1b, P2a, P2b, P3a, P3b-0, P3b-1, P3b-2, P3c, P4, and P5a are complete, independently
   reviewed, validated, and integrated.
   Preserve their type boundary: raw Jones intensity is still neither irradiance nor modal power,
   the harmonic bridge reconstructs fields rather than a gauge potential, general coherency still
   carries no Jones-purity assumption, the Pauli coordinates remain basis-fixed but independent of
   Relativity and Optics conventions, the neutral positive cone carries no optical Stokes ordering,
   and zero Jones data has no polarization direction.
2. O2/N1 is complete, including predicate characterizations, binary parallel composition,
   relabeling, and rephasing. N2a typed ports and convention-free routing is now ready; preserve
   the distinction between incident and outgoing channel ends and do not encode feedback as
   ordinary matrix multiplication.
3. Preserve P3c's proved boundary. Its unit-Jones result is an algebraic orbit-set equivalence,
   not a topological equivalence or a continuous choice of representatives; any topology upgrade
   must separately prove continuity and quotient-topology results. Unit Jones intensity remains a
   raw electric-amplitude-squared normalization, not irradiance or modal power.
4. Preserve the completed P6a raw-Jones layer, P6b-1 reduced representation bridge, and P6b-2
   ordered polarizer--retarder system: the reference axis has eigenvalue one, the orthogonal axis
   has relative phase `exp (-I * retardance)`, `M.comp N` applies `N` first, and neither Jones
   unitarity nor fixed Stokes intensity implies electromagnetic power. Keep P6b-3's
   field/irradiance portion blocked on P5b/E3b.
5. Preserve E0's exposure-only public Maxwell repair, the completed E1 material layer, E2a's
   off-shell harmonic carrier: positive frequency and wave number remain independent, the built-in
   `B = (κ / ω) n × E` candidate is not described as Maxwell-derived, and transversality and
   material dispersion are separate; and E2b's completed positive-branch dispersion, exact
   differential laws, source-free Maxwell solution, honest nonzero-amplitude converse, and
   on-shell `B`/`H` relations. Preserve E2c's local oriented-frame Jones embedding, exact
   quadrature and `E`/`B`/`H` realizations, coherent-phase time translation, complete material
   Maxwell endpoint, fixed-vacuum field regression, and proof-bearing incidence geometry:
   `s = normalize (n × k)`, `p = k × s`, Jones order `(s, p)`, explicit tangent selection at
   normal incidence, and exact orientation regressions. Preserve E2e's dimension-generic
   complex-wavevector geometry, non-Hermitian bilinear pairing, convention
   `K = q - I a`, exact positive-normal spatial decay, and interface/power exclusions. Preserve the
   now-complete off-shell complex carrier and exact real-wave bridge: physical fields remain
   ordinary real fields, transversality and material dispersion remain separate, amplitudes are
   relative to a selected origin/carrier phase rather than intrinsically power-normalized, and no
   interface role is inferred from positive decay alone. Preserve the now-complete separate
   calculus layer and its exact `partial_t C = I omega C`, `partial_j C = -I K_j C`, divergence
   through the complex-bilinear pairing, and `K cross A` curl signs. Preserve the now-complete
   bilinear material shell, its `K = q - I a` decomposition, nonzero-wave-vector consequence,
   exact `K cross (K cross E0)` and `K cross B0` coefficients, and real positive-branch bridge.
   Preserve the now-complete forward ordinary-real-field Maxwell layer, especially the off-shell
   magnetic Gauss and Faraday laws and the stronger hypotheses used only by electric Gauss and
   Ampere--Maxwell. Preserve the now-complete guarded converse, especially its two-time amplitude
   recovery, the nonzero electric-amplitude guard needed only for dispersion, and the explicit
   zero-amplitude off-shell degeneracy. Preserve the exact algebraic and ordinary-field regression
   suite, especially its bilinear-versus-Hermitian distinction, direct signed cross calculations,
   two-phase sampling, zero-amplitude guard, complex-null failure, and embedded-image limitation.
   Preserve the completed neutral oriented-affine-hyperplane layer: its normal points from the
   geometric negative side toward the positive side, its closed half-spaces both contain the
   carrier, and its side names have no medium, wave-role, outgoing, or power meaning. Preserve also
   the completed neutral finite exponential-character independence and positive-frequency
   ordinary-real-sum uniqueness layers. Preserve the now-complete primitive independent-frequency
   interface traces, electromagnetic noncancellation, guarded label matching, fixed-frequency
   reduction, reflection/Snell/critical geometry, and the positive-phase subcritical plus
   positive-normal-decay supercritical carrier constructions. The latter is interface-oriented
   decay geometry only: Maxwell-qualified evanescent/outgoing semantics, flux-based TIR, and
   Fresnel power claims remain. Proceed through E3s/E3a/E3b before making those power claims.
6. Keep polarizers and retarders as separate component PR concepts and do not translate Jones
   intensity into physical power before E3b. P5b remains blocked on that bridge even though the raw
   P5a Malus law and P6a retarder intensity preservation are complete.
7. Keep the new source-to-Lean parity ledger as a human-owned gate while developing its independent
   infrastructure: N2a typed routing, N3 behavior semantics, N3T chain views, and N4C certified
   compilation. Do not claim HOL parity from a formula or case-study topic alone.

The next session should not jump directly to a microring formula or stored Fresnel coefficient.
P6b-2 now connects the completed polarizer and retarder stacks in all reduced representations;
P6b-3's physical observables and all Fresnel work must still follow the named electromagnetic
medium, boundary, and flux dependencies. With E2's real material-Maxwell layer, oriented
Jones/phasor realization, incidence frames, complex-wavevector decay geometry, off-shell complex
carrier, exact real-wave bridge, generic carrier calculus, and bilinear material dispersion now
connected with forward and converse ordinary-real-field Maxwell and exact algebraic plus
  ordinary-real-field falsification regressions, neutral oriented-affine-hyperplane geometry,
  positive-frequency ordinary-real-sum uniqueness, primitive interface traces and
  noncancellation, guarded fixed-frequency reduction, reflection/Snell/critical geometry, and both
  canonical transmitted carrier branches now connected, the next physical-optics front is E3s's
  reusable cross-product divergence identity and E3a/E3b's Poynting, irradiance, and modal-power
  normalization. Those layers can then support Maxwell-qualified evanescent/outgoing semantics,
  flux-based TIR, and Fresnel balance without retroactively treating carrier decay as power flow.
  The reflected conservation result must continue to allow zero reflection, and reduced amplitudes
  remain referenced to the interface point. The independent circuit front remains N2a/N3.
