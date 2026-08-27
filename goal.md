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
law, the plane-of-incidence law, reflection, Snell's law, Fresnel amplitudes, and normal
energy-flux balance. Every observable must commute through the relevant raw-field, irradiance,
and power-normalized-mode bridges.

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

The integrated-photonics track states the closed microring coefficients `R` and `T` inside its
behavior predicate (DATE'14 Def. 3; SysCon'15 Def. 3, p. 565) and then extracts the corresponding
matrices. The electromagnetic track is different: SPIE'14 proves the plane-of-incidence,
reflection, frequency-conservation, Snell, and one-linear-mode Fresnel results from its stated
interface predicate (Thms. 4.5--4.9, p. 8). It does not derive that predicate from a formalized
Maxwell system.

Physlib reaches this baseline when the corresponding results are obtained from typed components
and a common network semantics, with every division, inverse, infinite sum, and stability statement
carrying its real nondegeneracy or convergence hypotheses.

**The Concordia corpus reports no numerical or simulation cross-validation of any formalized
result.** MATLAB appears only as future work in FMICS'15 (p. 176) and NSV'16 (p. 44), and as a box
in the proposed MCS'14 architecture (Fig. 12, p. 25). Instead, proof is used to audit published
literature: the sources report a missing Sylvester hypothesis (DATE'14, PDF p. 5), two missing
microring assumptions (SysCon'15, p. 569), incorrect stability values (FMICS'15, p. 175), and
missing transfer-function terms plus a sign mismatch (NSV'16, p. 44). Physlib's independent
SAX/FDTD comparison lane is therefore a separate validation axis, not a source-parity capability.

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

The source's paraxial interface law is postulated directly in Thesis'15 Def. 3.7 (p. 44), while
deriving the small-angle model from wave or electromagnetic optics is left as future work
(pp. 124--125). Requiring R1's paraxial law to be an explicit model assumption or a proved limit,
and relating it to E5b, is thus a Physlib strengthening. The same thesis does contain one genuine
shared-algebra bridge: its ray `interface_matrix` and `system_composition` are reused unchanged as
the ABCD action on Gaussian `q` parameters (Thms. 4.5--4.7, pp. 78--79).

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

Here "bridge coverage" means bridges between physical models. The HOL corpus does reuse the
ray-system ABCD algebra for Gaussian beams, but its cross-level unification remains a proposal
(MCS'14, p. 31), and ray optics as an approximation of wave/electromagnetic optics remains future
work (Thesis'15, p. 125). Its ray-level and electromagnetic Fabry--Perot developments are separate
and have no relating theorem, while the circuit track shares no type or lemma with the ray,
electromagnetic, or quantum tracks.

The foundation-level differentiator is E4b. SPIE'14's chain is a prose appeal to Maxwell theory,
then `boundary_conditions` (Def. 4.2, p. 6), then `is_plane_wave_at_int` (Def. 4.4, p. 7), which
also postulates `H = (1 / (η₀ k₀)) k × E` and the three wavenumber magnitudes, and only then
the proved interface laws. MCS'14 prints Maxwell equations as prose mathematics (pp. 11--12) but
formalizes no curl, divergence, or PDE. E4b's Maxwell-to-boundary theorem therefore closes a step
the source never formalized; it remains mandatory for physical Optics v0.1.

### B.4. Separate parity claims

The project has three independently auditable completion claims. None implies either of the
others.

1. **Physical Optics v0.1 parity:** the connected electromagnetic, polarization, interface, and
   observable slice in section A.1.
2. **Integrated-photonics parity:** the source-backed component, chain, network, recurrence,
   Z-transform, signal-flow, microring, cascade, and resonator capabilities in sections H.3 and
   H.4.
3. **Extended HOL optical-suite parity:** the geometrical-, Gaussian-, and resonator-optics work in
   section H.5 and any later named case studies explicitly added to its parity ledger.

Integrated-photonics parity does not wait for the stronger Maxwell-to-boundary derivation in E4b;
physical v0.1 does. Conversely, a completed physical v0.1 does not establish the transfer-system,
Z-transform, or signal-flow capabilities of the integrated-photonics sources.

S1's Mach--Zehnder system, N7's reusable coupler/delay component laws, and S7C's full `M × N`
lattice theorem are Physlib extensions, not contributors to the parity claim. The corpus mentions
an MZI only as motivation (SysCon'15, p. 562), represents couplers only by scalar coefficients, and
proves only DATE'14's uncoupled row sublattice; it contains no `M × N` lattice theorem.

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

The ledger must not inherit hypotheses omitted by the source prose. The current primary-source
audit records these mandatory repairs:

| Required hypothesis or domain | Source statement that omits it |
|---|---|
| `t ≠ 0` for the factor `1 / (I * t)` | DATE'14 Thm. 1 / SysCon'15 Thm. 1 |
| `R ≠ 0` and `1 - r² τ exp (-I * δ) ≠ 0` | DATE'14 Thm. 2 |
| `M₁₁ ≠ 0` before terminated transmission/reflection division | DATE'14 Thm. 5 |
| `C * q + D ≠ 0` for the Gaussian ABCD quotient | Thesis'15 Thms. 4.5--4.7 |
| positivity of both logarithm operands and the logarithm domain | SysCon'15 Thm. 7 |
| convergence of each infinite wave sum | SPIE'14 Thm. 5.6 |

Conversely, retain and credit assumptions that the formal sources added to repair their cited
literature: `-1 < re M₁₁ < 1` in DATE'14 (PDF p. 5), the additional DCDR stability and
resonance conditions in FMICS'15 (p. 174), and `0 < x_r` with `‖x_r * u₁ * u₂‖ < 1` in
SysCon'15 (p. 569).

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

### D.2. Relevant implemented foundations

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
- `Optics.Polarization.PositiveNormalDecayFrame` supplies the complex-bilinear `s`/`p` basis,
  unique raw TE/TM coordinates for every bilinearly transverse amplitude, full-vector/fixed-plane
  conversion, and exact Hermitian-versus-bilinear diagnostics. Its planar dielectric connector
  supplies the negative-radicand Maxwell carrier and zero stored-normal one-period mean flux.
- `Optics.Evanescent` supplies the named nonzero lossless half-space classification, its exact
  side-normal decay representation and electromagnetic scaling, Maxwell and mean-flux
  consequences without assigning support or outgoing semantics.
- `Optics.Interfaces.PlanarDielectric.SupercriticalPolarization` supplies the canonical
  negative-radicand Jones connector and its exact nonzero-data characterization.
- `Optics.Mode.Embedding` supplies dimension-independent bundled amplitude restriction, together
  with restriction and zero extension transforms along finite mode-family embeddings, their
  selected identity and ambient range projector, and passive zero extension of rectangular
  transforms. It deliberately treats omitted coordinates as algebraically discarded modal data
  rather than as physical absorption.
- `Optics.Network.Port` supplies dependent port/channel families, nominal incident and outgoing
  endpoint types, presentation-independent local bidirectional connections, the typed scattering
  adapter, and convention-free unit-gain routing with its exact local `C * S` action order. It
  deliberately stops at one local connection.
- `Optics.Network.ConnectionFamily` supplies proof-carrying indexed connection families with
  physical-port endpoint uniqueness, the dependent connected-channel embedding, the blockwise
  fixed-point-free mate, exact total routing over connected channels, and the exact equivalence
  between connected-channel membership and endpoint-port membership. It does not itself supply
  external complements, ambient routing, or netlists.
- `Optics.Network.PartialRouting` zero-extends connected routing to a total ambient
  outgoing-to-incident internal-wiring transform. Its two Gram matrices are the connected range
  projectors; it is globally passive in normalized modal coordinates and power-preserving exactly
  on inputs supported on connected outgoing channels. Complement zeros mean no internal feedback
  or no internal-wiring contribution, not termination or absorption.
- `Optics.Network.ExternalChannel` defines the exact channel complement, identifies it with the
  dependent sum of modeled modes over unconnected physical ports, and supplies the incident
  injection `E_in`, outgoing exposure `E_out`, and restriction readout `E_outᴴ`. Their exact
  coordinate, isometry, Gram, cross-zero, and projector-completeness laws give complete nominal
  boundary decompositions. Its `C b + E_in u` assembly has exact connected/external action and
  additive normalized modal power. These coordinate operations are not a source, detector,
  termination, network energy balance, or feedback solution.
- `Optics.Network.LinearBehavior` supplies singular-safe complex-linear component relations,
  embeds linear maps and finite mode transforms as graphs, and proves identity, relational series,
  and independent parallel composition laws. It characterizes total single-valued behaviors,
  extracts their unique complex-linear maps behind an explicit proof gate, and proves graph round
  trips plus identity, series, and parallel functionality closure. Its source-neutral feedback
  construction retains every complete state satisfying paired forward and return relations. Its
  concrete regressions distinguish cascade order, partial and multivalued behavior, singular
  functionality, and disjoint parallel branches without assigning physical realizability,
  causality, passivity, or losslessness.
- `Optics.Network.RectangularBehavior` supplies algebraic copy, coherent sum, heterogeneous branch
  selection, and direct-coefficient weighted split/combine graphs. The three-four-five regression
  proves a one-sided identity and a nonidentity reverse-order idempotent with nonzero kernel, while
  exact modal-power sentinels prevent interpreting copy or coherent sum as passive wiring.
- `Optics.Network.FlatNetlist` owns heterogeneous components and proof-carrying connections on one
  aggregate boundary. It derives `S`, `C`, `E_in`, `E_out`, and `E_outᴴ`, retains all complete
  feedback states, and projects their external relation without assuming existence, uniqueness,
  or an inverse.
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

- [ ] outgoing/limiting-absorption semantics, kept separate from positive-side decay;
- [ ] Maxwell-derived complex boundary laws, outgoing semantics, and admittance-normalized
  scattering;
- [ ] a physical time-reversed external-port pairing and convention-aware reciprocity. The local
  two-device X-01 agreement between the singular-safe Redheffer route, `FlatNetlist`, N5H
  composition, and N5 elimination is complete; the broader Mason/system cross-semantics oracle
  remains open. Canonical external scattering packaging and normalized modal network conservation
  are complete;
- [ ] reusable beam splitters, mirrors, polarization components, and dielectric-interface
  scattering; fixed-carrier propagation, a directional coupler, Mach--Zehnder, and one-bus
  all-pass microring slices are complete;
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
  N3 + N2a typed-endpoint core --> N3T two-port chain semantics
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
half-space-decaying square-root branch; any outgoing interpretation is a separate limiting-
absorption or radiation condition. An evanescent field is not an ordinary positive-power
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
Poynting-flux, modal-power, or electromagnetic-passivity theorem is included in the raw component
files; the separate P5b follow-up supplies the first two for its propagating plane-wave family.

#### P5b. Physical Malus bridge

Candidate location: the Optics normalization bridge beside E3b, not the Jones core file.

Status: complete on the fork. The propagating material-wave irradiance and actual mean-flux slice,
the explicit singleton Jones-to-Maxwell-mode carrier bridge, and the conditional E3b transport to
normalized modal power are connected through the same analyzer output.

Deliverables:

- [x] translate P5a's squared-Jones-intensity theorem to irradiance for the plane-wave family covered
  by E3b; and
- [x] translate it through E3b to `ModeAmplitude.power` only for the proved flux-normalized mode
  family.

The completed first slice proves single- and sequential-polarizer irradiance laws, arbitrary-input
irradiance contraction, and Malus' law directly for the actual one-period-averaged Poynting vector.
The field theorem constructs both waves with the same medium, propagation frame, positive
frequency, phase convention, period origin, and observation point. It is an ideal thin-analyzer
model: the discarded component's fate and the component's internal, reflected, absorbed, and
thermal fields are not modeled. Local infinite-plane-wave irradiance is not aperture or modal
power, and contraction alone is not called electromagnetic passivity.

Exit achieved: `linearPolarizer_scaledWave_eq` proves that the analyzer's modal output is exactly
the material wave constructed from P5a's Jones output. Its modal-coordinate power obeys Malus'
law, and separate incident/outgoing `IsApertureFluxOrthonormal` proofs transport that identity to
actual integrated one-period normal Poynting flux. The exact regression uses wave impedance
`1 / 2`, opposite input/output normals, complex coordinate `1 + I`, and a `pi / 4` analyzer to pin
input power two, output power one, both flux signs, and the coherent output carrier.

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

Status: complete on the fork. Export locations:
`Optics/Polarization/HarmonicMaterialWave.lean` and
`Optics/Systems/PolarizerRetarderPhysical*.lean`.

Deliverables:

- [x] a connected example starting at P1b's `harmonicWaveX` bridge and passing through a P5a
  polarizer and P6a wave plate; and
- [x] field realization, irradiance, and normalized-power observables, using P5b/E3b before any
  physical-power claim.

Exit achieved: the reduced connected chain is realized as electromagnetic fields and its
irradiance, modal-coordinate power, and signed actual aperture flux agree through named P5b/E3b
normalization bridge theorems. This coherent singleton result is not a complete-device power
balance and makes no partially polarized or coherency-mixture claim.

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
- [x] a positive-normal-decay complex-bilinear `s`/`p` frame normalized by the shell
  wavenumber, including raw TE/TM coordinate recovery, the exact full-vector/fixed-plane `p`
  conversion, the shell-wavenumber cross-product quarter-turn, a connected transverse
  positive-medium carrier, exact affine-plane-referenced Jones data, zero stored-normal mean
  flux, and the exact `K = (5, 0, -4 I)`, `beta = 3` sign and norm regressions at both origin and
  nonzero plane reference points;
- [x] a named nonzero half-space evanescent-field classification for the connected carrier,
  including its exact positive-side decay representation and Maxwell/mean-flux consequences; and
- [ ] outgoing or limiting-absorption semantics, without identifying them with decay geometry.

Exit: incident, reflected, transmitted, and side-decaying candidate carriers share one field API;
the connected negative-radicand positive-normal-decay carrier is Maxwell qualified and has its
separate nonzero evanescent-field label, while outgoing interpretation remains pending.

#### E3s. Cross-product divergence identity — complete

Owner: SpaceAndTime.

- [x] the pointwise real three-dimensional identity
  `div (f × g) = g · curl f - f · curl g` under `DifferentiableAt` hypotheses, together with its
  function-level form under global `Differentiable` hypotheses; and
- [x] neutral ownership in SpaceAndTime, with no electromagnetic field role, constitutive law,
  complex-phasor convention, boundary integral, energy, flux, irradiance, or power semantics.

Exit achieved: E3a can derive energy balance from Maxwell equations without reproving general
vector calculus inside Electromagnetism.

#### E3a. Electromagnetic energy and Poynting flux — complete

Owner: Electromagnetism.

- [x] instantaneous energy density and Poynting vector;
- [x] the sourced local Maxwell work identity
  `div S = -E · JFree - E · ∂ₜ D - H · ∂ₜ B` for `S = E × H`, using the differentiability already
  carried by `IsMacroscopicMaxwell`;
- [x] the fixed time-independent nondispersive-medium Poynting theorem
  `∂ₜ u + div S = -E · JFree`;
- [x] the conventional constitutive form `u = 1 / 2 * (E · D + B · H)`, nonnegativity, and the
  exact storage-term time derivative under E1's fixed-medium constitutive laws;
- [x] the pointwise zero-free-current and source-free local conservation corollaries; and
- [x] the explicit potential-derived real-vacuum equation
  `∂ₜ [1 / 2 * (ε₀ E · E + μ₀⁻¹ B · B)] + div [μ₀⁻¹ (E × B)] = 0`, with no extra factor of `c`.

Exit achieved: instantaneous real electromagnetic energy flow exists independently of Jones or
finite-mode conventions. The results are pointwise differential laws; harmonic averaging,
integrated boundary flux, irradiance, and modal power remain E3b.

#### E3b. Harmonic flux and Optics normalization — complete on the declared finite synthesis image

Owner: Optics, importing E3a.

- [x] local harmonic time average and complex-phasor formula with the factor, cross-product order,
  and conjugation derived from the adopted peak-phasor convention;
- [x] the propagating material plane-wave mean Poynting vector and nonnegative irradiance,
  including impedance and the exact raw-Jones-amplitude bridge;
- [x] signed normal flux density of a propagating material plane wave, plus a strict positive local
  mean-flux predicate whose nonzero referenced-wave specialization is equivalent to strict phase
  direction without assigning an incident, transmitted, or outgoing role;
- [x] a pointwise bridge from Euclidean phasor realization to the componentwise real part of a
  positive-exponential complex-carrier scaling, without broadening the Jones foundations;
- [x] local electric and material magnetic-field-strength phasors for the off-shell complex
  carrier, with the actual one-period mean Poynting vector equal to their harmonic-flux formula
  and to the stored-reference formula scaled by the spatial factor's squared modulus;
- [x] the plane-referenced propagating material Jones connector and its guarded zero-field form,
  with actual one-period vector and signed-normal flux at the stored plane point;
- [x] zero normal average flux for a bilinearly transverse, Maxwell-qualified
  positive-normal-decay transmitted wave at every point and period start;
- [x] a measured-profile integral with an explicitly supplied measure rather than an inferred
  geometric aperture-area measure;
- [x] the Hermitian signed-power flux pairing for supplied finite phasor-profile families, with its
  self-pairing equal to the closed time-averaged normal Poynting expression, mutual flux
  orthogonality, normalization, and
  incident/outgoing sign conventions proved before extending a one-mode result to coherent
  superpositions; and
- [x] an explicit map from raw Jones field amplitudes to material plane-wave irradiance; and
- [x] an explicit map from a declared normalized measured profile family to
  `ModeAmplitude.power` on its finite synthesis image; and
- [x] a physical specialization connecting that abstract profile family to Maxwell-qualified,
  common-positive-frequency propagating modes, with an explicit aperture parameterization or
  justified geometric area measure and an integrated actual one-period Poynting-flux theorem.

The completed local slice defines componentwise Euclidean phasor realization and conjugation,
derives the scalar coherent-product average, and proves for arbitrary locally realized
common-frequency fields that the one-period average of the actual instantaneous
`ThreeDimension.poyntingVector` is
`(1 / 2) Re (Ephasor cross conj Hphasor)`. The frequency is positive, the period may begin at any
time, and exact linear and quadrature regressions independently pin the factor one half and
second-phasor conjugation. The supplied phasors are local at the selected spatial point. Thus a
complex plane-wave connector must include its spatial factor there rather than silently dropping
attenuation. No Maxwell, irradiance, normal-flux, aperture-power, modal-normalization,
outgoing-wave, or evanescence conclusion is part of this first slice.

The separate pointwise realization bridge now identifies `Phasor.realizeEuclidean` with the
componentwise real part of a positive-exponential carrier scaling. It is isolated from the Jones
foundations so later complex-carrier field connectors can reuse the exact sign and scalar-action
convention without forcing WaveEquation imports on every polarization consumer.

The completed complex-material-wave connector now keeps the common spatial factor in both local
`E` and `H` phasors, realizes the actual ordinary-real fields from them, and derives their
one-period mean Poynting vector without on-shell hypotheses. Its reference-amplitude form exposes
`Complex.normSq (spatialFactor x)`. Exact transverse TE and TM Maxwell fixtures give respective
mean vectors `(5 / 6, 0, 0)` and `(15 / 2, 0, 0)` at the origin, while positive-depth displacement
scales the TE mean by `exp (-8 * depth)`, not the amplitude factor `exp (-4 * depth)`. These
connector identities alone assign no interface, outgoing, evanescent-field, Fresnel,
aperture-power, or modal-power semantics.

The completed positive-normal-decay follow-up proves the zero-normal-flux conclusion without
smuggling dispersion into the algebra. For `K = q - I * alpha * n`, tangent real phase `q`, purely
normal positive attenuation, and a complex-bilinearly transverse electric phasor, every real
multiple of `K cross E₀` used as `H₀` gives zero mean Poynting component along `n`. The actual
ordinary-real fields inherit this result at every point and arbitrary period start. At the planar
dielectric layer, a positive-normal-decay transmitted candidate already supplies positive-medium
dispersion; adding the same explicit transversality both certifies the fields as a source-free
macroscopic Maxwell solution and specializes the mean-flux result to the interface's stored
normal. The transverse TM fixture still has instantaneous vector `(15 / 2, 0, -6)` at quarter
phase, while an on-shell but nontransverse fixture has mean `(5 / 6, 0, -5 / 6)`. Thus the result
is genuinely averaged, permits nonzero tangential flow, and cannot drop bilinear transversality.

The completed material-wave slice now proves that formula first for local electric and
magnetic-field-strength phasors and then for the actual ordinary-real Maxwell material wave at
every spatial point and arbitrary period start. The proof keeps the full local spatial phase, the
coefficient is nonnegative, and its equality with the norm of the averaged Poynting vector earns
the name `materialPlaneWaveIrradiance`. This is flux density for an infinite propagating plane
wave; aperture integration and modal normalization remain separate steps. An exact instantaneous
identity and complementary quadrature-versus-linear regressions also show that a positive-`I`
quadrature state has constant instantaneous mean flux, whereas a linear state has a zero
quarter-period instantaneous sample but nonzero one-period mean.

The completed signed-normal follow-up projects that actual averaged vector onto an arbitrary
oriented plane. Relative to the stored normal it yields irradiance times the propagation unit
vector's signed normal component; relative to either geometric side it yields irradiance times the
cosine of the propagation direction's side-relative angle. Negative cosine and grazing zero flux
remain valid, while the geometric sides acquire no incident, reflected, transmitted, outward, or
outgoing meaning. The theorem is for the propagating ordinary-real material wave and supplies no
evanescent-field conclusion.

The completed measured-profile slice takes an explicit measure on an arbitrary profile-coordinate
type rather than inventing a geometric surface measure. Its Hermitian pairing uses the declared
peak-phasor convention, is complex-linear in the first profile, conjugate-linear in the second,
and has self-pairing equal to the integral of the stored-normal component of the existing closed
time-averaged Poynting expression. Finite coherent synthesis first expands to the complete double
sum of modal cross terms. Only a pairwise-integrable, mutually flux-orthogonal, unit-normalized
family then reduces that sum to `ModeAmplitude.power`, with incident and outgoing signs selected
by an explicit role relative to the stored normal. The conclusion holds on the supplied synthesis
image. It does not assert that the family is complete, that arbitrary supplied profiles satisfy
Maxwell or share a physical carrier frequency, that the supplied measure is geometric area, that
raw Jones coordinates are power normalized, or that omitted and evanescent channels carry
ordinary positive modal power. Exact unequal-cell and nonorthogonal regressions make the measure,
slot convention, role signs, coherent terms, and mutual-orthogonality requirement load-bearing.

The physical specialization now packages zero-attenuation, transverse, dispersion-matched complex
plane-wave carriers in one homogeneous medium at a common positive angular frequency. Complex
modal coordinates scale carrier phasors before ordinary-real realization; finite synthesis is
proved to remain a source-free fixed-medium Maxwell solution. Its actual one-period Poynting mean
is then integrated either against the earlier supplied profile measure or against a
`GeometricAperture`'s ambient two-dimensional Hausdorff measure restricted to a measurable planar
region. Under the same explicit pairwise integrability, mutual flux orthogonality, unit
normalization, and incident/outgoing role hypotheses, the resulting actual integrated flux is the
appropriate signed `ModeAmplitude.power`. Exact singleton regressions pin the `E`/`H` convention,
complex coefficient phase, arbitrary period start, Maxwell preservation, and the value `25` for
the coordinate `3 + 4 I`.

Exit achieved on the supplied finite synthesis image. This does not prove modal completeness,
absence of omitted channels, raw-Jones normalization, interface boundary laws, or positive-power
semantics for evanescent or absorptive channels.

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
itself construct half-space-supported fields or analytic one-sided traces, establish genuine
one-sided illumination, or package on-shellness. E4b now supplies the general full-half-space trace
foundation; propagation roles and branches remain separate later hypotheses.

Exit: the primitive independent-frequency ordinary-real pointwise boundary-data problem is stated
honestly from explicit local laws, at the same abstraction level as the audited HOL interface work.

#### E4b. Maxwell derivation of the boundary laws

Owner: SpaceAndTime and Electromagnetism.

- [x] local open-half-space domains, genuine one-sided traces, and the continuous-restriction
  constructor;
- [x] the thin-cell regularity and limit-interchange hypotheses needed beyond pointwise traces;
- [x] integral curl and divergence laws under the explicit finite-sheet carrier and
  witnessed-interchange premise;
- [x] literal integral Maxwell equations with volume and surface sources, including explicit
  integrability witnesses for every displayed path, face, and volume pullback; and
- [x] derivation that E4a's tangential and normal boundary predicates hold under the corresponding
  thin-loop and pillbox limits.

The neutral weak-calculus prerequisite now includes selected-coordinate splitting, pushforward of
tangential distributions onto coordinate hyperplanes, and the identity that differentiating a
selected positive-coordinate Heaviside distribution in the inward `+e_i` direction gives the
corresponding boundary delta. An independent `Fin 2` Gaussian regression distinguishes selected
and swapped coordinate hyperplanes, while the retained one-dimensional Gaussian regression pins
normalization and the sign under normal reversal. An anisotropic `Fin 2` point-source fixture also
pins generic pushforward coefficient preservation and coordinate placement. The Space-side bridge
transports these coordinate distributions through the standard orthonormal basis and represents
distribution-bounded ambient extensions only on their selected strict half-spaces. For the field
which is zero on the negative side and constant on the positive side of an origin coordinate
hyperplane, it proves that the inward coordinate derivative is the constant-coefficient sheet and
that this sheet is the transported generic coordinate-hyperplane pushforward. Direct `7`, `-7`, and
swapped-coordinate regressions pin the coefficient, orientation, and selected sheet independently.
This does not prove a variable-trace derivative formula on an arbitrary oriented plane, derive a
weak or measure-valued Maxwell equation, or derive the finite-sheet premise.

The local-calculus chain is complete. `PlanarRectangleLocalStokes.lean` and
`AffineBoxLocalDivergence.lean` prove oriented Stokes and divergence identities for independent
half-cell fields without cross-carrier continuity. `FiniteSheetPremise.lean` then names the
explicit carrier-source identifications and witnessed time/integral interchanges, and
`FiniteSheetIntegralMaxwell.lean` derives the four literal finite Maxwell laws and all four local
jump laws. Positive and hostile regressions make the premise load-bearing and independently pin
the carrier signs. The remaining stronger step is deriving `HasPlanarFiniteSheetMaxwellPremise`
itself from weak or measure-valued Maxwell equations.

Exit: once that premise derivation is supplied, the local laws used by E5a/E5b/E6 become physical
theorems from Maxwell equations without a separately supplied finite-sheet model. Physical Optics
v0.1 requires this stronger exit; integrated-photonics work does not.

This exit is intentionally stronger than SPIE'14: its boundary predicate is stated (Def. 4.2,
p. 6), justified only by a prose citation from Maxwell theory, and combined with additional
in-medium field and wavenumber assumptions in Def. 4.4 (p. 7). Snell and Fresnel are then genuine
consequences of that predicate, but the Maxwell-to-boundary step itself is absent from the corpus.

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
  joint electric amplitude-balance predicates;
- [x] a guarded equivalence relating its amplitude equations to the primitive two-law electric trace
  problem, with the non-null guard used only to derive label matching in the primitive-to-reduced
  direction and no claim of reconstructing either magnetic boundary law;
- [x] a medium-dependent tangential-`H` complex amplitude, its stored-plane-point reference, and
  exact realization as the actual ordinary-real tangential magnetic field, while deliberately
  stating only the valid one-way zero-electric-amplitude implication; and
- [x] a one-way reduction from the primitive full local boundary with arbitrary free surface charge
  and zero free surface current to the referenced tangential-`H` balance, under transmitted
  frequency matching and the reflected zero-referenced-tangential-`H`-amplitude-or-frequency-
  matching alternative, with an electric-phase-matching convenience wrapper and no hidden
  magnetic converse;
- [x] neutral projection of exactly aligned full-vector Jones frames into a common oriented-plane
  frame, giving the signed coordinate laws `(J0, chi J1)` and `(-J1, chi J0)` for tangential
  electric data and its propagation quarter-turn, including grazing `chi = 0` without division;
- [x] a stored-plane-point material Jones connector that fixes the real propagating material wave
  vector and complete referenced electric phasor, derives transversality, dispersion, Maxwell
  satisfaction, the exact `v inverse` referenced magnetic-induction phasor, and the exact
  `Z inverse` referenced tangential magnetic-field-strength phasor, while retaining a role-neutral
  zero-electric-and-Jones-amplitude guard with arbitrary dummy carrier labels; and
- [x] aligned common-plane-frame scalarization of the referenced tangential-`E` and tangential-`H`
  balances into the four unsolved full-vector Jones equations with signed unit-direction normal
  components and the correct negative- and positive-medium intrinsic admittances. This step assumes
  neither common frequency nor phase matching, divides by no cosine or amplitude, and does not
  claim normal-`D` or normal-`B` redundancy.

Exit: every later fixed-frequency electric-boundary calculation and the required tangential-`H`
amplitude equation are connected one way to the independent-frequency physical problem, and no
conservation conclusion is hidden in its own premises. The aligned planar-frame scalar equations
are now available; redundancy of normal-`B` continuity, canonical incidence-frame specialization,
and their general Fresnel solution remain explicit later steps.

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
- [x] the law of the plane of incidence: tangential phase matching places the transmitted and
  every active reflected phase vector in the real span of the incident phase vector and interface
  normal, while exact hyperplane reflection supplies an unguarded reflected specialization;
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
- [x] Maxwell qualification and zero stored-normal one-period mean flux for the canonical raw
  TE/TM-amplitude carrier built from the side-decaying complex transmitted branch;
- [x] boundary-amplitude total-internal-reflection characterization: the referenced electric and
  magnetic balances select the complex `s`/`p` coefficients of the positive-normal-decay branch,
  both reflected coefficients have unit modulus and explicit positive-time-convention phase, and
  arbitrary incident Jones data retains its raw reflected intensity;
- [x] connected reflected and incident-plus-reflected actual normal-flux balance against the
  transmitted branch's proved zero normal mean flux, including separate- and superposed-wave
  predicates and a zero-inclusive guarded reflected branch;
- [x] a named nonzero half-space evanescent classification for the connected branch, with the
  zero-Jones case characterized exactly; and
- [ ] any outgoing or limiting-absorption interpretation, kept distinct both from positive-side
  decay and from an ordinary positive-power propagating mode.

Exit: the geometric laws follow from the field and boundary setup.

#### E6. Fresnel amplitudes and flux balance

- [x] the four referenced tangential-`E`/`H` equations expressed in an exactly aligned common
  planar frame, with full-vector Jones coordinates, signed normal factors, intrinsic admittances,
  and an exact nonzero-reference-point regression that solves one rational fixture;
- [x] real propagating full-vector `s`- and `p`-polarized reflection and transmission coefficients,
  guarded cross-multiplied and quotient scalar solution lemmas, positive physical denominator
  values, and a connected theorem deriving all four component laws from the referenced vector
  balances without assuming a nonzero incident amplitude;
- [x] algebraic normal-incidence signs `r_p = -r_s` and `t_p = t_s`, the transmitted-grazing
  case, the zero-reflection dummy-carrier branch, and exact agreement with the independently
  solved nonzero-phase fixture;
- [x] derive the reflected normal guard and aligned-frame hypotheses from canonical incidence
  frames, electric phase matching, material dispersion, and explicit positive-incident plus
  active-negative-reflected normal selection: the referenced connector identifies those signs
  with phase direction, the selected complex reflection descends to real propagation-vector
  reflection, positive tangential phase scaling aligns the incident and transmitted canonical
  `s` axes, and hyperplane reflection aligns the active reflected axis. Canonical component,
  separate-wave flux, and actual-superposition wrappers preserve completely arbitrary reflected
  carrier, frame, direction, and frequency labels in the zero-field branch by locally reframing
  only its proved-zero Jones data;
- [x] selected-tangent normal-incidence relations for positive- and negative-side propagation,
  their exact second-axis and fixed-plane `p` signs, and a connected boundary specialization that
  preserves arbitrary reflected carrier and frame data when the reflected field is zero;
- [x] a proof-independent canonical non-normal `s`/`p` frame predicate and a guarded
  incident/reflected/transmitted role bundle consumed by the canonical Fresnel amplitude and flux
  endpoints; the bundle keeps phase matching, material connectivity, propagation signs,
  reflection, and power semantics separate, makes reflected canonicality conditional on a nonzero
  electric field, and remains deliberately unavailable at normal incidence;
- [x] explicit total fixed-plane tangential-`p` reflection and transmission coefficients,
  division-free full-vector conversion laws, normal-incidence reconciliation, and exact normal and
  oblique regressions;
- [x] the positive-normal-decay complex-bilinear `s`/`p` frame, its fixed-plane tangential
  conversion factor `-I alpha / beta`, raw TE/TM amplitude embedding, shell-wavenumber
  cross-product quarter-turn, and exact `5-4-3` sign/norm regression needed to scalarize the
  supercritical boundary problem;
- [x] exact affine-plane referencing of the canonical transmitted Jones amplitude, including a
  nonzero stored-point regression that detects omitted or reversed carrier phase;
- [x] complex `s`/`p` Fresnel denominators and full-vector coefficients, exact compatibility with
  the real propagating API, fixed-plane tangential-`p` conversion, guarded scalar solvers, and a
  connected theorem deriving all four coefficients from the referenced electric and magnetic
  balances with the canonical positive-normal-decay transmitted candidate;
- [ ] Brewster-angle results with the exact magnetic/nonmagnetic and positivity hypotheses needed
  for existence;
- [x] total-internal-reflection unit reflection modulus and explicit `Real.Angle` phase results,
  including the closed positive-time-convention `2 * arctan` formulas, physical specialization to
  the canonical normalized decay factor, fixed-plane `p` sign separation, and arbitrary-Jones
  reflected-intensity preservation;
- [x] reconstruct the unit-modulus `s` and `p` coefficients from their named phases, package one
  reflection as a diagonal Jones transform, prove the sign-locked retarder parameter
  `rho = phi_s - phi_p`, raw Jones unitarity/intensity and Mueller equivalence, connect the matrix
  action back to the boundary-selected reflected wave, and prove conditional matrix-self-
  composition quarter-wave laws with a physically shell-compatible exact negative-quarter-wave
  design regression; interpreting self-composition as two bounces still requires external frame
  identification, so this is the verified polarization kernel of a future Fresnel rhomb, not its
  two-face geometry or path-phase model;
- [x] the full-vector power transmission factor with the common normal-admittance multiplier
  `(Y2 chi_t) / (Y1 chi_i)` for both polarizations;
- [x] denominator-local unnormalized flux identities and physical `R + T = 1` for lossless real
  propagating interfaces, including transmitted grazing, arbitrary complex Jones polarization,
  zero input, and a connected balance of the three separate waves' actual mean normal fluxes;
- [x] prove pointwise incident-reflected normal-interference cancellation, common-interval and
  guarded own-period additivity, and a fixed-frequency connected theorem identifying the separate
  negative-side sum with the actual mean normal Poynting flux of the superposed
  incident-plus-reflected field; and
- [x] connect the complex boundary-selected coefficients to the propagating incident/reflected
  actual normal-flux and superposed-field APIs, and combine them with the canonical transmitted
  candidate's zero normal mean flux without treating the evanescent field as a positive-power
  port; and
- [x] construct the algebraic two-side scalar kernel obtained by completing each established
  left-incident s/p Fresnel column with the square root of its normal-admittance flux factor, prove
  its exact action and losslessness from `R + T = 1`, and pin the unequal-admittance radicals and
  signs independently; this completion is not a reverse-incidence Maxwell derivation; and
- [ ] the complete bidirectional Fresnel multiport matrix derived from both incidence directions
  and normalized by square roots of normal admittance, with unitarity
  proved in those power coordinates for strictly positive-admittance propagating channels rather
  than for raw electric-field amplitudes, grazing channels, or TIR evanescent fields.

SPIE'14 supplies Fresnel amplitudes for one linear polarization only, and its own scope label is
internally inconsistent: p. 7 says the paper focuses on TE, while the Fabry--Perot application on
p. 11 says its Fresnel use is restricted to TM. The parity ledger records the inconsistency rather
than selecting one label; Physlib's separate `s` and `p` results are stronger than that source row.

Exit: the full Optics v0.1 example proves Jones/Stokes/component/interface results from connected
definitions.

### H.3. Typed finite-network milestone

#### N1. Modal algebra completion — complete

O2 now supplies the converse characterizations, parallel closure, convention-free coordinate
changes, and sparse restriction/zero-extension maps required by the network layer.

- [x] dimension-independent bundled amplitude restriction and finite-dimensional restriction and
  zero extension along mode embeddings, with exact coordinate action, `R * E = 1`, an ambient
  star range projector `E * R`, and the correct isometry, contraction, passivity, arbitrary-input
  action, exact output-power, and zero-extended-transform laws;
- [x] the exact restriction-power boundary: ambient modal power is preserved precisely when every
  omitted coordinate has zero amplitude;

#### N2a. Ports, channels, and convention-free routing — in progress

- [x] a `PortModeFamily` with dependent flattened channel type `Σ p, Mode p`, with finiteness required
  only by finite operations;
- [x] nominally distinct incident and outgoing channel-end types with explicit canonical equivalences
  and no coercion erasing the boundary;
- [x] a typed connection between distinct ports carrying an explicit equivalence between their mode
  fibers;
- [x] the local mate permutation and fixed-point-free involution, including invariance under
  exchanging the connection's endpoint presentation;
- [x] proof-carrying indexed connection families with global physical-port no-endpoint-reuse,
  while finiteness is required only by finite connected-channel operations;
- [x] the canonical component adapter `Incident → Outgoing` and ideal unit-gain routing
  `Outgoing → Incident` obtained by reindexing, with exact endpoint action and power
  preservation proved;
- [x] covariance of ideal routing under input and output channel relabeling, including the exact
  exchanged-presentation routing law;
- [x] matched-gauge covariance of connection routing under channel-end rephasing; arbitrary
  independent endpoint rephasings do not leave a unit-gain wire unchanged;
- [x] convention-free port/network power, passivity, and losslessness predicates that do not
  require time-reversal data;
- [x] the dependent connected-channel embedding, blockwise mate, and exact unit routing on every
  connected channel, including cross-connection zeros and normalized modal-power preservation;
- [x] the total ambient internal-wiring transform obtained by zero-extending connected routing,
  with exact connected and complement action, input and output range-projector Gram laws, global
  normalized-modal passivity, and power equality exactly for amplitudes supported on connected
  outgoing channels; complement zeros model neither termination nor absorption;
- [x] an explicit external-channel complement with typed incident injection `E_in`, outgoing
  exposure `E_out`, and readout `E_outᴴ`, including structural endpoint partitions, cross-zero and
  projector-completeness laws, a channel-versus-port equivalence, and an empty-mode regression
  proving that an unconnected physical port need not contribute a channel; and
- [x] the typed local `C * S : Incident → Incident` action order, without claiming feedback
  solvability or assigning component gains, path phase, or delay to a wire.

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

- [x] a relation/submodule for linear component behavior;
- [x] embedding of `ModeTransform` as a graph;
- [x] a membership characterization for the embedded graph;
- [x] identity, series, and parallel behavior composition;
- [x] rectangular copy, coherent-sum, branch-selection, and weighted split/combine behaviors,
  without pretending copy is wiring or a passive square optical splitter;
- [x] agreement between relational composition and functional composition for graph behaviors;
- [x] proof-gated extraction and round trip of a total single-valued behavior as a linear map; and
- [x] no invertibility requirement merely to state a component.

Exit: transfer matrices are derived views of suitable behavior, not the only possible component
definition.

#### N3T. Two-port chain semantics

- [x] backward-first travelling-wave states and an independently stated relational two-port
  behavior between oriented left and right reference planes;
- [x] a left-to-right chain-transform view only when the behavior determines every right state
  uniquely from its left state;
- [x] a canonical lossless relabeling adapter from `ScatteringMatrix (ι ⊕ κ)` through the typed
  `Incident → Outgoing` boundary to ordered left/right scattering coordinates, with exact entries,
  amplitude action, graph behavior, and label round trip;
- [x] scattering-to-chain conversion derived from the regrouped behavior exactly when the
  right-incident to left-outgoing transmission block is bijective, with its exact four-block
  formula and graph equality proved without a full scattering-matrix inverse;
- [x] chain-to-scattering conversion under bijectivity of the exact leading chain block, plus both
  behavioral and matrix round trips and independent scalar/noncommutative formula regressions;
- [x] unconditional behavioral equivalence and round trips for the reversible regrouping between
  incident/outgoing scattering coordinates and backward-first reference-plane states;
- [x] series connection as chain-matrix multiplication, proved from relational composition;
- [x] agreement between the canonical two-device N5 netlist elimination and Redheffer feedback on
  their common well-posed domain, with unconditional agreement at the relational layer; and
- [x] relational right-load termination with complete internal-wave solutions, exact well-posedness,
  proof-gated reflection and forward-response extraction, noncommutative loaded-chain block formulas,
  and zero-return agreement with the existing scattering blocks.

Exit: the transfer/chain calculations used by the audited cascade and microring sources are
derived views of the same component behavior, not illicit multiplication of scattering matrices.

The convention-explicit, source-neutral N3T core is complete. Source-specific microring parameter
dictionaries and the DATE/SysCon two- and four-port matrix specializations belong to S0 and S7C;
they consume this API and do not reopen the generic chain-semantics milestone.

#### N4. Scattering netlists and equations

- [x] component-owned channel spaces used through the existing incident/outgoing wrappers, retaining
  explicit ownership of every physical port and local mode;
- [x] block-diagonal assembly of heterogeneous component scattering matrices, with exact
  same-component, cross-component-zero, and componentwise amplitude-action laws;
- [x] a routing transform `C : A_out → A_in`, an input exposure `E_in : U → A_in`, and an output
  exposure `E_out : Y → A_out`, each derived from typed endpoint selections;
- [x] proofs of the exposure isometries and projection identities, and of routing/exposure
  disjointness and completeness;
- [x] derivation of `b = S*a`, `a = C*b + E_in*u`, `y = E_outᴴ*b`, and
  `(I - C*S)*a = E_in*u`;
- [x] a singular-safe `FlatNetlist.behavior` defined by existential internal amplitudes, together
  with a theorem that it is the relational composition of the assembled component graph, return
  relation, state projection, and external readout;
- [x] an order-free dependent-family relation requiring every individual component graph,
  proved equal to the assembled component graph as the typed analogue of parallel composition;
  and
- [x] invariance under wiring-preserving relabelling of connected channels, instantiated by
  connection-index reindexing and endpoint-presentation exchange. The ambient `C` and
  `1 - C * S` are literally equal; external layers are equal up to the canonical
  identity-on-channels relabelling. Component reordering and phase gauge remain separate
  covariance statements.

Exit: network equations come from a typed netlist rather than being supplied independently.

#### N4C. Certified finite-netlist compiler

- [x] finite executable `Fin`-indexed component, port, mode-fiber, incidence, local-gain, and
  bidirectional physical-connection data, with explicit mode maps in both directions;
- [x] decidable well-formedness reflected exactly to mutual mode-map inversion and physical-port
  endpoint injectivity, rejecting self-wiring, same-side or mixed-end reuse, and wire-level
  fan-out. Connections are bidirectional data; incident/outgoing channel direction is enforced by
  N4's derived map types rather than stored as an unverified direction flag;
- [x] executable construction of `S`, `C`, `E_in`, `E_out`, and the transposed output readout,
  together with the implicit matrix `1 - C * S`;
- [x] a soundness theorem equating the evaluated compiled matrix equations with N4's flat
  relational semantics, including a singular multivalued regression at zero external input, a
  nonzero-input exposure witness, and a non-self-inverse three-mode routing cycle;
- [x] an algebraic backend over an appropriate field, with an executable normalized coefficient
  representation and a proof-exact univariate rational-function interpretation;
  and
- [x] evaluation into `ℂ` away from every required denominator, proved to commute with compilation.

Exit: exact executable fixtures test an implementation that is proved correct with respect to the
kernel semantics; a noncomputable complex matrix inverse is not the sole oracle.

#### N5. Well-posed elimination

- [x] unique-solvability definition for the complete incident/outgoing state;
- [x] equivalence with trivial homogeneous kernel, injectivity/surjectivity, determinant nonzero, and
  matrix invertibility in the finite complex case;
- [x] proof-gated complete-state and rectangular external response transforms, including
  `E_outᴴ * S * (I - C*S)⁻¹ * E_in`, with every domain and codomain shape visible;
- [x] agreement of those formulas with the singular-safe relational semantics, plus invariance of
  well-posedness and covariance of the response under wiring-preserving presentation changes;
- [x] a separate square scattering specialization on the exact external-channel complement,
  using the canonical incident/outgoing wrapper pairing while explicitly withholding any
  time-reversed physical-port or reciprocity claim;
- [x] reflection-free series cascade as a specialization, with the later directional
  transmission block on the left; and
- [x] Redheffer star products for declared matched block partitions, with the particular feedback
  block's invertibility hypothesis stated explicitly and reflective feedback kept distinct from
  one-way cascade. The singular-safe relation, proof-gated matrix formula, canonical two-device
  `FlatNetlist` realization, N5H `closeBehavior` agreement, common-domain N5 response agreement,
  and independent regular/singular regressions are complete. No converse minimality of the local
  pivot gate, associativity, or identity element is claimed.

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

- [x] a hierarchical network whose child components may themselves be well-formed networks;
- [x] a relational flattening operation preserving typed external ports, mode compatibility, and
  conventions, with no well-posedness assumption required merely to flatten;
- [x] equality between hierarchical relational semantics and the semantics of the flattened
  netlist, with the N-08 fixture supplying independent raw-equation membership, universal forward
  forcing, and a mis-lifted-port negative control;
- [x] functional packaging of a child as a scattering/response component only after that child's
  well-posedness and external-channel pairing have been proved; and
- [x] transport of a `PortConnectionFamily` along an equivalence of port families, with covariance
  of incident assembly, external readout, and relational closure. This supports replacement of an
  inner family by another with the same boundary relation and literal three-stage append
  associativity after the canonical port-family transport. The fixed-inner-wiring congruence is
  also complete. All N-08 reuse hypotheses are structural `Fintype` assumptions on channel
  indices, not physical assumptions.

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

The reusable coupler, beam-splitter, and fixed-carrier propagation laws in this package are
Physlib-original. The HOL corpus uses coupler and propagation coefficients as bare scalars inside
larger formulas and proves no independently reusable component law for them.

- [x] an algebraic reflectionless two-port substrate with arbitrary directional mode transforms,
  independently stated amplitude equations and an exact zero-reflection block realization; this
  is not yet a matched propagation, coupler, beam-splitter, physical-port, reciprocity, or
  material-realization law;
- [x] its stacked exact normalized-modal-power decomposition and passivity/losslessness
  classifications, with the directional hypotheses proved necessary as well as sufficient;
- basic component definitions may start after N2a and the O2 direct-sum/reindexing support, before
  the general eliminator is complete;
- [x] the algebraic fixed-carrier matched-propagation phase and normalized-modal-amplitude
  transmission law on typed two-port channel labels, with independent directional equations, a
  zero-reflection scattering realization, exact modal-power scaling, passivity in the valid
  amplitude range, and losslessness at unit amplitude;
- [x] the matched-propagation physical-port presentation, with owned left/right mode fibers,
  pinned raw-to-physical channel coordinates, transported independent behavior and scattering,
  exact realization, modal-power transport, and direct `ScatteringComponentFamily` consumption;
- [x] an ideal real-quadrature directional-coupler law with explicit `-I` cross phase,
  independent bidirectional behavior, reflectionless scattering realization, exact `t² + k²`
  normalized-modal-power factor, passive/unitary parameter predicates, and losslessness;
- [x] its four independently wireable physical-port presentation, pinned nested channel order,
  exact behavior and scattering transport, and direct `ScatteringComponentFamily` consumption;
- [ ] component-owned physical-port packaging consumed by `ScatteringComponentFamily`: the
  beam-splitter and mirror packages are complete, while polarization and interface primitives
  remain;
- [ ] frequency-parameterized propagation and actual time/group-delay statements under N5F, with
  their frequency-domain, causality, and dispersion hypotheses explicit;
- mirror and termination;
- a named beam-splitter specialization with its own optical-port behavior and explicit unitary
  parameter constraints, rather than an alias claimed to satisfy the independent-specification rule;
- polarization components embedded into multimode channels;
- dielectric interface scattering connected to E6;
- an independent behavioral specification for every component, followed by a realization lemma
  proving that its matrix or relation satisfies that specification; and
- explicit passivity and losslessness proofs under each component's real parameter hypotheses,
  rather than merely storing or assuming those classifications.

Exit: every core component has orientation, an independent behavioral specification, a realization
lemma, parameter validity, and intensity/power classification suitable for automatic system
proofs. Reciprocity extensions are added only after N2b/N6b conventions are available.

The shipped S0 propagation parameters remain fixed-carrier and nondispersive. S4's local group
delay applies to selected proof-gated network response entries, so it does not by itself discharge
the open component-level frequency-family and physical time-delay item above.

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

#### S1. Mach-Zehnder interferometer — complete Physlib extension, no HOL source

No Concordia source defines or analyzes a Mach--Zehnder interferometer; SysCon'15 mentions it only
as a motivating citation (p. 562). S1 is valuable system verification, but it is not a parity row.

- [x] depend on the N5 solver and the N6a/N7 conservation and component laws, rather than supplying an
  interferometer-specific transfer formula;
- [x] construct it solely from two couplers and two arms;
- [x] prove complex output amplitudes and both output powers;
- [x] prove lossless power balance; and
- [x] specialize to balanced, dark-port, and phase-sensing cases.

The implementation is an explicit feed-forward `FlatNetlist`; its N5 well-posedness is proved for
every parameter record, and the closed amplitudes are derived from `responseTransform`. Balanced
phase-zero and phase-`π` regressions independently follow the channel equations, while N6 supplies
the all-phase normalized-modal power balance. The phase-ratio theorem identifies the relative arm
phase factor under a nonzero-input hypothesis. This is not a HOL-parity claim and supplies no
time-domain delay, dispersion, polarization, reciprocity, or material model.

#### S2. All-pass and add-drop microring resonators — amplitude/series slices complete

- [x] construct the one-bus all-pass ring as an explicit `FlatNetlist` from the proved N7
  directional coupler and matched-propagation components;
- [x] derive its through transfer amplitude from the N5 response transform;
- [x] prove well-posedness exactly equivalent to `1 - t * gamma ≠ 0`, including a singular-input
  kernel witness for the converse;
- [x] prove the multiple-round-trip geometric series only under `‖t * gamma‖ < 1` and identify
  it with the algebraic-elimination response where both views apply;
- [x] identify the exhaustive two-channel bus boundary, derive both directional response laws,
  and prove that the singular-safe relabeled behavior equals an independently stated
  reflectionless two-port law on the exact solve gate;
- [x] prove that the backward-first chain view exists exactly when the bus transmission is
  nonzero, derive `diag(H⁻¹, H)` under that independent pivot gate, and reconstruct the typed
  scattering law by the generic round trip;
- [x] construct the two-bus add-drop ring as an explicit feedback network; and
- [x] derive its through/drop transfer amplitudes, exact solve gate, and convergent-series bridge.

For the all-pass ring, the input-side and through-side bus channels exhaust the external boundary.
The independently derived reverse response completes a typed left/right scattering law without
assuming reciprocity; the matrix realization is functional only on the existing solve gate.

The add-drop implementation is a four-port `FlatNetlist` made from two directional couplers and
two fixed-carrier half arcs. Its complete-state well-posedness is equivalent to
`1 - t₁ * t₂ * gamma ≠ 0`; N5 elimination derives both transfer amplitudes. Their totalized
round-trip series acquire the geometric-series interpretation only under contraction. The equal
half-arc attenuation/phase split fixes a model and a drop-port reference-plane convention. Power
observables, gated parameter recovery, rejection ratios, and nondispersive free spectral range are
supplied by S3 below. Extrema, reciprocity, material dispersion, and source-parity claims beyond
the explicitly gated DATE/SysCon/SFG identifications recorded below remain later work.

#### S3. Ring observables — complete as a Physlib layer; source bridge is explicitly gated

- [x] derive observables from the S2 pointwise N5F response and the N6a/N7 normalization and
  conservation theorems;
- [x] through/drop power responses;
- [x] lossless power balance;
- [x] named resonance and antiresonance phase conditions;
- [x] critical coupling and extinction conditions;
- [x] rejection ratio with positive numerator/denominator and explicit log convention; and
- [x] free spectral range under an explicit nondispersive group-index hypothesis.

The observable powers are squared moduli of the S2 response amplitudes, while lossless balance is
routed through N6 componentwise conservation. Critical-coupling extinction has a converse under
the stated parameter gates, and parameter recovery is phase-resolved or explicitly
critical-coupling-gated rather than an intensity-only identifiability claim. Frequency periodicity
uses N5F's response domain and a constant group-index model. Resonance and antiresonance are named
phase conditions, not extremum theorems. The separate source-bridge modules identify the audited
DATE two- and four-port equations and the SysCon/SFG add-drop formulas with these N5 responses
under explicit unitary, denominator, pivot, port-order, principal-root, and logarithm-base gates.
IP-03, IP-04, and IP-05 are discharged and IP-12 is conditional. The printed SysCon power
denominator and its unspecified logarithm base keep IP-06 and IP-07 open. No bandwidth, linewidth,
quality factor, response-derived group delay, reciprocity, or material realization is inferred.

#### S4. Delay-variable transfer functions

- [x] build on N5F's parameterized compilation and response domain;
- [x] formal delay indeterminate `q` and evaluation map;
- [ ] rational transfer functions for finite-delay linear networks whose component entries are
  rational in the declared finite family of delay variables;
- [x] proof that evaluating `q = exp (-s*τ)` agrees with the direct frequency response on the
  pointwise well-posed domain;
- [x] at the abstract reduction layer, singular internal operators as candidate poles and reduced
  response poles identified under the explicit pointwise `NoPoleCancellation` gate; the stronger
  network reachability/observability criterion remains the open S4P item below; and
- [x] no claim of rational dependence on physical frequency without the required model.

The shipped component-entry layer retains numerator/denominator representatives and evaluation
domains, then compiles them through N5F and reparameterizes the proof-gated response along Laplace
and reciprocal-Z maps. Symbolic rational elimination of the external response is still required
before the third item can be checked. The internal-determinant/reduced-response API proves the
candidate-to-actual inclusion and its converse under an explicit no-cancellation predicate, but a
network-level reachability/observability or no-cancellation theorem remains open
(`Physlib/Optics/Systems/DelayTransfer/Poles.lean:187-236`).

#### S4P. Poles, zeros, stability, and frequency response

- [x] reduced rational responses and their evaluation domains;
- [x] zeros and transfer-function poles after cancellation, distinct from candidate singularities of
  the internal network operator;
- [x] degree and finiteness bounds;
- [ ] a reachability/observability or explicit no-cancellation criterion connecting internal
  singularities to actual poles;
- [x] discrete-time Schur stability and BIBO equivalence only for a stated proper causal rational
  class;
- [x] frequency response under the chosen `q = exp (-s * τ) = z⁻¹` convention; and
- [x] **Physlib extension (source claim unverified):** group delay and dispersion through a local
  logarithmic derivative or another branch-audited construction, not an unqualified global
  complex argument, implemented for selected N5F network-response entries on explicit interior,
  differentiability, and nonzero-response domains.

Names must state literal mathematical content. In particular, source terminology that calls all
zeros inside the unit disk a “resonance condition” is not adopted without a separate physical
resonance theorem. The audited source definition is
`is_resonant_psp system ↔ ∀ z ∈ zeros system, ‖z‖ < 1` (FMICS'15 Def. 7, p. 170), with
`zeros` defined by nonzero numerator roots (Def. 6); that paper proves no separate physical
resonance theorem. The implemented local domains and formulas are at
`Physlib/Optics/Systems/DelayTransfer/GroupDelay.lean:79-186`, and their proof-gated N5F
network-entry lift is at `GroupDelay.lean:237-391`.

#### S5. Difference equations and Z-transform

Lane ownership: a controller-managed worker begins S5 after N5 is registered. The spine agent does
not implement or coordinate this lane; it reviews and merges the completed worker branch. The
neutral mathematics package is now complete in the limit-at-infinity formulation described below.

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
  convergence for the selected causal rational class;
- inverse Z-transform and uniqueness under the journal source's exterior-circle ROC hypotheses;
  and
- connection between coefficient recurrences and the formal power-series view.

Source parity here targets both ITP'14 and its JAL'18 journal extension. ITP'14's ROC is defined by
absolute summability and leaves inverse/uniqueness as future work (p. 497); JAL'18 adds the
exterior-circle ROC shape (Def. 19) and makes inverse Z-transform and uniqueness mandatory parity
rows (Thms. 15--16, p. 894). Keeping conditional and absolute convergence distinct remains a
Physlib strengthening. `Physlib.Mathematics.ZTransform.Inverse` recovers every sample by a proved
limit at infinity and proves causal uniqueness; the source's literal Taylor-coefficient formula
is deliberately not claimed and remains recorded in `tbd.md`.

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

Current fork status: the neutral mathematics layer supplies node equations, exact unique-
solvability, node- and edge-indexed path/loop enumeration, distinguished terminals, the graph-
determinant/system-determinant identity, classical forward-path Mason gain, linear-system
extraction, and independent definition-level regressions. `FlatNetlist.feedbackSignalFlowGraph`
now extracts the scalar graph `C * S` from the N5 feedback operator `1 - C * S`; its graph-
determinant gate is exactly relational well-posedness. Entrywise Mason gains reconstruct the
proof-gated feedback inverse, and `FlatNetlist.responseTransform_eq_masonResponseTransform`
proves equality with the typed external N5 response. A nonsymmetric netlist fixture gives
independent value agreement on its principal symmetric `I`-by-`I` loop. Its forward-path numerator
`I`, loop-family determinant `2`, and Mason gain `I / 2` are expanded independently; separately
derived N5 elimination gives `1 + 4 * I`, which equals the direct path plus the enumerated loop response
without either agreement theorem. A singular determinant is obtained directly from a known
noninjective feedback operator. The generic S6/N5 bridge is therefore complete. Ring- and DCDR-
specific G-04/X-01 instantiations remain in the S7 system suite rather than being inferred from
this generic theorem. The all-pass ring now supplies the first system instance: on
`HasNonzeroDenominator`, its relational behavior is identified with the complete N5-extracted
Mason response, and an independently defined two-node circulation model has determinant
`1 - t * gamma` and reconstructs the same through response. No reduction from the complete graph
is claimed. Direct path/loop enumeration and raw channel elimination meet independently at the
exact `1 / 7` fixture. Its exhaustive bus boundary and complete reflectionless typed scattering
law are also identified on the same solve gate. On the additional exact gate `throughTransfer ≠
0`, its backward-first chain matrix is `diag(throughTransfer⁻¹, throughTransfer)` and converts
back to the packaged typed scattering law. The causal recurrence is now derived through the same
rational N7/N5F netlist, with its absolute ROC, algebraic solve gate, contraction/Schur condition,
and chain pivot kept distinct. On their explicit intersection, one theorem identifies the causal
transform, rational response, circulation series, fixed N5 response, complete Mason response,
typed scattering, backward-first chain, and original relational behavior. This completes the ring
instance of X-01. The DCDR instance now adds its independently gated nominal backward-first chain
to the same causal-Z, rational, feedback, N5, Mason, scattering, and relational agreement. The
two-system regression packages those two agreements as a conjunction on their respective common
domains and proves their fixture values differ; it does not equate the ring and DCDR responses.
Thus X-01 is complete only in this systemwise sense.

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
- the NSV'16 18-node PANDA Vernier resonator with both through- and drop-port responses;
- transfer amplitude, spectral power, resonance, and rejection-ratio results;
- at least one difference-equation/Z-transform derivation; and
- at least one signal-flow/Mason derivation proved equal to network elimination; and
- [x] for an eligible ring and the DCDR case, a systemwise cross-semantics theorem equating
  relational behavior, compiled elimination, chain response, feedback algebra, Mason gain, and
  recurrence/Z response for each system on its own common domain. The joint theorem is a
  conjunction and does not assert equality of the two devices' response values.

The cross-semantics theorem keeps three conditions distinct: algebraic feedback requires an
invertible internal operator; an infinite round-trip series requires contraction or summability;
and a Z-transform identity additionally requires causality and a stated convergence region.

For source-backed two-ring through/drop parity, NSV'16's 18-node PANDA Vernier resonator is the
mandatory comparator. The DCDR remains a separate audited circuit case rather than standing in for
the PANDA through/drop pair.

#### S7D. DCDR parity suite

- the human-audited eight-node, eleven-edge topology with parallel edges retained;
- the transfer result by N5 elimination and independently by S6 Mason gain;
- active/passive, unit-delay, and multiple-delay specializations;
- [x] coherent and incoherent interpretations through N6c, where `incoherent` means diagonal or
  mutually decorrelated second-order coherency data only; this does not identify the coherent N7
  DCDR with FMICS'15's separately printed incoherent coefficient model;
- poles, zeros, and stability results; and
- an exact or interval-certified, human-audited version of the source's reported unstable passive
  parameter case.

#### S7C. Cascade and Physlib-original lattice suite

- arbitrary heterogeneous microring cascades;
- an identical-`N` cascade as a chain-matrix power;
- a Sylvester/Chebyshev closed form with its actual determinant and trace-domain assumptions;
- terminated reflection and transmission;
- the source-backed uncoupled row-sublattice result;
- coupled row/column decompositions and the full `M × N` lattice theorem, explicitly classified
  as Physlib-original rather than DATE'14 parity;
- the source-mapped SFG-TR'14 add-drop case and NSV'16 PANDA Vernier case; and
- no quadruple-ring parity row unless the FMICS'15 prose claim is located in a primary formal
  source and independently verified.

Exit for H.4: the integrated-photonics results in the cited HOL program can be reproduced as
instances of a more general typed system API, and every mandatory row in the integrated-photonics
parity ledger is discharged by a public declaration and regression.

### H.5. Foundational ray, imaging, Gaussian-beam, and resonator milestone

Lane ownership: a separate controller-managed worker develops R1--R5. The spine agent skips
implementation in that lane and reviews and merges exact completed cutoffs presented by the
controller. The R1--R5 foundational slices are integrated. The E5b cross-layer bridge, R3's
representative subsystem, source-style resonator unfolding, and the additional R5 resonator
topologies remain open, so this milestone is still in progress.

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
- Fabry-Perot and ring resonators; and
- agreement between ray-stability and Gaussian fixed-point views where applicable.

Phase-conjugated ring resonators and the associated Thesis'15 chaos definitions and theorems
(Defs. 5.6--5.9/5.12 and Thms. 5.9--5.10/5.19--5.20) are outside this foundation milestone. They
remain deferred to the separate RS-07 scope and physics review named by this section's exit.

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

Independent numerical checks are a Physlib extension, not a HOL-parity row: the audited Concordia
corpus reports no numerical or simulation cross-validation of a formalized result.

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
| E-00d | the exact `K = (5, 0, -4 I)`, `beta = 3` complex `s`/`p` frame and the `5-12-13` planar negative-radicand configuration prove the incident shell and, from an unrelated transmitted slot, recover the TM carrier, `E_tan = (4, 0, 0)`, `H_tan = (0, 3 I, 0)`, Maxwell, and zero stored-normal mean flux | complex-axis, branch, hidden stored-data reuse, tangential-conversion, impedance, or quarter-turn sign error |
| E-00e | the exact active `K = (5, 0, -4 I)` TM carrier is half-space evanescent only into the positive side with decay rate four, its on-shell zero-amplitude copy fails only the activity guard, and the canonical planar Jones carrier exercises the same classification | side-sign erasure, zero-field misclassification, or disconnected interface semantics |
| E-01 | interface at normal incidence specializes consistently using a selected tangent frame | hidden `s`/`p` degeneracy or normal-direction errors |
| E-01a | the `(3/5, 0, 4/5)` planar fixture places the reflected and transmitted phase vectors in the span of the incident vector and interface normal | unproved or misoriented plane-of-incidence law |
| E-02 | reflection and Snell laws follow from phase matching | assumed rather than derived geometry |
| E-03 | Fresnel boundary equations imply the amplitude formulas | sign and impedance errors |
| E-04 | an unequal-admittance exact supercritical fixture derives both complex coefficient pairs from one simultaneous `s`/`p` boundary solution, proves unit reflected modulus and Jones-intensity preservation, and retains the canonical positive-normal-decay transmitted carrier | admittance swap, full-vector/fixed-plane `p` sign, normalized-decay, or disconnected-boundary errors |
| E-04a | translating the interface reference point multiplies the canonical transmitted Jones data by its exact complex spatial factor | omitted, conjugated, or reversed affine-reference phase |
| E-04b | a physically shell-compatible exact irrational-admittance design has incident normal factor `sqrt 2 / 2`, positive normalized decay, the exact negative-radicand identity, TIR phases `pi/4` and `pi/2`, and one-copy retarder parameter `-pi/4`; matrix self-composition is a negative quarter-wave plate up to common phase, while the unequal-admittance boundary fixture independently equals the same diagonal matrix action | off-shell design data, p-s sign, retarder convention, composition order, coefficient ordering, or disconnected-boundary errors |
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
| S-01 | **Physlib extension met:** balanced Mach-Zehnder outputs and power balance | coupler phase convention errors |
| S-02 | **met:** all-pass and add-drop elimination agree with their contractive round-trip series | feedback orientation errors |
| S-03 | **met:** microring transfer, power, named-phase, critical-coupling, and rejection specializations | hidden nondegeneracy assumptions |
| S-04 | **met:** the physical add-drop realization yields both exact transfer responses | disconnected ring formula |
| S-05 | **met:** add-drop power and rejection ratio satisfy their positivity and logarithm domains | amplitude/power or dB-convention error |
| S-06 | the audited eight-node DCDR response agrees between elimination and Mason gain | graph topology or path/loop error |
| S-07 | DCDR pole/zero/stability theorems include the audited unstable parameter case | cancellation or strictness error |
| S-08 | **Physlib extension:** the `M × N` lattice flattening agrees with its row/column decomposition | hierarchy or cascade-index error |
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

- `lake-lock exe cache get`;
- `lake-lock build`;
- `lake-lock exe lint_all`, recording repository-baseline failures separately from new failures;
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
2. inspect the integration branch, current reusable worktree, upstream base, and outstanding agent
   reviews, and confirm at least 30 GB is free on `/`;
3. select the earliest unblocked work package on a critical path;
4. reuse the current worktree on a focused feature branch from the latest appropriate foundation;
5. record any new convention or architecture decision in this file before dependent APIs spread;
6. implement one coherent concept with its required physics-facing lemmas;
7. validate locally and request independent review of statements as well as proofs;
8. commit without modifying unrelated user work, merge into `optics/development`, and push only to
   the user's fork;
9. update the progress ledger and `tbd.md`; and
10. continue to the next unblocked package rather than stopping merely because one commit landed.

Every Lean or Lake invocation in this machine-local workflow must go through `lake-lock`. Let the
wrapper wait on its machine-wide mutex without inspecting or counting Lean processes; one build
normally owns several worker processes. Do not create additional worktrees, and stop to recover
space if `/` has less than 30 GB free before a Lean job.

If a package is blocked by a missing general theorem, place that theorem in the correct parent API
and keep the Optics import direction clean. If it is blocked by a human convention, license, or
upstream ownership decision, record the exact decision needed and work on an independent package.

## L. Decision gates requiring explicit human confirmation

- [x] Confirm the phasor time convention, positive-frequency convention, and resulting right/left
  circular and `S₃` sign, including whether the observer looks along propagation or into the beam.
- [x] Confirm whether the first material-medium API should use current raw real field values or wait
  for a stronger dimensional-units refactor.
- [x] Confirm the upstream home and intended generality of surface traces and integral Maxwell laws.
- [x] Confirm whether the initial planar-interface PR may state local boundary laws as named
  hypotheses while their Maxwell-integral derivation is developed in a stacked Electromagnetism PR.
- [x] Confirm the oriented incident/reflected/transmitted `s`/`p` bases and whether Fresnel `p`
  coefficients scale full electric-vector amplitudes or tangential components.
- [x] Confirm time-reversal pairing and reference-plane conventions before N2b/N6b reciprocity is
  named; this does not block convention-free N2a/N6a work.
- [x] Independently confirm before upstreaming the fork's DATE-compatible convention, with SysCon
  corroborating the four-wave arrows and behavior: states are backward-first, scattering
  `(aL, aR; bL, bR)` regroups as `((bL, aL), (aR, bR))`, and the left-to-right scattering
  conversion inverts the right-incident to left-outgoing block. The fork uses only
  convention-explicit names while this human verification remains open.
- [ ] Confirm that every ring model distinguishes field from power attenuation and amplitude from
  power coupling coefficients.
- [ ] Confirm the exact `z` versus `q = z⁻¹` convention, the sign in `exp (-s * τ)`, and every
  startup term before S4/S5 identities are named.
- [x] Confirm the dB/logarithm convention and parentheses of every rejection-ratio formula.
- [ ] Confirm whether each stability condition is strict or non-strict and whether it concerns
  poles, zeros, an internal operator, BIBO behavior, or a source-specific named condition.
- [ ] Replace source decimal examples by human-audited exact data or certified intervals and record
  every source assumption that the Lean statement strengthens, corrects, or rejects.
- [x] Confirm the exact HOL source licenses before adapting any source implementation.
- [x] discharged as the three-way record of `decision-L14.md` Rev. 5 — Class A (18 sources)
  body-verified; Class B (Gu 2017, Reshef 2017, de Bernardis 2025) consumed-but-body-unverified —
  de Bernardis body-read with a documented abstract/body discrepancy — each with integrity notes
  at every consumer; Class C open and non-load-bearing with evidence; standing promotion rule in
  force.
- [ ] Conduct all maintainer/reviewer communication and certify every contributed line. Deferred
  HUMAN-ONLY; residual act: at the trigger, personally certify the exact chosen PR diff and conduct
  every maintainer/reviewer communication.

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
| O2 modal algebra | done | O1 | predicate characterizations, binary parallel composition, relabeling, rephasing, and finite mode-embedding suites |
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
| P5b physical Malus bridge | done | P5a, E3b | exact Jones/modal carrier agreement, cosine-squared coordinate power, and conditional incident/outgoing normalized actual-flux transport |
| P6a retarder core | complete | P1a | unitary Jones action and canonical-state suite |
| P6b-1 retarder representations | complete | P2b, P3b-2, P4, P6a | relative-phase Stokes bridge, exact coherency outputs, arbitrary Mueller block/action, and sign regressions |
| P6b-2 reduced polarization chain | complete | P5a, P6b-1 | ordered polarizer--retarder exact Jones/coherency outputs, arbitrary raw-Stokes action, and connected QWP regression |
| P6b-3 physical observables | done | P1b, P5b, P6b-2, E3b | potential-derived input bridge, ordered material carrier, irradiance, modal power, separately normalized signed actual flux, and hostile phase/axis/sign regressions |
| E0 Maxwell public API | complete | existing three-dimensional Maxwell module | exported free-space-constant declarations and downstream build |
| E1 media/macroscopic Maxwell | complete | E0 | medium data, differentiability-aware field predicate, source-free/superposition API, and one-way vacuum bridge |
| E2 material plane waves | in progress | E1, plane-wave vector calculus | real carrier/dispersion/Maxwell/converse, oriented Jones/phasor frame, incidence frames, neutral complex-wavevector decay geometry, off-shell complex carrier, exact real-wave bridge, complex calculus, bilinear complex dispersion, forward/converse complex-carrier Maxwell, exact algebraic and ordinary-field falsification regressions, interface-oriented side-decaying carrier geometry, its complex-bilinear s/p frame, transverse positive-medium Maxwell qualification, and named nonzero half-space evanescence are complete; separate outgoing semantics remain |
| E3s cross-product divergence | done | Space derivative API | pointwise and function-level real three-dimensional div-cross identity under first differentiability |
| E3a Poynting | done | E1, E3s | sourced local work balance, fixed-medium Poynting theorem, and source-free/explicit vacuum conservation |
| E3b Optics normalization | complete on finite synthesis image | O1, P1a, E2, E3a | common-positive-frequency propagating Maxwell families, finite complex synthesis, actual one-period integrated Poynting flux, restricted two-dimensional Hausdorff aperture area, and signed modal-power identification are complete; no modal completeness claim |
| E4a local boundary semantics | complete (pointwise explicit-wave slice) | E1, E2 | oriented geometry, medium assignment, signed boundary laws, an independent off-shell three-label configuration, side-medium pointwise traces, and sourceful/source-free local predicates; genuine propagation roles remain E5b |
| E4b derived boundary laws | in progress | E4a, oriented surfaces/integral Maxwell | genuine full-half-space traces, a coordinate constant-jump distribution bridge, local oriented Stokes/divergence for independent half-cell fields, an explicit finite-sheet carrier/interchange premise, its derivation of the literal sourceful finite-cell Maxwell balances and all four jump laws, sign-sensitive regressions, and the explicit-wave optical bridge are complete; a variable-trace arbitrary-plane weak derivative and derivation of the finite-sheet premise from weak or measure-valued Maxwell remain |
| E5a conservation/reduction | done | E2, E4a | neutral harmonic uniqueness, real and complex hyperplane projection geometry, primitive independent-frequency electric traces, exact joint-data/character/coefficient equivalences, positive-rate harmonic noncancellation, guarded label matching, explicit frequency/tangential-projection conservation, the fixed-frequency electric reduction, and the zero-current referenced tangential-H reduction |
| E5b reflection/Snell/TIR | in progress | E2, E5a | neutral reflection/two-root geometry, material normal-shell and direction-selected root APIs, guarded reflected-root selection, angular reflection, the guarded phase-vector law of the plane of incidence, phase Snell laws, critical sine/angle and radicand-sign classification, unique subcritical positive-phase and supercritical positive-normal-decay transmitted constructions with arbitrary-amplitude carrier lifts, complex-bilinear polarization plus transverse positive-medium Maxwell and zero-normal-mean-flux consequences, named nonzero half-space evanescence, boundary-selected unit-modulus complex reflection with explicit phase, connected reflected/separate/superposed actual normal-flux TIR, and the connected TIR Jones-retarder action are complete; separate outgoing semantics remain |
| E6 Fresnel/flux | in progress | E3b, E5a, E5b | referenced vector balances, aligned Jones scalarization, proof-independent canonical non-normal frame recognition, guarded role-specific incident/reflected/transmitted basis bundles, canonical non-normal and selected-tangent normal-incidence frame specializations with zero-field dummy-label preservation, guarded real propagating s/p amplitudes, the complex positive-normal-decay s/p basis with unique transverse coordinates and fixed-plane conversion, exact affine referencing, its Maxwell/zero-normal-mean-flux carrier, boundary-selected complex s/p coefficients, unit reflected modulus, closed positive-time phase, reflected Jones-intensity preservation, the sign-locked TIR retarder factorization and matrix-self-composition quarter-wave kernel, the common full-vector normal-admittance transmission factor, channel `R + T = 1`, arbitrary-Jones signed irradiance balance, connected separate-wave actual mean normal flux, pointwise incident-reflected normal-interference cancellation, guarded period reconciliation, both explicit-frame and canonical-frame actual superposed-field balances, the connected complex-TIR reflected/separate/superposed actual-flux endpoint, and a lossless algebraic square-root-normalized completion of each real left-incident s/p column are complete; external frame transport is still required before interpreting self-composition as a two-bounce device, while Brewster, full Fresnel-rhomb geometry, outgoing semantics, and a Maxwell-derived bidirectional power-normalized interface scattering matrix remain |
| N1 modal completion | done | O1 | completed O2 modal predicate, parallel, coordinate-change, restriction, zero-extension, and range-projector API |
| N2a ports/routing | in progress | O2 reindex/direct-sum/embedding support | typed local connection, proof-carrying indexed families, physical-port endpoint uniqueness, blockwise mate, connected-channel routing, ambient partial-isometry routing, exact external-channel complements, `E_in`, `E_out`, adjoint readout, both boundary projector decompositions, and convention-free network predicates are complete; matched-gauge covariance remains |
| N2b reciprocity metadata | blocked | human convention decision | time-reversal/reference-plane API |
| N3 behaviors | done | O1 | relation/graph embedding, proof-gated functional extraction, identity/series/parallel closure, and rectangular junction behaviors |
| N3T chain semantics | done | N3 + completed N2a typed-endpoint core | backward-first relational states, scattering regrouping, the canonical typed two-port adapter, proof-gated chain extraction, graph uniqueness, series multiplication, both exact behavior-derived matrix conversions and their round trips, relational right-load termination, and canonical two-device FlatNetlist/Redheffer agreement; source-specific matrix specializations are S0/S7C consumers |
| N4 network equations | done | N1/O2, N2a, N3 | derived maps, the order-free local-component graph bridge, singular-safe complete/external relations, exact shaped and implicit feedback equations, the N-11 singular regression, and wiring-presentation invariance are complete |
| N4C certified compiler | done | N4 | finite executable data, reflected structural checker, proof-carrying N4 compilation, generic executable `S`, `C`, `E_in`, `E_out`, transposed readout, `1 - C * S`, exact evaluated semantic soundness, normalized executable rational coefficients, guarded rational-function evaluation, and hostile singular regressions |
| N5 elimination | done | N4, N4C | complete-state unique solvability, all finite square feedback criteria, proof-gated inverse, exact solution/response graphs, wiring covariance, canonical external scattering packaging, singular-safe two-port series, reflection-free cascade, proof-gated Redheffer realization, and canonical FlatNetlist/N5H/common-domain response agreement are complete |
| N5F parameterized compilation | done | N5, N7 parameterized components | validity, solve, and response domains; guarded compilation/response commutation; reparameterization and algebraic regularity are complete |
| N5H hierarchy/flattening | done | N4, N5 | connection append, hierarchy data, flattening, well-posed subsystem packaging, close behavior, append assembly, unconditional hierarchical/flattened semantic equality, N-08 evidence, fixed-inner-wiring congruence, port-family transport, inner-family replacement, and literal three-stage append associativity after canonical transport are complete |
| N6a conservation | done | N2a, N5; E3b for physical meaning | exact wiring power balance, componentwise passive/lossless closure, and lossless external scattering matrix |
| N6b reciprocity | blocked | N2b, N6a | convention-aware reciprocity closure suite |
| N6c coherent/incoherent observables | done | P2a, N5, N6a | PSD amplitude/channel-power coherencies, congruence response, trace power bounds/equalities, incoherent sums, channel powers, and explicit cross-term identity |
| N7 components | in progress | N2a, O2; E6 only for interface specialization | reflectionless substrate, physically packaged fixed-carrier propagation, and ideal four-port directional coupler complete; beam splitter, mirror, polarization, and interface suite open |
| S0 physical microrings | done | completed N3T core plus the N7 directional coupler and matched propagation | independent all-pass/add-drop field relations (`PhysicalRealization.lean:123-180`), N7 primitive realization and N5 response identification (`PhysicalRealization.lean:186-492`), and DATE/SysCon/SFG source-specific chain and response views (`PhysicalSourceBridge.lean:275-360,407-465`), with hostile fixtures in `PhysicalRegression.lean`; IP-66--IP-69 |
| S1 Mach-Zehnder (Physlib extension) | done | N5, N6a, N7 | explicit two-coupler/two-arm netlist, unconditional feed-forward well-posedness, N5 amplitudes, balanced power/dark-port/phase-ratio results, and N6 power balance; no HOL source |
| S2/S3 microrings | in progress: S2 amplitudes/series, S3 observables, the gated source bridge, and the all-pass X-01 ring instance are integrated | S0, N5, N5F, N6a, N7 | explicit one- and two-bus netlists, exact solve gates, N5 responses, contraction-gated series, N6 power balance, observables, nondispersive FSR, DATE/SysCon/SFG response identifications, and common-domain causal-Z/N5F/N5/Mason/scattering/chain/relational agreement are complete under their stated gates; IP-06/IP-07 source questions and the remaining physical/source extensions stay open |
| S4 delay transfer | in progress | N5F, N7 | formal rational component entries, retained evaluation domains, N5F compilation, Laplace/reciprocal-Z/frequency evaluation, and abstract pole-reduction schema are complete; symbolic external-response elimination and a network actual-pole criterion remain |
| S4P poles/zeros/stability | in progress | S4, N5F | reduced zeros/poles, reciprocal-coordinate finite sets and degree bounds, a stated one-pole Schur/BIBO equivalence, and branch-audited local group delay/dispersion are complete; a network reachability/no-cancellation criterion remains |
| S5 Z-transform | done | Mathlib analysis audit | causal sequence, conditional/absolute ROC, shift, recurrence/transfer, stability, limit inversion, uniqueness, convolution, and causal-solution existence suites; literal Taylor presentation remains in `tbd.md` |
| S6 Mason | done | N5, finite graph audit | neutral node- and edge-indexed Mason theory, `C * S` extraction, exact determinant gate, Mason feedback inverse, and typed external-response equality are complete; ring and DCDR instantiations belong to the S7 system suite |
| S7 HOL integrated parity | blocked | N5H, S0--S6 | source ledger and cross-semantics suite |
| S7D DCDR parity | in progress | N4C, N5H, N6c, S4P--S6 | controller-managed worker is formalizing the audited DCDR topology and observable suite |
| S7C cascade/lattice suite | in progress | N3T, N5H, S0, S4P | controller-managed worker is formalizing source-backed cascades plus the Physlib-original full lattice |
| R1--R5 ray/beam foundations | in progress: the R1--R5 foundational slices and exact E5b bridge are integrated, including proved paraxial approximation error, component-derived ABCD systems, cardinal-point specifications, physical-domain Gaussian transport, matrix-level bounded-ray stability, two-mirror boundary fixtures, and a proof-gated fixed Gaussian beam; an R3 representative subsystem, source-style resonator unfolding, ring and phase-conjugate resonators, and selected source case studies remain open | E1/E5b plus focused ray API map | ray, imaging, ABCD, resonator suite |
| Fourier/quantum extensions | future | relevant classical layers | separate API maps and bridges |

## O. Overall completion checklist

The long-running goal is complete only when:

- [x] the polarization milestone P1a--P6b, including every lettered subpackage, is complete;
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
- [x] external-source licenses and bibliography are verified by `decision-L13.md`,
  `decision-L14.md`, and `bibliography-table.md` under L14's three-class discipline — Class A
  items body-verified (URL fetched, page-cited claims checked, sha256 against `PROVENANCE.md` where
  applicable), Class B consumed with integrity notes, Class C metadata-only and non-load-bearing —
  hostile-checked by A5/A6;
- [ ] every fork-delta theorem passes three independent verification channels: (a) the **Lean
  kernel** — proof correctness, total, with no `sorry`/`axiom`/`native_decide`; (b) an
  **adversarial statement audit**, exhaustive over the fork-delta theorem inventory per
  `AUDIT-PACK-SPEC.md` — an agent that did not write the module reads the printed source page and
  the Lean statement side by side and must try to find a mismatch, recording the page and the
  quoted text, and a second attacker from a **different model family** attacks each page; and (c) a
  **simulation binding** — the COMPARISON-CONTRACT row and its numeric referent, or an explicit
  recorded "no numeric referent exists" with the reason, for structural and distribution-level
  statements; and
- [ ] upstream work has been split into reviewable single-concept PRs and discussed by the human
  author with maintainers.

## P. Research inputs to verify before upstream use

- U. Siddique, O. Hasan, and S. Tahar, [*Formal Modeling and Verification of Integrated Photonic
  Systems*](https://hvg.ece.concordia.ca/Publications/Conferences/SysCon-15.pdf), IEEE International
  Systems Conference, 2015, pp. 562--569.
- U. Siddique, S. M. Beillahi, and S. Tahar, [*On the Formal Analysis of Photonic Signal Processing
  Systems*](https://doi.org/10.1007/978-3-319-19458-5_11), FMICS 2015, LNCS 9128, pp. 162--177,
  for directed signal-flow graphs, Mason gain, DCDR, poles, and zeros. Its prose claims about group
  delay, dispersion, and a quadruple-ring result remain unverified in the fetched formal sources.
- S. Khan-Afshar, O. Hasan, and S. Tahar, [*Formal Analysis of Electromagnetic
  Optics*](https://hvg.ece.concordia.ca/Publications/Conferences/SPIE14.pdf), *Novel Optical Systems
  Design and Optimization XVII*, Proc. SPIE 9193, 91930A, 2014, for the plane-of-incidence,
  reflection, frequency-conservation, Snell, one-mode Fresnel, and electromagnetic Fabry--Perot
  results. Its polarization label is internally inconsistent between TE (PDF p. 7) and TM (PDF
  p. 12).
- U. Siddique and S. Tahar, [*Towards the Formal Analysis of Microresonators based Photonic
  Systems*](https://hvg.ece.concordia.ca/Publications/Conferences/DATE14.pdf), IEEE/ACM DATE 2014,
  pp. 1--6, for finite cascades, matrix powers, and terminated formulas whose required `M₁₁ ≠ 0`
  hypothesis the paper omits. It proves only the uncoupled row sublattice, not a coupled or full
  `M × N` lattice theorem.
- S. M. Beillahi, U. Siddique, and S. Tahar, [*On the Formalization of Signal-Flow-Graphs in
  HOL*](https://hvg.ece.concordia.ca/Publications/TECH_REP/SFG_TR14.pdf), Concordia Technical
  Report, November 2014, for the eight-node add-drop model and transfer theorem.
- S. M. Beillahi, U. Siddique, and S. Tahar, [*Formal Analysis of Engineering Systems Based on
  Signal-Flow-Graph Theory*](https://hvg.ece.concordia.ca/Publications/Conferences/NSV16.pdf), NSV
  2016, LNCS 10152, pp. 31--46, published 2017, for undirected SFGs, transpose invariance, and the
  PANDA Vernier resonator's through- and drop-port responses.
- U. Siddique, M. Y. Mahmoud, and S. Tahar, [*On the Formalization of Z-Transform in
  HOL*](https://hvg.ece.concordia.ca/Publications/Conferences/ITP14-1.pdf), ITP 2014, LNCS 8558,
  pp. 483--498, for unilateral transforms, absolute-summability ROC, shifts, recurrences, and IIR
  examples.
- U. Siddique, M. Y. Mahmoud, and S. Tahar, [*Formal Analysis of Discrete-Time Systems using
  z-Transform*](https://hvg.ece.concordia.ca/Publications/Journals/JAL18.pdf), *Journal of Applied
  Logics -- IfCoLog Journal of Logics and their Applications* 5(4):875--906, 2018, for the
  exterior-circle ROC, inverse and uniqueness theorems, initial-value theorem, higher differences,
  and LCCDE results.
- S. Khan-Afshar, U. Siddique, M. Y. Mahmoud, V. Aravantinos, O. Seddiki, O. Hasan, and S. Tahar,
  [*Formal Analysis of Optical Systems*](https://arxiv.org/abs/1403.3039), *Mathematics in Computer
  Science* 8(1):39--70, 2014.
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
   relabeling, rephasing, and finite mode-family restriction and zero extension. The sparse maps
   prove `R * E = 1`, retain `E * R` as the ambient range projector, and zero-extend arbitrary
   rectangular transforms without treating omitted coordinates as absorption. N2a now has the
   typed local port/connection seam, the oriented
   scattering adapter, presentation-independent unit routing, and the incident-space `C * S`
   action order. Proof-carrying indexed connection families now add physical-port endpoint
   uniqueness, dependent connected-channel embedding, blockwise mating, and exact total routing
   over connected channels. The connected router is now lifted to the total ambient
   internal-wiring transform `C`: `Cᴴ * C` and `C * Cᴴ` are the outgoing and incident connected
   range projectors, its arbitrary-input power is exactly the connected-input power, and a
   nonempty complement-channel fixture proves strict decrease for one complement-supported input
   and therefore failure of global power preservation, without interpreting the deficit as
   absorption. The explicit external channel complement now partitions the ambient channel type,
   is equivalent to the dependent sum of modes over unconnected ports, and supplies the typed
   incident injection `E_in`, outgoing exposure `E_out`, and exact restriction readout `E_outᴴ`.
   Their two Gram laws, cross-zero identities with `C`, and connected/external projector sums prove
   complete incident and outgoing coordinate decompositions. The expression `C b + E_in u` has
   exact connected/external action and normalized modal power equal to connected outgoing power
   plus external incident power. This is not a network energy balance. The empty-mode fixture
   proves that an unconnected physical port need not create a channel. These boundary maps now
   feed the source-neutral `FlatNetlist` relational semantics while remaining coordinate maps,
   rather than source or detector models; no feedback inverse or ordinary scattering-matrix
   multiplication is introduced.
   The N3 core now represents implicit complex-linear behavior independently of invertibility,
   embeds maps and mode transforms as graphs, and proves identity, existential series, independent
   parallel, graph-composition, matrix-cascade, and block-diagonal laws. Its regressions distinguish
   forward and reverse nonsymmetric cascades, a singular but functional zero graph, a genuinely
   multivalued relation, and a rejected branch-incorrect parallel output. Rectangular copy,
   coherent sum, heterogeneous selection, and weighted split/combine now have exact membership,
   composition, kernel, idempotence, and modal-power laws with complex and three-four-five
   regressions. N3 is complete with explicit totality and single-valuedness predicates,
   proof-gated extraction of the unique linear map, graph round trips, functionality closure under
   identity/series/parallel composition, and exact complex gain/cascade regressions. N3T now fixes
   convention-explicit backward-first states, reversibly regroups scattering variables, connects
   raw sum-labelled scattering matrices to the typed two-port boundary, proves both exact
   proof-gated scattering/chain conversions and round trips, derives later-times-earlier matrix
   multiplication from relational series, and supplies singular-safe right-load termination with
   exact response formulas. N4 has begun with dependent component-owned port/channel sums,
   canonical channel reassociation, and block-diagonal scattering with exact entry and mixed-action
   laws. N4 now derives the aggregate component graph and shaped maps from the same typed data,
   retains every complete state satisfying `b = S a` and `a = C b + E_in u`, projects the
   singular-safe relation `y = E_outᴴ b`, and proves the equivalent implicit equation
   `(1 - C * S) a = E_in u` without inversion. Its shared-link regression has invertible local
   component matrices but both multiple zero-input solutions and an unsolvable input. The
   order-free componentwise relation now proves that the assembled graph is exactly simultaneous
   satisfaction of every canonically restricted local component graph. Wiring-preserving
   relabellings now leave ambient routing and feedback literally equal and transport the complete
   external behavior canonically, even for the singular fixture. N4 is complete. N4C now has a
   finite executable data model, an exact reflected checker for inverse mode tables and unique
   physical endpoints, proof-carrying compilation into the same relational kernel, generic
   executable `S`, `C`, `E_in`, `E_out`, transposed readout and `1 - C * S`, and an exact bridge
   from evaluated matrix equations to the singular-safe external relation. The normalized
   little-endian coefficient backend now has an exact `RatFunc` interpretation, a conservative
   stored-denominator guard, and a regular-at-point subring on which evaluation is a ring
   homomorphism. Guarded evaluation commutes with `S`, `C`, every external boundary matrix, and
   `1 - C * S`; its exact rational regression preserves a nonzero singular feedback kernel. N4C
   is complete. N5 now defines well-posedness as functionality of the complete-state relation,
   proves its exact finite equivalence with feedback injectivity, surjectivity, bijectivity,
   trivial kernel, matrix unithood, and nonzero determinant, constructs the inverse only from that
   proof, and identifies the complete solution
   and rectangular external response formulas with the relational semantics. Its exact complex
   fixture pins every stage of `E_outᴴ * S * (1 - C * S)⁻¹ * E_in`; the earlier singular fixture
   is rejected without erasing its relation, and wiring-presentation exchange preserves both the
   gate and the canonically relabelled response. Continue N5 with the paired-external scattering
   specialization, series cascade, and Redheffer feedback.
3. Preserve P3c's proved boundary. Its unit-Jones result is an algebraic orbit-set equivalence,
   not a topological equivalence or a continuous choice of representatives; any topology upgrade
   must separately prove continuity and quotient-topology results. Unit Jones intensity remains a
   raw electric-amplitude-squared normalization, not irradiance or modal power.
4. Preserve the completed P6a raw-Jones layer, P6b-1 reduced representation bridge, and P6b-2
   ordered polarizer--retarder system: the reference axis has eigenvalue one, the orthogonal axis
   has relative phase `exp (-I * retardance)`, `M.comp N` applies `N` first, and neither Jones
   unitarity nor fixed Stokes intensity implies electromagnetic power. Keep P6b-3's
   field/irradiance continuation can now use P5b's propagating material-wave Malus theorem, and
   its normalized-power portion is unblocked by P5b's explicit E3b transport.
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
   positive-normal-decay supercritical carrier constructions. The latter now has a separate
   nonzero half-space evanescent classification, transverse positive-medium Maxwell
   qualification, exact side-normal scaling, and zero-normal-mean-flux theorem; outgoing
   semantics remain distinct and unfinished. With E3s, E3a, E3b's local harmonic-average and
   material-wave irradiance bridges, and E6's separate-wave plus actual-superposition normal-flux
   balances and the canonical non-normal reflected-branch wrappers complete, the selected-tangent
   normal-incidence, coefficient-convention, and guarded role-specific canonical-basis milestones
   are now complete. The positive-normal-decay Fresnel boundary elimination, unit reflected
   modulus, explicit phase, reflected Jones-intensity preservation, and the connected
   reflected/separate/superposed actual-flux TIR endpoint are also complete. The relative `p-s`
   phase is now connected to an independently defined diagonal Jones transform, the existing
   retarder convention, the boundary-selected reflected wave, and exact matrix-self-composition
   quarter-wave regressions using physically shell-compatible incidence data. Do not interpret
   self-composition as two bounces, or call that algebraic kernel a Fresnel rhomb, until two-face
   geometry, frame transport, affine path phase, and entrance/exit faces are modeled. Preserve
   the completed named evanescent semantics and develop outgoing semantics separately before any
   modal normalization; do not make evanescent-port power claims early.
6. Keep polarizers and retarders as separate component PR concepts and do not translate Jones
   intensity into physical power without E3b's explicit hypotheses. P5b now connects the Jones
   analyzer output to the same Maxwell carrier, then obtains normalized modal and actual-flux
   Malus laws only under separately proved incident/outgoing flux normalization.
7. Keep the new source-to-Lean parity ledger as a human-owned gate while developing its independent
   infrastructure: N2a typed routing, N3 behavior semantics, N3T chain views, and N4C certified
   compilation. Do not claim HOL parity from a formula or case-study topic alone.

The next session should not jump directly to a microring formula.
P6b-2 now connects the completed polarizer and retarder stacks in all reduced representations;
P6b-3's physical observables and the complex Fresnel/TIR boundary-selection work must follow the named
electromagnetic medium, boundary, and flux dependencies. With E2's real material-Maxwell layer,
oriented Jones/phasor realization, incidence frames, complex-wavevector decay geometry, off-shell
complex carrier, exact real-wave bridge, generic carrier calculus, and bilinear material
dispersion now connected with forward and converse ordinary-real-field Maxwell and exact
algebraic plus ordinary-real-field falsification regressions, neutral
oriented-affine-hyperplane geometry,
  positive-frequency ordinary-real-sum uniqueness, primitive interface traces and
  noncancellation, guarded fixed-frequency reduction, reflection/Snell/critical geometry, both
  canonical transmitted carrier branches, and the reusable real three-dimensional cross-product
  divergence identity, real Poynting theorem, and local peak-phasor Poynting average now connected,
  E3b's material-wave irradiance, signed propagating normal-flux, and Maxwell-qualified
  positive-normal-decay zero-normal-flux bridges are now complete. The tangential magnetic
  reduction, guarded real propagating Fresnel amplitudes, normal-admittance power ratios,
  arbitrary-Jones channel balance, connected separate-wave actual mean normal flux, pointwise
  incident-reflected normal-interference cancellation, guarded own-period reconciliation, and the
  fixed-frequency actual superposed-field balance are also complete. Canonical non-normal
  incidence geometry now derives the active reflection vector, normal guard, and common `s`-axis
  alignment all the way through canonical Fresnel amplitude and actual-flux wrappers while
  preserving arbitrary zero-field reflected labels. A proof-independent canonical non-normal
  frame predicate and guarded incident/reflected/transmitted bundle now make that basis convention
  explicit without assigning direction semantics from role labels; both active and noncanonical
  zero-reflection regressions consume it. The complex positive-normal-decay `s`/`p` frame,
  fixed-plane conversion, Maxwell carrier, and zero-normal-mean-flux prerequisite are complete.
  Boundary-selected complex Fresnel coefficients, unit reflected modulus, the closed positive-time
  phase formulas, affine referenced transmission, reflected Jones-intensity preservation, and the
  connected reflected/separate/superposed actual-flux TIR endpoint are now complete with an
  unequal-admittance exact regression whose signed values are `8/15`, `-8/15`, and zero. The
  relative `p-s` phase now factors the independently defined reflection matrix as the existing
  linear retarder with `rho = phi_s - phi_p`; a physically shell-compatible exact design makes
  matrix self-composition a negative quarter-wave plate up to common phase, and the
  unequal-admittance boundary fixture recovers the same matrix action. This remains only the
  polarization kernel of a future Fresnel rhomb: raw self-composition does not prove intermediate
  frame identification and deliberately omits two-plane geometry, frame transport, inter-bounce
  affine path phase, and entrance/exit faces. Named nonzero half-space evanescence is now complete;
  the next independent physical-optics front is outgoing semantics.
  Aperture and modal-power normalization remain separate E3b work; carrier decay must not be
  retroactively treated as power flow.
  The reflected conservation result must continue to allow zero reflection, and reduced amplitudes
  remain referenced to the interface point. The independent circuit front remains N2a/N3.
