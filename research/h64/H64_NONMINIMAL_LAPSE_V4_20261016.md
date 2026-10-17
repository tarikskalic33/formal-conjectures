# AEGIS Ω — nonminimal H64 scalar–tensor radial projection V4

**Date:** 2026-10-16. **Scope:** exact mathematical consistency identity + independently executed SymPy and integer witness (28/28 PASS). **Admission:** not a full Einstein-scalar-NED solution, not a physical emergence theorem, not unconditional RH or TOE.

## Source-bound spectral data

At the existing PR #89, the genuine full signed Weil Gram of an admissible 64-packet moment-zero common-window family is the Hermitian matrix `G=(B(g_i,g_j))`; set `K=-G⪰0` under the **stated window assumptions**. Every one of the 4,096 ordered entries is included in `z†Kz = ∑_{i,j=0}^{63} conj(z_i) K_ij z_j`. In normalized six-bit Walsh coordinates `U=H64/8`, `U²=I` and the Hermitian quadratic form is preserved by `K->UKU†, z->Uz`. The physical scalar amplitudes z(x) and their kinetic model remain hypotheses, not automatic properties of an arithmetic packet.

## Covariant action and exact radial-difference field equation

In `G=c=1` units use the explicit diffeomorphism-covariant Jordan-frame ansatz

```text
S=∫sqrt(-g) d⁴x [ A(z) R/(16π)
  - g^{μν} K_{a bbar} ∂μ z^a ∂ν conj(z^b)
  - V(z) + L_NED(F,z) ] .
```

Assume a constant Hermitian field-space K, radial static z(r), a magnetic NED whose mixed temporal and radial stresses coincide, and metric
`ds²=-exp(2Φ(r)) f(r) dt²+dr²/f(r)+r²dΩ²`.

With `J=z'†K z'≥0`, the independently derived geometry and matter projections are

```text
Gr_r-Gt_t=2f Φ'/r,
Tr_r-Tt_t=2f J,
nabla^r nabla_r A-nabla^t nabla_t A=f(A''-Φ'A').
```

Variation of `A R/(16π)` yields
`A G^μ_ν=8πT^μ_ν+nabla^μ nabla_ν A-δ^μ_ν box A`.
Thus for f≠0

```text
       (2A/r + A') Φ' = A'' + 16π J.               (V4.1)
```

Horizon points follow by continuous extension when the fields are regular; this is not a claim of global existence.

## Exact Schwarzschild-gauge radial obstruction (bounded regular branch)

If one freezes `Φ=0` on all r≥0, and `A∈C²([0,∞))` has `A'(0)=0` and a finite `A(∞)`, while `K⪰0` and (V4.1) holds continuously, then `A''=-16πJ≤0`. A' starts at zero and is nonincreasing. If A'(r0)<0, concavity implies A(r)->-∞, contradicting its finite limit. Therefore A'≡0 and J≡0. For strictly positive-definite K also z'≡0. For PSD K, kernel directions are not excluded. This no-go is only for the stated radial ansatz and regular boundary conditions.

## Nontrivial explicit smooth 64-field profile satisfying (V4.1)

Select a vector `v∈C^64` with `v†K v=1` (requires at least one positive direction), a>0, real η, ξ, and |ξ|η²<1. Take

```text
z(r)=η a² v/(r²+a²);
J(r)=4 η² a⁴ r²/(r²+a²)^4;
A(z)=1+ξ z†Kz=1+ξ η²a⁴/(r²+a²)².
```

The scalar and coupling are smooth as functions on R³, z'(0)=A'(0)=0. Positivity A>0 and the absence of a denominator zero follow from |ξ|η²<1.

Substitution in V4.1 yields **exactly**

```text
Φ' = 2 η²a⁴ r [(5ξ+16π)r² - ξ a²] /
     ((r²+a²)^4 [1+ξ η²a⁴(a²-r²)/(r²+a²)^3]).
```

The derivative is O(r) near r=0 and O(r^-5) at infinity, so Φ(r)=-∫_r^∞Φ'(s)ds is finite and smooth. At ξ=0 it integrates explicitly to

```text
Φ(r)= -8π η²a⁴/(r²+a²)² +16π η²a⁶/[3(r²+a²)³],
Φ(∞)=0,    Φ(0)=-8π η²/3.
```

For ξ=0 the ordinary scalar kinetic term already forces the lapse to vary; for ξ≠0 a concrete nonminimal information-norm coupling appears. This closes only the t-r Einstein projection.

## Required angular equation and non-negotiable next proof

The independent angular source equation reads

```text
8π(ρ_NED+p_t,NED) =
 A [f''/2+(1-f)/r² + f Φ''+f(Φ')²
    +(3f'/2+f/r)Φ']
 -(f/r-f'/2-fΦ') A'.
```

The full temporal Einstein equation, scalar EOM, magnetic field equations, conservation, physical boundary conditions, regularity of all curvature invariants and an independently predicted photon-sphere shift must be solved at once. The photon-sphere condition for the metric is

```text
r (f'+2f Φ') - 2f = 0.
```

Inserting an existing Bardeen metric and then reverse-engineering V or L_NED is a consistency construction, NOT independent emergent gravity. The remaining falsifiable assignment is to specify a genuine moment-zero Weil packet-field map and all couplings independently of the desired metric, then solve all coupled equations without fit-after-the-fact.

## Evidence and restrictions

A local, independently executed `verify_h64_nonminimal_v4.py` produced 28/28 exact SymPy and integer-matrix PASS tests and a JSON receipt (shared in the same conversation), covering the source projections, rational formula for Φ', its regularity, the ξ=0 primitive, Bardeen anisotropy, and exact H64 congruence retaining all 4,096 entries. The synthetic numerical PSD sample is **not an actual Weil matrix**. These are not Lean-kernel checks of GR or a cosmological Theory of Everything.

Sources: De Felice and Tsujikawa, *Living Reviews in Relativity* **13**:3 (2010), https://doi.org/10.12942/lrr-2010-3; Faraoni et al., *Physics Reports* **925** (2021), https://doi.org/10.1016/j.physrep.2021.04.003.

**Exact disposition:** projection algebra PASS (independent symbolic arithmetic); mathematically complete full gravity solution PENDING; emergent spacetime derivation PENDING; unconditional RH not asserted.
