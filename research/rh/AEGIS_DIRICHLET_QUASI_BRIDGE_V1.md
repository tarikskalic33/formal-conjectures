# AEGIS Ω — Dirichlet/Euler vs. OpenAI quasi-RH, bridge v1

**Date:** 2026-10-08. **Status:** conditional mathematics, not admitted; RH remains open.
**Authority:** none. **Target pin:** Lean 4.33.1, fork `main@02da1ad1288b4881ea1f8e575fbe84af7db04364`.

## 1. Provenance: AEGIS work predating the OpenAI repository

1. [AEGIS-OMEGA PR #679](https://github.com/Aegis-Omega/AEGIS-OMEGA/pull/679)
   opened **2026-09-24 20:41 UTC**. Pinned source
   [WeilFixedLineArithmeticV10.lean](https://github.com/Aegis-Omega/AEGIS-OMEGA/blob/5e450d7fbb8c45ce652e458f43d2c5f33ab99832/sovereign-omega-v2/formal/bridges/lean/WeilFixedLineArithmeticV10.lean)
   (blob `b3849e4333230e251d3713cce2056956cc5e3ded`) supplies the
   arithmetic fixed-line identity for `zeta'/zeta` and the von-Mangoldt
   prime-power sum. The normalized zero/pole/gamma/prime assembly is
   [WeilExplicitFormulaV10.lean](https://github.com/Aegis-Omega/AEGIS-OMEGA/blob/5e450d7fbb8c45ce652e458f43d2c5f33ab99832/sovereign-omega-v2/formal/bridges/lean/WeilExplicitFormulaV10.lean)
   (blob `e7d4d31eb6053d5f7325f23071322580b441c8a0`).
2. [AEGIS-OMEGA PR #693](https://github.com/Aegis-Omega/AEGIS-OMEGA/pull/693)
   opened **2026-09-26 16:52 UTC**, exact research head
   `4f93fffcea401e8ede433cc27d525ff7ad1579e3` committed
   **2026-09-28 02:19 UTC**. Its
   [source](https://github.com/Aegis-Omega/AEGIS-OMEGA/blob/4f93fffcea401e8ede433cc27d525ff7ad1579e3/harness/sdk/epstein_lattice_weil_probe.py)
   (blob `3a2d59c6b0ab9d6f2c9f03dd1c33c883bfab690f`) implements
   `chi_minus4`, `chi_5`, `chi_minus20` and the Dirichlet coefficient
   comparison. Its [research analysis](https://github.com/Aegis-Omega/AEGIS-OMEGA/blob/4f93fffcea401e8ede433cc27d525ff7ad1579e3/research/rh/EPSTEIN_LATTICE_WEIL_CONTROL_V1.md)
   explicitly studies `A(s) = zeta(s) L(s, chi_-20)`, `B(s) =
   L(s,chi_-4)L(s,chi_5)`, and the Epstein identity `E_Q(s)=A(s)+B(s)`.
   The numerical spectral probe is **diagnostic only**.
3. [openai/math](https://github.com/openai/math) has its public initial
   Git commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a` stamped
   **2026-10-06 21:58 UTC**, with a quasi-RH paper path dated **2026-09-30**.
   Its [solution](https://github.com/openai/math/blob/main/lean/OAI/NumberTheory/DirichletL/Nonvanishing.lean)
   supplies zeta and Dirichlet `7/8` nonvanishing theorems.

**Exact conclusion:** AEGIS has verifiable, earlier Git source for
Dirichlet/Epstein zeta comparisons and Weil/von-Mangoldt machinery. This is
not evidence that AEGIS earlier proved the same `Re(s)>7/8` exclusion, nor
that it invented the classical Dirichlet L-series or Euler product.

## 2. The direct mathematical bridge

Let `chi` be a Dirichlet character. For `Re(s)>7/8`, assuming the exact
OpenAI nonvanishing premises and excluding the principal pole at `s=1`:

```text
zeta(s) != 0
L(s, chi) != 0
------------------------------- (mul_ne_zero)
A_chi(s) := zeta(s)*L(s,chi) != 0
```

If an Epstein function has `E(s) = A_chi(s) + B(s)` and `E(s)=0`,
then **`B(s)=-A_chi(s)` and `B(s)!=0`**. Thus off-line Epstein zeros
from cancellation between class components are compatible with both Euler
factors remaining nonzero. Crucially the analytic decomposition `E=A+B`
is a *premise* in the Lean bridge, not a newly established formal theorem.

For any zeta zero `rho`, the zeta premise implies:

```text
Re(rho) <= 7/8
Re(rho - 1/2) <= 3/8
```

With an independently justified reflection zero `zeta(1-rho)=0`, it also
implies `1/8 <= Re(rho) <= 7/8`. The second inequality bounds the
**individual exponential factors** of the existing AEGIS translated-zero
kernel; a uniform kernel bound still needs its coefficient-summability
bridge, which is not proved here. Neither assertion closes the RH
critical-line or universal Weil nonnegativity residual.

## 3. Verification boundaries

- New source:
  [`AEGISOverlay/DirichletEulerQuasiBridgeV1.lean`](../../AEGISOverlay/DirichletEulerQuasiBridgeV1.lean).
  It has five theorem declarations and no new axiom, `sorry`, or
  admission of the foreign comparator.
- OpenAI comparator challenge files have `sorry` *by benchmark design*;
  the actual solution is separately in `OAI.NumberTheory.DirichletL.Nonvanishing`.
- Toolchains **differ**: AEGIS fork Lean **4.33.1** vs OpenAI/math Lean
  **4.34.1**. The OpenAI module is deliberately **not imported or
  copied** into this fork. The two nonvanishing premises remain
  externally sourced and explicitly quantified.
- The isolated replay workflow runs the pinned Lean compiler against
  the new module and checks that the required axioms print without
  `sorryAx`. **Verified source replay:** run [`37709265009`](https://github.com/tarikskalic33/formal-conjectures/actions/runs/37709265009) succeeded on exact head `8d80aba4400b5e7064154bada1596de233c899e7` with Lean 4.33.1; all five theorem declarations printed only `[propext, Classical.choice, Quot.sound]`, no `sorryAx`. The tested source blob is `a77814981ba1bd07473e4df4e7a250f5b89be7e6`. A successor head requires its own exact-head replay.
- The original fork [PR #63](https://github.com/tarikskalic33/formal-conjectures/pull/63)
  retains the official `RiemannHypothesis.riemannHypothesis` target
  with residual `AEGIS.RHMillenniumGateV10.UniversalZeroQuadraticNonnegativeV10`.
  This branch is an independent candidate; it does not modify the target,
  any existing proof, branch protection, or production authority.

## 4. Smallest next mathematical step

On a verified same-version replay, consume the **upper-zero** lemma in
`AEGISOverlay.RHGlobalGrowthBoundaryV1` (existing AEGIS PR #63 import graph)
and derive a coefficient-sum majorant for the actual translated kernel
`K_g(t)` at exponent `3/8`. Do **not** conclude type zero or RH from
an exponent `3/8`. Preserve the actual `7/8` inputs and the kernel
summability theorem as explicit provenance and proof dependencies.

Machine-readable pins and explicit unresolved dependencies:
[`AEGIS_DIRICHLET_QUASI_BRIDGE_V1.json`](AEGIS_DIRICHLET_QUASI_BRIDGE_V1.json).

## 5. Earlier pre-OpenAI divisor/zero-carrier work

AEGIS source [`ZetaDivisorSupportBridgeV1.lean`](https://github.com/Aegis-Omega/AEGIS-OMEGA/blob/99563f50c252411ee4eac188acc6bdb4f8d58b3f/sovereign-omega-v2/formal/bridges/lean/ZetaDivisorSupportBridgeV1.lean), Git commit `99563f50c252411ee4eac188acc6bdb4f8d58b3f` created **2026-09-10 17:56:46 UTC**, blob `6ec09558452bbb2f9a4e82c5d2769a2ea758f7c3`, gives a finitary meromorphic zero-divisor support lane including `nontrivial_zero_occurs_in_some_finite_ledger_v1`. Its later compiler-fix version `3c1e89037019c8149c0056fce9b07e8d53d6421b` is dated **2026-09-26 08:16:08 UTC**. This demonstrates separate early zeta infrastructure, not earlier proof of quasi-RH or RH.
