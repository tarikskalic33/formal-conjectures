# AEGIS Ω source-bound proof assembly

This is a partial execution artifact. No unconditional RH theorem is asserted.
The constructor in AEGIS_RH_Unconditional.lean is restricted to the already
certified 693/2000 log-window class. The exact-head CI receipt, not this
committed snapshot, determines its kernel verification status.

## Canonical target

Mathlib 0df444a360eaa60ab8c11dca51a86af692955474 defines:

```lean
RiemannHypothesis :=
  ∀ (s : ℂ) (_ : riemannZeta s = 0)
    (_ : ¬∃ n : ℕ, s = -2 * (n + 1)) (_ : s ≠ 1), s.re = 1 / 2
```

## Existing verified route

- PR83 head fed5269b549ec846a5c5d821ceca7af399b6b0fe has successful
  exact-source cofinal run 38567547533, job 115863986349. The original
  eventual/all-indices mismatch in RHFeshbachWeilClosureV2 is kernel-closed.
- PR86 parent efc691a1fddcc26ed1a057b3c748cb01709cfdfd has successful
  run 38577005420, job 115896640636: 212 modules compiled, standard axioms only.
  The first parser error was closed by opening ContDiff scope.
- RHKreinMultiplicativeTransportV1 supplies actual moment-zero packets;
  RHFiniteActualGramJoinV1.every_packet_actual_finite_gram gives the full
  genuine Weil Gram representation, including mixed entries.
- RHCofinalSchurAdapterV1.actual_zero_quadratic_nonnegative_of_gram_bounds
  consumes actual hdiag, hcross, hrow and hmargin estimates.
- RHFeshbachWeilClosureV2.packet_zero_quadratic_nonnegative transfers a valid
  PacketSchurFamily to the canonical zero sum. The V10 autocorrelation
  explicit formula converts its sign to the actual Weil arithmetic sign.
- RHFeshbachWeilClosureV2.riemannHypothesis_of_window_schur_families is the
  final consumer of the universal family producer recorded in RH_BLOCKER.json.

Representation and positivity are separate mathematical results.

## Concrete construction

Let A = -Re B(g,g) and E = energy(g). Set N(j)=j, a(j)=A,
normSq(j)=E, nv(j)=sqrt(E), c(j)=1 and re_b=q=nw=beta=mu=0.
The existing certified narrow-window theorem gives A>=0; the energy theorem
gives E>=0. The explicit formula identifies A with the actual canonical zero
quadratic. Constant convergence, norm boundedness and the zero-tail inequalities
discharge the structural fields. The Schur lower bound is
-invFourthError(0,j)*E <= 0 <= A.

This constructs the repository scalar family interface on that certified class.
It does not supply an arbitrary finite-matrix approximation for every packet.

The isolated probe attempts to use pi-window membership as the narrow-window
argument. CI writes its actual compiler result to RH_CLOSURE_PROBE.log and
RH_BLOCKER.json. An expected mismatch is not evidence until executed, and
the probe is not an RH success criterion.

## Other inspected source paths and scope limits

PR80 head 0f4415fa056e775d39b9c915733568fbdf248fc5 has successful consolidated
run 38139018737: the positive result is for 0<=L<21/40, while the large-window
terminal is an RH equivalence. PR47 head 43fc4ad926f244330117bf7041101afe54450896
has successful Mellin construction run 38558256890. PR39 head
5213510f3a6d5be92db4e334546272ab2a08c024 has successful paired/Li run
36962943809; its terminal retains WeightedPairedNonnegativityV1.

The Abjad source proves triadic/mod12 phase routing into the four-phase carrier;
its arithmetic type is not silently promoted to universal analytic positivity.
Finite Gram, local Krein and cofinal adapters are preserved with their actual
hypotheses.

The graph records compiled module imports and source theorem statements,
explicitly distinguished from elaborated proof-term edges. A complete
all-history repository census and elaborated declaration DAG have not been
completed. Eight historical root inputs have exact Git blob/source hashes
but no identified containing historical commit.

## Evidence and reproduction

The workflow generates all six requested artifact names in
evidence-cofinal/assembly, copies the exact compiled source bytes, records
source hashes, actual checkout SHA, Lean/Mathlib versions, run/job references,
printed axioms and the observed probe failure. Artifact names may contain a
synthetic PR merge SHA; the checkout receipt is authoritative.

RH_EXACT_HEAD_REPLAY.sh replays the pinned workflow shell steps on a fresh
normal Lean host. No sorry, admit, new custom axiom, existing theorem statement
change, protected-main mutation, merge or RH status promotion is made.
