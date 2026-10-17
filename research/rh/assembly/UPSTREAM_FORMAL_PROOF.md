# RH external formal-proof submission

Status: preparation only. No upstream PR has been opened and no formal RH proof
is asserted by this packet. This preparation file does not set RH proof
admission: the status must come from an exact-head kernel proof-type and axiom audit.

## Exact upstream target

- Repository: google-deepmind/formal-conjectures
- Inspected upstream commit: 2c24ebe7eb2a79b47f9ffcab618cd611c2bc1ea6
- File: FormalConjectures/Millennium/RiemannHypothesis.lean
- File Git blob: 5b1dcd5c46ab4a5f449d7d4a5c5ddce7c89c3542
- Declaration: RiemannHypothesis.riemannHypothesis
- Statement: RiemannHypothesis (the Mathlib proposition, with no extra hypotheses)
- Existing category: research open; AMS 11

The patch template changes only the formal_proof metadata. It leaves the
statement, catalogue placeholder, category and GRH declarations intact.
The official repository permits a catalogue placeholder when the full proof
is hosted externally. The linked external theorem must itself have a complete
proof without sorryAx or custom axioms.

## Existing preparation and evidence

The active proof assembly is PR #88 on
research/rh-actual-proof-assembly-20261014.
Source snapshot inspected for this packet:
a672e4685a27392b81db905d02158312a43a03cf.

The cofinal workflow, source-bound checkpoint restoration, proof graph exporter
and positive/negative closure probes are the existing verification path.
No additional acceptance system is introduced.

Historical local and finite certificates retain their stated domains.
A source link to a conditional terminal or finite-window constructor must not
be presented as a proof of the unconditional official target.

## Complete the link after selecting and verifying the final theorem

Replace the three explicit fields in upstream-formal-proof.patch.in:
- FINAL_VERIFIED_SHA: full immutable commit SHA containing the verified proof.
- FINAL_PROOF_PATH: repository-relative Lean file containing that declaration.
- FINAL_DECLARATION_LINE: the declaration's line number at that commit.

Do not use a branch URL, a workflow page, an archive, or an assumed theorem name
as the formal_proof destination.

The evidence accompanying the link must identify:
- Exact external module and fully qualified declaration.
- An independently compiled term of type _root_.RiemannHypothesis using that
  declaration without supplying mathematical assumptions.
- The final declaration's #print axioms result, containing at most
  propext, Classical.choice and Quot.sound.
- Lean/Mathlib pins, source/import closure, successful replay run and artifact
  identifiers, and artifact hashes.
- Confirmation that the proof does not depend on the catalogue's placeholder
  RiemannHypothesis.riemannHypothesis declaration.

The existing scripts/rh_official_target_gate.py classifies direct proofs of
the catalogue target. Its source-placeholder rejection must not be weakened to
accommodate the external-link route: audit the linked external theorem instead.

## Upstream PR draft

Title: Add an external Lean proof reference for the Riemann hypothesis

Body template (not a present claim):

Adds a commit-pinned formal_proof using lean4 reference to
RiemannHypothesis.riemannHypothesis. The linked declaration has the unchanged
Mathlib RiemannHypothesis type without extra hypotheses. The long proof remains
in the external repository.

Validation: [insert actual exact-commit replay, final axiom report and the
changed upstream module's successful build]. [Insert exact declaration link.]

Before submission, verify the Google CLA requirement and link the relevant
upstream issue if one exists. Do not claim CLA completion or maintainer approval
without evidence. Category changes are outside this preparation.

## Apply and check

First fill in the verified fields and refresh the patch against current upstream.
Then, in the upstream checkout:

    git apply --check upstream-formal-proof.patch
    git apply upstream-formal-proof.patch
    lake --wfail build FormalConjectures.Millennium.RiemannHypothesis

The .patch.in file is a preparation template, not a submission-ready patch.
No submit, merge, status change or paid service is performed by this packet.

## Official instructions

- https://github.com/google-deepmind/formal-conjectures/blob/2c24ebe7eb2a79b47f9ffcab618cd611c2bc1ea6/PROOFS.md
- https://github.com/google-deepmind/formal-conjectures/blob/2c24ebe7eb2a79b47f9ffcab618cd611c2bc1ea6/CONTRIBUTING.md
