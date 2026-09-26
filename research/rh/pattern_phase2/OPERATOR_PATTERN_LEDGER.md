# OPERATOR_PATTERN_LEDGER

Discovery record only. `RH_PROVEN=false`; `authority_effect=NONE`.
The statuses qualify only the exact statement described in each entry.
Source baseline: FormalConjectures `ab791e06dd9368fdcc8684b8bc8dec2feb0ee3ac`
and AEGIS `2c3d041b633147ec97c7ef753aa9d157a47bb9f5`.
No ledger entry is an input axiom or a replacement for kernel replay.

## A. Snowflake / A2 / independent scale

- OBSERVATION: Sixfold geometry suggests the Eisenstein arithmetic scale 3.
- ABSTRACT STRUCTURE: Multiplicatively independent integers induce rationally
  independent logarithms and a dense additive subgroup.
- PRIOR FORMAL YIELD: Log 2 / log 3 irrationality, dense subgroup, and conditional
  continuous sign closure are present in the audited baseline.
- CURRENT RH RELEVANCE: Supplies translations and complementary scales; it does
  not supply positivity of mixed Gram matrices.
- CHEAPEST FALSIFIER: A function with a common transform zero throughout its
  translate span; the previous spectral obstruction covers this case.
- POSSIBLE THEOREM PRODUCER: Common-zero exclusion for two separately scaled
  transforms, followed by an independently stated approximation theorem.
- STATUS: CONFIRMED for scale independence; PROMISING for multiple generators.

## B. Nineteen points / discriminant -19

- OBSERVATION: 19 = 1 + 6 + 12 is the radius-two A2 cluster count; -19 is also
  a class-number-one quadratic discriminant.
- ABSTRACT STRUCTURE: There is an exact identity
  `1 + 3*n*(n+1) = (n+1)^2 + (n+1)*n + n^2`.
  Centered hexagonal counts are A2 norm values; in particular `Q_A2(3,2)=19`.
- PRIOR FORMAL YIELD: No claimed prior theorem tying spline order 19 to this
  norm identity or to the discriminant -19.
- CURRENT RH RELEVANCE: The norm identity is real structure, but it supplies no
  sign theorem for the Weil form. A2 has discriminant -3, not -19.
- CHEAPEST FALSIFIER: Compare norm-form symmetry. Exact exhaustive column
  enumeration gives six proper integral automorphisms of `x^2+xy+y^2` and only
  two of `x^2+xy+5y^2`. Their smallest norm shells have six and two points.
- POSSIBLE THEOREM PRODUCER: The polynomial norm identity and distinct symmetry
  counts; neither closes a missing universal analytic estimate.
- STATUS: CONFIRMED for the norm/count identity; FALSIFIED for identifying the
  two lattices through their shared integer 19. An unspecified deeper connection
  is not claimed to have been disproved.

## C. Euler product / prime-power purity

- OBSERVATION: Multiplicativity distinguishes Euler products from the
  discriminant -20 principal-class Epstein control.
- ABSTRACT STRUCTURE: Logarithmic derivative support on prime powers.
- PRIOR FORMAL YIELD: Existing exact von Mangoldt prime-power support and
  translation-window estimates.
- CURRENT RH RELEVANCE: This is arithmetic structure missing from purely
  topological or support arguments. Positive coefficients in a shifted measure
  are not by themselves positivity of the full Weil operator.
- CHEAPEST FALSIFIER: Evaluate proposed operator signs on exact two-point Gram
  matrices and on the discriminant -20 non-Euler-product control.
- POSSIBLE THEOREM PRODUCER: A quantitative global bound controlling actual
  prime cross terms against the Archimedean form.
- STATUS: CONFIRMED for support and the discriminant -20 n=6 control.
  The parallel Euler lane computes principal-class coefficients at 1,2,3,6
  as `[1,0,0,2]`, other-class coefficients as `[0,1,2,0]`, and
  `b_6=(a_6-a_2*a_3)*log(6)`: nonzero for the principal class, zero for
  their class sum. Its `RHEulerOperatorObstructionV1` Lean declarations are
  candidates pending the director's exact-head replay. The inference from
  positive prime weights to positive convolution operator is FALSIFIED by
  a two-point section; the global arithmetic bound is not established.

## D. Order-19 genuine-function approximation

- OBSERVATION: Smooth spline columns approximate distributional edge columns.
- ABSTRACT STRUCTURE: Regularization preserving support and Fourier dual geometry.
- PRIOR FORMAL YIELD: Existing genuine-function Krein pairing interface; the
  baseline rational order-19 explicit-symbol certificate is external arithmetic,
  not a Lean theorem about the actual Weil form.
- CURRENT RH RELEVANCE: Permits a continuous compactly supported correction.
- CHEAPEST FALSIFIER: Compare orders at fixed support width and normalization.
- POSSIBLE THEOREM PRODUCER: Concrete spline regularity/Fourier expression and
  actual symbol identity, then exact interval replay.
- STATUS: CONFIRMED as a useful regularization mechanism. FALSIFIED in the
  controlled experiment for the claim that 19 is the exceptional order.
  Orders 17 through 21 give nearly equal, slightly decreasing LP margins;
  this is a numerical observation, not a rigorous ordering theorem.

## E. A2 box-spline dimensional lifting

- OBSERVATION: Three line directions are natural for sixfold geometry.
- ABSTRACT STRUCTURE: A box spline is the distribution of a sum of independent
  uniform line segments. A linear projection commutes with that sum, so its
  one-dimensional Fourier transform is a product of projected sinc factors.
- PRIOR FORMAL YIELD: None assumed in this packet.
- CURRENT RH RELEVANCE: Provides alternative genuine signed correction columns.
  Two explicit projections were tested at equal total support width.
- CHEAPEST FALSIFIER: A product keeps the union of factor zero sets. Projection
  does not repair a single-generator zero obstruction. In addition, any
  positive-definite correction vanishing on a neighborhood of zero is zero:
  the two-point Gram bound gives `|H(x)| <= H(0) = 0`.
- POSSIBLE THEOREM PRODUCER: Projection identity for Fourier transforms;
  zero-diagonal positive-definite kernel obstruction. Signed corrections are
  not required to be positive definite and remain possible.
- STATUS: CONFIRMED for projected convolution structure; FALSIFIED for a
  nonzero positive-definite correction satisfying the Krein forbidden window.
  A small numerical improvement of signed LP columns is retained as discovery.

## F. Complementarity instead of one generator

- OBSERVATION: An extra transform zero need not be shared by another scale.
- ABSTRACT STRUCTURE: Intersection of zero sets for separate generators,
  contrasted with their union for a convolution/product generator.
- PRIOR FORMAL YIELD: Baseline single-generator spectral obstruction.
- CURRENT RH RELEVANCE: Directly addresses that obstruction, but not mixed-form
  positivity, approximation topology, support control, or conditioning.
- CHEAPEST FALSIFIER: A common real transform zero, or an unjustified use of
  pointwise zero exclusion as a uniform positive lower bound.
- POSSIBLE THEOREM PRODUCER: No common real sinc zero at irrational scale ratio;
  separate density and mixed-Gram statements remain necessary.
- STATUS: PROMISING; the parallel Lean lane supplies the formal assessment.

## G. Variable width and local moment correction

- OBSERVATION: Width can shrink with dimension, and there are only two moments.
- ABSTRACT STRUCTURE: Correct quantifier order and a codimension-two kernel.
- PRIOR FORMAL YIELD: Width-quantifier counterexample, actual Krein factorization,
  and the conditional arithmetic-value convergence interface.
- CURRENT RH RELEVANCE: May construct admissible approximants. It does not
  automatically preserve positivity under their sum.
- CHEAPEST FALSIFIER: Total covered support shrinking to zero; a singular local
  correction determinant; corrections whose norm dominates the target; or
  missing mixed cross-term estimates.
- POSSIBLE THEOREM PRODUCER: Explicit two-moment correction, support-preserving
  differential decomposition, and normed continuity of the actual form.
- STATUS: PROMISING; no positivity or density is asserted by this ledger.
