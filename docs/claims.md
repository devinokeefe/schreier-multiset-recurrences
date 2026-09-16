# Proof and declaration map

The declarations below have been checked with the pinned Lean toolchain.
The portable receipt in `dist/validation.json` identifies the native run
and binds its evidence to the formal source set. The table distinguishes
formal statements from arguments proved in the article.

## Common argument

| Article claim | Source declarations | Status |
|---|---|---|
| Ambient multiset and margin family | `SchreierUnified.ambient`, `family`, `mem_family` | Compiled |
| Ternary words, cost, finite enumeration | `Word`, `cost`, `boundedWords`, `mem_boundedWords`, `words`, `mem_words` | Compiled |
| Multiset reconstruction and both inverses | `encode_reconstruct`, `decode_mem`, `decode_encode`, `encode_decode` | Compiled |
| Margin-word equivalence and count transfer | `originalWordEquiv`, `family_card_eq_wordCount` | Compiled |
| First- and last-digit cost laws | `cost_cons`, `cost_append`, `carry_le_one` | Compiled |
| Finite residue partition and count equation | `residue_partition`, `count_step`, `wordCount_equation` | Compiled |
| Uniqueness of coefficient solution | `ResidueEquation`, `residue_unique`, `wordCount_certificate` | Compiled |
| All nine polynomial rows | `certificate_q2`, `certificate_q3`, `certificate_q4` | Compiled |
| Last-digit multiset transformation | `appendMap`, `decode_append`, `appendMap_encode`, `encode_appendMap` | Compiled |
| General terminal-composition bijection (Proposition 5.1) | `IsTerminalComposition`, `wordTerminalCompositionEquiv`, `originalTerminalCompositionEquiv` | Compiled for every positive q and r < q |
| Actual formal counting series and unique residue solution | `wordSeries_eq_familySeries`, `wordSeries_equation`, `seriesResidue_unique` | Compiled over the integers |
| All nine rational generating-function identities | `wordSeries_of_certificate`, `generatingFunctions2`, `generatingFunctions3`, `generatingFunctions4` | Compiled as formal power-series identities |
| Coefficient extraction, including the initial indices | `recurrencePolynomial_mul_coeff_all`, `coefficient_extraction` | Compiled with negative-index guards |
| Minimal eventual recurrence orders 3,5,5 (Corollary 4.2) | `eventualRecurrence_iff_polynomial_multiplier`, `denominator_degree_lower_bound`, `original_minimal_orders` | Compiled over the rationals, for arbitrary starting indices |

Unqualified common names in this table have namespace `SchreierUnified`.
`wordCount_certificate` is a conditional certificate principle: its candidate
must satisfy the explicit residue equations. The equation for actual word
counts is proved separately; no recurrence or semantic count bridge is assumed.
The equivalence uses maximum `N+1`, not ambient index zero. Its Lean source
allows any natural margin with `q>0`; the article uses `r<q`. The zero-cost
initial value and the residue equations explicitly require `r<q`. Negative
coefficient indices are guarded out, not replaced by zero through truncated
natural subtraction. The carry bound requires `q>=2`; the general cost law
also covers `q=1` with a carry of two.

## Positive-index adapters

All adapter declarations have been compiled. Their namespaces are
`SchreierUnified.Q2Adapter`, `Q3Adapter`, and `Q4Adapter`.

- `Q2Adapter.family_bridge` identifies every margin with
  `SchreierQ2.familyD`; `relaxed_bridge`, `strict_bridge`, and `count_bridge`
  specialize this. The six `zero_relaxed_word`, `zero_strict_word`,
  `one_relaxed_word`, `one_strict_word`, `two_relaxed_word`, and
  `two_strict_word` declarations compare the actual outputs of the six
  restricted equivalences with common word appending. The auxiliary
  `append_zero`, `append_one_relaxed`, `append_one_strict`, and `append_two`
  compare the literal multiset formulas.
- `Q3Adapter.family_bridge` and `count_bridge` identify the positive original
  family. `pack_read` compares the natural-number and finite-digit readers;
  `encoding_agreement` identifies the actual old encoding with the common
  word followed by the terminal part. No ambient equality at zero is claimed.
- `Q4Adapter.family_bridge` and `count_bridge` identify the original family.
  `cost_agreement`, `reader_agreement`, `expansion_agreement`,
  `encoding_agreement`, and `decoding_agreement` compare the actual maps,
  not just their cardinalities. The old first-digit transition is not called
  the same multiset map as the q2 last-digit transition.

`formal/common/SchreierUnified/Audit.lean` prints key signatures and their
transitive axiom closures. Every adapter ends with exact closed endpoint
checks, signature checks, and axiom checks for its bridges and map agreements.
The validator requires all axiom reports that occur in each compiled source,
including the retained case audit files. A successful compiler invocation,
not a text scanner, checks each explicit theorem type.

## Retained alternative proof chains

The case developments retain their separate mathematical proofs and endpoint
statements. Their documentation, imports and style have been revised for this
release. The article supplies the combined ordinary proof. Each case defines
its counting sequence directly from the multiset family.

For q2, `SchreierQ2.Equivalences` proves the six restricted bijections.
`SchreierQ2.a_coupled` and `SchreierQ2.b_coupled` in `Counting`, with
`Elimination`, yield
`SchreierQ2.target : SchreierQ2.Target`, including initial values and the
recurrence for every `n>=4`.

For q3, `Encoding` and `Bridge` prove the composition correspondence and
`SchreierQ3.count_bridge`; `SchreierQ3.c_step` in `Compositions` and
`SchreierQ3.stride_three` in `RecurrenceAlgebra`
yield `SchreierQ3.main : SchreierQ3.MainClaim`, with the five initial values
and the recurrence for every `n>=6`. The article's residue-series argument is not a dependency of that formal endpoint.

For q4, `SchreierQ4.OriginalBridge.originalWordEquiv`,
`SchreierQ4.WordCounting.a_eq_wordCount`,
and `WordDynamics` connect literal multisets to a six-coordinate orbit.
`SchreierQ4.LinearCertificate.seed_relation` propagates along that orbit and yields
`SchreierQ4.mainClaim : SchreierQ4.Target`, with all five initial values and
all `n>=6`. The polynomial annihilates the designated seed/orbit; it is not
asserted to annihilate the entire operator. The retained
`SchreierQ4.PolynomialCertificate.kernel_certificate` is an alternative finite algebra
certificate, not an additional assumption in the original-object endpoint.

The three retained case endpoints remain in separate module environments.
The common layer additionally constructs the actual counting series in
`PowerSeries ℤ`, proves the residue system and its unique solution, and
establishes all nine rational identities using denominators with constant
coefficient one. `coefficient_extraction` proves the coefficient equation
at every index; the retained case proofs of the explicit initial values
and recurrences remain independent of this formal-series derivation.

`HasEventualRecurrence` is defined directly on sequence coefficients, with
an arbitrary starting index and current-term coefficient one. The equivalence
with a polynomial multiplier is proved, not included in the definition.
Explicit Bezout identities force every such multiplier to be divisible by
the displayed denominator. `original_minimal_orders` states both attainment
and the lower bounds 3, 5, 5 for the original families over the rationals.
The sequences are indexed by maximum `N+1`, consistently with the paper.

Proposition 5.3 is proved in the article; the common Lean layer proves the
transformation formulas and word-map agreements, and q2 additionally has
the six formal restricted bijections.
