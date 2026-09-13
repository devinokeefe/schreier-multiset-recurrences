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
| General terminal-composition bijection (Proposition 5.1) | Article proof; `terminalComposition` defines only the map | Ordinary proof; q3 special case formalized |
| Formal-series division/extraction and minimal orders 3,5,5 | Propositions 3.1 and 4.1, proof of Theorem 1.1, Corollary 4.2 | Ordinary proofs; no Lean formal-series derivation |

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

The three closed endpoints remain in separate module environments.
The nine common polynomial identities and coefficient uniqueness are checked
separately. The formal recurrence endpoints follow the retained case chains;
there is no Lean derivation of those endpoints by dividing the common
polynomials as formal power series. Proposition 5.3 is proved in the article;
the common Lean layer proves the transformation formulas and word-map
agreements, and q2 additionally has the six formal restricted bijections.
General terminal compositions, generating-function extraction, and eventual
minimality are outside the formalized endpoints.
