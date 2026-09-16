import SchreierUnified.Multisets
import SchreierUnified.Certificates
import SchreierUnified.TerminalCompositions
import SchreierUnified.Minimality

-- Run this file, not an excerpt: the output records types and transitive axioms.
set_option autoImplicit false
set_option pp.fullNames true
set_option pp.universes true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.deepTerms true

#check SchreierUnified.family
#check SchreierUnified.mem_family
#check SchreierUnified.mem_boundedWords
#check SchreierUnified.mem_words
#check SchreierUnified.decode_mem
#check SchreierUnified.cost_cons
#check SchreierUnified.cost_append
#check SchreierUnified.carry_le_one
#check SchreierUnified.cost
#check SchreierUnified.originalWordEquiv
#check SchreierUnified.residue_partition
#check SchreierUnified.ResidueEquation
#check SchreierUnified.residue_unique
#check SchreierUnified.decode_encode
#check SchreierUnified.encode_decode
#check SchreierUnified.family_card_eq_wordCount
#check SchreierUnified.decode_append
#check SchreierUnified.encode_appendMap
#check SchreierUnified.wordCount_equation
#check SchreierUnified.wordCount_certificate
#check SchreierUnified.certificate_q2
#check SchreierUnified.certificate_q3
#check SchreierUnified.certificate_q4

#check (SchreierUnified.originalWordEquiv : ∀ q r N, 0 < q →
  {F // F ∈ SchreierUnified.family q r (N + 1)} ≃
    {w : SchreierUnified.Word // SchreierUnified.cost q r w = N})

#print axioms SchreierUnified.decode_encode
#print axioms SchreierUnified.encode_decode
#print axioms SchreierUnified.originalWordEquiv
#print axioms SchreierUnified.family_card_eq_wordCount
#print axioms SchreierUnified.residue_partition
#print axioms SchreierUnified.count_step
#print axioms SchreierUnified.decode_append
#print axioms SchreierUnified.encode_appendMap
#print axioms SchreierUnified.wordCount_equation
#print axioms SchreierUnified.residue_unique
#print axioms SchreierUnified.certificate_q2
#print axioms SchreierUnified.certificate_q3
#print axioms SchreierUnified.certificate_q4
#print axioms SchreierUnified.mem_family
#print axioms SchreierUnified.mem_boundedWords
#print axioms SchreierUnified.mem_words
#print axioms SchreierUnified.decode_mem
#print axioms SchreierUnified.cost_cons
#print axioms SchreierUnified.cost_append
#print axioms SchreierUnified.carry_le_one
#print axioms SchreierUnified.wordCount_certificate

#print SchreierUnified.IsTerminalComposition
#print SchreierUnified.HasEventualRecurrence
#check SchreierUnified.originalTerminalCompositionEquiv
#check SchreierUnified.wordSeries_eq_familySeries
#check SchreierUnified.wordSeries_equation
#check SchreierUnified.seriesResidue_unique
#check SchreierUnified.generatingFunctions2
#check SchreierUnified.generatingFunctions3
#check SchreierUnified.generatingFunctions4
#check SchreierUnified.coefficient_extraction
#check SchreierUnified.eventualRecurrence_iff_polynomial_multiplier
#check SchreierUnified.denominator_degree_lower_bound
#check SchreierUnified.original_minimal_orders

#check (SchreierUnified.originalTerminalCompositionEquiv : ∀ q r N, 0 < q → r < q →
  {F // F ∈ SchreierUnified.family q r (N + 1)} ≃
    {c : List ℕ // SchreierUnified.IsTerminalComposition q
      (q * (N + 1) + q - 1 - r) c})

#print axioms SchreierUnified.originalTerminalCompositionEquiv
#print axioms SchreierUnified.wordSeries_eq_familySeries
#print axioms SchreierUnified.wordSeries_equation
#print axioms SchreierUnified.seriesResidue_unique
#print axioms SchreierUnified.generatingFunctions2
#print axioms SchreierUnified.generatingFunctions3
#print axioms SchreierUnified.generatingFunctions4
#print axioms SchreierUnified.coefficient_extraction
#print axioms SchreierUnified.eventualRecurrence_iff_polynomial_multiplier
#print axioms SchreierUnified.denominator_degree_lower_bound
#print axioms SchreierUnified.original_minimal_orders
