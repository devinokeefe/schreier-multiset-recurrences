import SchreierQ4.Main
import SchreierQ4.PolynomialCertificate
import SchreierQ4.SemanticAudit

/-!
Dedicated audit of the actual imported declarations. No alternative target
or assumed bridge is introduced here. Full signatures expose implicit binders
and universes; explicit @ checks prohibit inserting hidden section arguments.
The validator requires every report, parses complete axiom lists, and enforces
its allowlist. These commands are inspection, not an independent proof checker.
-/

set_option pp.all true
set_option pp.maxSteps 1000000

#print "Q4:definitions:begin"
#print SchreierQ4.doublePrefix
#print SchreierQ4.ambient
#print SchreierQ4.admissibleMultisets
#print SchreierQ4.a
#print SchreierQ4.PublishedRecurrence
#print SchreierQ4.Target
#print SchreierQ4.WordModel.cost
#print SchreierQ4.OriginalBridge.encode
#print SchreierQ4.OriginalBridge.decode
#print SchreierQ4.WordCounting.countState
#print SchreierQ4.LinearCertificate.step
#print SchreierQ4.LinearCertificate.orbit
#print "Q4:definitions:end"

#print "Q4:types:begin"
#print sig SchreierQ4.mem_admissibleMultisets
#print sig SchreierQ4.a_zero
#print sig SchreierQ4.size_bound_iff_quarter
#print sig SchreierQ4.admissible_card_pos
#print sig SchreierQ4.admissible_quarter_lt
#print sig SchreierQ4.admissible_quarter_lt_max
#print sig SchreierQ4.WordModel.cost_nil
#print sig SchreierQ4.WordModel.length_le_cost
#print sig SchreierQ4.WordModel.cost_eq_zero_iff
#print sig SchreierQ4.WordModel.carry_le_one
#print sig SchreierQ4.WordModel.cost_cons
#print sig SchreierQ4.LinearCertificate.relation_step
#print sig SchreierQ4.LinearCertificate.seed_relation
#print sig SchreierQ4.LinearCertificate.orbit_relation
#print sig SchreierQ4.LinearCertificate.b_recurrence
#print sig SchreierQ4.LinearCertificate.b_initial
#print sig SchreierQ4.PolynomialCertificate.kernel_certificate
#print sig SchreierQ4.OriginalBridge.count_doublePrefix
#print sig SchreierQ4.OriginalBridge.count_ambient_succ
#print sig SchreierQ4.OriginalBridge.count_ambient_max
#print sig SchreierQ4.OriginalBridge.count_ambient_le_two
#print sig SchreierQ4.OriginalBridge.admissible_count_le_two
#print sig SchreierQ4.OriginalBridge.admissible_count_max
#print sig SchreierQ4.OriginalBridge.admissible_member_le
#print sig SchreierQ4.OriginalBridge.card_expand
#print sig SchreierQ4.OriginalBridge.expand_bounds
#print sig SchreierQ4.OriginalBridge.count_expand_outside
#print sig SchreierQ4.OriginalBridge.count_expand_head
#print sig SchreierQ4.OriginalBridge.count_expand_le_two
#print sig SchreierQ4.OriginalBridge.expand_injective_of_length
#print sig SchreierQ4.OriginalBridge.expand_le_doublePrefix
#print sig SchreierQ4.OriginalBridge.length_readDigits
#print sig SchreierQ4.OriginalBridge.count_expand_readDigits
#print sig SchreierQ4.OriginalBridge.reconstruct_interval
#print sig SchreierQ4.OriginalBridge.encode_length
#print sig SchreierQ4.OriginalBridge.encode_reconstruct
#print sig SchreierQ4.OriginalBridge.encode_weight
#print sig SchreierQ4.OriginalBridge.encode_cost
#print sig SchreierQ4.OriginalBridge.card_decode
#print sig SchreierQ4.OriginalBridge.decode_admissible
#print sig SchreierQ4.OriginalBridge.decode_encode
#print sig SchreierQ4.OriginalBridge.decode_injective_of_cost
#print sig SchreierQ4.OriginalBridge.encode_decode
#print sig SchreierQ4.OriginalBridge.originalWordEquiv
#print sig SchreierQ4.OriginalBridge.exists_unique_word
#print sig SchreierQ4.WordCounting.digit_cases
#print sig SchreierQ4.WordCounting.mem_boundedWords
#print sig SchreierQ4.WordCounting.mem_words
#print sig SchreierQ4.WordCounting.a_eq_wordCount
#print sig SchreierQ4.WordCounting.card_prepend
#print sig SchreierQ4.WordCounting.prepend_disjoint
#print sig SchreierQ4.WordCounting.card_join3
#print sig SchreierQ4.WordCounting.words_zero
#print sig SchreierQ4.WordCounting.wordCount_zero
#print sig SchreierQ4.WordCounting.words_0_step
#print sig SchreierQ4.WordCounting.words_1_step
#print sig SchreierQ4.WordCounting.words_2_step
#print sig SchreierQ4.WordCounting.words_3_step
#print sig SchreierQ4.WordCounting.count_0_step
#print sig SchreierQ4.WordCounting.count_1_step
#print sig SchreierQ4.WordCounting.count_2_step
#print sig SchreierQ4.WordCounting.count_3_step
#print sig SchreierQ4.WordCounting.countState_zero
#print sig SchreierQ4.WordCounting.countState_step
#print sig SchreierQ4.WordCounting.countState_eq_orbit
#print sig SchreierQ4.WordCounting.countState_first
#print sig SchreierQ4.WordCounting.countState_zero_delays
#print sig SchreierQ4.WordCounting.wordCount_eq_b
#print sig SchreierQ4.a_eq_b
#print sig SchreierQ4.original_initial
#print sig SchreierQ4.recurrence_shifted
#print sig SchreierQ4.publishedRecurrence
#print sig SchreierQ4.mainClaim
#print sig SchreierQ4.SemanticAudit.mem_admissible_iff
#print sig SchreierQ4.SemanticAudit.doublePrefix_count
#print sig SchreierQ4.SemanticAudit.ambient_count
#print sig SchreierQ4.SemanticAudit.mem_ambient_iff
#print sig SchreierQ4.SemanticAudit.mem_admissible_iff_counts
#print sig SchreierQ4.SemanticAudit.member_range
#print sig SchreierQ4.SemanticAudit.index_pos
#print sig SchreierQ4.SemanticAudit.count_max
#print sig SchreierQ4.SemanticAudit.count_lower_le_two
#print sig SchreierQ4.SemanticAudit.count_outside_eq_zero
#print sig SchreierQ4.SemanticAudit.support_nonempty
#print sig SchreierQ4.SemanticAudit.card_predecessor_add_one
#print sig SchreierQ4.SemanticAudit.zero_family
#print sig SchreierQ4.SemanticAudit.a_zero
#print sig SchreierQ4.SemanticAudit.all_member_bound_iff_min
#print sig SchreierQ4.SemanticAudit.mem_admissible_iff_source
#print sig SchreierQ4.SemanticAudit.positive_lag
#print sig SchreierQ4.SemanticAudit.reindex_from_six
#print sig SchreierQ4.SemanticAudit.integer_identity_iff_balanced
#print sig SchreierQ4.SemanticAudit.published_iff_balanced
#print "Q4:types:end"

#print "Q4:exact:begin"
#check (@SchreierQ4.OriginalBridge.originalWordEquiv :
  ∀ N : ℕ, {F // F ∈ SchreierQ4.admissibleMultisets (N + 1)} ≃
    {w : SchreierQ4.WordModel.Word // SchreierQ4.WordModel.cost 0 w = N})
#check (@SchreierQ4.WordCounting.a_eq_wordCount :
  ∀ N : ℕ, SchreierQ4.a (N + 1) = SchreierQ4.WordCounting.wordCount 0 N)
#check (@SchreierQ4.WordCounting.wordCount_eq_b :
  ∀ N : ℕ, (SchreierQ4.WordCounting.wordCount 0 N : ℤ) = SchreierQ4.LinearCertificate.b N)
#check (@SchreierQ4.a_eq_b :
  ∀ N : ℕ, (SchreierQ4.a (N + 1) : ℤ) = SchreierQ4.LinearCertificate.b N)
#check (@SchreierQ4.original_initial :
  SchreierQ4.a 1 = 1 ∧ SchreierQ4.a 2 = 3 ∧ SchreierQ4.a 3 = 8 ∧
    SchreierQ4.a 4 = 18 ∧ SchreierQ4.a 5 = 41)
#check (@SchreierQ4.publishedRecurrence :
  ∀ n : ℕ, 6 ≤ n → (SchreierQ4.a n : ℤ) =
    3 * (SchreierQ4.a (n - 1) : ℤ) - 3 * (SchreierQ4.a (n - 2) : ℤ) +
    3 * (SchreierQ4.a (n - 3) : ℤ) + 2 * (SchreierQ4.a (n - 4) : ℤ) +
    (SchreierQ4.a (n - 5) : ℤ))
#check (@SchreierQ4.mainClaim : SchreierQ4.Target)
#print "Q4:exact:end"

#print "Q4:axioms:begin"
#print axioms SchreierQ4.mem_admissibleMultisets
#print axioms SchreierQ4.a_zero
#print axioms SchreierQ4.size_bound_iff_quarter
#print axioms SchreierQ4.admissible_card_pos
#print axioms SchreierQ4.admissible_quarter_lt
#print axioms SchreierQ4.admissible_quarter_lt_max
#print axioms SchreierQ4.WordModel.cost_nil
#print axioms SchreierQ4.WordModel.length_le_cost
#print axioms SchreierQ4.WordModel.cost_eq_zero_iff
#print axioms SchreierQ4.WordModel.carry_le_one
#print axioms SchreierQ4.WordModel.cost_cons
#print axioms SchreierQ4.LinearCertificate.relation_step
#print axioms SchreierQ4.LinearCertificate.seed_relation
#print axioms SchreierQ4.LinearCertificate.orbit_relation
#print axioms SchreierQ4.LinearCertificate.b_recurrence
#print axioms SchreierQ4.LinearCertificate.b_initial
#print axioms SchreierQ4.PolynomialCertificate.kernel_certificate
#print axioms SchreierQ4.OriginalBridge.count_doublePrefix
#print axioms SchreierQ4.OriginalBridge.count_ambient_succ
#print axioms SchreierQ4.OriginalBridge.count_ambient_max
#print axioms SchreierQ4.OriginalBridge.count_ambient_le_two
#print axioms SchreierQ4.OriginalBridge.admissible_count_le_two
#print axioms SchreierQ4.OriginalBridge.admissible_count_max
#print axioms SchreierQ4.OriginalBridge.admissible_member_le
#print axioms SchreierQ4.OriginalBridge.card_expand
#print axioms SchreierQ4.OriginalBridge.expand_bounds
#print axioms SchreierQ4.OriginalBridge.count_expand_outside
#print axioms SchreierQ4.OriginalBridge.count_expand_head
#print axioms SchreierQ4.OriginalBridge.count_expand_le_two
#print axioms SchreierQ4.OriginalBridge.expand_injective_of_length
#print axioms SchreierQ4.OriginalBridge.expand_le_doublePrefix
#print axioms SchreierQ4.OriginalBridge.length_readDigits
#print axioms SchreierQ4.OriginalBridge.count_expand_readDigits
#print axioms SchreierQ4.OriginalBridge.reconstruct_interval
#print axioms SchreierQ4.OriginalBridge.encode_length
#print axioms SchreierQ4.OriginalBridge.encode_reconstruct
#print axioms SchreierQ4.OriginalBridge.encode_weight
#print axioms SchreierQ4.OriginalBridge.encode_cost
#print axioms SchreierQ4.OriginalBridge.card_decode
#print axioms SchreierQ4.OriginalBridge.decode_admissible
#print axioms SchreierQ4.OriginalBridge.decode_encode
#print axioms SchreierQ4.OriginalBridge.decode_injective_of_cost
#print axioms SchreierQ4.OriginalBridge.encode_decode
#print axioms SchreierQ4.OriginalBridge.originalWordEquiv
#print axioms SchreierQ4.OriginalBridge.exists_unique_word
#print axioms SchreierQ4.WordCounting.digit_cases
#print axioms SchreierQ4.WordCounting.mem_boundedWords
#print axioms SchreierQ4.WordCounting.mem_words
#print axioms SchreierQ4.WordCounting.a_eq_wordCount
#print axioms SchreierQ4.WordCounting.card_prepend
#print axioms SchreierQ4.WordCounting.prepend_disjoint
#print axioms SchreierQ4.WordCounting.card_join3
#print axioms SchreierQ4.WordCounting.words_zero
#print axioms SchreierQ4.WordCounting.wordCount_zero
#print axioms SchreierQ4.WordCounting.words_0_step
#print axioms SchreierQ4.WordCounting.words_1_step
#print axioms SchreierQ4.WordCounting.words_2_step
#print axioms SchreierQ4.WordCounting.words_3_step
#print axioms SchreierQ4.WordCounting.count_0_step
#print axioms SchreierQ4.WordCounting.count_1_step
#print axioms SchreierQ4.WordCounting.count_2_step
#print axioms SchreierQ4.WordCounting.count_3_step
#print axioms SchreierQ4.WordCounting.countState_zero
#print axioms SchreierQ4.WordCounting.countState_step
#print axioms SchreierQ4.WordCounting.countState_eq_orbit
#print axioms SchreierQ4.WordCounting.countState_first
#print axioms SchreierQ4.WordCounting.countState_zero_delays
#print axioms SchreierQ4.WordCounting.wordCount_eq_b
#print axioms SchreierQ4.a_eq_b
#print axioms SchreierQ4.original_initial
#print axioms SchreierQ4.recurrence_shifted
#print axioms SchreierQ4.publishedRecurrence
#print axioms SchreierQ4.mainClaim
#print axioms SchreierQ4.SemanticAudit.mem_admissible_iff
#print axioms SchreierQ4.SemanticAudit.doublePrefix_count
#print axioms SchreierQ4.SemanticAudit.ambient_count
#print axioms SchreierQ4.SemanticAudit.mem_ambient_iff
#print axioms SchreierQ4.SemanticAudit.mem_admissible_iff_counts
#print axioms SchreierQ4.SemanticAudit.member_range
#print axioms SchreierQ4.SemanticAudit.index_pos
#print axioms SchreierQ4.SemanticAudit.count_max
#print axioms SchreierQ4.SemanticAudit.count_lower_le_two
#print axioms SchreierQ4.SemanticAudit.count_outside_eq_zero
#print axioms SchreierQ4.SemanticAudit.support_nonempty
#print axioms SchreierQ4.SemanticAudit.card_predecessor_add_one
#print axioms SchreierQ4.SemanticAudit.zero_family
#print axioms SchreierQ4.SemanticAudit.a_zero
#print axioms SchreierQ4.SemanticAudit.all_member_bound_iff_min
#print axioms SchreierQ4.SemanticAudit.mem_admissible_iff_source
#print axioms SchreierQ4.SemanticAudit.positive_lag
#print axioms SchreierQ4.SemanticAudit.reindex_from_six
#print axioms SchreierQ4.SemanticAudit.integer_identity_iff_balanced
#print axioms SchreierQ4.SemanticAudit.published_iff_balanced
#print "Q4:axioms:end"
