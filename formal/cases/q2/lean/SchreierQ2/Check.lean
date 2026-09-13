import SchreierQ2.Counting

/-!
Dedicated signature and transitive-axiom audit; no proof module imports this file.
Each bare-identifier `#check` prints the declaration's complete signature.
The final example checks the theorem against the expanded target statement.
The validation driver must reject missing reports and axioms outside
`propext`, `Classical.choice`, and `Quot.sound`.
-/

set_option autoImplicit false
set_option pp.fullNames true
set_option pp.universes true
set_option pp.explicit true
set_option pp.proofs false
set_option pp.deepTerms true

-- Only these small definitions are printed, never the target proof term.
#print SchreierQ2.Target
#print SchreierQ2.a
#print SchreierQ2.Bound
#print SchreierQ2.Good

-- Initial counts.
#check SchreierQ2.a_zero
#print axioms SchreierQ2.a_zero
#check SchreierQ2.a_one
#print axioms SchreierQ2.a_one
#check SchreierQ2.a_two
#print axioms SchreierQ2.a_two
#check SchreierQ2.a_three
#print axioms SchreierQ2.a_three
#check SchreierQ2.a_four
#print axioms SchreierQ2.a_four
#check SchreierQ2.b_zero
#print axioms SchreierQ2.b_zero
#check SchreierQ2.b_one
#print axioms SchreierQ2.b_one
#check SchreierQ2.b_two
#print axioms SchreierQ2.b_two
#check SchreierQ2.b_three
#print axioms SchreierQ2.b_three

-- O1: original multiset and family correspondence.
#check SchreierQ2.mem_family_iff
#print axioms SchreierQ2.mem_family_iff
#check SchreierQ2.all_bounds_iff_minimum
#print axioms SchreierQ2.all_bounds_iff_minimum
#check SchreierQ2.shape_iff_original
#print axioms SchreierQ2.shape_iff_original
#check SchreierQ2.mem_strictFamily_iff
#print axioms SchreierQ2.mem_strictFamily_iff
#check SchreierQ2.mem_familyD_literal
#print axioms SchreierQ2.mem_familyD_literal
#check SchreierQ2.mem_familyD_iff
#print axioms SchreierQ2.mem_familyD_iff
#check SchreierQ2.familyD_zero
#print axioms SchreierQ2.familyD_zero
#check SchreierQ2.familyD_one
#print axioms SchreierQ2.familyD_one
#check SchreierQ2.mem_part_iff
#print axioms SchreierQ2.mem_part_iff

-- O2: boundary hypotheses and equivalence construction.
#check SchreierQ2.two_le_of_card_slack
#print axioms SchreierQ2.two_le_of_card_slack
#check SchreierQ2.shiftUp_shiftDown
#print axioms SchreierQ2.shiftUp_shiftDown
#check SchreierQ2.shape_shiftDown
#print axioms SchreierQ2.shape_shiftDown
#check SchreierQ2.bound_replace_iff
#print axioms SchreierQ2.bound_replace_iff
#check SchreierQ2.good_shift_inverse
#print axioms SchreierQ2.good_shift_inverse
#check SchreierQ2.equivOfMaps
#print axioms SchreierQ2.equivOfMaps

-- O2: the six concrete equivalences.
#check SchreierQ2.zeroRelaxedEquiv
#print axioms SchreierQ2.zeroRelaxedEquiv
#check SchreierQ2.zeroStrictEquiv
#print axioms SchreierQ2.zeroStrictEquiv
#check SchreierQ2.oneRelaxedEquiv
#print axioms SchreierQ2.oneRelaxedEquiv
#check SchreierQ2.oneStrictEquiv
#print axioms SchreierQ2.oneStrictEquiv
#check SchreierQ2.twoRelaxedEquiv
#print axioms SchreierQ2.twoRelaxedEquiv
#check SchreierQ2.twoStrictEquiv
#print axioms SchreierQ2.twoStrictEquiv

-- O2: agreement with the original forward and inverse maps.
#check SchreierQ2.zeroEquiv_val
#print axioms SchreierQ2.zeroEquiv_val
#check SchreierQ2.zeroEquiv_symm_val
#print axioms SchreierQ2.zeroEquiv_symm_val
#check SchreierQ2.oneRelaxedEquiv_val
#print axioms SchreierQ2.oneRelaxedEquiv_val
#check SchreierQ2.oneRelaxedEquiv_symm_val
#print axioms SchreierQ2.oneRelaxedEquiv_symm_val
#check SchreierQ2.oneStrictEquiv_val
#print axioms SchreierQ2.oneStrictEquiv_val
#check SchreierQ2.oneStrictEquiv_symm_val
#print axioms SchreierQ2.oneStrictEquiv_symm_val
#check SchreierQ2.twoRelaxedEquiv_val
#print axioms SchreierQ2.twoRelaxedEquiv_val
#check SchreierQ2.twoRelaxedEquiv_symm_val
#print axioms SchreierQ2.twoRelaxedEquiv_symm_val
#check SchreierQ2.twoStrictEquiv_val
#print axioms SchreierQ2.twoStrictEquiv_val
#check SchreierQ2.twoStrictEquiv_symm_val
#print axioms SchreierQ2.twoStrictEquiv_symm_val

-- O3: finite cardinality transfer, partition, and actual recurrences.
#check SchreierQ2.card_eq_of_equiv
#print axioms SchreierQ2.card_eq_of_equiv
#check SchreierQ2.part_disjoint
#print axioms SchreierQ2.part_disjoint
#check SchreierQ2.familyD_partition
#print axioms SchreierQ2.familyD_partition
#check SchreierQ2.familyD_card_partition
#print axioms SchreierQ2.familyD_card_partition
#check SchreierQ2.a_coupled
#print axioms SchreierQ2.a_coupled
#check SchreierQ2.b_coupled
#print axioms SchreierQ2.b_coupled
#check SchreierQ2.source_recurrence
#print axioms SchreierQ2.source_recurrence

-- Closed target.
#check SchreierQ2.target
#print axioms SchreierQ2.target

-- Check the theorem against the literal conjunction, not an assumed recurrence.
example :
    SchreierQ2.a 1 = 1 ∧
    SchreierQ2.a 2 = 2 ∧
    SchreierQ2.a 3 = 4 ∧
    ∀ n : ℕ, 4 ≤ n →
      SchreierQ2.a n = SchreierQ2.a (n - 1) +
        2 * SchreierQ2.a (n - 2) + SchreierQ2.a (n - 3) :=
  SchreierQ2.target
