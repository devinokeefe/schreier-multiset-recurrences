import SchreierQ2.Equivalences
import SchreierQ2.Elimination

/-! Disjoint partitions and the recurrence for the multiset count. -/

namespace SchreierQ2

theorem part_disjoint (δ n i j : ℕ) (hij : i ≠ j) :
    Disjoint (part δ n i) (part δ n j) := by
  apply Finset.disjoint_left.mpr
  intro F hi hj
  have hi' := (Finset.mem_filter.mp hi).2
  have hj' := (Finset.mem_filter.mp hj).2
  exact hij (hi'.symm.trans hj')

theorem familyD_partition (δ n : ℕ) (hn : 1 ≤ n) :
    familyD δ n = part δ n 0 ∪ part δ n 1 ∪ part δ n 2 := by
  ext F
  simp only [part, Finset.mem_union, Finset.mem_filter]
  constructor
  · intro hF
    have hgood := (mem_familyD_iff hn).mp hF
    have hcount := hgood.1.count_le (n - 1)
    have hcases : F.count (n - 1) = 0 ∨ F.count (n - 1) = 1 ∨
        F.count (n - 1) = 2 := by omega
    rcases hcases with h0 | h1 | h2
    · exact Or.inl (Or.inl ⟨hF, h0⟩)
    · exact Or.inl (Or.inr ⟨hF, h1⟩)
    · exact Or.inr ⟨hF, h2⟩
  · rintro ((⟨hF, _⟩ | ⟨hF, _⟩) | ⟨hF, _⟩) <;> exact hF

theorem familyD_card_partition (δ n : ℕ) (hn : 1 ≤ n) :
    (familyD δ n).card =
      (part δ n 0).card + (part δ n 1).card + (part δ n 2).card := by
  have h01 := part_disjoint δ n 0 1 (by decide)
  have h02 := part_disjoint δ n 0 2 (by decide)
  have h12 := part_disjoint δ n 1 2 (by decide)
  have h012 : Disjoint (part δ n 0 ∪ part δ n 1) (part δ n 2) := by
    apply Finset.disjoint_left.mpr
    intro F hF h2
    rcases Finset.mem_union.mp hF with h0 | h1
    · exact Finset.disjoint_left.mp h02 h0 h2
    · exact Finset.disjoint_left.mp h12 h1 h2
  rw [familyD_partition δ n hn, Finset.card_union_of_disjoint h012,
    Finset.card_union_of_disjoint h01]

/-- Count the three disjoint target parts using the relaxed-family equivalences. -/
theorem a_coupled (k : ℕ) :
    a (k + 3) = a (k + 2) + b (k + 2) + a (k + 1) := by
  have h := familyD_card_partition 0 (k + 3) (by omega)
  have h0 := card_eq_of_equiv (zeroRelaxedEquiv k)
  have h1 := card_eq_of_equiv (oneRelaxedEquiv k)
  have h2 := card_eq_of_equiv (twoRelaxedEquiv k)
  rw [← h0, ← h1, ← h2] at h
  simpa only [familyD_zero, familyD_one, a, b] using h

/-- Count the same three multiplicities in the strict companion family. -/
theorem b_coupled (k : ℕ) :
    b (k + 3) = b (k + 2) + a (k + 1) + b (k + 1) := by
  have h := familyD_card_partition 1 (k + 3) (by omega)
  have h0 := card_eq_of_equiv (zeroStrictEquiv k)
  have h1 := card_eq_of_equiv (oneStrictEquiv k)
  have h2 := card_eq_of_equiv (twoStrictEquiv k)
  rw [← h0, ← h1, ← h2] at h
  simpa only [familyD_zero, familyD_one, a, b] using h

theorem source_recurrence (n : ℕ) (hn : 4 ≤ n) :
    a n = a (n - 1) + 2 * a (n - 2) + a (n - 3) := by
  apply RecurrenceAlgebra.source_indexed_recurrence_of_coupled a b
    a_coupled b_coupled ?_ n hn
  simp

/-- The initial values and recurrence specified in `Statement.lean`. -/
theorem target : Target := by
  exact ⟨a_one, a_two, a_three, source_recurrence⟩

end SchreierQ2
