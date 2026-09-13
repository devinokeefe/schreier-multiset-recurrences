import Statement
import Lean.Elab.Tactic.Omega

namespace SchreierQ4

/-- Membership uses the multiplicity-sensitive multiset order. -/
theorem mem_admissibleMultisets (n : ℕ) (F : Multiset ℕ) :
    F ∈ admissibleMultisets n ↔
      F ≤ ambient n ∧ n ∈ F ∧ ∀ x ∈ F, F.card ≤ 4 * x := by
  simp [admissibleMultisets]

/-- A convention outside the published range. -/
theorem a_zero : a 0 = 0 := by
  simp [a, admissibleMultisets, ambient]

/-- The strict threshold corresponds to total size m + 1. -/
theorem size_bound_iff_quarter (m x : ℕ) :
    m + 1 ≤ 4 * x ↔ m / 4 < x := by
  omega

/-- Admissibility implies nonemptiness through the required maximum. -/
theorem admissible_card_pos {n : ℕ} {F : Multiset ℕ}
    (hF : F ∈ admissibleMultisets n) : 0 < F.card := by
  have hn := ((mem_admissibleMultisets n F).mp hF).2.1
  exact Multiset.card_pos_iff_exists_mem.mpr ⟨n, hn⟩

/-- Every present value lies strictly above the deletion threshold. -/
theorem admissible_quarter_lt {n x : ℕ} {F : Multiset ℕ}
    (hF : F ∈ admissibleMultisets n) (hx : x ∈ F) :
    (F.card - 1) / 4 < x := by
  have hpos := admissible_card_pos hF
  have hb := ((mem_admissibleMultisets n F).mp hF).2.2 x hx
  apply (size_bound_iff_quarter (F.card - 1) x).mp
  omega

/-- In particular, deleting the initial zero slots cannot pass the maximum. -/
theorem admissible_quarter_lt_max {n : ℕ} {F : Multiset ℕ}
    (hF : F ∈ admissibleMultisets n) : (F.card - 1) / 4 < n := by
  exact admissible_quarter_lt hF
    (((mem_admissibleMultisets n F).mp hF).2.1)

end SchreierQ4
