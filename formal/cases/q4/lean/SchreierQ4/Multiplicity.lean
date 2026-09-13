import SchreierQ4.Basic

namespace SchreierQ4.OriginalBridge

theorem count_doublePrefix (m x : ℕ) :
    (doublePrefix m).count x = if 1 ≤ x ∧ x ≤ m then 2 else 0 := by
  induction m with
  | zero =>
      simp only [doublePrefix, Multiset.count_zero]
      split <;> omega
  | succ m ih =>
      rw [doublePrefix, Multiset.count_add, ih, Multiset.count_replicate]
      by_cases hx : x = m + 1
      · subst x
        have ht : 1 ≤ m + 1 ∧ m + 1 ≤ m + 1 := by omega
        simp [ht]
      · have he : (1 ≤ x ∧ x ≤ m + 1) ↔ (1 ≤ x ∧ x ≤ m) := by omega
        simp [Ne.symm hx, he]

theorem count_ambient_succ (n x : ℕ) :
    (ambient (n + 1)).count x =
      (if 1 ≤ x ∧ x ≤ n then 2 else 0) +
      (if x = n + 1 then 1 else 0) := by
  simp only [ambient, Multiset.count_add, count_doublePrefix,
    Multiset.count_singleton]

theorem count_ambient_max (n : ℕ) : (ambient (n + 1)).count (n + 1) = 1 := by
  rw [count_ambient_succ]
  simp

theorem count_ambient_le_two (n x : ℕ) : (ambient (n + 1)).count x ≤ 2 := by
  by_cases hx : x = n + 1
  · subst x
    rw [count_ambient_max]
    decide
  · rw [count_ambient_succ]
    simp only [hx, ite_false, Nat.add_zero]
    split <;> omega

theorem admissible_count_le_two {n : ℕ} {F : Multiset ℕ}
    (hF : F ∈ admissibleMultisets (n + 1)) (x : ℕ) : F.count x ≤ 2 := by
  have hle := ((mem_admissibleMultisets (n + 1) F).mp hF).1
  exact (Multiset.count_le_of_le x hle).trans (count_ambient_le_two n x)

theorem admissible_count_max {n : ℕ} {F : Multiset ℕ}
    (hF : F ∈ admissibleMultisets (n + 1)) : F.count (n + 1) = 1 := by
  have hs := (mem_admissibleMultisets (n + 1) F).mp hF
  have hl := Multiset.count_pos.mpr hs.2.1
  have hu := Multiset.count_le_of_le (n + 1) hs.1
  rw [count_ambient_max] at hu
  omega

theorem admissible_member_le {n x : ℕ} {F : Multiset ℕ}
    (hF : F ∈ admissibleMultisets (n + 1)) (hx : x ∈ F) : x ≤ n + 1 := by
  have hs := (mem_admissibleMultisets (n + 1) F).mp hF
  have hl := Multiset.count_pos.mpr hx
  have hu := Multiset.count_le_of_le x hs.1
  by_contra hn
  have he : x ≠ n + 1 := by omega
  have hf : ¬(1 ≤ x ∧ x ≤ n) := by omega
  rw [count_ambient_succ] at hu
  simp only [he, hf, ite_false, Nat.zero_add] at hu
  omega

end SchreierQ4.OriginalBridge
