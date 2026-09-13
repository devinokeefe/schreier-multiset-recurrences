import Statement
import Mathlib.Data.Multiset.Count
import Mathlib.Data.Multiset.Replicate
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.SplitIfs
import Lean.Elab.Tactic.Omega

/-!
Support, multiplicity and minimum characterizations of the multiset family.
These lemmas also relate the integer recurrence to its balanced natural-number form.
-/

namespace SchreierQ4.SemanticAudit

theorem mem_admissible_iff {n : ℕ} {F : Multiset ℕ} :
    F ∈ admissibleMultisets n ↔
      F ≤ ambient n ∧ n ∈ F ∧
        ∀ x ∈ F, F.card ≤ 4 * x := by
  simp only [admissibleMultisets, Finset.mem_filter,
    Multiset.mem_toFinset, Multiset.mem_powerset]

theorem doublePrefix_count (m x : ℕ) :
    (doublePrefix m).count x =
      if 1 ≤ x ∧ x ≤ m then 2 else 0 := by
  induction m with
  | zero =>
      simp only [doublePrefix, Multiset.count_zero]
      split_ifs <;> omega
  | succ m ih =>
      simp only [doublePrefix, Multiset.count_add, ih,
        Multiset.count_replicate]
      split_ifs <;> omega

theorem ambient_count (n x : ℕ) :
    (ambient n).count x =
      if x = n ∧ 0 < n then 1
      else if 1 ≤ x ∧ x < n then 2 else 0 := by
  cases n with
  | zero =>
      simp only [ambient, Multiset.count_zero]
      split_ifs <;> omega
  | succ m =>
      simp only [ambient, Multiset.count_add,
        doublePrefix_count, Multiset.count_singleton]
      split_ifs <;> omega

theorem mem_ambient_iff (n x : ℕ) :
    x ∈ ambient n ↔ 1 ≤ x ∧ x ≤ n := by
  rw [← Multiset.count_pos, ambient_count]
  split_ifs <;> omega

theorem mem_admissible_iff_counts {n : ℕ} {F : Multiset ℕ} :
    F ∈ admissibleMultisets n ↔
      (∀ x : ℕ, F.count x ≤
        (if x = n ∧ 0 < n then 1
         else if 1 ≤ x ∧ x < n then 2 else 0)) ∧
      0 < F.count n ∧
      ∀ x ∈ F, F.card ≤ 4 * x := by
  rw [mem_admissible_iff, Multiset.le_iff_count]
  simp only [ambient_count, Multiset.count_pos]

theorem member_range {n : ℕ} {F : Multiset ℕ}
    (h : F ∈ admissibleMultisets n) {x : ℕ} (hx : x ∈ F) :
    1 ≤ x ∧ x ≤ n := by
  exact (mem_ambient_iff n x).mp
    (Multiset.mem_of_le (mem_admissible_iff.mp h).1 hx)

theorem index_pos {n : ℕ} {F : Multiset ℕ}
    (h : F ∈ admissibleMultisets n) :
    0 < n := by
  have hm := (mem_admissible_iff.mp h).2.1
  have hr := member_range h hm
  omega

theorem count_max {n : ℕ} {F : Multiset ℕ}
    (h : F ∈ admissibleMultisets n) :
    F.count n = 1 := by
  have hc :=
    Multiset.count_le_of_le n (mem_admissible_iff.mp h).1
  have hp :=
    Multiset.count_pos.mpr (mem_admissible_iff.mp h).2.1
  have hn := index_pos h
  have hcap : (ambient n).count n = 1 := by
    simp [ambient_count, hn]
  rw [hcap] at hc
  omega

theorem count_lower_le_two {n : ℕ} {F : Multiset ℕ}
    (h : F ∈ admissibleMultisets n)
    (x : ℕ) (hx : 1 ≤ x) (hxn : x < n) :
    F.count x ≤ 2 := by
  have hxne : x ≠ n := by omega
  have hc :=
    Multiset.count_le_of_le x (mem_admissible_iff.mp h).1
  simpa [ambient_count, hxne, hx, hxn] using hc

theorem count_outside_eq_zero {n : ℕ} {F : Multiset ℕ}
    (h : F ∈ admissibleMultisets n)
    (x : ℕ) (hout : x = 0 ∨ n < x) :
    F.count x = 0 := by
  apply Multiset.count_eq_zero_of_notMem
  intro hx
  have hr := member_range h hx
  omega

theorem support_nonempty {n : ℕ} {F : Multiset ℕ}
    (h : F ∈ admissibleMultisets n) :
    F.toFinset.Nonempty := by
  exact ⟨n, Multiset.mem_toFinset.mpr
    (mem_admissible_iff.mp h).2.1⟩

theorem card_predecessor_add_one {n : ℕ} {F : Multiset ℕ}
    (h : F ∈ admissibleMultisets n) :
    F.card - 1 + 1 = F.card := by
  have hm := count_max h
  have hc := Multiset.count_le_card n F
  omega

theorem zero_family :
    admissibleMultisets 0 = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro F h
  have hn := index_pos h
  omega

theorem a_zero :
    a 0 = 0 := by
  rw [a, zero_family, Finset.card_empty]

theorem all_member_bound_iff_min
    (F : Multiset ℕ) (hne : F.toFinset.Nonempty) :
    (∀ x ∈ F, F.card ≤ 4 * x) ↔
      F.card ≤ 4 * F.toFinset.min' hne := by
  constructor
  · intro hb
    exact hb _
      (Multiset.mem_toFinset.mp
        (Finset.min'_mem F.toFinset hne))
  · intro hb x hx
    have hmin : F.toFinset.min' hne ≤ x :=
      Finset.min'_le F.toFinset x
        (Multiset.mem_toFinset.mpr hx)
    omega

theorem mem_admissible_iff_source {n : ℕ} {F : Multiset ℕ} :
    F ∈ admissibleMultisets n ↔
      F ≤ ambient n ∧ n ∈ F ∧
        ∃ hne : F.toFinset.Nonempty,
          F.card ≤ 4 * F.toFinset.min' hne := by
  constructor
  · intro h
    rcases mem_admissible_iff.mp h with ⟨hsub, hn, hb⟩
    have hne : F.toFinset.Nonempty :=
      ⟨n, Multiset.mem_toFinset.mpr hn⟩
    exact ⟨hsub, hn, hne,
      (all_member_bound_iff_min F hne).mp hb⟩
  · rintro ⟨hsub, hn, hne, hb⟩
    exact mem_admissible_iff.mpr
      ⟨hsub, hn, (all_member_bound_iff_min F hne).mpr hb⟩

theorem positive_lag (n k : ℕ)
    (hn : 6 ≤ n) (hk : k ≤ 5) :
    1 ≤ n - k := by
  omega

theorem reindex_from_six (n : ℕ) (hn : 6 ≤ n) :
    (n - 6) + 6 = n := by
  omega

theorem integer_identity_iff_balanced
    (u v w x y z : ℕ) :
    ((u : ℤ) =
      3 * (v : ℤ) - 3 * (w : ℤ) +
      3 * (x : ℤ) + 2 * (y : ℤ) + (z : ℤ)) ↔
    u + 3 * w = 3 * v + 3 * x + 2 * y + z := by
  omega

theorem published_iff_balanced :
    PublishedRecurrence ↔
      ∀ n : ℕ, 6 ≤ n →
        a n + 3 * a (n - 2) =
          3 * a (n - 1) + 3 * a (n - 3) +
          2 * a (n - 4) + a (n - 5) := by
  unfold PublishedRecurrence
  constructor
  · intro h n hn
    exact
      (integer_identity_iff_balanced
        (a n) (a (n - 1)) (a (n - 2))
        (a (n - 3)) (a (n - 4)) (a (n - 5))).mp
        (h n hn)
  · intro h n hn
    exact
      (integer_identity_iff_balanced
        (a n) (a (n - 1)) (a (n - 2))
        (a (n - 3)) (a (n - 4)) (a (n - 5))).mpr
        (h n hn)

end SchreierQ4.SemanticAudit
