import SchreierQ2.Basics
import Mathlib.Tactic.SplitIfs

/-! Exact support, multiplicity, and unique-maximum characterization. -/

namespace SchreierQ2

@[simp] theorem mem_below_iff (k x : ℕ) :
    x ∈ below k ↔ 1 ≤ x ∧ x ≤ k := by
  simp only [below, Multiset.mem_map, Multiset.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    omega
  · rintro ⟨hx, hk⟩
    exact ⟨x - 1, by omega, by omega⟩

theorem count_below (k x : ℕ) :
    (below k).count x = if 1 ≤ x ∧ x ≤ k then 1 else 0 := by
  have hnd : (below k).Nodup := by
    exact Multiset.Nodup.map (f := fun i : ℕ => i + 1)
      (by
        intro i j h
        change i + 1 = j + 1 at h
        omega) (Multiset.nodup_range k)
  simpa only [mem_below_iff] using
    (Multiset.count_eq_of_nodup (a := x) hnd)

theorem count_ambient_succ (k x : ℕ) :
    (ambient (k + 1)).count x =
      (if 1 ≤ x ∧ x ≤ k then 2 else 0) +
      (if x = k + 1 then 1 else 0) := by
  simp only [ambient, Multiset.count_add, count_below, Multiset.count_singleton]
  split_ifs <;> omega

@[simp] theorem mem_ambient_iff (n x : ℕ) :
    x ∈ ambient n ↔ 1 ≤ x ∧ x ≤ n := by
  cases n with
  | zero =>
      constructor
      · intro hx
        simp [ambient] at hx
      · rintro ⟨hp, hb⟩
        omega
  | succ k =>
      simp only [ambient, Multiset.mem_add, mem_below_iff, Multiset.mem_singleton]
      omega

theorem count_ambient_top {n : ℕ} (hn : 1 ≤ n) :
    (ambient n).count n = 1 := by
  cases n with
  | zero => omega
  | succ k =>
      rw [count_ambient_succ]
      have h : ¬(1 ≤ k + 1 ∧ k + 1 ≤ k) := by omega
      rw [ite_eq_right h, ite_eq_left rfl]

theorem count_ambient_below {n x : ℕ}
    (hx : 1 ≤ x) (hxn : x < n) : (ambient n).count x = 2 := by
  cases n with
  | zero => omega
  | succ k =>
      rw [count_ambient_succ]
      have h : 1 ≤ x ∧ x ≤ k := by omega
      have hne : x ≠ k + 1 := by omega
      simp [h, hne]

theorem count_ambient_le_two (n x : ℕ) : (ambient n).count x ≤ 2 := by
  cases n with
  | zero => simp [ambient]
  | succ k =>
      rw [count_ambient_succ]
      split_ifs <;> omega

/-- A count-based description of the original uncolored ambient restriction. -/
structure Shape (n : ℕ) (F : Multiset ℕ) : Prop where
  positive : ∀ x ∈ F, 1 ≤ x
  bounded : ∀ x ∈ F, x ≤ n
  count_le : ∀ x, F.count x ≤ 2
  top : F.count n = 1

theorem Shape.top_mem {n : ℕ} {F : Multiset ℕ} (h : Shape n F) : n ∈ F := by
  apply Multiset.count_pos.mp
  rw [h.top]
  decide

theorem Shape.card_pos {n : ℕ} {F : Multiset ℕ} (h : Shape n F) :
    1 ≤ F.card := by
  have hc := Multiset.count_le_card n F
  rw [h.top] at hc
  exact hc

theorem Shape.count_above {n x : ℕ} {F : Multiset ℕ}
    (h : Shape n F) (hx : n < x) : F.count x = 0 := by
  apply Multiset.count_eq_zero_of_notMem
  intro hmem
  have hb := h.bounded x hmem
  omega

theorem Shape.erase_top_lt {n x : ℕ} {F : Multiset ℕ}
    (h : Shape n F) (hx : x ∈ F.erase n) : x < n := by
  have hb := h.bounded x (Multiset.mem_of_mem_erase hx)
  have hne : x ≠ n := by
    intro he
    subst x
    have hp := Multiset.count_pos.mpr hx
    have hz : (F.erase n).count n = 0 := by simp [h.top]
    omega
  omega

/-- This is the required bridge from count data to actual submultisets. -/
theorem shape_iff_original {n : ℕ} {F : Multiset ℕ} (hn : 1 ≤ n) :
    Shape n F ↔ F ≤ ambient n ∧ n ∈ F := by
  constructor
  · intro h
    refine ⟨Multiset.le_iff_count.mpr ?_, h.top_mem⟩
    intro x
    by_cases hx : x ∈ F
    · by_cases he : x = n
      · subst x
        simp [h.top, count_ambient_top hn]
      · have hp := h.positive x hx
        have hb := h.bounded x hx
        rw [count_ambient_below (n := n) hp (by omega)]
        exact h.count_le x
    · rw [Multiset.count_eq_zero_of_notMem hx]
      exact Nat.zero_le _
  · rintro ⟨hle, hmem⟩
    have hs : ∀ x ∈ F, 1 ≤ x ∧ x ≤ n := by
      intro x hx
      exact (mem_ambient_iff n x).mp ((Multiset.subset_of_le hle) hx)
    refine ⟨fun x hx => (hs x hx).1, fun x hx => (hs x hx).2, ?_, ?_⟩
    · intro x
      exact (Multiset.count_le_of_le x hle).trans (count_ambient_le_two n x)
    · have hl := Multiset.count_pos.mpr hmem
      have hu := Multiset.count_le_of_le n hle
      rw [count_ambient_top hn] at hu
      omega

end SchreierQ2
