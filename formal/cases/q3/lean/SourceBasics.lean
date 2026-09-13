import Statement
import Lean.Elab.Tactic.Omega

namespace SchreierQ3

@[simp] theorem mem_family {n : ℕ} {F : Multiset ℕ} :
    F ∈ family n ↔
      F ≤ ambient n ∧ 0 < n ∧ n ∈ F ∧ Schreier3 F := by
  simp [family]

theorem schreier3_iff (F : Multiset ℕ) :
    Schreier3 F ↔ ∀ i ∈ F, F.card ≤ 3 * i := by
  simp [Schreier3]

theorem schreier3_iff_at_minimum {F : Multiset ℕ} {m : ℕ}
    (hm : m ∈ F) (hmin : ∀ i ∈ F, m ≤ i) :
    Schreier3 F ↔ F.card ≤ 3 * m := by
  rw [schreier3_iff]
  constructor
  · intro h
    exact h m hm
  · intro h i hi
    exact le_trans h (Nat.mul_le_mul_left 3 (hmin i hi))

theorem mem_ambient_iff {n i : ℕ} (hn : 0 < n) :
    i ∈ ambient n ↔ 0 < i ∧ i ≤ n := by
  simp only [ambient, Multiset.mem_add, Finset.mem_val,
    Finset.mem_Icc, Multiset.mem_singleton]
  omega

theorem count_ambient (n i : ℕ) :
    (ambient n).count i =
      (if 1 ≤ i ∧ i ≤ n - 1 then 2 else 0) +
      (if i = n then 1 else 0) := by
  have hb : (Finset.Icc 1 (n - 1)).val.count i =
      if 1 ≤ i ∧ i ≤ n - 1 then 1 else 0 := by
    simpa using (Multiset.count_eq_of_nodup (a := i)
      (Finset.Icc 1 (n - 1)).nodup)
  simp only [ambient, Multiset.count_add, hb, Multiset.count_singleton]
  by_cases hi : 1 ≤ i ∧ i ≤ n - 1 <;> simp [hi]

theorem source_card_pos {n : ℕ} {F : Multiset ℕ}
    (hF : F ∈ family n) : 0 < F.card := by
  have hnF := (mem_family.mp hF).2.2.1
  have hp : 0 < F.count n := Multiset.count_pos.mpr hnF
  have hb := Multiset.count_le_card n F
  omega

theorem source_support {n i : ℕ} {F : Multiset ℕ}
    (hF : F ∈ family n) (hi : i ∈ F) : 0 < i ∧ i ≤ n := by
  rcases mem_family.mp hF with ⟨hsub, hn, _, _⟩
  exact (mem_ambient_iff hn).mp (Multiset.mem_of_le hsub hi)

theorem source_top_count {n : ℕ} {F : Multiset ℕ}
    (hF : F ∈ family n) : F.count n = 1 := by
  rcases mem_family.mp hF with ⟨hsub, hn, hnF, _⟩
  have hlo : 0 < F.count n := Multiset.count_pos.mpr hnF
  have hhi := Multiset.count_le_of_le n hsub
  rw [count_ambient] at hhi
  have he : ¬(1 ≤ n ∧ n ≤ n - 1) := by omega
  simp [he] at hhi
  omega

theorem source_lower_count {n i : ℕ} {F : Multiset ℕ}
    (hF : F ∈ family n) (hi : 0 < i) (hin : i < n) :
    F.count i ≤ 2 := by
  have hc := Multiset.count_le_of_le i (mem_family.mp hF).1
  rw [count_ambient] at hc
  have hI : 1 ≤ i ∧ i ≤ n - 1 := by omega
  have hne : i ≠ n := by omega
  simpa [hI, hne] using hc

theorem source_size_le_top {n : ℕ} {F : Multiset ℕ}
    (hF : F ∈ family n) : F.card ≤ 3 * n := by
  rcases mem_family.mp hF with ⟨_, _, hnF, hS⟩
  exact (schreier3_iff F).mp hS n hnF

@[simp] theorem family_zero : family 0 = ∅ := by
  simp [family]

@[simp] theorem a_zero : a 0 = 0 := by
  simp [a]

end SchreierQ3
