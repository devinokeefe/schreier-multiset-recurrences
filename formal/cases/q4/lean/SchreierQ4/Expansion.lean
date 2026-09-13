import SchreierQ4.Multiplicity
import SchreierQ4.WordArithmetic

namespace SchreierQ4.OriginalBridge

open WordModel

/-- Slots represent consecutive numerical labels; zero slots are retained. -/
def expand : ℕ → Word → Multiset ℕ
  | _, [] => 0
  | s, d :: w => Multiset.replicate d.val s + expand (s + 1) w

@[simp] theorem card_expand (s : ℕ) (w : Word) : (expand s w).card = weight w := by
  induction w generalizing s with
  | nil => rfl
  | cons d w ih =>
      simp only [expand, Multiset.card_add, Multiset.card_replicate, ih,
        weight, List.map_cons, List.sum_cons]

theorem expand_bounds (s : ℕ) (w : Word) :
    ∀ x, x ∈ expand s w → s ≤ x ∧ x < s + w.length := by
  induction w generalizing s with
  | nil =>
      intro x hx
      simp [expand] at hx
  | cons d w ih =>
      intro x hx
      change x ∈ Multiset.replicate d.val s + expand (s + 1) w at hx
      rcases Multiset.mem_add.mp hx with hx | hx
      · have hxs := Multiset.eq_of_mem_replicate hx
        subst x
        simp only [List.length_cons]
        omega
      · have ht := ih (s + 1) x hx
        simp only [List.length_cons]
        omega

theorem count_expand_outside (s : ℕ) (w : Word) (x : ℕ)
    (h : ¬(s ≤ x ∧ x < s + w.length)) : (expand s w).count x = 0 := by
  apply Multiset.count_eq_zero_of_notMem
  intro hx
  exact h (expand_bounds s w x hx)

@[simp] theorem count_expand_head (s : ℕ) (d : Fin 3) (w : Word) :
    (expand s (d :: w)).count s = d.val := by
  have hz : (expand (s + 1) w).count s = 0 :=
    count_expand_outside (s + 1) w s (by omega)
  simp only [expand, Multiset.count_add, Multiset.count_replicate_self,
    hz, Nat.add_zero]

theorem count_expand_le_two (s : ℕ) (w : Word) :
    ∀ x, (expand s w).count x ≤ 2 := by
  induction w generalizing s with
  | nil => intro x; simp [expand]
  | cons d w ih =>
      intro x
      by_cases hx : x = s
      · subst x
        rw [count_expand_head]
        have hd := d.isLt
        omega
      · have he : s ≠ x := Ne.symm hx
        simp only [expand, Multiset.count_add, Multiset.count_replicate,
          he, ite_false, Nat.zero_add]
        exact ih (s + 1) x

/-- Equal expansions determine digits only after length is fixed. -/
theorem expand_injective_of_length (s : ℕ) (u v : Word)
    (hl : u.length = v.length) (h : expand s u = expand s v) : u = v := by
  induction u generalizing s v with
  | nil =>
      cases v with
      | nil => rfl
      | cons d v => simp at hl
  | cons d u ih =>
      cases v with
      | nil => simp at hl
      | cons e v =>
          have hd : d = e := by
            apply Fin.ext
            have hc := congrArg (Multiset.count s) h
            simpa only [count_expand_head] using hc
          subst e
          have ht : expand (s + 1) u = expand (s + 1) v :=
            Multiset.add_right_inj.mp h
          exact congrArg (List.cons d)
            (ih (s := s + 1) (v := v) (by simpa using hl) ht)

theorem expand_le_doublePrefix (s m : ℕ) (w : Word)
    (hs : 1 ≤ s) (hend : s + w.length ≤ m + 1) :
    expand s w ≤ doublePrefix m := by
  apply Multiset.le_iff_count.mpr
  intro x
  by_cases hx : x ∈ expand s w
  · have hb := expand_bounds s w x hx
    have hi : 1 ≤ x ∧ x ≤ m := by omega
    rw [count_doublePrefix, ite_eq_left hi]
    exact count_expand_le_two s w x
  · rw [Multiset.count_eq_zero_of_notMem hx]
    exact Nat.zero_le _

/-- The modulo only totalizes the reader outside the bounded-multiplicity domain. -/
def readDigits : ℕ → ℕ → Multiset ℕ → Word
  | _, 0, _ => []
  | s, L + 1, F =>
      ⟨F.count s % 3, Nat.mod_lt _ (by decide)⟩ :: readDigits (s + 1) L F

@[simp] theorem length_readDigits (s L : ℕ) (F : Multiset ℕ) :
    (readDigits s L F).length = L := by
  induction L generalizing s with
  | zero => rfl
  | succ L ih => simp only [readDigits, List.length_cons, ih]

theorem count_expand_readDigits (s L : ℕ) (F : Multiset ℕ) (x : ℕ) :
    (expand s (readDigits s L F)).count x =
      if s ≤ x ∧ x < s + L then F.count x % 3 else 0 := by
  induction L generalizing s with
  | zero =>
      simp [readDigits, expand]
  | succ L ih =>
      by_cases hx : x = s
      · subst x
        rw [readDigits, count_expand_head]
        have ht : s ≤ s ∧ s < s + (L + 1) := by omega
        rw [ite_eq_left ht]
      · have he : s ≠ x := Ne.symm hx
        rw [readDigits, expand, Multiset.count_add, Multiset.count_replicate, ih]
        have hi : (s ≤ x ∧ x < s + (L + 1)) ↔
            (s + 1 ≤ x ∧ x < (s + 1) + L) := by omega
        simp only [he, ite_false, Nat.zero_add, hi]

/-- Reconstruction on a numerical interval, with one separate terminal maximum. -/
theorem reconstruct_interval (s L n : ℕ) (F : Multiset ℕ)
    (hbound : ∀ x, F.count x < 3) (hmax : F.count n = 1)
    (hsupp : ∀ x ∈ F, s ≤ x ∧ x ≤ n) (hend : s + L = n) :
    expand s (readDigits s L F) + {n} = F := by
  apply Multiset.ext.mpr
  intro x
  rw [Multiset.count_add, count_expand_readDigits, Multiset.count_singleton]
  by_cases hx : x = n
  · subst x
    have hf : ¬(s ≤ n ∧ n < s + L) := by omega
    simp [hf, hmax]
  · by_cases hi : s ≤ x ∧ x < s + L
    · rw [ite_eq_left hi, ite_eq_right hx, Nat.add_zero,
        Nat.mod_eq_of_lt (hbound x)]
    · have hz : F.count x = 0 := by
        apply Multiset.count_eq_zero_of_notMem
        intro hm
        have hb := hsupp x hm
        apply hi
        omega
      simp only [hi, hx, ite_false, Nat.zero_add, hz]

end SchreierQ4.OriginalBridge
