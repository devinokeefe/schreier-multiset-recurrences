import SchreierQ2.Families
import SchreierQ2.Maps

/-! Concrete erasure, insertion, shift, and bound transport lemmas. -/

namespace SchreierQ2

@[simp] theorem erase_append (F : Multiset ℕ) (x : ℕ) :
    (F + {x}).erase x = F := by
  rw [Multiset.erase_add_right_pos F (Multiset.mem_singleton_self x)]
  simp

theorem restore_erase {F : Multiset ℕ} {x : ℕ} (hx : x ∈ F) :
    F.erase x + {x} = F :=
  Multiset.add_singleton_eq_iff.mpr ⟨hx, rfl⟩

@[simp] theorem count_shiftUp_succ (F : Multiset ℕ) (x : ℕ) :
    (shiftUp F).count (x + 1) = F.count x :=
  Multiset.count_map_eq_count' Nat.succ F Nat.succ_injective x

@[simp] theorem count_shiftUp_zero (F : Multiset ℕ) :
    (shiftUp F).count 0 = 0 := by
  apply Multiset.count_eq_zero_of_notMem
  simp [shiftUp]

theorem shiftUp_shiftDown {F : Multiset ℕ}
    (hp : ∀ x ∈ F, 1 ≤ x) : shiftUp (shiftDown F) = F := by
  unfold shiftUp shiftDown
  rw [Multiset.map_map]
  calc
    F.map (Nat.succ ∘ Nat.pred) = F.map id := by
      apply Multiset.map_congr rfl
      intro x hx
      have h := hp x hx
      change x - 1 + 1 = x
      omega
    _ = F := by simp

theorem count_shiftDown {F : Multiset ℕ}
    (hp : ∀ x ∈ F, 1 ≤ x) (x : ℕ) :
    (shiftDown F).count x = F.count (x + 1) := by
  have h := congrArg (fun H : Multiset ℕ => H.count (x + 1)) (shiftUp_shiftDown hp)
  simpa only [count_shiftUp_succ] using h

theorem shape_shiftUp {m : ℕ} {F : Multiset ℕ} (h : Shape m F) :
    Shape (m + 1) (shiftUp F) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hx
    omega
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hx
    have hb := h.bounded y hy
    omega
  · intro x
    cases x with
    | zero => simp
    | succ y => simpa only [count_shiftUp_succ] using h.count_le y
  · simpa only [count_shiftUp_succ] using h.top

theorem shape_shiftDown {m : ℕ} {F : Multiset ℕ} (h : Shape (m + 1) F)
    (hp : ∀ x ∈ F, 2 ≤ x) : Shape m (shiftDown F) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hx
    have hy' := hp y hy
    change 1 ≤ y - 1
    omega
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hx
    have hb := h.bounded y hy
    change y - 1 ≤ m
    omega
  · intro x
    rw [count_shiftDown h.positive]
    exact h.count_le (x + 1)
  · rw [count_shiftDown h.positive]
    exact h.top

/-- Append a fresh positive maximum to any multiplicity-bounded remainder. -/
theorem shape_append {n : ℕ} {F : Multiset ℕ} (hn : 1 ≤ n)
    (hp : ∀ x ∈ F, 1 ≤ x) (hb : ∀ x ∈ F, x < n)
    (hc : ∀ x, F.count x ≤ 2) : Shape n (F + {n}) := by
  have hz : F.count n = 0 := by
    apply Multiset.count_eq_zero_of_notMem
    intro hx
    have h := hb n hx
    omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    rcases Multiset.mem_add.mp hx with hx | hx
    · exact hp x hx
    · have he := Multiset.mem_singleton.mp hx
      omega
  · intro x hx
    rcases Multiset.mem_add.mp hx with hx | hx
    · exact Nat.le_of_lt (hb x hx)
    · have he := Multiset.mem_singleton.mp hx
      omega
  · intro x
    by_cases he : x = n
    · subst x
      simp [hz]
    · simpa [Multiset.count_singleton, he] using hc x
  · simp [hz]

theorem shape_one_forward {m : ℕ} {F : Multiset ℕ} (h : Shape m F) :
    Shape (m + 1) (F + {m + 1}) := by
  apply shape_append (by omega) h.positive ?_ h.count_le
  intro x hx
  have hb := h.bounded x hx
  omega

theorem shape_one_inverse {m : ℕ} {G : Multiset ℕ}
    (h : Shape (m + 1) G) (hc : G.count m = 1) :
    Shape m (G.erase (m + 1)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    exact h.positive x (Multiset.mem_of_mem_erase hx)
  · intro x hx
    have hb := h.erase_top_lt hx
    omega
  · intro x
    exact (Multiset.count_le_of_le x (Multiset.erase_le (m + 1) G)).trans (h.count_le x)
  · simpa only [Multiset.count_erase_of_ne (by omega : m ≠ m + 1)] using hc

theorem shape_two_forward {m : ℕ} {F : Multiset ℕ} (h : Shape m F) :
    Shape (m + 1) (F + {m} + {m + 1}) := by
  apply shape_append (by omega)
  · intro x hx
    rcases Multiset.mem_add.mp hx with hx | hx
    · exact h.positive x hx
    · have he := Multiset.mem_singleton.mp hx
      have hm := h.positive m h.top_mem
      omega
  · intro x hx
    rcases Multiset.mem_add.mp hx with hx | hx
    · have hb := h.bounded x hx
      omega
    · have he := Multiset.mem_singleton.mp hx
      omega
  · intro x
    by_cases he : x = m
    · subst x
      simp [h.top]
    · simpa [Multiset.count_singleton, he] using h.count_le x

theorem shape_two_inverse {m : ℕ} {G : Multiset ℕ}
    (h : Shape (m + 1) G) (hc : G.count m = 2) :
    Shape m ((G.erase (m + 1)).erase m) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    exact h.positive x (Multiset.mem_of_mem_erase (Multiset.mem_of_mem_erase hx))
  · intro x hx
    have hb := h.erase_top_lt (Multiset.mem_of_mem_erase hx)
    omega
  · intro x
    exact ((Multiset.count_le_of_le x (Multiset.erase_le m (G.erase (m + 1)))).trans
      (Multiset.count_le_of_le x (Multiset.erase_le (m + 1) G))).trans (h.count_le x)
  · simp [Multiset.count_erase_of_ne (by omega : m ≠ m + 1), hc]

theorem shape_zero_forward {m : ℕ} {F : Multiset ℕ} (h : Shape m F) :
    Shape (m + 1) (F.erase m + {m + 1}) := by
  apply shape_append (by omega)
  · intro x hx
    exact h.positive x (Multiset.mem_of_mem_erase hx)
  · intro x hx
    have hb := h.erase_top_lt hx
    omega
  · intro x
    exact (Multiset.count_le_of_le x (Multiset.erase_le m F)).trans (h.count_le x)

theorem shape_zero_inverse {m : ℕ} {G : Multiset ℕ} (hm : 1 ≤ m)
    (h : Shape (m + 1) G) (hc : G.count m = 0) :
    Shape m (G.erase (m + 1) + {m}) := by
  apply shape_append hm
  · intro x hx
    exact h.positive x (Multiset.mem_of_mem_erase hx)
  · intro x hx
    have hb := h.erase_top_lt hx
    have he : x ≠ m := by
      intro he
      subst x
      have hp := Multiset.count_pos.mpr (Multiset.mem_of_mem_erase hx)
      omega
    omega
  · intro x
    exact (Multiset.count_le_of_le x (Multiset.erase_le (m + 1) G)).trans (h.count_le x)

theorem bound_shift_iff (δ : ℕ) (F : Multiset ℕ) :
    Bound (δ + 2) (shiftUp F) ↔ Bound δ F := by
  constructor
  · intro h x hx
    have hh := h (x + 1) (Multiset.mem_map_of_mem Nat.succ hx)
    simp only [shiftUp_card] at hh
    omega
  · intro h x hx
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hx
    have hh := h y hy
    simp only [shiftUp_card]
    omega

theorem bound_append_iff {δ m t : ℕ} {F : Multiset ℕ}
    (hm : m ∈ F) (hmt : m ≤ t) :
    Bound δ (F + {t}) ↔ Bound (δ + 1) F := by
  constructor
  · intro h x hx
    have hh := h x (Multiset.mem_add.mpr (Or.inl hx))
    simp only [Multiset.card_add, Multiset.card_singleton] at hh
    omega
  · intro h x hx
    rcases Multiset.mem_add.mp hx with hx | hx
    · have hh := h x hx
      simp only [Multiset.card_add, Multiset.card_singleton]
      omega
    · have he := Multiset.mem_singleton.mp hx
      have hh := h m hm
      simp only [Multiset.card_add, Multiset.card_singleton]
      omega

theorem bound_two_iff {δ m : ℕ} {F : Multiset ℕ} (hm : m ∈ F) :
    Bound δ (F + {m} + {m + 1}) ↔ Bound (δ + 2) F := by
  have hm' : m ∈ F + {m} := by simp
  rw [bound_append_iff hm' (by omega : m ≤ m + 1)]
  simpa only [Nat.add_assoc] using
    (bound_append_iff (δ := δ + 1) hm (Nat.le_refl m))

/-- The singleton case is why the zero-copy map uses δ ≤ 1. -/
theorem bound_replace_iff {δ m t : ℕ} {H : Multiset ℕ}
    (hm : 1 ≤ m) (hδ : δ ≤ 1) (hmt : m ≤ t)
    (hH : ∀ x ∈ H, x ≤ m) :
    Bound δ (H + {m}) ↔ Bound δ (H + {t}) := by
  constructor
  · intro h x hx
    rcases Multiset.mem_add.mp hx with hx | hx
    · have hh := h x (Multiset.mem_add.mpr (Or.inl hx))
      simpa only [Multiset.card_add, Multiset.card_singleton] using hh
    · have he := Multiset.mem_singleton.mp hx
      have hh := h m (by simp)
      simp only [Multiset.card_add, Multiset.card_singleton] at hh ⊢
      omega
  · intro h
    have hsmall : (H + {m}).card + δ ≤ 2 * m := by
      by_cases hex : ∃ y, y ∈ H
      · obtain ⟨y, hy⟩ := hex
        have hh := h y (Multiset.mem_add.mpr (Or.inl hy))
        have hu := hH y hy
        simp only [Multiset.card_add, Multiset.card_singleton] at hh ⊢
        omega
      · have hz : H = 0 := by
          apply Multiset.ext.mpr
          intro x
          have hx : x ∉ H := fun hx => hex ⟨x, hx⟩
          simp [hx]
        simp only [hz, Multiset.zero_add, Multiset.card_singleton]
        omega
    intro x hx
    rcases Multiset.mem_add.mp hx with hx | hx
    · have hh := h x (Multiset.mem_add.mpr (Or.inl hx))
      simpa only [Multiset.card_add, Multiset.card_singleton] using hh
    · have he := Multiset.mem_singleton.mp hx
      simpa only [he] using hsmall

end SchreierQ2
