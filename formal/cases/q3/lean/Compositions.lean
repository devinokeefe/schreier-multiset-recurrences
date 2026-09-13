import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Lean.Elab.Tactic.Omega

namespace SchreierQ3

/-- Every part is one of 3, 4, and 5. -/
def Parts (p : List ℕ) : Prop :=
  ∀ t ∈ p, 3 ≤ t ∧ t ≤ 5

/-- Ordered compositions specified independently of their finite enumeration. -/
def IsComposition (N : ℕ) (p : List ℕ) : Prop :=
  p.sum = N ∧ Parts p

@[simp] theorem parts_nil : Parts [] := by
  simp [Parts]

@[simp] theorem parts_cons {t : ℕ} {p : List ℕ} :
    Parts (t :: p) ↔ (3 ≤ t ∧ t ≤ 5) ∧ Parts p := by
  simp [Parts]

theorem parts_length (p : List ℕ) :
    Parts p → 3 * p.length ≤ p.sum := by
  induction p with
  | nil => simp
  | cons t p ih =>
      intro hp
      rcases parts_cons.mp hp with ⟨ht, hp⟩
      have hb := ih hp
      simp only [List.length_cons, List.sum_cons]
      omega

theorem composition_length_le {n : ℕ} {p : List ℕ}
    (hp : IsComposition (3 * n + 2) p) : p.length ≤ n := by
  have hb := parts_length p hp.2
  have hs := hp.1
  omega

theorem composition_ne_nil {n : ℕ} {p : List ℕ}
    (hp : IsComposition (3 * n + 2) p) : p ≠ [] := by
  intro he
  have hs := hp.1
  rw [he, List.sum_nil] at hs
  omega

theorem split_last (p : List ℕ) (hp : p ≠ []) :
    ∃ b t, p = b ++ [t] :=
  ⟨p.dropLast, p.getLast hp, (List.dropLast_concat_getLast hp).symm⟩

/-- Finite enumeration by first part; total zero contains the empty composition. -/
def compositions (N : ℕ) : Finset (List ℕ) :=
  if N = 0 then {[]} else
    ((if 3 ≤ N then (compositions (N - 3)).image (List.cons 3) else ∅) ∪
     (if 4 ≤ N then (compositions (N - 4)).image (List.cons 4) else ∅)) ∪
     (if 5 ≤ N then (compositions (N - 5)).image (List.cons 5) else ∅)
termination_by N
decreasing_by all_goals omega

/-- The enumeration contains exactly the lists with the prescribed sum and parts. -/
theorem mem_compositions (N : ℕ) (p : List ℕ) :
    p ∈ compositions N ↔ IsComposition N p := by
  induction N using Nat.strong_induction_on generalizing p with
  | h N ih =>
      rw [compositions]
      by_cases h0 : N = 0
      · simp only [ite_eq_left h0]
        subst N
        rw [Finset.mem_singleton]
        change p = [] ↔ p.sum = 0 ∧ Parts p
        constructor
        · rintro rfl
          exact ⟨rfl, parts_nil⟩
        · rintro ⟨hs, hp⟩
          cases p with
          | nil => rfl
          | cons t p =>
              have ht := (parts_cons.mp hp).1.1
              simp only [List.sum_cons] at hs
              omega
      · simp only [ite_eq_right h0]
        have branch (b : ℕ) (hb : 0 < b) :
            p ∈ (if b ≤ N then
              (compositions (N - b)).image (List.cons b) else ∅) ↔
            ∃ q, p = b :: q ∧ q.sum + b = N ∧ Parts q := by
          by_cases hbN : b ≤ N
          · rw [ite_eq_left hbN]
            have hlt : N - b < N := by omega
            constructor
            · intro hp
              obtain ⟨q, hq, he⟩ := Finset.mem_image.mp hp
              rcases (ih (N - b) hlt q).mp hq with ⟨hs, hparts⟩
              exact ⟨q, he.symm, by omega, hparts⟩
            · rintro ⟨q, rfl, hs, hq⟩
              apply Finset.mem_image.mpr
              refine ⟨q, (ih (N - b) hlt q).mpr ?_, rfl⟩
              exact ⟨by omega, hq⟩
          · rw [ite_eq_right hbN]
            constructor
            · intro hp
              simp at hp
            · rintro ⟨q, _, hs, _⟩
              omega
        rw [Finset.mem_union, Finset.mem_union,
          branch 3 (by decide), branch 4 (by decide), branch 5 (by decide)]
        constructor
        · intro hp
          rcases hp with (h3 | h4) | h5
          · rcases h3 with ⟨q, rfl, hs, hq⟩
            exact ⟨by simpa [List.sum_cons, Nat.add_comm] using hs,
              parts_cons.mpr ⟨by decide, hq⟩⟩
          · rcases h4 with ⟨q, rfl, hs, hq⟩
            exact ⟨by simpa [List.sum_cons, Nat.add_comm] using hs,
              parts_cons.mpr ⟨by decide, hq⟩⟩
          · rcases h5 with ⟨q, rfl, hs, hq⟩
            exact ⟨by simpa [List.sum_cons, Nat.add_comm] using hs,
              parts_cons.mpr ⟨by decide, hq⟩⟩
        · rintro ⟨hs, hp⟩
          cases p with
          | nil =>
              simp only [List.sum_nil] at hs
              omega
          | cons t q =>
              rcases parts_cons.mp hp with ⟨ht, hq⟩
              simp only [List.sum_cons] at hs
              have ht' : t = 3 ∨ t = 4 ∨ t = 5 := by omega
              rcases ht' with rfl | rfl | rfl
              · exact Or.inl (Or.inl ⟨q, rfl, by omega, hq⟩)
              · exact Or.inl (Or.inr ⟨q, rfl, by omega, hq⟩)
              · exact Or.inr ⟨q, rfl, by omega, hq⟩

/-- The number of ordered compositions of `N` into parts three, four and five. -/
def c (N : ℕ) : ℕ := (compositions N).card

theorem compositions_step (k : ℕ) :
    compositions (k + 5) =
      (((compositions (k + 2)).image (List.cons 3)) ∪
       ((compositions (k + 1)).image (List.cons 4))) ∪
       ((compositions k).image (List.cons 5)) := by
  have h0 : k + 5 ≠ 0 := by omega
  have h3 : 3 ≤ k + 5 := by omega
  have h4 : 4 ≤ k + 5 := by omega
  have h5 : 5 ≤ k + 5 := by omega
  have e3 : k + 5 - 3 = k + 2 := by omega
  have e4 : k + 5 - 4 = k + 1 := by omega
  have e5 : k + 5 - 5 = k := by omega
  rw [compositions, ite_eq_right h0, ite_eq_left h3, ite_eq_left h4, ite_eq_left h5]
  rw [e3, e4, e5]

theorem disjoint_prepend (b d : ℕ) (hbd : b ≠ d)
    (s t : Finset (List ℕ)) :
    Disjoint (s.image (List.cons b)) (t.image (List.cons d)) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  obtain ⟨u, _, hu⟩ := Finset.mem_image.mp hp
  obtain ⟨v, _, hv⟩ := Finset.mem_image.mp hq
  exact hbd (List.cons.inj (hu.trans hv.symm)).1

theorem card_prepend (b : ℕ) (s : Finset (List ℕ)) :
    (s.image (List.cons b)).card = s.card := by
  apply Finset.card_image_of_injective
  intro p q he
  exact (List.cons.inj he).2

theorem c_step (k : ℕ) :
    c (k + 5) = c (k + 2) + c (k + 1) + c k := by
  have h34 := disjoint_prepend 3 4 (by decide)
    (compositions (k + 2)) (compositions (k + 1))
  have h35 := disjoint_prepend 3 5 (by decide)
    (compositions (k + 2)) (compositions k)
  have h45 := disjoint_prepend 4 5 (by decide)
    (compositions (k + 1)) (compositions k)
  have h345 : Disjoint
      (((compositions (k + 2)).image (List.cons 3)) ∪
       ((compositions (k + 1)).image (List.cons 4)))
      ((compositions k).image (List.cons 5)) := by
    apply Finset.disjoint_left.mpr
    intro p hp h5
    rcases Finset.mem_union.mp hp with h3 | h4
    · exact (Finset.disjoint_left.mp h35) h3 h5
    · exact (Finset.disjoint_left.mp h45) h4 h5
  unfold c
  rw [compositions_step, Finset.card_union_of_disjoint h345,
    Finset.card_union_of_disjoint h34]
  rw [card_prepend, card_prepend, card_prepend]

theorem c_selected_values :
    c 5 = 1 ∧ c 8 = 3 ∧ c 11 = 6 ∧ c 14 = 13 ∧ c 17 = 31 := by
  -- The empty composition and the single parts determine counts below five.
  have h0 : c 0 = 1 := by simp [c, compositions]
  have h1 : c 1 = 0 := by simp [c, compositions]
  have h2 : c 2 = 0 := by simp [c, compositions]
  have h3 : c 3 = 1 := by simp [c, compositions]
  have h4 : c 4 = 1 := by simp [c, compositions]
  -- The first-part recurrence supplies the larger totals needed by the bridge.
  have h5 : c 5 = 1 := by
    calc
      c 5 = c 2 + c 1 + c 0 := c_step 0
      _ = 1 := by rw [h2, h1, h0]
  have h6 : c 6 = 1 := by
    calc
      c 6 = c 3 + c 2 + c 1 := c_step 1
      _ = 1 := by rw [h3, h2, h1]
  have h7 : c 7 = 2 := by
    calc
      c 7 = c 4 + c 3 + c 2 := c_step 2
      _ = 2 := by rw [h4, h3, h2]
  have h8 : c 8 = 3 := by
    calc
      c 8 = c 5 + c 4 + c 3 := c_step 3
      _ = 3 := by rw [h5, h4, h3]
  have h9 : c 9 = 3 := by
    calc
      c 9 = c 6 + c 5 + c 4 := c_step 4
      _ = 3 := by rw [h6, h5, h4]
  have h10 : c 10 = 4 := by
    calc
      c 10 = c 7 + c 6 + c 5 := c_step 5
      _ = 4 := by rw [h7, h6, h5]
  have h11 : c 11 = 6 := by
    calc
      c 11 = c 8 + c 7 + c 6 := c_step 6
      _ = 6 := by rw [h8, h7, h6]
  have h12 : c 12 = 8 := by
    calc
      c 12 = c 9 + c 8 + c 7 := c_step 7
      _ = 8 := by rw [h9, h8, h7]
  have h13 : c 13 = 10 := by
    calc
      c 13 = c 10 + c 9 + c 8 := c_step 8
      _ = 10 := by rw [h10, h9, h8]
  have h14 : c 14 = 13 := by
    calc
      c 14 = c 11 + c 10 + c 9 := c_step 9
      _ = 13 := by rw [h11, h10, h9]
  have h17 : c 17 = 31 := by
    calc
      c 17 = c 14 + c 13 + c 12 := c_step 12
      _ = 31 := by rw [h14, h13, h12]
  exact ⟨h5, h8, h11, h14, h17⟩

end SchreierQ3
