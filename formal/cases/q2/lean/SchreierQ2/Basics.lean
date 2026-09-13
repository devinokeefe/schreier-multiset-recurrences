import Statement
import Lean.Elab.Tactic.Omega

/-! Literal family membership, minimum bounds, and kernel-checked initial counts. -/

namespace SchreierQ2

/-- Membership in the family expressed using the multiset order and size bound. -/
@[simp] theorem mem_family_iff (n : ℕ) (F : Multiset ℕ) :
    F ∈ family n ↔
      F ≤ ambient n ∧ n ∈ F ∧ ∀ x ∈ F, F.card ≤ 2 * x := by
  simp [family, admissible]

/-- No minimum convention for the empty multiset is being used. -/
theorem all_bounds_iff_minimum
    (F : Multiset ℕ) (m δ : ℕ)
    (hm : m ∈ F) (hmin : ∀ x ∈ F, m ≤ x) :
    (∀ x ∈ F, F.card + δ ≤ 2 * x) ↔ F.card + δ ≤ 2 * m := by
  constructor
  · intro h
    exact h m hm
  · intro h x hx
    have hx' := hmin x hx
    omega

/-- A downshift is safe whenever cardinality plus slack is at least three. -/
theorem two_le_of_card_slack
    (F : Multiset ℕ) (δ : ℕ)
    (hbound : ∀ x ∈ F, F.card + δ ≤ 2 * x)
    (hcard : 3 ≤ F.card + δ) :
    ∀ x ∈ F, 2 ≤ x := by
  intro x hx
  have h := hbound x hx
  omega

-- Initial counts computed by kernel reduction of the finite families.
set_option maxRecDepth 10000 in
@[simp] theorem a_zero : a 0 = 0 := by decide

set_option maxRecDepth 10000 in
@[simp] theorem a_one : a 1 = 1 := by decide

set_option maxRecDepth 10000 in
@[simp] theorem a_two : a 2 = 2 := by decide

set_option maxRecDepth 10000 in
@[simp] theorem a_three : a 3 = 4 := by decide

set_option maxRecDepth 10000 in
@[simp] theorem a_four : a 4 = 9 := by decide

end SchreierQ2
