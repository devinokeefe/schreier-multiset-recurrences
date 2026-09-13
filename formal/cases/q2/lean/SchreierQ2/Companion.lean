import Statement

/-! The one-unit-slack uncolored companion used in the coupled recurrence. -/

namespace SchreierQ2

/-- Containment of the maximum with the strict bound `F.card + 1 ≤ 2 * x`. -/
def strictAdmissible (n : ℕ) (F : Multiset ℕ) : Prop :=
  n ∈ F ∧ ∀ x ∈ F.toFinset, F.card + 1 ≤ 2 * x

instance strictAdmissibleDecidable (n : ℕ) : DecidablePred (strictAdmissible n) :=
  fun F => by
    unfold strictAdmissible
    infer_instance

/-- The finite family of strict admissible submultisets of `ambient n`. -/
def strictFamily (n : ℕ) : Finset (Multiset ℕ) :=
  (ambient n).powerset.toFinset.filter (strictAdmissible n)

/-- The strict-family count used as the companion to `a`. -/
def b (n : ℕ) : ℕ := (strictFamily n).card

@[simp] theorem mem_strictFamily_iff (n : ℕ) (F : Multiset ℕ) :
    F ∈ strictFamily n ↔
      F ≤ ambient n ∧ n ∈ F ∧ ∀ x ∈ F, F.card + 1 ≤ 2 * x := by
  simp [strictFamily, strictAdmissible]

set_option maxRecDepth 10000 in
@[simp] theorem b_zero : b 0 = 0 := by decide

set_option maxRecDepth 10000 in
@[simp] theorem b_one : b 1 = 1 := by decide

set_option maxRecDepth 10000 in
@[simp] theorem b_two : b 2 = 1 := by decide

set_option maxRecDepth 10000 in
@[simp] theorem b_three : b 3 = 3 := by decide

end SchreierQ2
