import Mathlib.Data.Multiset.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Filter
import Mathlib.Order.Interval.Finset.Nat

namespace SchreierQ3

/-- Two copies of each integer from one to `n - 1`, followed by maximum `n`. -/
def ambient (n : ℕ) : Multiset ℕ :=
  (Finset.Icc 1 (n - 1)).val +
  (Finset.Icc 1 (n - 1)).val + {n}

/-- The Schreier bound `F.card ≤ 3 * i` for every member `i`. -/
def Schreier3 (F : Multiset ℕ) : Prop :=
  ∀ i ∈ F.toFinset, F.card ≤ 3 * i

instance decidableSchreier3 (F : Multiset ℕ) :
    Decidable (Schreier3 F) := by
  unfold Schreier3
  infer_instance

/-- Admissible submultisets containing a positive maximum `n`. -/
def family (n : ℕ) : Finset (Multiset ℕ) :=
  ((ambient n).powerset.toFinset).filter fun F =>
    0 < n ∧ n ∈ F ∧ Schreier3 F

/-- The cardinality of the original multiset family. -/
def a (n : ℕ) : ℕ := (family n).card

/-- The five positive-index values needed to start the recurrence. -/
def InitialValues : Prop :=
  a 1 = 1 ∧ a 2 = 3 ∧ a 3 = 6 ∧ a 4 = 13 ∧ a 5 = 31

/-- The fifth-order recurrence for `n ≥ 6`, with coefficients interpreted in the integers. -/
def Recurrence : Prop :=
  ∀ n : ℕ, 6 ≤ n →
    (a n : ℤ) =
      3 * (a (n - 1) : ℤ) - 3 * (a (n - 2) : ℤ) +
      4 * (a (n - 3) : ℤ) - 2 * (a (n - 4) : ℤ) +
      (a (n - 5) : ℤ)

/-- The initial values and recurrence for the original multiset count. -/
def MainClaim : Prop := InitialValues ∧ Recurrence

end SchreierQ3
