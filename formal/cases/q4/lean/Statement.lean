import Mathlib.Data.Finset.Card
import Mathlib.Data.Multiset.Powerset

/-!
# Schreier multisets for q = 4
Chu et al., Integers 26 (2026), A53, Section 5, numbered item 3, p. 19.

The counting sequence is the cardinality of the finite multiset family.
The initial values and recurrence are proved in `SchreierQ4.Main`.
The n = 0 convention is an empty family; the published target starts at n = 1.
-/

namespace SchreierQ4

/-- Two indistinguishable copies of each of 1, ..., m. -/
def doublePrefix : ℕ → Multiset ℕ
  | 0 => 0
  | m + 1 => doublePrefix m + Multiset.replicate 2 (m + 1)

/-- For n > 0: {1,1,2,2,...,n-1,n-1,n}, with a unique maximum. -/
def ambient : ℕ → Multiset ℕ
  | 0 => 0
  | m + 1 => doublePrefix m + {m + 1}

/--
Distinct uncolored admissible multisets. `toFinset` is essential: a multiset
powerset retains multiple selections that become the same uncolored multiset.
For a nonempty F, bounding its card by 4*x for every member x is equivalent
to bounding it by 4*min(F). Membership of n ensures nonemptiness.
-/
def admissibleMultisets (n : ℕ) : Finset (Multiset ℕ) :=
  ((ambient n).powerset.toFinset).filter
    (fun F => n ∈ F ∧ ∀ x ∈ F, F.card ≤ 4 * x)

/-- The number of distinct admissible multisets of maximum `n`. -/
def a (n : ℕ) : ℕ := (admissibleMultisets n).card

/-- Integer subtraction, not truncated subtraction of natural-number counts. -/
def PublishedRecurrence : Prop :=
  ∀ n : ℕ, 6 ≤ n →
    (a n : ℤ) =
      3 * (a (n - 1) : ℤ) - 3 * (a (n - 2) : ℤ) +
      3 * (a (n - 3) : ℤ) + 2 * (a (n - 4) : ℤ) +
      (a (n - 5) : ℤ)

/-- The recurrence together with its five positive-index initial values. -/
def Target : Prop :=
  a 1 = 1 ∧ a 2 = 3 ∧ a 3 = 8 ∧ a 4 = 18 ∧ a 5 = 41 ∧
    PublishedRecurrence

end SchreierQ4
