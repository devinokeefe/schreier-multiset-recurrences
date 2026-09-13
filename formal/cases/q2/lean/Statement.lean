import Mathlib.Data.Multiset.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Filter

/-!
# Schreier multisets for q = 2

Source: Chu et al., Integers 26 (2026), A53, Section 5, item 1, p. 19.
`family n` consists of actual, uncolored submultisets of
  {1,1,2,2,...,n-1,n-1,n}
that contain n and satisfy card F <= 2 * min F.

The finite-set conversion of the multiset powerset is essential: it removes
repeated presentations of the same uncolored submultiset.

The ambient multiset is empty at n = 0. The target theorem concerns positive
indices and is proved in `SchreierQ2.Counting`.
-/

namespace SchreierQ2

/-- One copy of each positive integer from 1 through k. -/
def below (k : ℕ) : Multiset ℕ :=
  (Multiset.range k).map (fun i => i + 1)

/-- Two copies below the unique maximum; an explicit empty extension at zero. -/
def ambient : ℕ → Multiset ℕ
  | 0 => 0
  | k + 1 => below k + below k + {k + 1}

/-- On a nonempty multiset, the universal bound equals the minimum bound. -/
def admissible (n : ℕ) (F : Multiset ℕ) : Prop :=
  n ∈ F ∧ ∀ x ∈ F.toFinset, F.card ≤ 2 * x

instance admissibleDecidable (n : ℕ) : DecidablePred (admissible n) :=
  fun F => by
    unfold admissible
    infer_instance

/-- The finite family of distinct uncolored admissible submultisets. -/
def family (n : ℕ) : Finset (Multiset ℕ) :=
  (ambient n).powerset.toFinset.filter (admissible n)

/-- The source count, defined without using any recurrence. -/
def a (n : ℕ) : ℕ := (family n).card

/-- The third-order recurrence and its three positive-index initial values. -/
def Target : Prop :=
  a 1 = 1 ∧
  a 2 = 2 ∧
  a 3 = 4 ∧
  ∀ n : ℕ, 4 ≤ n → a n = a (n - 1) + 2 * a (n - 2) + a (n - 3)

end SchreierQ2
