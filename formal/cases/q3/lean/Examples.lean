import Encoding

namespace SchreierQ3

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- Direct counts from the original family, independent of count_bridge. -/
theorem direct_initial_values : InitialValues := by
  unfold InitialValues
  decide

-- Inclusive containment, repeated entries, size bounds, and the required maximum.
example : ({1, 1, 2} : Multiset ℕ) ∈ family 2 := by decide
example : ({1, 2, 3} : Multiset ℕ) ∈ family 3 := by decide
example : ({1, 1, 2, 3} : Multiset ℕ) ∉ family 3 := by decide
example : ({1, 1, 1, 2} : Multiset ℕ) ∉ family 2 := by decide
example : ({1} : Multiset ℕ) ∉ family 2 := by decide
example : ({0, 1} : Multiset ℕ) ∉ family 1 := by decide

-- The smallest family and all three multiplicities at n = 2.
example : encode 1 ({1} : Multiset ℕ) = [5] := by decide
example : encode 2 ({2} : Multiset ℕ) = [3, 5] := by decide
example : encode 2 ({1, 2} : Multiset ℕ) = [4, 4] := by decide
example : encode 2 ({1, 1, 2} : Multiset ℕ) = [5, 3] := by decide
-- A cutoff below the actual minimum retains every zero multiplicity.
example : encode 5 ({5} : Multiset ℕ) = [3, 3, 3, 3, 5] := by decide
example : decode 2 [5, 3] = ({1, 1, 2} : Multiset ℕ) := by decide

end SchreierQ3
