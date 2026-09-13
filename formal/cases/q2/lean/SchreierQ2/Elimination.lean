import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega

/-!
Arithmetic elimination of the companion sequence, using addition throughout.
The invariant starts at index two; the coupled recurrences start at index three.
`SchreierQ2.Counting` supplies the concrete counting identities.
-/

namespace SchreierQ2.RecurrenceAlgebra

/-- A conserved additive identity; no subtraction or negative indices are used. -/
theorem invariant_of_coupled
    (u v : ℕ → ℕ)
    (hu : ∀ k : ℕ, u (k + 3) = u (k + 2) + v (k + 2) + u (k + 1))
    (hv : ∀ k : ℕ, v (k + 3) = v (k + 2) + u (k + 1) + v (k + 1))
    (hbase : u 2 = v 2 + v 1) :
    ∀ k : ℕ, u (k + 2) = v (k + 2) + v (k + 1) := by
  intro k
  induction k with
  | zero =>
      simpa using hbase
  | succ k ih =>
      change u (k + 3) = v (k + 3) + v (k + 2)
      have h1 := hu k
      have h2 := hv k
      omega

/-- Express the companion in terms of two consecutive original counts. -/
theorem companion_of_coupled
    (u v : ℕ → ℕ)
    (hu : ∀ k : ℕ, u (k + 3) = u (k + 2) + v (k + 2) + u (k + 1))
    (hv : ∀ k : ℕ, v (k + 3) = v (k + 2) + u (k + 1) + v (k + 1))
    (hbase : u 2 = v 2 + v 1) (k : ℕ) :
    v (k + 3) = u (k + 2) + u (k + 1) := by
  have h1 := invariant_of_coupled u v hu hv hbase k
  have h2 := hv k
  omega

/-- The exact third-order recurrence, in subtraction-free indexing. -/
theorem recurrence_of_coupled
    (u v : ℕ → ℕ)
    (hu : ∀ k : ℕ, u (k + 3) = u (k + 2) + v (k + 2) + u (k + 1))
    (hv : ∀ k : ℕ, v (k + 3) = v (k + 2) + u (k + 1) + v (k + 1))
    (hbase : u 2 = v 2 + v 1) (k : ℕ) :
    u (k + 4) = u (k + 3) + 2 * u (k + 2) + u (k + 1) := by
  have h1 : u (k + 4) = u (k + 3) + v (k + 3) + u (k + 2) := by
    simpa only [Nat.add_assoc] using hu (k + 1)
  have h2 := companion_of_coupled u v hu hv hbase k
  omega

/-- Restore the exact source indexing and its lower bound. -/
theorem source_indexed_recurrence_of_coupled
    (u v : ℕ → ℕ)
    (hu : ∀ k : ℕ, u (k + 3) = u (k + 2) + v (k + 2) + u (k + 1))
    (hv : ∀ k : ℕ, v (k + 3) = v (k + 2) + u (k + 1) + v (k + 1))
    (hbase : u 2 = v 2 + v 1) (n : ℕ) (hn : 4 ≤ n) :
    u n = u (n - 1) + 2 * u (n - 2) + u (n - 3) := by
  have h := recurrence_of_coupled u v hu hv hbase (n - 4)
  have h0 : n - 4 + 4 = n := by omega
  have h1 : n - 4 + 3 = n - 1 := by omega
  have h2 : n - 4 + 2 = n - 2 := by omega
  have h3 : n - 4 + 1 = n - 3 := by omega
  simpa only [h0, h1, h2, h3] using h

end SchreierQ2.RecurrenceAlgebra
