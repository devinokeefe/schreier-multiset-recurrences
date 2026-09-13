import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.Fin.Basic
import Lean.Elab.Tactic.Omega

namespace SchreierQ4.WordModel

/-- A finite word with digits zero, one and two. -/
abbrev Word := List (Fin 3)

/-- Sum of the multiplicities encoded by a ternary word. -/
def weight (w : Word) : ℕ := (w.map Fin.val).sum

/-- Cost when the initial residue of the accumulated weight is r. -/
def cost (r : Fin 4) (w : Word) : ℕ :=
  w.length + (r.val + weight w) / 4

/-- The residue after adding digit `d`, reduced modulo four. -/
def nextResidue (r : Fin 4) (d : Fin 3) : Fin 4 :=
  ⟨(r.val + d.val) % 4, Nat.mod_lt _ (by decide)⟩

/-- The quotient produced by adding digit `d` to the starting residue. -/
def carry (r : Fin 4) (d : Fin 3) : ℕ := (r.val + d.val) / 4

@[simp] theorem cost_nil (r : Fin 4) : cost r [] = 0 := by
  have hr := r.isLt
  simp only [cost, weight, List.length_nil, List.map_nil, List.sum_nil,
    Nat.add_zero, Nat.zero_add]
  omega

theorem length_le_cost (r : Fin 4) (w : Word) : w.length ≤ cost r w := by
  dsimp [cost]
  omega

/-- No nonempty word has cost zero, in any starting residue. -/
theorem cost_eq_zero_iff (r : Fin 4) (w : Word) :
    cost r w = 0 ↔ w = [] := by
  constructor
  · intro h
    have hl := length_le_cost r w
    have hz : w.length = 0 := by omega
    exact List.length_eq_zero_iff.mp hz
  · intro h
    subst w
    exact cost_nil r

/-- A ternary digit can wrap around the four residues at most once. -/
theorem carry_le_one (r : Fin 4) (d : Fin 3) : carry r d ≤ 1 := by
  have hr := r.isLt
  have hd := d.isLt
  dsimp [carry]
  omega

/-- Exact first-letter cost decomposition, including the wrap-around charge. -/
theorem cost_cons (r : Fin 4) (d : Fin 3) (w : Word) :
    cost r (d :: w) = 1 + carry r d + cost (nextResidue r d) w := by
  simp only [cost, weight, List.length_cons, List.map_cons, List.sum_cons,
    carry, nextResidue]
  omega

end SchreierQ4.WordModel
