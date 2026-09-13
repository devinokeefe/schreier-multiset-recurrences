import SchreierQ4.WordArithmetic

/-!
A six-integer certificate for the seeded word-count dynamics.
Coordinates x0 through x3 are the four residue counts; x4 and x5 are the
previous cost layer of residues 0 and 1. Integer arithmetic propagates the
seed relation. Only the later original-object bridge identifies b with a.
-/

namespace SchreierQ4.LinearCertificate

/-- Four current counts and two delayed counts, represented over the integers. -/
structure State where
  /-- The current count at residue 0. -/
  x0 : ℤ
  /-- The current count at residue 1. -/
  x1 : ℤ
  /-- The current count at residue 2. -/
  x2 : ℤ
  /-- The current count at residue 3. -/
  x3 : ℤ
  /-- The previous cost-layer count at residue 0. -/
  x4 : ℤ
  /-- The previous cost-layer count at residue 1. -/
  x5 : ℤ
  deriving DecidableEq

/-- Advance the four residue counts and retain the two counts needed for the next delay. -/
def step (v : State) : State :=
  ⟨v.x0 + v.x1 + v.x2, v.x1 + v.x2 + v.x3,
   v.x2 + v.x3 + v.x4, v.x3 + v.x4 + v.x5, v.x0, v.x1⟩

/-- Iterates of `step`, starting from the four empty-word counts and two zero delays. -/
def orbit : ℕ → State
  | 0 => ⟨1, 1, 1, 1, 0, 0⟩
  | n + 1 => step (orbit n)

/-- The balanced recurrence, imposed on each of the six coordinates. -/
def Relation (u v w x y z : State) : Prop :=
  u.x0 + 3 * v.x0 = 3 * w.x0 + 3 * x.x0 + 2 * y.x0 + z.x0 ∧
  u.x1 + 3 * v.x1 = 3 * w.x1 + 3 * x.x1 + 2 * y.x1 + z.x1 ∧
  u.x2 + 3 * v.x2 = 3 * w.x2 + 3 * x.x2 + 2 * y.x2 + z.x2 ∧
  u.x3 + 3 * v.x3 = 3 * w.x3 + 3 * x.x3 + 2 * y.x3 + z.x3 ∧
  u.x4 + 3 * v.x4 = 3 * w.x4 + 3 * x.x4 + 2 * y.x4 + z.x4 ∧
  u.x5 + 3 * v.x5 = 3 * w.x5 + 3 * x.x5 + 2 * y.x5 + z.x5

theorem relation_step {u v w x y z : State} (h : Relation u v w x y z) :
    Relation (step u) (step v) (step w) (step x) (step y) (step z) := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  dsimp [Relation, step]
  exact ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩

/-- The recurrence polynomial annihilates the initial state of the orbit. -/
theorem seed_relation :
    Relation (orbit 5) (orbit 3) (orbit 4) (orbit 2) (orbit 1) (orbit 0) := by
  unfold Relation
  decide

theorem orbit_relation (n : ℕ) :
    Relation (orbit (n + 5)) (orbit (n + 3)) (orbit (n + 4))
      (orbit (n + 2)) (orbit (n + 1)) (orbit n) := by
  induction n with
  | zero => exact seed_relation
  | succ n ih =>
      change Relation (step (orbit (n + 5))) (step (orbit (n + 3)))
        (step (orbit (n + 4))) (step (orbit (n + 2)))
        (step (orbit (n + 1))) (step (orbit n))
      exact relation_step ih

/-- The residue-zero coordinate of the seeded orbit. -/
def b (n : ℕ) : ℤ := (orbit n).x0

theorem b_recurrence (n : ℕ) :
    b (n + 5) + 3 * b (n + 3) =
      3 * b (n + 4) + 3 * b (n + 2) + 2 * b (n + 1) + b n := by
  exact (orbit_relation n).1

theorem b_initial :
    b 0 = 1 ∧ b 1 = 3 ∧ b 2 = 8 ∧ b 3 = 18 ∧ b 4 = 41 := by
  decide

end SchreierQ4.LinearCertificate
