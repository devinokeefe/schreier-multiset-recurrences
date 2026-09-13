import SchreierUnified.Words
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

/-!
# Residue-equation uniqueness and polynomial identities

Positive delays determine the coefficient sequences. The polynomial identities
verify the numerators and denominators used for the three cases in the article.
-/

namespace SchreierUnified

/-- Coefficients below zero are absent, not natural-number indices truncated to zero. -/
def delayed (q r : ℕ) (d : Fin 3) (f : ℕ → ℕ → ℤ) (N : ℕ) : ℤ :=
  if 1 + carry q r d ≤ N then
    f (nextResidue q r d) (N - (1 + carry q r d)) else 0

/-- The first-digit equations for all residues below `q`, with empty-word contribution one. -/
def ResidueEquation (q : ℕ) (f : ℕ → ℕ → ℤ) : Prop :=
  ∀ r, r < q → ∀ N,
    f r N = (if N = 0 then 1 else 0) + delayed q r 0 f N +
      delayed q r 1 f N + delayed q r 2 f N

/-- The positive delays determine every coefficient, including its initial value. -/
theorem residue_unique {q : ℕ} (hq : 0 < q) {f g : ℕ → ℕ → ℤ}
    (hf : ResidueEquation q f) (hg : ResidueEquation q g) :
    ∀ N r, r < q → f r N = g r N := by
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
      intro r hr
      have hd (d : Fin 3) : delayed q r d f N = delayed q r d g N := by
        unfold delayed
        split_ifs with hb
        · apply ih (N - (1 + carry q r d)) (by omega)
          exact Nat.mod_lt _ hq
        · rfl
      rw [hf r hr N, hg r hr N, hd 0, hd 1, hd 2]

/-- The finite word counts satisfy the first-digit residue equations. -/
theorem wordCount_equation (q : ℕ) (hq : 0 < q) :
    ResidueEquation q (fun r N => (wordCount q r N : ℤ)) := by
  intro r hr N
  cases N with
  | zero => simp [wordCount_zero q r hr, delayed]
  | succ N =>
      have hd (d : Fin 3) : ((branch q r (N + 1) d).card : ℤ) =
          delayed q r d (fun s k => (wordCount q s k : ℤ)) (N + 1) := by
        unfold branch delayed
        split_ifs <;> rfl
      change (wordCount q r (N + 1) : ℤ) = _
      rw [count_step q r N hq hr]
      simp only [Nat.cast_add, hd]
      simp

/-- A residue-equation certificate identifies the actual independently counted words. -/
theorem wordCount_certificate {q : ℕ} (hq : 0 < q) {f : ℕ → ℕ → ℤ}
    (hf : ResidueEquation q f) :
    ∀ N r, r < q → (wordCount q r N : ℤ) = f r N :=
  residue_unique hq (wordCount_equation q hq) hf

section PolynomialCertificates

variable {R : Type*} [CommRing R]

/-- The common denominator of the two residue series for `q = 2`. -/
def D2 (x : R) : R := 1 - x - 2 * x ^ 2 - x ^ 3

/-- The common denominator of the three residue series for `q = 3`. -/
def D3 (x : R) : R := 1 - 3 * x + 3 * x ^ 2 - 4 * x ^ 3 + 2 * x ^ 4 - x ^ 5

/-- The common denominator of the four residue series for `q = 4`. -/
def D4 (x : R) : R := 1 - 3 * x + 3 * x ^ 2 - 3 * x ^ 3 - 2 * x ^ 4 - x ^ 5

/-- The polynomial whose powers give the residue numerators for `q = 3`. -/
def H (x : R) : R := 1 - x + x ^ 2

/-- The residue-zero numerator for `q = 4`. -/
def N40 (x : R) : R := 1 + 2 * x ^ 2

/-- The residue-one numerator for `q = 4`. -/
def N41 (x : R) : R := 1 + x ^ 3

/-- The residue-two numerator for `q = 4`. -/
def N42 (x : R) : R := 1 - x + x ^ 2 + x ^ 3 + x ^ 4

/-- The residue-three numerator for `q = 4`. -/
def N43 (x : R) : R := 1 - 2 * x + 3 * x ^ 2

/-- The two rows of the q = 2 polynomial certificate. -/
theorem certificate_q2 (x : R) :
    (1 - x - x ^ 2) * (1 + x) - x = D2 x ∧
    (1 - x - x ^ 2) - x ^ 2 * (1 + x) = D2 x := by
  constructor <;> dsimp [D2] <;> ring

/-- The three rows of the q = 3 polynomial certificate. -/
theorem certificate_q3 (x : R) :
    (1 - x) - x * H x - x * (H x) ^ 2 = D3 x ∧
    (1 - x) * H x - x * (H x) ^ 2 - x ^ 2 = D3 x ∧
    (1 - x) * (H x) ^ 2 - x ^ 2 - x ^ 2 * H x = D3 x := by
  refine ⟨?_, ?_, ?_⟩ <;> dsimp [D3, H] <;> ring

/-- The four rows of the q = 4 polynomial certificate. -/
theorem certificate_q4 (x : R) :
    (1 - x) * N40 x - x * N41 x - x * N42 x = D4 x ∧
    (1 - x) * N41 x - x * N42 x - x * N43 x = D4 x ∧
    (1 - x) * N42 x - x * N43 x - x ^ 2 * N40 x = D4 x ∧
    (1 - x) * N43 x - x ^ 2 * N40 x - x ^ 2 * N41 x = D4 x := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> dsimp [D4, N40, N41, N42, N43] <;> ring

end PolynomialCertificates

end SchreierUnified
