import Mathlib.Tactic.Ring

/-! Optional generating - function certificate; not needed for the linear route. -/

namespace SchreierQ4.PolynomialCertificate

variable {R : Type*} [CommRing R]

/-- The common denominator of the four residue series. -/
def Q (x : R) : R := 1 - 3 * x + 3 * x ^ 2 - 3 * x ^ 3 - 2 * x ^ 4 - x ^ 5

/-- The numerator for starting residue zero. -/
def N0 (x : R) : R := 1 + 2 * x ^ 2

/-- The numerator for starting residue one. -/
def N1 (x : R) : R := 1 + x ^ 3

/-- The numerator for starting residue two. -/
def N2 (x : R) : R := 1 - x + x ^ 2 + x ^ 3 + x ^ 4

/-- The numerator for starting residue three. -/
def N3 (x : R) : R := 1 - 2 * x + 3 * x ^ 2

/-- The four rows of (I - M(x)) * N(x)=Q(x) * (1,1,1,1). -/
theorem kernel_certificate (x : R) :
    ((1 - x) * N0 x - x * N1 x - x * N2 x = Q x) ∧
    ((1 - x) * N1 x - x * N2 x - x * N3 x = Q x) ∧
    ((1 - x) * N2 x - x * N3 x - x ^ 2 * N0 x = Q x) ∧
    ((1 - x) * N3 x - x ^ 2 * N0 x - x ^ 2 * N1 x = Q x) := by
  dsimp [Q, N0, N1, N2, N3]
  exact ⟨by ring, by ring, by ring, by ring⟩

end SchreierQ4.PolynomialCertificate
