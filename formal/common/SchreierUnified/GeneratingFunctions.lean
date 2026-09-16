import SchreierUnified.Certificates
import SchreierUnified.Multisets
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic

/-!
# Generating functions of the actual multiset counts

The formal series are constructed from the independently enumerated finite word
families. The residue system is proved coefficientwise and has a unique solution
on the residues `r < q`. All identities here are in `ℤ⟦X⟧`.
-/

noncomputable section
namespace SchreierUnified
open PowerSeries

/-- Generating series indexed by word cost (maximum minus one). -/
def wordSeries (q r : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk (fun N => (wordCount q r N : ℤ))

@[simp] theorem coeff_wordSeries (q r N : ℕ) :
    PowerSeries.coeff N (wordSeries q r) = (wordCount q r N : ℤ) := by
  simp [wordSeries]

/-- The series is the ordinary generating function of the original families. -/
theorem wordSeries_eq_familySeries (q r : ℕ) (hq : 0 < q) :
    wordSeries q r = PowerSeries.mk (fun N => ((family q r (N + 1)).card : ℤ)) := by
  ext N
  simp [family_card_eq_wordCount q r N hq]

/-- The finite residue system, as an equality of formal power series. -/
def SeriesResidueEquation (q : ℕ) (F : ℕ → PowerSeries ℤ) : Prop :=
  ∀ r, r < q → F r = 1 +
    X ^ (1 + carry q r 0) * F (nextResidue q r 0) +
    X ^ (1 + carry q r 1) * F (nextResidue q r 1) +
    X ^ (1 + carry q r 2) * F (nextResidue q r 2)

theorem seriesResidueEquation_iff (q : ℕ) (F : ℕ → PowerSeries ℤ) :
    SeriesResidueEquation q F ↔
      ResidueEquation q (fun r N => PowerSeries.coeff N (F r)) := by
  constructor
  · intro h r hr N
    have he := congrArg (PowerSeries.coeff N) (h r hr)
    simpa only [map_add, PowerSeries.coeff_one, PowerSeries.coeff_X_pow_mul', delayed] using he
  · intro h r hr
    apply PowerSeries.ext
    intro N
    simpa only [map_add, PowerSeries.coeff_one, PowerSeries.coeff_X_pow_mul', delayed] using h r hr N

/-- Existence, including `q = 1` and its possible carry of two. -/
theorem wordSeries_equation (q : ℕ) (hq : 0 < q) :
    SeriesResidueEquation q (wordSeries q) := by
  apply (seriesResidueEquation_iff q _).mpr
  simpa only [coeff_wordSeries] using wordCount_equation q hq

/-- Uniqueness is simultaneous in every allowed residue, coefficient by coefficient. -/
theorem seriesResidue_unique (q : ℕ) (hq : 0 < q)
    (F J : ℕ → PowerSeries ℤ)
    (hF : SeriesResidueEquation q F) (hJ : SeriesResidueEquation q J) :
    ∀ r, r < q → F r = J r := by
  intro r hr
  apply PowerSeries.ext
  intro N
  exact residue_unique hq ((seriesResidueEquation_iff q F).mp hF)
    ((seriesResidueEquation_iff q J).mp hJ) N r hr

/-- Polynomial identities expressed in the ambient power-series ring. -/
def SeriesCertificate (q : ℕ) (D : PowerSeries ℤ) (A : ℕ → PowerSeries ℤ) : Prop :=
  ∀ r, r < q → A r -
    X ^ (1 + carry q r 0) * A (nextResidue q r 0) -
    X ^ (1 + carry q r 1) * A (nextResidue q r 1) -
    X ^ (1 + carry q r 2) * A (nextResidue q r 2) = D

/-- Division by a denominator with constant coefficient one solves the system. -/
theorem wordSeries_of_certificate (q : ℕ) (hq : 0 < q)
    (D : PowerSeries ℤ) (A : ℕ → PowerSeries ℤ)
    (hD : PowerSeries.constantCoeff D = 1) (hA : SeriesCertificate q D A) :
    ∀ r, r < q → wordSeries q r = A r * D.invOfUnit 1 := by
  have hDI : D * D.invOfUnit 1 = 1 := PowerSeries.mul_invOfUnit D 1 hD
  apply seriesResidue_unique q hq _ _ (wordSeries_equation q hq)
  intro r hr
  have h := hA r hr
  linear_combination D.invOfUnit 1 * h + hDI

/-- Cross-multiplied form, avoiding any interpretation of division. -/
theorem denominator_mul_wordSeries (q : ℕ) (hq : 0 < q)
    (D : PowerSeries ℤ) (A : ℕ → PowerSeries ℤ)
    (hD : PowerSeries.constantCoeff D = 1) (hA : SeriesCertificate q D A)
    (r : ℕ) (hr : r < q) : D * wordSeries q r = A r := by
  rw [wordSeries_of_certificate q hq D A hD hA r hr]
  calc
    D * (A r * D.invOfUnit 1) = A r * (D * D.invOfUnit 1) := by ring
    _ = A r := by rw [PowerSeries.mul_invOfUnit D 1 hD, mul_one]

/-- Numerator vectors, indexed by natural residues; values outside the range are unused. -/
def numerator2 (r : ℕ) : PowerSeries ℤ := if r = 0 then 1 + X else 1

/-- Numerator vector for the three residue classes when `q = 3`. -/
def numerator3 (r : ℕ) : PowerSeries ℤ :=
  if r = 0 then 1 else if r = 1 then H X else (H X) ^ 2

/-- Numerator vector for the four residue classes when `q = 4`. -/
def numerator4 (r : ℕ) : PowerSeries ℤ :=
  if r = 0 then N40 X else if r = 1 then N41 X else if r = 2 then N42 X else N43 X

theorem seriesCertificate2 : SeriesCertificate 2 (D2 X) numerator2 := by
  intro r hr
  interval_cases r <;> norm_num [numerator2, carry, nextResidue, D2] <;> ring

theorem seriesCertificate3 : SeriesCertificate 3 (D3 X) numerator3 := by
  intro r hr
  interval_cases r <;> norm_num [numerator3, carry, nextResidue, D3, H] <;> ring

theorem seriesCertificate4 : SeriesCertificate 4 (D4 X) numerator4 := by
  intro r hr
  interval_cases r <;> norm_num [numerator4, carry, nextResidue, D4, N40, N41, N42, N43] <;> ring

theorem D2_constantCoeff : PowerSeries.constantCoeff (D2 (X : PowerSeries ℤ)) = 1 := by
  simp [D2]

theorem D3_constantCoeff : PowerSeries.constantCoeff (D3 (X : PowerSeries ℤ)) = 1 := by
  simp [D3]

theorem D4_constantCoeff : PowerSeries.constantCoeff (D4 (X : PowerSeries ℤ)) = 1 := by
  simp [D4]

/-- All nine rational generating-function identities, over the integers. -/
theorem generatingFunctions2 (r : ℕ) (hr : r < 2) :
    wordSeries 2 r = numerator2 r * (D2 X).invOfUnit 1 :=
  wordSeries_of_certificate 2 (by decide) _ _ D2_constantCoeff seriesCertificate2 r hr

theorem generatingFunctions3 (r : ℕ) (hr : r < 3) :
    wordSeries 3 r = numerator3 r * (D3 X).invOfUnit 1 :=
  wordSeries_of_certificate 3 (by decide) _ _ D3_constantCoeff seriesCertificate3 r hr

theorem generatingFunctions4 (r : ℕ) (hr : r < 4) :
    wordSeries 4 r = numerator4 r * (D4 X).invOfUnit 1 :=
  wordSeries_of_certificate 4 (by decide) _ _ D4_constantCoeff seriesCertificate4 r hr

theorem D2_mul_wordSeries : D2 X * wordSeries 2 0 = 1 + X := by
  simpa [numerator2] using denominator_mul_wordSeries 2 (by decide) _ _
    D2_constantCoeff seriesCertificate2 0 (by decide)

theorem D3_mul_wordSeries : D3 X * wordSeries 3 0 = 1 := by
  simpa [numerator3] using denominator_mul_wordSeries 3 (by decide) _ _
    D3_constantCoeff seriesCertificate3 0 (by decide)

theorem D4_mul_wordSeries : D4 X * wordSeries 4 0 = 1 + 2 * X ^ 2 := by
  simpa [numerator4, N40] using denominator_mul_wordSeries 4 (by decide) _ _
    D4_constantCoeff seriesCertificate4 0 (by decide)

#print axioms SchreierUnified.wordSeries_equation
#print axioms SchreierUnified.seriesResidue_unique
#print axioms SchreierUnified.generatingFunctions4

end SchreierUnified
