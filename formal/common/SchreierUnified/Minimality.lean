import SchreierUnified.GeneratingFunctions
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic

/-!
# Eventual recurrence orders

A recurrence is defined directly on coefficients, with an arbitrary starting
index. The polynomial-multiplier characterisation is proved, rather than
assumed. Explicit Bezout certificates then rule out every smaller order.
-/

noncomputable section
namespace SchreierUnified
open scoped BigOperators

/-- A homogeneous rational recurrence of order at most `d`, valid eventually.
The coefficient of the current term is normalised to one. -/
def HasEventualRecurrence (a : ℕ → ℚ) (d : ℕ) : Prop :=
  ∃ c : ℕ → ℚ, c 0 = 1 ∧ ∃ B : ℕ, ∀ n : ℕ, B ≤ n → d ≤ n →
    ∑ i ∈ Finset.range (d + 1), c i * a (n - i) = 0

/-- The polynomial associated with the finitely many recurrence coefficients. -/
def recurrencePolynomial (c : ℕ → ℚ) (d : ℕ) : Polynomial ℚ :=
  ∑ i ∈ Finset.range (d + 1), Polynomial.C (c i) * Polynomial.X ^ i

theorem recurrencePolynomial_coeff (c : ℕ → ℚ) (d n : ℕ) :
    (recurrencePolynomial c d).coeff n = if n ≤ d then c n else 0 := by
  simp [recurrencePolynomial]

theorem recurrencePolynomial_degree (c : ℕ → ℚ) (d : ℕ) :
    (recurrencePolynomial c d).natDegree ≤ d := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  simp [recurrencePolynomial_coeff, Nat.not_le.mpr hn]

theorem recurrencePolynomial_reconstruct (R : Polynomial ℚ) (d : ℕ)
    (hd : R.natDegree ≤ d) : recurrencePolynomial R.coeff d = R := by
  ext n
  rw [recurrencePolynomial_coeff]
  split_ifs with hn
  · rfl
  · exact (Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)).symm

theorem recurrencePolynomial_coe (c : ℕ → ℚ) (d : ℕ) :
    (recurrencePolynomial c d : PowerSeries ℚ) =
      ∑ i ∈ Finset.range (d + 1), PowerSeries.C (c i) * PowerSeries.X ^ i := by
  change Polynomial.coeToPowerSeries.ringHom (recurrencePolynomial c d) = _
  simp [recurrencePolynomial]

/-- Coefficient extraction at every index, including indices below the degree.
The guards implement the convention that negative-index coefficients vanish. -/
theorem recurrencePolynomial_mul_coeff_all (c : ℕ → ℚ) (d n : ℕ)
    (F : PowerSeries ℚ) :
    PowerSeries.coeff n ((recurrencePolynomial c d : PowerSeries ℚ) * F) =
      ∑ i ∈ Finset.range (d + 1),
        if i ≤ n then c i * PowerSeries.coeff (n - i) F else 0 := by
  rw [recurrencePolynomial_coe, Finset.sum_mul]
  simp only [map_sum, mul_assoc, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_X_pow_mul', mul_ite, mul_zero]

/-- The coefficient equation used for both the initial values and the tail. -/
theorem coefficient_extraction (D N : Polynomial ℚ) (F : PowerSeries ℚ)
    (d n : ℕ) (hd : D.natDegree ≤ d) (h : (D : PowerSeries ℚ) * F = N) :
    (∑ i ∈ Finset.range (d + 1),
      if i ≤ n then D.coeff i * PowerSeries.coeff (n - i) F else 0) = N.coeff n := by
  rw [← recurrencePolynomial_mul_coeff_all, recurrencePolynomial_reconstruct D d hd,
    h, Polynomial.coeff_coe]

/-- Coefficient extraction, without any assumption that the recurrence holds. -/
theorem recurrencePolynomial_mul_coeff (c : ℕ → ℚ) (d n : ℕ)
    (F : PowerSeries ℚ) (hn : d ≤ n) :
    PowerSeries.coeff n ((recurrencePolynomial c d : PowerSeries ℚ) * F) =
      ∑ i ∈ Finset.range (d + 1), c i * PowerSeries.coeff (n - i) F := by
  rw [recurrencePolynomial_coe, Finset.sum_mul]
  simp only [map_sum, mul_assoc, PowerSeries.coeff_C_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [PowerSeries.coeff_X_pow_mul', ite_eq_left (by have := Finset.mem_range.mp hi; omega)]

/-- A series whose coefficients eventually vanish is an actual polynomial. -/
theorem polynomial_of_eventually_zero (F : PowerSeries ℚ) (B : ℕ)
    (h : ∀ n, B ≤ n → PowerSeries.coeff n F = 0) :
    ∃ P : Polynomial ℚ, F = P := by
  refine ⟨PowerSeries.trunc B F, ?_⟩
  apply PowerSeries.ext
  intro n
  rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
  split_ifs with hn
  · rfl
  · exact h n (by omega)

/-- The standard eventual-recurrence condition is equivalent to a normalised
polynomial multiplier of bounded degree taking the series to a polynomial. -/
theorem eventualRecurrence_iff_polynomial_multiplier (F : PowerSeries ℚ) (d : ℕ) :
    HasEventualRecurrence (fun n => PowerSeries.coeff n F) d ↔
      ∃ R P : Polynomial ℚ, R.coeff 0 = 1 ∧ R.natDegree ≤ d ∧
        (R : PowerSeries ℚ) * F = P := by
  constructor
  · rintro ⟨c, hc, B, hB⟩
    let R := recurrencePolynomial c d
    have hz : ∀ n, max B d ≤ n → PowerSeries.coeff n ((R : PowerSeries ℚ) * F) = 0 := by
      intro n hn
      rw [recurrencePolynomial_mul_coeff c d n F (by omega)]
      exact hB n (by omega) (by omega)
    obtain ⟨P, hP⟩ := polynomial_of_eventually_zero ((R : PowerSeries ℚ) * F) (max B d) hz
    refine ⟨R, P, ?_, recurrencePolynomial_degree c d, hP⟩
    simp [R, recurrencePolynomial_coeff, hc]
  · rintro ⟨R, P, hR, hd, hP⟩
    refine ⟨R.coeff, hR, P.natDegree + 1, ?_⟩
    intro n hn hdn
    rw [← recurrencePolynomial_mul_coeff R.coeff d n F hdn,
      recurrencePolynomial_reconstruct R d hd, hP, Polynomial.coeff_coe]
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)

/-- A reduced denominator divides every polynomial that kills the tail. -/
theorem denominator_dvd_multiplier (F : PowerSeries ℚ)
    (D N U V R P : Polynomial ℚ)
    (hbez : U * N + V * D = 1)
    (hDN : (D : PowerSeries ℚ) * F = N)
    (hRP : (R : PowerSeries ℚ) * F = P) : D ∣ R := by
  have hcross : R * N = D * P := by
    apply Polynomial.coe_injective ℚ
    simp only [Polynomial.coe_mul]
    rw [← hDN, ← hRP]
    ring
  refine ⟨U * P + V * R, ?_⟩
  calc
    R = R * (U * N + V * D) := by rw [hbez, mul_one]
    _ = U * (R * N) + D * (V * R) := by ring
    _ = D * (U * P + V * R) := by rw [hcross]; ring

/-- The lower bound is independent of the starting index of the recurrence. -/
theorem denominator_degree_lower_bound (F : PowerSeries ℚ)
    (D N U V : Polynomial ℚ) (hbez : U * N + V * D = 1)
    (hDN : (D : PowerSeries ℚ) * F = N) (d : ℕ)
    (hrec : HasEventualRecurrence (fun n => PowerSeries.coeff n F) d) :
    D.natDegree ≤ d := by
  obtain ⟨R, P, hR, hd, hRP⟩ := (eventualRecurrence_iff_polynomial_multiplier F d).mp hrec
  have hne : R ≠ 0 := by intro h; simp [h] at hR
  exact (Polynomial.natDegree_le_of_dvd
    (denominator_dvd_multiplier F D N U V R P hbez hDN hRP) hne).trans hd

/-- Rational coefficients of the same independently counted word family. -/
def rationalWordSeries (q : ℕ) : PowerSeries ℚ :=
  PowerSeries.map (Int.castRingHom ℚ) (wordSeries q 0)

@[simp] theorem coeff_rationalWordSeries (q n : ℕ) :
    PowerSeries.coeff n (rationalWordSeries q) = (wordCount q 0 n : ℚ) := by
  simp [rationalWordSeries]

theorem rational_identity2 :
    ((D2 Polynomial.X : Polynomial ℚ) : PowerSeries ℚ) * rationalWordSeries 2 =
      ((1 + Polynomial.X : Polynomial ℚ) : PowerSeries ℚ) := by
  have h := congrArg (PowerSeries.map (Int.castRingHom ℚ)) D2_mul_wordSeries
  norm_num [rationalWordSeries, D2] at h ⊢
  exact h

theorem rational_identity3 :
    ((D3 Polynomial.X : Polynomial ℚ) : PowerSeries ℚ) * rationalWordSeries 3 =
      ((1 : Polynomial ℚ) : PowerSeries ℚ) := by
  have h := congrArg (PowerSeries.map (Int.castRingHom ℚ)) D3_mul_wordSeries
  norm_num [rationalWordSeries, D3] at h ⊢
  exact h

theorem rational_identity4 :
    ((D4 Polynomial.X : Polynomial ℚ) : PowerSeries ℚ) * rationalWordSeries 4 =
      ((N40 Polynomial.X : Polynomial ℚ) : PowerSeries ℚ) := by
  have h := congrArg (PowerSeries.map (Int.castRingHom ℚ)) D4_mul_wordSeries
  norm_num [rationalWordSeries, D4, N40] at h ⊢
  exact h

/-- Explicit coprimality certificate for q = 2. -/
theorem bezout2 :
    ((Polynomial.X : Polynomial ℚ)^2 + Polynomial.X) * (1 + Polynomial.X) +
      D2 Polynomial.X = 1 := by
  dsimp [D2]
  ring

/-- Integral form of the q = 4 Bezout certificate. -/
theorem bezout4_integral :
    (28 * (Polynomial.X : Polynomial ℚ)^4 + 40 * Polynomial.X^3 +
      38 * Polynomial.X^2 - 152 * Polynomial.X + 113) * N40 Polynomial.X +
      (56 * Polynomial.X - 32) * D4 Polynomial.X = 81 := by
  dsimp [D4, N40]
  ring

/-- Explicit coprimality certificate for q = 4. -/
theorem bezout4 :
    ((1/81 : ℚ) • (28 * (Polynomial.X : Polynomial ℚ)^4 +
      40 * Polynomial.X^3 + 38 * Polynomial.X^2 - 152 * Polynomial.X + 113)) *
      N40 Polynomial.X +
      ((1/81 : ℚ) • (56 * Polynomial.X - 32)) * D4 Polynomial.X = 1 := by
  rw [smul_mul_assoc, smul_mul_assoc, ← smul_add, bezout4_integral]
  have h81 : (81 : Polynomial ℚ) = (81 : ℚ) • (1 : Polynomial ℚ) := by
    norm_num [Polynomial.smul_eq_C_mul]
  rw [h81, smul_smul]
  norm_num

theorem degree_D2 : (D2 (Polynomial.X : Polynomial ℚ)).natDegree = 3 := by
  unfold D2
  compute_degree!

theorem degree_D3 : (D3 (Polynomial.X : Polynomial ℚ)).natDegree = 5 := by
  unfold D3
  compute_degree!

theorem degree_D4 : (D4 (Polynomial.X : Polynomial ℚ)).natDegree = 5 := by
  unfold D4
  compute_degree!

/-- The minimal eventual order for q = 2 is exactly three. -/
theorem minimal_order2 :
    HasEventualRecurrence (fun n => (wordCount 2 0 n : ℚ)) 3 ∧
      ∀ d, HasEventualRecurrence (fun n => (wordCount 2 0 n : ℚ)) d → 3 ≤ d := by
  constructor
  · have h := (eventualRecurrence_iff_polynomial_multiplier (rationalWordSeries 2) 3).mpr
      ⟨D2 Polynomial.X, 1 + Polynomial.X, by simp [D2], degree_D2.le, rational_identity2⟩
    simpa using h
  · intro d hd
    have h := denominator_degree_lower_bound (rationalWordSeries 2)
      (D2 Polynomial.X) (1 + Polynomial.X) (Polynomial.X^2 + Polynomial.X) 1
      (by simpa using bezout2) rational_identity2 d (by simpa using hd)
    simpa [degree_D2] using h

/-- The minimal eventual order for q = 3 is exactly five. -/
theorem minimal_order3 :
    HasEventualRecurrence (fun n => (wordCount 3 0 n : ℚ)) 5 ∧
      ∀ d, HasEventualRecurrence (fun n => (wordCount 3 0 n : ℚ)) d → 5 ≤ d := by
  constructor
  · have h := (eventualRecurrence_iff_polynomial_multiplier (rationalWordSeries 3) 5).mpr
      ⟨D3 Polynomial.X, 1, by simp [D3], degree_D3.le, rational_identity3⟩
    simpa using h
  · intro d hd
    have h := denominator_degree_lower_bound (rationalWordSeries 3)
      (D3 Polynomial.X) 1 1 0 (by simp) rational_identity3 d (by simpa using hd)
    simpa [degree_D3] using h

/-- The minimal eventual order for q = 4 is exactly five. -/
theorem minimal_order4 :
    HasEventualRecurrence (fun n => (wordCount 4 0 n : ℚ)) 5 ∧
      ∀ d, HasEventualRecurrence (fun n => (wordCount 4 0 n : ℚ)) d → 5 ≤ d := by
  constructor
  · have h := (eventualRecurrence_iff_polynomial_multiplier (rationalWordSeries 4) 5).mpr
      ⟨D4 Polynomial.X, N40 Polynomial.X, by simp [D4], degree_D4.le, rational_identity4⟩
    simpa using h
  · intro d hd
    have h := denominator_degree_lower_bound (rationalWordSeries 4)
      (D4 Polynomial.X) (N40 Polynomial.X) _ _ bezout4 rational_identity4 d
      (by simpa using hd)
    simpa [degree_D4] using h

/-- The three minimality statements for the original multiset counts, indexed
from maximum one, as in the generating functions of the paper. -/
theorem original_minimal_orders :
    (HasEventualRecurrence (fun n => ((family 2 0 (n+1)).card : ℚ)) 3 ∧
      ∀ d, HasEventualRecurrence (fun n => ((family 2 0 (n+1)).card : ℚ)) d → 3 ≤ d) ∧
    (HasEventualRecurrence (fun n => ((family 3 0 (n+1)).card : ℚ)) 5 ∧
      ∀ d, HasEventualRecurrence (fun n => ((family 3 0 (n+1)).card : ℚ)) d → 5 ≤ d) ∧
    (HasEventualRecurrence (fun n => ((family 4 0 (n+1)).card : ℚ)) 5 ∧
      ∀ d, HasEventualRecurrence (fun n => ((family 4 0 (n+1)).card : ℚ)) d → 5 ≤ d) := by
  simpa only [family_card_eq_wordCount 2 0 _ (by decide),
    family_card_eq_wordCount 3 0 _ (by decide),
    family_card_eq_wordCount 4 0 _ (by decide)] using
      And.intro minimal_order2 (And.intro minimal_order3 minimal_order4)

#print axioms SchreierUnified.coefficient_extraction
#print axioms SchreierUnified.eventualRecurrence_iff_polynomial_multiplier
#print axioms SchreierUnified.original_minimal_orders

end SchreierUnified
