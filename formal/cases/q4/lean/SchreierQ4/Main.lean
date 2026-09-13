import SchreierQ4.WordDynamics

namespace SchreierQ4

/-- The multiset count equals the residue-zero coordinate of the seeded orbit. -/
theorem a_eq_b (N : ℕ) : (a (N + 1) : ℤ) = LinearCertificate.b N := by
  rw [WordCounting.a_eq_wordCount]
  exact WordCounting.wordCount_eq_b N

theorem original_initial :
    a 1 = 1 ∧ a 2 = 3 ∧ a 3 = 8 ∧ a 4 = 18 ∧ a 5 = 41 := by
  have h0 : (a 1 : ℤ) = LinearCertificate.b 0 := a_eq_b 0
  have h1 : (a 2 : ℤ) = LinearCertificate.b 1 := a_eq_b 1
  have h2 : (a 3 : ℤ) = LinearCertificate.b 2 := a_eq_b 2
  have h3 : (a 4 : ℤ) = LinearCertificate.b 3 := a_eq_b 3
  have h4 : (a 5 : ℤ) = LinearCertificate.b 4 := a_eq_b 4
  rcases LinearCertificate.b_initial with ⟨hb0, hb1, hb2, hb3, hb4⟩
  exact ⟨by omega, by omega, by omega, by omega, by omega⟩

/-- Balanced recurrence with only nonnegative shifts, before source reindexing. -/
theorem recurrence_shifted (N : ℕ) :
    (a (N + 6) : ℤ) + 3 * (a (N + 4) : ℤ) =
      3 * (a (N + 5) : ℤ) + 3 * (a (N + 3) : ℤ) +
      2 * (a (N + 2) : ℤ) + (a (N + 1) : ℤ) := by
  have h0 := a_eq_b N
  have h1 : (a (N + 2) : ℤ) = LinearCertificate.b (N + 1) := a_eq_b (N + 1)
  have h2 : (a (N + 3) : ℤ) = LinearCertificate.b (N + 2) := a_eq_b (N + 2)
  have h3 : (a (N + 4) : ℤ) = LinearCertificate.b (N + 3) := a_eq_b (N + 3)
  have h4 : (a (N + 5) : ℤ) = LinearCertificate.b (N + 4) := a_eq_b (N + 4)
  have h5 : (a (N + 6) : ℤ) = LinearCertificate.b (N + 5) := a_eq_b (N + 5)
  have recurrence := LinearCertificate.b_recurrence N
  omega

/-- Translate the balanced shift identity to precisely the published n >= 6 range. -/
theorem publishedRecurrence : PublishedRecurrence := by
  intro n hn
  obtain ⟨N, rfl⟩ : ∃ N : ℕ, n = N + 6 := ⟨n - 6, by omega⟩
  have recurrence := recurrence_shifted N
  change (a (N + 6) : ℤ) =
    3 * (a (N + 5) : ℤ) - 3 * (a (N + 4) : ℤ) +
    3 * (a (N + 3) : ℤ) + 2 * (a (N + 2) : ℤ) + (a (N + 1) : ℤ)
  omega

/-- The initial values and recurrence for the original multiset count. -/
theorem mainClaim : Target := by
  rcases original_initial with ⟨h1, h2, h3, h4, h5⟩
  exact ⟨h1, h2, h3, h4, h5, publishedRecurrence⟩

end SchreierQ4
