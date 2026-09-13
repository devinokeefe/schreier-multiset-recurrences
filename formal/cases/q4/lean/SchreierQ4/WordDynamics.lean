import SchreierQ4.FiniteWords
import SchreierQ4.LinearCertificate

/-! Disjoint first-letter partitions, their cardinalities, and the seeded orbit. -/

namespace SchreierQ4.WordCounting

open WordModel LinearCertificate

/-- Prepend digit `d` to every word in the finite set. -/
def prepend (d : Fin 3) (s : Finset Word) : Finset Word := s.image (List.cons d)

/-- The disjoint union of suffix sets prefixed by zero, one and two. -/
def join3 (s0 s1 s2 : Finset Word) : Finset Word :=
  prepend 0 s0 ∪ prepend 1 s1 ∪ prepend 2 s2

theorem card_prepend (d : Fin 3) (s : Finset Word) : (prepend d s).card = s.card := by
  apply Finset.card_image_of_injective
  intro u v h
  exact (List.cons.inj h).2

theorem prepend_disjoint {d e : Fin 3} (hde : d ≠ e) (s t : Finset Word) :
    Disjoint (prepend d s) (prepend e t) := by
  apply Finset.disjoint_left.mpr
  intro w hs ht
  obtain ⟨u, _, hu⟩ := Finset.mem_image.mp hs
  obtain ⟨v, _, hv⟩ := Finset.mem_image.mp ht
  exact hde (List.cons.inj (hu.trans hv.symm)).1

theorem card_join3 (s0 s1 s2 : Finset Word) :
    (join3 s0 s1 s2).card = s0.card + s1.card + s2.card := by
  have h01 := prepend_disjoint (d := 0) (e := 1) (by decide) s0 s1
  have h02 := prepend_disjoint (d := 0) (e := 2) (by decide) s0 s2
  have h12 := prepend_disjoint (d := 1) (e := 2) (by decide) s1 s2
  have h012 : Disjoint (prepend 0 s0 ∪ prepend 1 s1) (prepend 2 s2) := by
    apply Finset.disjoint_left.mpr
    intro w hw h2
    rcases Finset.mem_union.mp hw with h0 | h1
    · exact (Finset.disjoint_left.mp h02) h0 h2
    · exact (Finset.disjoint_left.mp h12) h1 h2
  rw [join3, Finset.card_union_of_disjoint h012,
    Finset.card_union_of_disjoint h01]
  simp only [card_prepend]

theorem words_zero (r : Fin 4) : words r 0 = {[]} := by
  apply Finset.ext
  intro w
  simp only [mem_words, Finset.mem_singleton, cost_eq_zero_iff]

theorem wordCount_zero (r : Fin 4) : wordCount r 0 = 1 := by
  simp only [wordCount, words_zero, Finset.card_singleton]

/-- Every displayed union is disjoint because its three heads are distinct. -/
theorem words_0_step (N : ℕ) :
    words 0 (N + 1) = join3 (words 0 N) (words 1 N) (words 2 N) := by
  apply Finset.ext
  intro w
  cases w with
  | nil => simp [mem_words, join3, prepend, Finset.mem_image]
  | cons d w =>
      rcases digit_cases d with h | h | h
      all_goals subst d
      all_goals
        (simp [join3, prepend, Finset.mem_image, mem_words,
          cost_cons, carry, nextResidue]; omega)

theorem words_1_step (N : ℕ) :
    words 1 (N + 1) = join3 (words 1 N) (words 2 N) (words 3 N) := by
  apply Finset.ext
  intro w
  cases w with
  | nil => simp [mem_words, join3, prepend, Finset.mem_image]
  | cons d w =>
      rcases digit_cases d with h | h | h
      all_goals subst d
      all_goals
        (simp [join3, prepend, Finset.mem_image, mem_words,
          cost_cons, carry, nextResidue]; omega)

/-- The wrap-around branch has cost two, so its suffix has cost N. -/
theorem words_2_step (N : ℕ) :
    words 2 (N + 2) = join3 (words 2 (N + 1)) (words 3 (N + 1)) (words 0 N) := by
  apply Finset.ext
  intro w
  cases w with
  | nil => simp [mem_words, join3, prepend, Finset.mem_image]
  | cons d w =>
      rcases digit_cases d with h | h | h
      all_goals subst d
      all_goals
        (simp [join3, prepend, Finset.mem_image, mem_words,
          cost_cons, carry, nextResidue]; omega)

theorem words_3_step (N : ℕ) :
    words 3 (N + 2) = join3 (words 3 (N + 1)) (words 0 N) (words 1 N) := by
  apply Finset.ext
  intro w
  cases w with
  | nil => simp [mem_words, join3, prepend, Finset.mem_image]
  | cons d w =>
      rcases digit_cases d with h | h | h
      all_goals subst d
      all_goals
        (simp [join3, prepend, Finset.mem_image, mem_words,
          cost_cons, carry, nextResidue]; omega)

theorem count_0_step (N : ℕ) :
    wordCount 0 (N + 1) = wordCount 0 N + wordCount 1 N + wordCount 2 N := by
  simpa only [wordCount, card_join3] using congrArg Finset.card (words_0_step N)

theorem count_1_step (N : ℕ) :
    wordCount 1 (N + 1) = wordCount 1 N + wordCount 2 N + wordCount 3 N := by
  simpa only [wordCount, card_join3] using congrArg Finset.card (words_1_step N)

theorem count_2_step (N : ℕ) :
    wordCount 2 (N + 2) = wordCount 2 (N + 1) + wordCount 3 (N + 1) + wordCount 0 N := by
  simpa only [wordCount, card_join3] using congrArg Finset.card (words_2_step N)

theorem count_3_step (N : ℕ) :
    wordCount 3 (N + 2) = wordCount 3 (N + 1) + wordCount 0 N + wordCount 1 N := by
  simpa only [wordCount, card_join3] using congrArg Finset.card (words_3_step N)

/-- Only the auxiliary delayed coordinates are zero at index zero. -/
def countState : ℕ → State
  | 0 => ⟨wordCount 0 0, wordCount 1 0, wordCount 2 0, wordCount 3 0, 0, 0⟩
  | N + 1 => ⟨wordCount 0 (N + 1), wordCount 1 (N + 1),
      wordCount 2 (N + 1), wordCount 3 (N + 1), wordCount 0 N, wordCount 1 N⟩

theorem countState_zero : countState 0 = orbit 0 := by
  simp [countState, wordCount_zero, orbit]

theorem countState_step (N : ℕ) : countState (N + 1) = step (countState N) := by
  cases N with
  | zero => decide
  | succ N =>
      have h0 := count_0_step (N + 1)
      have h1 := count_1_step (N + 1)
      have h2 := count_2_step N
      have h3 := count_3_step N
      dsimp only [countState, step]
      have hindex : N + 1 + 1 = N + 2 := by omega
      simp only [hindex] at h0 h1 ⊢
      congr 1 <;> omega

theorem countState_eq_orbit (N : ℕ) : countState N = orbit N := by
  induction N with
  | zero => exact countState_zero
  | succ N ih =>
      rw [countState_step, ih]
      rfl

/-- The first coordinate is the current residue-zero count at every index. -/
theorem countState_first (N : ℕ) : (countState N).x0 = (wordCount 0 N : ℤ) := by
  cases N <;> rfl

/-- The two delayed coordinates start at zero before any positive cost layer. -/
theorem countState_zero_delays : (countState 0).x4 = 0 ∧ (countState 0).x5 = 0 := by
  exact ⟨rfl, rfl⟩

theorem wordCount_eq_b (N : ℕ) : (wordCount 0 N : ℤ) = b N := by
  rw [← countState_first N, countState_eq_orbit]
  rfl

end SchreierQ4.WordCounting
