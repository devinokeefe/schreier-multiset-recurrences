import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Union
import Lean.Elab.Tactic.Omega

/-!
# Ternary words and residue equations

The digits encode multiplicities. Splitting words by their first digit gives
the finite partitions and count equations used in the article.
-/

namespace SchreierUnified

/-- A finite word whose digits record multiplicities zero, one or two. -/
abbrev Word := List (Fin 3)

/-- The sum of the multiplicities in a word. -/
def weight (w : Word) : ℕ := (w.map Fin.val).sum

/-- The word length plus the quotient of the weight-plus-margin sum by `q`. -/
def cost (q r : ℕ) (w : Word) : ℕ := w.length + (weight w + r) / q

/-- The quotient produced by adding digit `d` to residue `r`. -/
def carry (q r : ℕ) (d : Fin 3) : ℕ := (r + d.val) / q

/-- The residue after adding digit `d`, reduced modulo `q`. -/
def nextResidue (q r : ℕ) (d : Fin 3) : ℕ := (r + d.val) % q

theorem quotient_add (q a b : ℕ) (hq : 0 < q) :
    (a + b) / q = a / q + (a % q + b) / q := by
  have h := Nat.mod_add_div a q
  have he : a + b = (a % q + b) + q * (a / q) := by omega
  rw [he, Nat.add_mul_div_left _ _ hq]
  omega

@[simp] theorem cost_nil (q r : ℕ) (hr : r < q) : cost q r [] = 0 := by
  simp [cost, weight, Nat.div_eq_of_lt hr]

theorem length_le_cost (q r : ℕ) (w : Word) : w.length ≤ cost q r w := by
  exact Nat.le_add_right _ _

theorem cost_eq_zero_iff (q r : ℕ) (hr : r < q) (w : Word) :
    cost q r w = 0 ↔ w = [] := by
  constructor
  · intro h
    have hl := length_le_cost q r w
    exact List.length_eq_zero_iff.mp (by omega)
  · rintro rfl
    exact cost_nil q r hr

/-- For `q ≥ 2`, a ternary digit crosses at most one residue boundary. -/
theorem carry_le_one (q r : ℕ) (hq : 2 ≤ q) (hr : r < q) (d : Fin 3) :
    carry q r d ≤ 1 := by
  have hd := d.isLt
  have h : (r + d.val) / q < 2 :=
    (Nat.div_lt_iff_lt_mul (by omega : 0 < q)).mpr (by omega)
  exact Nat.le_of_lt_succ h

theorem cost_cons (q r : ℕ) (d : Fin 3) (w : Word) (hq : 0 < q) :
    cost q r (d :: w) = 1 + carry q r d + cost q (nextResidue q r d) w := by
  change w.length + 1 + (d.val + weight w + r) / q =
    1 + (r + d.val) / q + (w.length + (weight w + (r + d.val) % q) / q)
  rw [show d.val + weight w + r = (r + d.val) + weight w by omega,
    quotient_add q (r + d.val) (weight w) hq]
  rw [Nat.add_comm ((r + d.val) % q) (weight w)]
  omega

theorem cost_append (q r : ℕ) (d : Fin 3) (w : Word) (hq : 0 < q) :
    cost q r (w ++ [d]) = 1 + carry q r d + cost q (nextResidue q r d) w := by
  calc
    cost q r (w ++ [d]) = cost q r (d :: w) := by
      simp [cost, weight, Nat.add_comm, Nat.add_assoc]
    _ = _ := cost_cons q r d w hq

theorem digit_cases (d : Fin 3) : d = 0 ∨ d = 1 ∨ d = 2 := by
  have hd := d.isLt
  have hv : d.val = 0 ∨ d.val = 1 ∨ d.val = 2 := by omega
  rcases hv with h | h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Or.inl (Fin.ext h))
  · exact Or.inr (Or.inr (Fin.ext h))

/-- All ternary words of length at most the given bound, including the empty word. -/
def boundedWords : ℕ → Finset Word
  | 0 => {[]}
  | N + 1 => {[]} ∪
      ((boundedWords N).image (List.cons 0) ∪
       (boundedWords N).image (List.cons 1) ∪
       (boundedWords N).image (List.cons 2))

theorem mem_boundedWords (N : ℕ) (w : Word) :
    w ∈ boundedWords N ↔ w.length ≤ N := by
  induction N generalizing w with
  | zero => cases w <;> simp [boundedWords]
  | succ N ih =>
      cases w with
      | nil => simp [boundedWords]
      | cons d w =>
          rcases digit_cases d with h | h | h
          all_goals subst d
          all_goals simp [boundedWords, Finset.mem_image, ih]

/-- An explicit finite enumeration, independent of the multiset family. -/
def words (q r N : ℕ) : Finset Word :=
  (boundedWords N).filter (fun w => cost q r w = N)

theorem mem_words (q r N : ℕ) (w : Word) :
    w ∈ words q r N ↔ cost q r w = N := by
  rw [words, Finset.mem_filter, mem_boundedWords]
  constructor
  · exact And.right
  · intro h
    have hl := length_le_cost q r w
    exact ⟨by omega, h⟩

/-- The number of words of cost `N` at parameter `q` and margin `r`. -/
def wordCount (q r N : ℕ) : ℕ := (words q r N).card

theorem words_zero (q r : ℕ) (hr : r < q) : words q r 0 = {[]} := by
  ext w
  simp only [mem_words, Finset.mem_singleton, cost_eq_zero_iff q r hr]

theorem wordCount_zero (q r : ℕ) (hr : r < q) : wordCount q r 0 = 1 := by
  simp only [wordCount, words_zero q r hr, Finset.card_singleton]

/-- Prepend the same digit to each word in a finite set. -/
def prepend (d : Fin 3) (s : Finset Word) : Finset Word := s.image (List.cons d)

/-- Join three sets of suffixes after prefixing them with digits zero, one and two. -/
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
  rw [join3, Finset.card_union_of_disjoint h012, Finset.card_union_of_disjoint h01]
  simp only [card_prepend]

/-- The guard prevents a negative coefficient index from becoming a false zero-cost term. -/
def branch (q r N : ℕ) (d : Fin 3) : Finset Word :=
  if 1 + carry q r d ≤ N then
    words q (nextResidue q r d) (N - (1 + carry q r d)) else ∅

theorem mem_branch (q r N : ℕ) (d : Fin 3) (w : Word) :
    w ∈ branch q r N d ↔ 1 + carry q r d + cost q (nextResidue q r d) w = N := by
  unfold branch
  split_ifs with h
  · rw [mem_words]
    omega
  · simp only [Finset.notMem_empty, false_iff]
    omega

/-- Disjoint first-digit partition for every positive cost, including q = 1. -/
theorem residue_partition (q r N : ℕ) (hq : 0 < q) (hr : r < q) :
    words q r (N + 1) =
      join3 (branch q r (N + 1) 0) (branch q r (N + 1) 1)
        (branch q r (N + 1) 2) := by
  ext w
  cases w with
  | nil => simp [mem_words, cost_nil q r hr, join3, prepend, Finset.mem_image]
  | cons d w =>
      rcases digit_cases d with h | h | h
      all_goals subst d
      all_goals
        simp [join3, prepend, Finset.mem_image, mem_words, mem_branch,
          cost_cons, hq]

theorem count_step (q r N : ℕ) (hq : 0 < q) (hr : r < q) :
    wordCount q r (N + 1) =
      (branch q r (N + 1) 0).card + (branch q r (N + 1) 1).card +
        (branch q r (N + 1) 2).card := by
  simpa only [wordCount, card_join3] using
    congrArg Finset.card (residue_partition q r N hq hr)

end SchreierUnified
