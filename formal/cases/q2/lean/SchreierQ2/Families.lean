import SchreierQ2.Ambient
import SchreierQ2.Companion
import Mathlib.Data.Fintype.Card

/-! Margin families, multiplicity parts and cardinality transport. -/

namespace SchreierQ2

/-- The Schreier inequality with margin `δ`, expressed at every member of the multiset. -/
def Bound (δ : ℕ) (F : Multiset ℕ) : Prop :=
  ∀ x ∈ F, F.card + δ ≤ 2 * x

/-- The required support and multiplicities together with the margin inequality. -/
def Good (δ n : ℕ) (F : Multiset ℕ) : Prop := Shape n F ∧ Bound δ F

/-- Admissible submultisets of maximum `n` with margin `δ`. -/
def familyD (δ n : ℕ) : Finset (Multiset ℕ) :=
  (ambient n).powerset.toFinset.filter
    (fun F => n ∈ F ∧ ∀ x ∈ F.toFinset, F.card + δ ≤ 2 * x)

@[simp] theorem mem_familyD_literal (δ n : ℕ) (F : Multiset ℕ) :
    F ∈ familyD δ n ↔
      F ≤ ambient n ∧ n ∈ F ∧ ∀ x ∈ F, F.card + δ ≤ 2 * x := by
  simp [familyD]

theorem mem_familyD_iff {δ n : ℕ} {F : Multiset ℕ} (hn : 1 ≤ n) :
    F ∈ familyD δ n ↔ Good δ n F := by
  rw [mem_familyD_literal]
  constructor
  · rintro ⟨hle, hm, hb⟩
    exact ⟨(shape_iff_original hn).mpr ⟨hle, hm⟩, hb⟩
  · rintro ⟨hs, hb⟩
    obtain ⟨hle, hm⟩ := (shape_iff_original hn).mp hs
    exact ⟨hle, hm, hb⟩

@[simp] theorem familyD_zero (n : ℕ) : familyD 0 n = family n := by
  ext F
  simp only [mem_familyD_literal, mem_family_iff, Nat.add_zero]

@[simp] theorem familyD_one (n : ℕ) : familyD 1 n = strictFamily n := by
  ext F
  simp only [mem_familyD_literal, mem_strictFamily_iff]

/-- The part of `familyD δ n` having exactly `j` copies of `n - 1`. -/
def part (δ n j : ℕ) : Finset (Multiset ℕ) :=
  (familyD δ n).filter (fun F => F.count (n - 1) = j)

theorem mem_part_iff {δ n j : ℕ} {F : Multiset ℕ} (hn : 1 ≤ n) :
    F ∈ part δ n j ↔ Good δ n F ∧ F.count (n - 1) = j := by
  simp only [part, Finset.mem_filter, mem_familyD_iff hn]

/-- Ordinary finite-set subtype equivalence with the specified, total maps. -/
def equivOfMaps {s t : Finset (Multiset ℕ)}
    (f g : Multiset ℕ → Multiset ℕ)
    (hf : ∀ F ∈ s, f F ∈ t) (hg : ∀ G ∈ t, g G ∈ s)
    (hgf : ∀ F ∈ s, g (f F) = F) (hfg : ∀ G ∈ t, f (g G) = G) :
    ↥s ≃ ↥t where
  toFun F := ⟨f F.val, hf F.val F.property⟩
  invFun G := ⟨g G.val, hg G.val G.property⟩
  left_inv F := Subtype.ext (hgf F.val F.property)
  right_inv G := Subtype.ext (hfg G.val G.property)

theorem card_eq_of_equiv {s t : Finset (Multiset ℕ)} (e : ↥s ≃ ↥t) :
    s.card = t.card := by
  simpa only [Fintype.card_coe] using Fintype.card_congr e

end SchreierQ2
