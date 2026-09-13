import SchreierUnified.Multisets
import SchreierQ2.Counting

namespace SchreierUnified.Q2Adapter

/-- Positive-index equality of the actual ambient multisets. -/
theorem ambient_bridge (N : ℕ) : ambient (N + 1) = SchreierQ2.ambient (N + 1) := by
  apply Multiset.ext.mpr
  intro x
  rw [count_ambient_succ, SchreierQ2.count_ambient_succ]

theorem family_bridge (r N : ℕ) :
    family 2 r (N + 1) = SchreierQ2.familyD r (N + 1) := by
  ext F
  simp only [mem_family, SchreierQ2.mem_familyD_literal, ambient_bridge]

theorem relaxed_bridge (N : ℕ) : family 2 0 (N + 1) = SchreierQ2.family (N + 1) := by
  rw [family_bridge, SchreierQ2.familyD_zero]

theorem strict_bridge (N : ℕ) : family 2 1 (N + 1) = SchreierQ2.strictFamily (N + 1) := by
  rw [family_bridge, SchreierQ2.familyD_one]

theorem count_bridge (N : ℕ) : SchreierQ2.a (N + 1) = wordCount 2 0 N := by
  unfold SchreierQ2.a
  rw [← relaxed_bridge]
  exact family_card_eq_wordCount 2 0 N (by decide)

theorem append_zero (r n : ℕ) (hr : r ≤ 1) (F : Multiset ℕ) :
    appendMap 2 r 0 n F = SchreierQ2.mapZero (n + 1) F := by
  have he : carry 2 r 0 = 0 := by dsimp [carry]; omega
  simp [appendMap, he, SchreierQ2.mapZero]

theorem append_one_relaxed (n : ℕ) (F : Multiset ℕ) (hm : n ∈ F) :
    appendMap 2 0 1 n F = SchreierQ2.mapOneRelaxed (n + 1) F := by
  simp [appendMap, carry, SchreierQ2.mapOneRelaxed, SchreierQ2.restore_erase hm]

theorem shift_restore (n : ℕ) (F : Multiset ℕ) (hm : n ∈ F) :
    (F.erase n).map Nat.succ + {n + 1} = SchreierQ2.shiftUp F := by
  have h := congrArg (fun G : Multiset ℕ => G.map Nat.succ) (SchreierQ2.restore_erase hm)
  simpa [Multiset.map_add, SchreierQ2.shiftUp] using h

theorem append_one_strict (n : ℕ) (F : Multiset ℕ) (hm : n ∈ F) :
    appendMap 2 1 1 n F = SchreierQ2.mapOneStrict (n + 2) F := by
  change ((F.erase n).map Nat.succ + {n + 1}) + {n + 2} =
    SchreierQ2.shiftUp F + {n + 2}
  rw [shift_restore n F hm]

theorem append_two (r n : ℕ) (hr : r ≤ 1) (F : Multiset ℕ) (hm : n ∈ F) :
    appendMap 2 r 2 n F = SchreierQ2.mapTwo (n + 2) F := by
  have he : carry 2 r 2 = 1 := by dsimp [carry]; omega
  have hp : Multiset.replicate 2 (n + 1) = {n + 1} + {n + 1} := rfl
  unfold appendMap
  rw [he]
  change (F.erase n).map Nat.succ + Multiset.replicate 2 (n + 1) + {n + 2} = _
  rw [hp, ← add_assoc ((F.erase n).map Nat.succ) {n + 1} {n + 1}, shift_restore n F hm]
  simp [SchreierQ2.mapTwo]

/-- Commutation of the six partition equivalences with word appending. -/
theorem zero_relaxed_word (k : ℕ) (F : ↥(SchreierQ2.familyD 0 (k + 2))) :
    encode 2 0 (k + 2) ((SchreierQ2.zeroRelaxedEquiv k) F).val =
      encode 2 0 (k + 1) F.val ++ [0] := by
  have hs : F.val ∈ family 2 0 ((k + 1) + 1) := by
    rw [family_bridge]
    exact F.property
  have he : ((SchreierQ2.zeroRelaxedEquiv k) F).val =
      appendMap 2 0 0 (k + 2) F.val := (append_zero 0 (k + 2) (by decide) F.val).symm
  rw [he]
  simpa [carry, nextResidue] using encode_appendMap (q := 2) (r := 0) 0 (by decide) hs

theorem zero_strict_word (k : ℕ) (F : ↥(SchreierQ2.familyD 1 (k + 2))) :
    encode 2 1 (k + 2) ((SchreierQ2.zeroStrictEquiv k) F).val =
      encode 2 1 (k + 1) F.val ++ [0] := by
  have hs : F.val ∈ family 2 1 ((k + 1) + 1) := by
    rw [family_bridge]
    exact F.property
  have he : ((SchreierQ2.zeroStrictEquiv k) F).val =
      appendMap 2 1 0 (k + 2) F.val := (append_zero 1 (k + 2) (by decide) F.val).symm
  rw [he]
  simpa [carry, nextResidue] using encode_appendMap (q := 2) (r := 1) 0 (by decide) hs

theorem one_relaxed_word (k : ℕ) (F : ↥(SchreierQ2.familyD 1 (k + 2))) :
    encode 2 0 (k + 2) ((SchreierQ2.oneRelaxedEquiv k) F).val =
      encode 2 1 (k + 1) F.val ++ [1] := by
  have hs : F.val ∈ family 2 1 ((k + 1) + 1) := by
    rw [family_bridge]
    exact F.property
  have hm := ((mem_family _ _ _ _).mp hs).2.1
  rw [SchreierQ2.oneRelaxedEquiv_val, ← append_one_relaxed (k + 2) F.val hm]
  simpa [carry, nextResidue] using encode_appendMap (q := 2) (r := 0) 1 (by decide) hs

theorem one_strict_word (k : ℕ) (F : ↥(SchreierQ2.familyD 0 (k + 1))) :
    encode 2 1 (k + 2) ((SchreierQ2.oneStrictEquiv k) F).val =
      encode 2 0 k F.val ++ [1] := by
  have hs : F.val ∈ family 2 0 (k + 1) := by
    rw [family_bridge]
    exact F.property
  have hm := ((mem_family _ _ _ _).mp hs).2.1
  rw [SchreierQ2.oneStrictEquiv_val, ← append_one_strict (k + 1) F.val hm]
  simpa [carry, nextResidue] using encode_appendMap (q := 2) (r := 1) 1 (by decide) hs

theorem two_relaxed_word (k : ℕ) (F : ↥(SchreierQ2.familyD 0 (k + 1))) :
    encode 2 0 (k + 2) ((SchreierQ2.twoRelaxedEquiv k) F).val =
      encode 2 0 k F.val ++ [2] := by
  have hs : F.val ∈ family 2 0 (k + 1) := by
    rw [family_bridge]
    exact F.property
  have hm := ((mem_family _ _ _ _).mp hs).2.1
  rw [SchreierQ2.twoRelaxedEquiv_val, ← append_two 0 (k + 1) (by decide) F.val hm]
  simpa [carry, nextResidue] using encode_appendMap (q := 2) (r := 0) 2 (by decide) hs

theorem two_strict_word (k : ℕ) (F : ↥(SchreierQ2.familyD 1 (k + 1))) :
    encode 2 1 (k + 2) ((SchreierQ2.twoStrictEquiv k) F).val =
      encode 2 1 k F.val ++ [2] := by
  have hs : F.val ∈ family 2 1 (k + 1) := by
    rw [family_bridge]
    exact F.property
  have hm := ((mem_family _ _ _ _).mp hs).2.1
  rw [SchreierQ2.twoStrictEquiv_val, ← append_two 1 (k + 1) (by decide) F.val hm]
  simpa [carry, nextResidue] using encode_appendMap (q := 2) (r := 1) 2 (by decide) hs

end SchreierUnified.Q2Adapter

set_option autoImplicit false
set_option pp.fullNames true
set_option pp.universes true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.deepTerms true

#check (SchreierQ2.target : SchreierQ2.Target)
#check SchreierUnified.Q2Adapter.family_bridge
#check SchreierUnified.Q2Adapter.relaxed_bridge
#check SchreierUnified.Q2Adapter.strict_bridge
#check SchreierUnified.Q2Adapter.count_bridge
#check SchreierUnified.Q2Adapter.zero_relaxed_word
#check SchreierUnified.Q2Adapter.zero_strict_word
#check SchreierUnified.Q2Adapter.one_relaxed_word
#check SchreierUnified.Q2Adapter.one_strict_word
#check SchreierUnified.Q2Adapter.two_relaxed_word
#check SchreierUnified.Q2Adapter.two_strict_word
#print axioms SchreierQ2.target
#print axioms SchreierUnified.Q2Adapter.family_bridge
#print axioms SchreierUnified.Q2Adapter.strict_bridge
#print axioms SchreierUnified.Q2Adapter.count_bridge
#print axioms SchreierUnified.Q2Adapter.zero_relaxed_word
#print axioms SchreierUnified.Q2Adapter.zero_strict_word
#print axioms SchreierUnified.Q2Adapter.one_relaxed_word
#print axioms SchreierUnified.Q2Adapter.one_strict_word
#print axioms SchreierUnified.Q2Adapter.two_relaxed_word
#print axioms SchreierUnified.Q2Adapter.two_strict_word
#print axioms SchreierUnified.Q2Adapter.relaxed_bridge
