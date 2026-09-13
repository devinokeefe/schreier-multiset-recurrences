import SchreierUnified.Multisets
import Main

namespace SchreierUnified.Q3Adapter

/-- No equality of the two ambient conventions at zero is asserted. -/
theorem ambient_bridge (N : ℕ) : ambient (N + 1) = SchreierQ3.ambient (N + 1) := by
  apply Multiset.ext.mpr
  intro x
  simp only [count_ambient_succ, SchreierQ3.count_ambient, Nat.add_sub_cancel]

theorem family_bridge (N : ℕ) : family 3 0 (N + 1) = SchreierQ3.family (N + 1) := by
  ext F
  simp only [mem_family, SchreierQ3.mem_family, SchreierQ3.schreier3_iff,
    ambient_bridge, Nat.add_zero, Nat.zero_lt_succ, true_and]

theorem count_bridge (N : ℕ) : SchreierQ3.a (N + 1) = wordCount 3 0 N := by
  unfold SchreierQ3.a
  rw [← family_bridge]
  exact family_card_eq_wordCount 3 0 N (by decide)

/-- The composition reader adds three to each multiplicity digit. -/
theorem pack_read (s L : ℕ) (F : Multiset ℕ) (hb : ∀ x, F.count x < 3) :
    SchreierQ3.pack s L F = (readDigits s L F).map (fun d => 3 + d.val) := by
  induction L generalizing s with
  | zero => rfl
  | succ L ih =>
      simp only [SchreierQ3.pack, readDigits, List.map_cons, Nat.mod_eq_of_lt (hb s), ih]

theorem encoding_agreement (N : ℕ) (F : Multiset ℕ) (hF : F ∈ SchreierQ3.family (N + 1)) :
    SchreierQ3.encode (N + 1) F = terminalComposition 3 0 (encode 3 0 N F) := by
  have hs : F ∈ family 3 0 (N + 1) := by rw [family_bridge]; exact hF
  have hk := SchreierQ3.source_card_pos hF
  have hj : SchreierQ3.cutoff F.card = cutoff 3 0 F + 1 := by
    unfold SchreierQ3.cutoff cutoff
    omega
  have hl : N + 1 - (cutoff 3 0 F + 1) = N - cutoff 3 0 F := by omega
  unfold SchreierQ3.encode terminalComposition
  rw [encode_weight (by decide) hs, pack_read _ _ F (source_count_lt_three hs)]
  simp only [SchreierQ3.terminal, encode, hj, hl, Nat.add_zero]

end SchreierUnified.Q3Adapter

set_option autoImplicit false
set_option pp.fullNames true
set_option pp.universes true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.deepTerms true

#check (SchreierQ3.main : SchreierQ3.MainClaim)
#check SchreierUnified.Q3Adapter.family_bridge
#check SchreierUnified.Q3Adapter.pack_read
#check SchreierUnified.Q3Adapter.count_bridge
#check SchreierUnified.Q3Adapter.encoding_agreement
#print axioms SchreierQ3.main
#print axioms SchreierUnified.Q3Adapter.family_bridge
#print axioms SchreierUnified.Q3Adapter.count_bridge
#print axioms SchreierUnified.Q3Adapter.encoding_agreement
#print axioms SchreierUnified.Q3Adapter.pack_read
