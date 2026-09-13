import SchreierUnified.Multisets
import SchreierQ4.Main

namespace SchreierUnified.Q4Adapter

theorem ambient_bridge (N : ℕ) : ambient (N + 1) = SchreierQ4.ambient (N + 1) := by
  apply Multiset.ext.mpr
  intro x
  rw [count_ambient_succ, SchreierQ4.OriginalBridge.count_ambient_succ]

theorem family_bridge (N : ℕ) :
    family 4 0 (N + 1) = SchreierQ4.admissibleMultisets (N + 1) := by
  ext F
  simp only [mem_family, SchreierQ4.mem_admissibleMultisets, ambient_bridge, Nat.add_zero]

theorem cost_agreement (r : Fin 4) (w : Word) :
    cost 4 r.val w = SchreierQ4.WordModel.cost r w := by
  simp only [cost, SchreierQ4.WordModel.cost, weight, SchreierQ4.WordModel.weight,
    Nat.add_comm]

theorem reader_agreement (s L : ℕ) (F : Multiset ℕ) :
    readDigits s L F = SchreierQ4.OriginalBridge.readDigits s L F := by
  induction L generalizing s with
  | zero => rfl
  | succ L ih => simp only [readDigits, SchreierQ4.OriginalBridge.readDigits, ih]

theorem expansion_agreement (s : ℕ) (w : Word) :
    expand s w = SchreierQ4.OriginalBridge.expand s w := by
  induction w generalizing s with
  | nil => rfl
  | cons d w ih => simp only [expand, SchreierQ4.OriginalBridge.expand, ih]

/-- Both total readers coincide, hence in particular on the original domain. -/
theorem encoding_agreement (N : ℕ) (F : Multiset ℕ) :
    encode 4 0 N F = SchreierQ4.OriginalBridge.encode N F := by
  simp only [encode, cutoff, Nat.add_zero, reader_agreement, SchreierQ4.OriginalBridge.encode]

theorem decoding_agreement (w : Word) :
    decode 4 0 w = SchreierQ4.OriginalBridge.decode w := by
  simp [decode, expansion_agreement, SchreierQ4.OriginalBridge.decode,
    cost, SchreierQ4.WordModel.cost, weight, SchreierQ4.WordModel.weight]

theorem count_bridge (N : ℕ) : SchreierQ4.a (N + 1) = wordCount 4 0 N := by
  unfold SchreierQ4.a
  rw [← family_bridge]
  exact family_card_eq_wordCount 4 0 N (by decide)

end SchreierUnified.Q4Adapter

set_option autoImplicit false
set_option pp.fullNames true
set_option pp.universes true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.deepTerms true

#check (SchreierQ4.mainClaim : SchreierQ4.Target)
#check SchreierUnified.Q4Adapter.family_bridge
#check SchreierUnified.Q4Adapter.reader_agreement
#check SchreierUnified.Q4Adapter.expansion_agreement
#check SchreierUnified.Q4Adapter.count_bridge
#check SchreierUnified.Q4Adapter.cost_agreement
#check SchreierUnified.Q4Adapter.encoding_agreement
#check SchreierUnified.Q4Adapter.decoding_agreement
#print axioms SchreierQ4.mainClaim
#print axioms SchreierUnified.Q4Adapter.family_bridge
#print axioms SchreierUnified.Q4Adapter.count_bridge
#print axioms SchreierUnified.Q4Adapter.cost_agreement
#print axioms SchreierUnified.Q4Adapter.encoding_agreement
#print axioms SchreierUnified.Q4Adapter.decoding_agreement
#print axioms SchreierUnified.Q4Adapter.reader_agreement
#print axioms SchreierUnified.Q4Adapter.expansion_agreement
