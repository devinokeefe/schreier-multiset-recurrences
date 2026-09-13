import SchreierQ4.Expansion

namespace SchreierQ4.OriginalBridge

open WordModel

/-- The forward map at maximum N+1, defined on every multiset. -/
def encode (N : ℕ) (F : Multiset ℕ) : Word :=
  readDigits ((F.card - 1) / 4 + 1) (N - (F.card - 1) / 4) F

@[simp] theorem encode_length (N : ℕ) (F : Multiset ℕ) :
    (encode N F).length = N - (F.card - 1) / 4 := by
  exact length_readDigits _ _ _

/-- On the source family, the totalized reader does not change any multiplicity. -/
theorem encode_reconstruct {N : ℕ} {F : Multiset ℕ}
    (hF : F ∈ admissibleMultisets (N + 1)) :
    expand ((F.card - 1) / 4 + 1) (encode N F) + {N + 1} = F := by
  unfold encode
  apply reconstruct_interval
  · intro x
    have hx := admissible_count_le_two hF x
    omega
  · exact admissible_count_max hF
  · intro x hx
    have hl := admissible_quarter_lt hF hx
    have hu := admissible_member_le hF hx
    omega
  · have hj := admissible_quarter_lt_max hF
    omega

theorem encode_weight {N : ℕ} {F : Multiset ℕ}
    (hF : F ∈ admissibleMultisets (N + 1)) :
    weight (encode N F) = F.card - 1 := by
  have hc := congrArg Multiset.card (encode_reconstruct hF)
  simp only [Multiset.card_add, card_expand, Multiset.card_singleton] at hc
  omega

theorem encode_cost {N : ℕ} {F : Multiset ℕ}
    (hF : F ∈ admissibleMultisets (N + 1)) : cost 0 (encode N F) = N := by
  change (encode N F).length + (0 + weight (encode N F)) / 4 = N
  rw [Nat.zero_add, encode_length, encode_weight hF]
  have hj := admissible_quarter_lt_max hF
  omega

/-- The inverse uses the word length and digit sum to recover its maximum. -/
def decode (w : Word) : Multiset ℕ :=
  expand (weight w / 4 + 1) w + {cost 0 w + 1}

@[simp] theorem card_decode (w : Word) : (decode w).card = weight w + 1 := by
  simp only [decode, Multiset.card_add, card_expand, Multiset.card_singleton]

theorem decode_admissible (w : Word) :
    decode w ∈ admissibleMultisets (cost 0 w + 1) := by
  apply (mem_admissibleMultisets _ _).mpr
  refine ⟨?_, ?_, ?_⟩
  · have hb : expand (weight w / 4 + 1) w ≤ doublePrefix (cost 0 w) := by
      apply expand_le_doublePrefix
      · omega
      · change weight w / 4 + 1 + w.length ≤
          (w.length + (0 + weight w) / 4) + 1
        omega
    apply Multiset.le_iff_count.mpr
    intro x
    change (expand (weight w / 4 + 1) w + {cost 0 w + 1}).count x ≤
      (doublePrefix (cost 0 w) + {cost 0 w + 1}).count x
    rw [Multiset.count_add, Multiset.count_add]
    exact Nat.add_le_add_right (Multiset.count_le_of_le x hb) _
  · change cost 0 w + 1 ∈ expand (weight w / 4 + 1) w + {cost 0 w + 1}
    exact Multiset.mem_add.mpr (Or.inr (Multiset.mem_singleton_self _))
  · intro x hx
    have hl : weight w / 4 + 1 ≤ x := by
      change x ∈ expand (weight w / 4 + 1) w + {cost 0 w + 1} at hx
      rcases Multiset.mem_add.mp hx with hx | hx
      · exact (expand_bounds _ w x hx).1
      · have he := Multiset.mem_singleton.mp hx
        change x = (w.length + (0 + weight w) / 4) + 1 at he
        omega
    rw [card_decode]
    omega

theorem decode_encode {N : ℕ} {F : Multiset ℕ}
    (hF : F ∈ admissibleMultisets (N + 1)) : decode (encode N F) = F := by
  unfold decode
  rw [encode_weight hF, encode_cost hF]
  exact encode_reconstruct hF

/-- Fixing cost supplies the length needed for injectivity of expansion. -/
theorem decode_injective_of_cost {u v : Word}
    (hc : cost 0 u = cost 0 v) (h : decode u = decode v) : u = v := by
  have hm : weight u = weight v := by
    have hh := congrArg Multiset.card h
    simp only [card_decode] at hh
    omega
  have hl : u.length = v.length := by
    have hh := hc
    change u.length + (0 + weight u) / 4 = v.length + (0 + weight v) / 4 at hh
    rw [hm] at hh
    omega
  have he : expand (weight u / 4 + 1) u = expand (weight u / 4 + 1) v := by
    unfold decode at h
    rw [← hm, ← hc] at h
    exact Multiset.add_left_inj.mp h
  exact expand_injective_of_length _ u v hl he

theorem encode_decode {N : ℕ} {w : Word} (hw : cost 0 w = N) :
    encode N (decode w) = w := by
  have hF : decode w ∈ admissibleMultisets (N + 1) := by
    simpa only [hw] using decode_admissible w
  apply decode_injective_of_cost
  · exact (encode_cost hF).trans hw.symm
  · exact decode_encode hF

/-- The encoding equivalence between admissible multisets and words of fixed cost. -/
def originalWordEquiv (N : ℕ) :
    {F // F ∈ admissibleMultisets (N + 1)} ≃ {w : Word // cost 0 w = N} where
  toFun F := ⟨encode N F.val, encode_cost F.property⟩
  invFun w := ⟨decode w.val, by
    simpa only [w.property] using decode_admissible w.val⟩
  left_inv F := Subtype.ext (decode_encode F.property)
  right_inv w := Subtype.ext (encode_decode w.property)

theorem exists_unique_word {N : ℕ} {F : Multiset ℕ}
    (hF : F ∈ admissibleMultisets (N + 1)) :
    ∃! w : Word, cost 0 w = N ∧ decode w = F := by
  refine ⟨encode N F, ⟨encode_cost hF, decode_encode hF⟩, ?_⟩
  intro w hw
  apply decode_injective_of_cost
  · exact hw.1.trans (encode_cost hF).symm
  · exact hw.2.trans (decode_encode hF).symm

end SchreierQ4.OriginalBridge
