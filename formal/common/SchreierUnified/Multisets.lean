import SchreierUnified.Words
import Mathlib.Data.Multiset.Powerset
import Mathlib.Data.Multiset.Replicate
import Mathlib.Tactic.Ring

/-!
# Multisets and their word encoding

The encoding reads multiplicities between the cardinality cutoff and the unique
maximum. Reconstruction proves the inverse laws and the equality of counts.
-/

namespace SchreierUnified

/-- Two copies of every integer from one through the given upper bound. -/
def doublePrefix : ℕ → Multiset ℕ
  | 0 => 0
  | m + 1 => doublePrefix m + Multiset.replicate 2 (m + 1)

/-- Two copies of each positive integer below `n`, followed by a single maximum `n`. -/
def ambient : ℕ → Multiset ℕ
  | 0 => 0
  | m + 1 => doublePrefix m + {m + 1}

/-- Submultisets containing `n` and satisfying `F.card + r ≤ q * x` for each member `x`. -/
def family (q r n : ℕ) : Finset (Multiset ℕ) :=
  ((ambient n).powerset.toFinset).filter
    (fun F => n ∈ F ∧ ∀ x ∈ F, F.card + r ≤ q * x)

theorem mem_family (q r n : ℕ) (F : Multiset ℕ) :
    F ∈ family q r n ↔
      F ≤ ambient n ∧ n ∈ F ∧ ∀ x ∈ F, F.card + r ≤ q * x := by
  simp [family]

theorem count_doublePrefix (m x : ℕ) :
    (doublePrefix m).count x = if 1 ≤ x ∧ x ≤ m then 2 else 0 := by
  induction m with
  | zero =>
      simp only [doublePrefix, Multiset.count_zero]
      split <;> omega
  | succ m ih =>
      rw [doublePrefix, Multiset.count_add, ih, Multiset.count_replicate]
      by_cases hx : x = m + 1
      · subst x
        have ht : 1 ≤ m + 1 ∧ m + 1 ≤ m + 1 := by omega
        simp [ht]
      · have he : (1 ≤ x ∧ x ≤ m + 1) ↔ (1 ≤ x ∧ x ≤ m) := by omega
        simp [Ne.symm hx, he]

theorem count_ambient_succ (N x : ℕ) :
    (ambient (N + 1)).count x =
      (if 1 ≤ x ∧ x ≤ N then 2 else 0) + (if x = N + 1 then 1 else 0) := by
  simp only [ambient, Multiset.count_add, count_doublePrefix, Multiset.count_singleton]

theorem count_ambient_max (N : ℕ) : (ambient (N + 1)).count (N + 1) = 1 := by
  rw [count_ambient_succ]
  simp

theorem count_ambient_le_two (N x : ℕ) : (ambient (N + 1)).count x ≤ 2 := by
  by_cases hx : x = N + 1
  · subst x
    rw [count_ambient_max]
    decide
  · rw [count_ambient_succ]
    simp only [hx, ite_false, Nat.add_zero]
    split <;> omega

theorem source_count_lt_three {q r N : ℕ} {F : Multiset ℕ}
    (hF : F ∈ family q r (N + 1)) (x : ℕ) : F.count x < 3 := by
  have h := Multiset.count_le_of_le x ((mem_family _ _ _ _).mp hF).1
  have hb := count_ambient_le_two N x
  omega

theorem source_count_max {q r N : ℕ} {F : Multiset ℕ}
    (hF : F ∈ family q r (N + 1)) : F.count (N + 1) = 1 := by
  have hs := (mem_family _ _ _ _).mp hF
  have hl := Multiset.count_pos.mpr hs.2.1
  have hu := Multiset.count_le_of_le (N + 1) hs.1
  rw [count_ambient_max] at hu
  omega

theorem source_member_le {q r N x : ℕ} {F : Multiset ℕ}
    (hF : F ∈ family q r (N + 1)) (hx : x ∈ F) : x ≤ N + 1 := by
  have hs := (mem_family _ _ _ _).mp hF
  have hl := Multiset.count_pos.mpr hx
  have hu := Multiset.count_le_of_le x hs.1
  by_contra hn
  have he : x ≠ N + 1 := by omega
  have hf : ¬(1 ≤ x ∧ x ≤ N) := by omega
  rw [count_ambient_succ] at hu
  simp only [he, hf, ite_false, Nat.zero_add] at hu
  omega

/-- The last position below the admissible support of a nonempty multiset. -/
def cutoff (q r : ℕ) (F : Multiset ℕ) : ℕ := (F.card - 1 + r) / q

theorem size_bound_iff (q K r x : ℕ) (hq : 0 < q) (hK : 0 < K) :
    K + r ≤ q * x ↔ (K - 1 + r) / q < x := by
  rw [Nat.div_lt_iff_lt_mul hq, Nat.mul_comm x q]
  omega

theorem source_cutoff_lt {q r n x : ℕ} {F : Multiset ℕ}
    (hq : 0 < q) (hF : F ∈ family q r n) (hx : x ∈ F) : cutoff q r F < x := by
  have hs := (mem_family _ _ _ _).mp hF
  have hp : 0 < F.card := Multiset.card_pos_iff_exists_mem.mpr ⟨n, hs.2.1⟩
  exact (size_bound_iff q F.card r x hq hp).mp (hs.2.2 x hx)

/-- All numerical slots are retained, whether or not occupied. -/
def expand : ℕ → Word → Multiset ℕ
  | _, [] => 0
  | s, d :: w => Multiset.replicate d.val s + expand (s + 1) w

@[simp] theorem card_expand (s : ℕ) (w : Word) : (expand s w).card = weight w := by
  induction w generalizing s with
  | nil => rfl
  | cons d w ih =>
      simp only [expand, Multiset.card_add, Multiset.card_replicate, ih,
        weight, List.map_cons, List.sum_cons]

theorem expand_bounds (s : ℕ) (w : Word) :
    ∀ x, x ∈ expand s w → s ≤ x ∧ x < s + w.length := by
  induction w generalizing s with
  | nil => intro x hx; simp [expand] at hx
  | cons d w ih =>
      intro x hx
      change x ∈ Multiset.replicate d.val s + expand (s + 1) w at hx
      rcases Multiset.mem_add.mp hx with hx | hx
      · have hxs := Multiset.eq_of_mem_replicate hx
        subst x
        simp only [List.length_cons]
        omega
      · have ht := ih (s + 1) x hx
        simp only [List.length_cons]
        omega

theorem count_expand_outside (s : ℕ) (w : Word) (x : ℕ)
    (h : ¬(s ≤ x ∧ x < s + w.length)) : (expand s w).count x = 0 := by
  apply Multiset.count_eq_zero_of_notMem
  intro hx
  exact h (expand_bounds s w x hx)

@[simp] theorem count_expand_head (s : ℕ) (d : Fin 3) (w : Word) :
    (expand s (d :: w)).count s = d.val := by
  have hz : (expand (s + 1) w).count s = 0 :=
    count_expand_outside (s + 1) w s (by omega)
  simp only [expand, Multiset.count_add, Multiset.count_replicate_self, hz, Nat.add_zero]

theorem count_expand_le_two (s : ℕ) (w : Word) :
    ∀ x, (expand s w).count x ≤ 2 := by
  induction w generalizing s with
  | nil => intro x; simp [expand]
  | cons d w ih =>
      intro x
      by_cases hx : x = s
      · subst x
        rw [count_expand_head]
        have hd := d.isLt
        omega
      · have he : s ≠ x := Ne.symm hx
        simp only [expand, Multiset.count_add, Multiset.count_replicate,
          he, ite_false, Nat.zero_add]
        exact ih (s + 1) x

theorem expand_injective_of_length (s : ℕ) (u v : Word)
    (hl : u.length = v.length) (h : expand s u = expand s v) : u = v := by
  induction u generalizing s v with
  | nil => cases v <;> simp_all
  | cons d u ih =>
      cases v with
      | nil => simp at hl
      | cons e v =>
          have hd : d = e := by
            apply Fin.ext
            have hc := congrArg (Multiset.count s) h
            simpa only [count_expand_head] using hc
          subst e
          have ht : expand (s + 1) u = expand (s + 1) v := Multiset.add_right_inj.mp h
          exact congrArg (List.cons d)
            (ih (s := s + 1) (v := v) (by simpa using hl) ht)

theorem expand_le_doublePrefix (s m : ℕ) (w : Word)
    (hs : 1 ≤ s) (hend : s + w.length ≤ m + 1) :
    expand s w ≤ doublePrefix m := by
  apply Multiset.le_iff_count.mpr
  intro x
  by_cases hx : x ∈ expand s w
  · have hb := expand_bounds s w x hx
    have hi : 1 ≤ x ∧ x ≤ m := by omega
    rw [count_doublePrefix, ite_eq_left hi]
    exact count_expand_le_two s w x
  · rw [Multiset.count_eq_zero_of_notMem hx]
    exact Nat.zero_le _

/-- Modulo three totalizes the reader only outside its bounded-multiplicity domain. -/
def readDigits : ℕ → ℕ → Multiset ℕ → Word
  | _, 0, _ => []
  | s, L + 1, F =>
      ⟨F.count s % 3, Nat.mod_lt _ (by decide)⟩ :: readDigits (s + 1) L F

@[simp] theorem length_readDigits (s L : ℕ) (F : Multiset ℕ) :
    (readDigits s L F).length = L := by
  induction L generalizing s with
  | zero => rfl
  | succ L ih => simp only [readDigits, List.length_cons, ih]

theorem count_expand_readDigits (s L : ℕ) (F : Multiset ℕ) (x : ℕ) :
    (expand s (readDigits s L F)).count x =
      if s ≤ x ∧ x < s + L then F.count x % 3 else 0 := by
  induction L generalizing s with
  | zero => simp [readDigits, expand]
  | succ L ih =>
      by_cases hx : x = s
      · subst x
        rw [readDigits, count_expand_head]
        have ht : s ≤ s ∧ s < s + (L + 1) := by omega
        rw [ite_eq_left ht]
      · have he : s ≠ x := Ne.symm hx
        rw [readDigits, expand, Multiset.count_add, Multiset.count_replicate, ih]
        have hi : (s ≤ x ∧ x < s + (L + 1)) ↔
            (s + 1 ≤ x ∧ x < (s + 1) + L) := by omega
        simp only [he, ite_false, Nat.zero_add, hi]

theorem reconstruct_interval (s L n : ℕ) (F : Multiset ℕ)
    (hbound : ∀ x, F.count x < 3) (hmax : F.count n = 1)
    (hsupp : ∀ x ∈ F, s ≤ x ∧ x ≤ n) (hend : s + L = n) :
    expand s (readDigits s L F) + {n} = F := by
  apply Multiset.ext.mpr
  intro x
  rw [Multiset.count_add, count_expand_readDigits, Multiset.count_singleton]
  by_cases hx : x = n
  · subst x
    have hf : ¬(s ≤ n ∧ n < s + L) := by omega
    simp [hf, hmax]
  · by_cases hi : s ≤ x ∧ x < s + L
    · rw [ite_eq_left hi, ite_eq_right hx, Nat.add_zero, Nat.mod_eq_of_lt (hbound x)]
    · have hz : F.count x = 0 := by
        apply Multiset.count_eq_zero_of_notMem
        intro hm
        have hb := hsupp x hm
        apply hi
        omega
      simp only [hi, hx, ite_false, Nat.zero_add, hz]

/-- Read multiplicities above the cutoff and below maximum `N + 1`, retaining zero slots. -/
def encode (q r N : ℕ) (F : Multiset ℕ) : Word :=
  readDigits (cutoff q r F + 1) (N - cutoff q r F) F

theorem encode_reconstruct {q r N : ℕ} {F : Multiset ℕ}
    (hq : 0 < q) (hF : F ∈ family q r (N + 1)) :
    expand (cutoff q r F + 1) (encode q r N F) + {N + 1} = F := by
  unfold encode
  apply reconstruct_interval
  · exact source_count_lt_three hF
  · exact source_count_max hF
  · intro x hx
    have hl := source_cutoff_lt hq hF hx
    have hu := source_member_le hF hx
    omega
  · have hj := source_cutoff_lt hq hF ((mem_family _ _ _ _).mp hF).2.1
    omega

theorem encode_weight {q r N : ℕ} {F : Multiset ℕ}
    (hq : 0 < q) (hF : F ∈ family q r (N + 1)) :
    weight (encode q r N F) = F.card - 1 := by
  have hc := congrArg Multiset.card (encode_reconstruct hq hF)
  simp only [Multiset.card_add, card_expand, Multiset.card_singleton] at hc
  omega

theorem encode_cost {q r N : ℕ} {F : Multiset ℕ}
    (hq : 0 < q) (hF : F ∈ family q r (N + 1)) : cost q r (encode q r N F) = N := by
  unfold cost
  rw [encode_weight hq hF]
  change (encode q r N F).length + cutoff q r F = N
  simp only [encode, length_readDigits]
  have hj := source_cutoff_lt hq hF ((mem_family _ _ _ _).mp hF).2.1
  omega

/-- Recover the positions from the word weight, then append the unique maximum. -/
def decode (q r : ℕ) (w : Word) : Multiset ℕ :=
  expand ((weight w + r) / q + 1) w + {cost q r w + 1}

@[simp] theorem card_decode (q r : ℕ) (w : Word) :
    (decode q r w).card = weight w + 1 := by
  simp only [decode, Multiset.card_add, card_expand, Multiset.card_singleton]

theorem decode_mem (q r : ℕ) (w : Word) (hq : 0 < q) :
    decode q r w ∈ family q r (cost q r w + 1) := by
  apply (mem_family _ _ _ _).mpr
  refine ⟨?_, ?_, ?_⟩
  · have hb : expand ((weight w + r) / q + 1) w ≤ doublePrefix (cost q r w) := by
      apply expand_le_doublePrefix
      · exact Nat.le_add_left 1 _
      · unfold cost
        omega
    apply Multiset.le_iff_count.mpr
    intro x
    change (expand ((weight w + r) / q + 1) w + {cost q r w + 1}).count x ≤
      (doublePrefix (cost q r w) + {cost q r w + 1}).count x
    rw [Multiset.count_add, Multiset.count_add]
    exact Nat.add_le_add_right (Multiset.count_le_of_le x hb) _
  · exact Multiset.mem_add.mpr (Or.inr (Multiset.mem_singleton_self _))
  · intro x hx
    have hl : (weight w + r) / q + 1 ≤ x := by
      change x ∈ expand ((weight w + r) / q + 1) w + {cost q r w + 1} at hx
      rcases Multiset.mem_add.mp hx with hx | hx
      · exact (expand_bounds _ w x hx).1
      · have he := Multiset.mem_singleton.mp hx
        unfold cost at he
        omega
    rw [card_decode]
    have hm := Nat.mod_lt (weight w + r) hq
    have he := Nat.div_add_mod (weight w + r) q
    calc
      weight w + 1 + r ≤ q * ((weight w + r) / q) + q := by omega
      _ = q * ((weight w + r) / q + 1) := by ring
      _ ≤ q * x := Nat.mul_le_mul_left q hl

theorem decode_encode {q r N : ℕ} {F : Multiset ℕ}
    (hq : 0 < q) (hF : F ∈ family q r (N + 1)) :
    decode q r (encode q r N F) = F := by
  unfold decode
  rw [encode_weight hq hF, encode_cost hq hF]
  exact encode_reconstruct hq hF

theorem decode_injective_of_cost {q r : ℕ} {u v : Word}
    (hc : cost q r u = cost q r v) (h : decode q r u = decode q r v) : u = v := by
  have hm : weight u = weight v := by
    have hh := congrArg Multiset.card h
    simp only [card_decode] at hh
    omega
  have hl : u.length = v.length := by
    unfold cost at hc
    rw [hm] at hc
    omega
  have he : expand ((weight u + r) / q + 1) u = expand ((weight u + r) / q + 1) v := by
    unfold decode at h
    rw [← hm, ← hc] at h
    exact Multiset.add_left_inj.mp h
  exact expand_injective_of_length _ u v hl he

theorem encode_decode {q r N : ℕ} {w : Word} (hq : 0 < q) (hw : cost q r w = N) :
    encode q r N (decode q r w) = w := by
  have hF : decode q r w ∈ family q r (N + 1) := by
    simpa only [hw] using decode_mem q r w hq
  apply decode_injective_of_cost
  · exact (encode_cost hq hF).trans hw.symm
  · exact decode_encode hq hF

/-- The equivalence between the margin family of maximum `N + 1` and words of cost `N`. -/
def originalWordEquiv (q r N : ℕ) (hq : 0 < q) :
    {F // F ∈ family q r (N + 1)} ≃ {w : Word // cost q r w = N} where
  toFun F := ⟨encode q r N F.val, encode_cost hq F.property⟩
  invFun w := ⟨decode q r w.val, by simpa only [w.property] using decode_mem q r w.val hq⟩
  left_inv F := Subtype.ext (decode_encode hq F.property)
  right_inv w := Subtype.ext (encode_decode hq w.property)

theorem family_card_eq_wordCount (q r N : ℕ) (hq : 0 < q) :
    (family q r (N + 1)).card = wordCount q r N := by
  unfold wordCount
  symm
  apply Finset.card_bij (fun w _ => decode q r w)
  · intro w hw
    have hc := (mem_words q r N w).mp hw
    simpa only [hc] using decode_mem q r w hq
  · intro u hu v hv h
    exact decode_injective_of_cost
      (((mem_words q r N u).mp hu).trans ((mem_words q r N v).mp hv).symm) h
  · intro F hF
    exact ⟨encode q r N F, (mem_words q r N _).mpr (encode_cost hq hF), decode_encode hq hF⟩

/-- Erasing one newly appended entry restores the multiset. -/
theorem erase_append (F : Multiset ℕ) (x : ℕ) : (F + {x}).erase x = F := by
  rw [Multiset.erase_add_right_pos F (Multiset.mem_singleton_self x)]
  simp

theorem expand_shift (s e : ℕ) (w : Word) :
    (expand s w).map (fun x => x + e) = expand (s + e) w := by
  induction w generalizing s with
  | nil => simp [expand]
  | cons d w ih =>
      simp only [expand, Multiset.map_add, Multiset.map_replicate, ih]
      congr 1
      congr 1
      omega

theorem expand_append (s : ℕ) (u v : Word) :
    expand s (u ++ v) = expand s u + expand (s + u.length) v := by
  induction u generalizing s with
  | nil => simp [expand]
  | cons d u ih =>
      simp [expand, ih, add_assoc, Nat.add_comm]

/-- Source maximum n; target maximum n + carry + 1. -/
def appendMap (q r : ℕ) (d : Fin 3) (n : ℕ) (F : Multiset ℕ) : Multiset ℕ :=
  (F.erase n).map (fun x => x + carry q r d) +
    Multiset.replicate d.val (n + carry q r d) + {n + carry q r d + 1}

theorem decode_append (q r : ℕ) (d : Fin 3) (w : Word) (hq : 0 < q) :
    decode q r (w ++ [d]) =
      appendMap q r d (cost q (nextResidue q r d) w + 1)
        (decode q (nextResidue q r d) w) := by
  let j := (weight w + nextResidue q r d) / q
  let e := carry q r d
  let c := cost q (nextResidue q r d) w
  have hc : cost q r (w ++ [d]) = 1 + e + c := cost_append q r d w hq
  have hj : (weight (w ++ [d]) + r) / q = j + e := by
    have hl : (w ++ [d]).length = w.length + 1 := by simp
    dsimp [c, cost, j] at hc ⊢
    rw [hl] at hc
    omega
  have hs : j + e + 1 = j + 1 + e := by omega
  have hp : j + e + 1 + w.length = c + 1 + e := by
    dsimp [c, cost, j]
    omega
  have hm : 1 + e + c + 1 = c + 1 + e + 1 := by omega
  change expand ((weight (w ++ [d]) + r) / q + 1) (w ++ [d]) +
      {cost q r (w ++ [d]) + 1} =
    ((expand (j + 1) w + {c + 1}).erase (c + 1)).map (fun x => x + e) +
      Multiset.replicate d.val (c + 1 + e) + {c + 1 + e + 1}
  rw [erase_append, expand_shift, hj, hc, expand_append]
  simp only [expand, add_zero]
  rw [hp, hs, hm]

theorem appendMap_encode {q r N : ℕ} (d : Fin 3) {F : Multiset ℕ}
    (hq : 0 < q) (hF : F ∈ family q (nextResidue q r d) (N + 1)) :
    decode q r (encode q (nextResidue q r d) N F ++ [d]) = appendMap q r d (N + 1) F := by
  rw [decode_append q r d _ hq, encode_cost hq hF, decode_encode hq hF]

theorem encode_appendMap {q r N : ℕ} (d : Fin 3) {F : Multiset ℕ}
    (hq : 0 < q) (hF : F ∈ family q (nextResidue q r d) (N + 1)) :
    encode q r (N + 1 + carry q r d) (appendMap q r d (N + 1) F) =
      encode q (nextResidue q r d) N F ++ [d] := by
  rw [← appendMap_encode d hq hF]
  apply encode_decode hq
  rw [cost_append q r d _ hq, encode_cost hq hF]
  omega

/-- Its bijectivity for general q is an ordinary theorem of the article. -/
def terminalComposition (q r : ℕ) (w : Word) : List ℕ :=
  w.map (fun d => q + d.val) ++ [2 * q - 1 - (weight w + r) % q]

end SchreierUnified
