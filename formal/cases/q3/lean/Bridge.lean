import Encoding

namespace SchreierQ3

/-- No occupied source position is lost below the cardinality cutoff. -/
theorem encode_restore {n : ℕ} {F : Multiset ℕ}
    (hF : F ∈ family n) :
    unpack (cutoff F.card) (pack (cutoff F.card) (n - cutoff F.card) F) +
      {n} = F := by
  have hm := cutoff_le_top hF
  have he : cutoff F.card + (n - cutoff F.card) = n := by omega
  have hs : ∀ i ∈ F,
      cutoff F.card ≤ i ∧ i ≤ cutoff F.card + (n - cutoff F.card) := by
    intro i hi
    have hlo := source_above_cutoff hF hi
    have hhi := (source_support hF hi).2
    omega
  have ht : F.count (cutoff F.card + (n - cutoff F.card)) = 1 := by
    rw [he]
    exact source_top_count hF
  simpa only [he] using
    unpack_pack_restore (cutoff F.card) (n - cutoff F.card) F hs ht

theorem encode_isComposition {n : ℕ} {F : Multiset ℕ}
    (hF : F ∈ family n) : IsComposition (3 * n + 2) (encode n F) := by
  have hk := source_card_pos hF
  have hm0 := (cutoff_spec F.card hk).1
  have hm := cutoff_le_top hF
  have hp : Parts (pack (cutoff F.card) (n - cutoff F.card) F) := by
    apply pack_parts
    intro i hi hj
    apply source_lower_count hF <;> omega
  have hw := unpack_weight (cutoff F.card)
    (pack (cutoff F.card) (n - cutoff F.card) F)
    (fun t ht => (hp t ht).1)
  rw [pack_length] at hw
  have hcard := congrArg Multiset.card (encode_restore hF)
  simp only [Multiset.card_add, Multiset.card_singleton] at hcard
  have hc := card_add_terminal F.card hk
  constructor
  · change (pack (cutoff F.card) (n - cutoff F.card) F ++
      [terminal F.card]).sum = 3 * n + 2
    rw [List.sum_append, List.sum_singleton]
    omega
  · intro t ht
    change t ∈ pack (cutoff F.card) (n - cutoff F.card) F ++
      [terminal F.card] at ht
    rcases List.mem_append.mp ht with ht | ht
    · exact hp t ht
    · have he : t = terminal F.card := by simpa using ht
      subst t
      exact terminal_range F.card

theorem encode_mem {n : ℕ} {F : Multiset ℕ}
    (hF : F ∈ family n) : encode n F ∈ compositions (3 * n + 2) :=
  (mem_compositions _ _).mpr (encode_isComposition hF)

theorem decode_encode {n : ℕ} {F : Multiset ℕ}
    (hF : F ∈ family n) : decode n (encode n F) = F := by
  have hm := cutoff_le_top hF
  have he : n - (n - cutoff F.card) = cutoff F.card := by omega
  simpa only [decode, encode, List.dropLast_concat, pack_length, he] using
    encode_restore hF

/-- Landing, cutoff recovery and terminal recovery for the inverse map. -/
theorem decode_append_spec {n : ℕ} {b : List ℕ} {t : ℕ}
    (hn : 0 < n) (hp : IsComposition (3 * n + 2) (b ++ [t])) :
    decode n (b ++ [t]) ∈ family n ∧
      cutoff (decode n (b ++ [t])).card = n - b.length ∧
      terminal (decode n (b ++ [t])).card = t := by
  have hl := composition_length_le hp
  simp only [List.length_append, List.length_singleton] at hl
  have hm : 0 < n - b.length := by omega
  have he : n - b.length + b.length = n := by omega
  have hb : Parts b := by
    intro u hu
    exact hp.2 u (List.mem_append.mpr (Or.inl hu))
  have ht : 3 ≤ t ∧ t ≤ 5 := hp.2 t (by simp)
  have hs : b.sum + t = 3 * n + 2 := by
    simpa only [List.sum_append, List.sum_singleton] using hp.1
  have hw := unpack_weight (n - b.length) b (fun u hu => (hb u hu).1)
  have hcard : (decode n (b ++ [t])).card =
      (unpack (n - b.length) b).card + 1 := by
    simp [decode]
  -- With m = n - b.length, the decoded cardinality is 3*m + 3 - t.
  have hk : (decode n (b ++ [t])).card =
      3 * (n - b.length) + 3 - t := by omega
  have hlo : ∀ i ∈ decode n (b ++ [t]), n - b.length ≤ i := by
    intro i hi
    simp only [decode, List.dropLast_concat, Multiset.mem_add,
      Multiset.mem_singleton] at hi
    rcases hi with hi | rfl
    · exact (unpack_support (n - b.length) b hi).1
    · omega
  have hsupport : ∀ i ∈ decode n (b ++ [t]), 0 < i ∧ i ≤ n := by
    intro i hi
    simp only [decode, List.dropLast_concat, Multiset.mem_add,
      Multiset.mem_singleton] at hi
    rcases hi with hi | rfl
    · have hu := unpack_support (n - b.length) b hi
      omega
    · exact ⟨hn, le_rfl⟩
  have hsub : decode n (b ++ [t]) ≤ ambient n := by
    apply Multiset.le_iff_count.mpr
    intro i
    by_cases hin : i = n
    · subst i
      have hz := count_unpack_zero (n - b.length) b n
        (Or.inr (by omega))
      have hI : ¬(1 ≤ n ∧ n ≤ n - 1) := by omega
      simp [decode, count_ambient, hz, hI]
    · by_cases hi : 0 < i ∧ i < n
      · have hc := unpack_count_le_two (n - b.length) b i hb
        have hI : 1 ≤ i ∧ i ≤ n - 1 := by omega
        simpa [decode, Multiset.count_singleton, count_ambient, hin, hI] using hc
      · have hz : (decode n (b ++ [t])).count i = 0 := by
          apply Multiset.count_eq_zero.mpr
          intro hmem
          have hu := hsupport i hmem
          omega
        rw [hz]
        exact Nat.zero_le _
  have hsch : Schreier3 (decode n (b ++ [t])) := by
    apply (schreier3_iff _).mpr
    intro i hi
    have hmi := hlo i hi
    have hki := (decoded_cardinality (n - b.length) t hm ht.1 ht.2).2.2
    rw [hk]
    omega
  refine ⟨mem_family.mpr ⟨hsub, hn, ?_, hsch⟩, ?_, ?_⟩
  · simp [decode]
  · rw [hk]
    exact (decoded_cardinality (n - b.length) t hm ht.1 ht.2).2.1
  · rw [hk]
    exact decoded_terminal (n - b.length) t hm ht.1 ht.2

theorem decode_mem {n : ℕ} {p : List ℕ}
    (hn : 0 < n) (hp : p ∈ compositions (3 * n + 2)) :
    decode n p ∈ family n := by
  have hc := (mem_compositions _ _).mp hp
  obtain ⟨b, t, rfl⟩ := split_last p (composition_ne_nil hc)
  exact (decode_append_spec hn hc).1

theorem encode_decode {n : ℕ} {p : List ℕ}
    (hn : 0 < n) (hp : p ∈ compositions (3 * n + 2)) :
    encode n (decode n p) = p := by
  have hc := (mem_compositions _ _).mp hp
  obtain ⟨b, t, rfl⟩ := split_last p (composition_ne_nil hc)
  have hd := decode_append_spec hn hc
  have hl := composition_length_le hc
  simp only [List.length_append, List.length_singleton] at hl
  have he : n - b.length + b.length = n := by omega
  have hlen : n - (n - b.length) = b.length := by omega
  have hb : ∀ u ∈ b, 3 ≤ u := by
    intro u hu
    exact (hc.2 u (List.mem_append.mpr (Or.inl hu))).1
  have hbody : pack (n - b.length) b.length
      (unpack (n - b.length) b + {n}) = b := by
    simpa only [he] using pack_unpack_top (n - b.length) b hb
  unfold encode
  simp only [hd.2.1, hd.2.2, hlen]
  simp only [decode, List.dropLast_concat]
  change pack (n - b.length) b.length
    (unpack (n - b.length) b + {n}) ++ [t] = b ++ [t]
  rw [hbody]

/-- Cardinalities of the literal original family and all restricted compositions. -/
theorem count_bridge {n : ℕ} (hn : 0 < n) : a n = c (3 * n + 2) := by
  unfold a c
  exact Finset.card_bij'
    (fun F _ => encode n F)
    (fun p _ => decode n p)
    (fun F hF => encode_mem hF)
    (fun p hp => decode_mem hn hp)
    (fun F hF => decode_encode hF)
    (fun p hp => encode_decode hn hp)

end SchreierQ3
