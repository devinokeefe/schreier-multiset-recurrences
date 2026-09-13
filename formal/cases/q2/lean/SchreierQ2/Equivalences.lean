import SchreierQ2.Transport

/-! Concrete finite-family equivalences, with both inverses and all bounds. -/

namespace SchreierQ2

theorem good_shift_forward {δ m : ℕ} {F : Multiset ℕ} (h : Good δ m F) :
    Good (δ + 2) (m + 1) (shiftUp F) :=
  ⟨shape_shiftUp h.1, (bound_shift_iff δ F).mpr h.2⟩

theorem good_shift_inverse {δ m : ℕ} {G : Multiset ℕ}
    (h : Good (δ + 2) (m + 1) G) : Good δ m (shiftDown G) := by
  have hcard : 3 ≤ G.card + (δ + 2) := by
    have hnonempty := h.1.card_pos
    omega
  have hp : ∀ x ∈ G, 2 ≤ x :=
    two_le_of_card_slack G (δ + 2) h.2 hcard
  refine ⟨shape_shiftDown h.1 hp, ?_⟩
  apply (bound_shift_iff δ (shiftDown G)).mp
  simpa only [shiftUp_shiftDown h.1.positive] using h.2

/-- Shifting every entry up by one increases the maximum by one and the margin by two. -/
def shiftEquiv (δ m : ℕ) (hm : 1 ≤ m) :
    ↥(familyD δ m) ≃ ↥(familyD (δ + 2) (m + 1)) :=
  equivOfMaps shiftUp shiftDown
    (by
      intro F hF
      exact (mem_familyD_iff (by omega)).mpr
        (good_shift_forward ((mem_familyD_iff hm).mp hF)))
    (by
      intro G hG
      exact (mem_familyD_iff hm).mpr
        (good_shift_inverse ((mem_familyD_iff (by omega)).mp hG)))
    (by intro F _; exact shiftDown_shiftUp F)
    (by
      intro G hG
      exact shiftUp_shiftDown ((mem_familyD_iff (by omega)).mp hG).1.positive)

theorem good_zero_forward {δ m : ℕ} {F : Multiset ℕ}
    (hm : 1 ≤ m) (hδ : δ ≤ 1) (h : Good δ m F) :
    Good δ (m + 1) (F.erase m + {m + 1}) ∧
      (F.erase m + {m + 1}).count m = 0 := by
  refine ⟨⟨shape_zero_forward h.1, ?_⟩, ?_⟩
  · have hu : ∀ x ∈ F.erase m, x ≤ m := by
      intro x hx
      exact h.1.bounded x (Multiset.mem_of_mem_erase hx)
    apply (bound_replace_iff hm hδ (by omega : m ≤ m + 1) hu).mp
    simpa only [restore_erase h.1.top_mem] using h.2
  · simp [h.1.top]

theorem good_zero_inverse {δ m : ℕ} {G : Multiset ℕ}
    (hm : 1 ≤ m) (hδ : δ ≤ 1) (h : Good δ (m + 1) G)
    (hc : G.count m = 0) : Good δ m (G.erase (m + 1) + {m}) := by
  refine ⟨shape_zero_inverse hm h.1 hc, ?_⟩
  have hu : ∀ x ∈ G.erase (m + 1), x ≤ m := by
    intro x hx
    have hb := h.1.erase_top_lt hx
    omega
  apply (bound_replace_iff hm hδ (by omega : m ≤ m + 1) hu).mpr
  simpa only [restore_erase h.1.top_mem] using h.2

/-- Replace the maximum `m` by `m + 1`, producing the zero-copy part at `m + 1`. -/
def zeroEquiv (δ m : ℕ) (hm : 1 ≤ m) (hδ : δ ≤ 1) :
    ↥(familyD δ m) ≃ ↥(part δ (m + 1) 0) :=
  equivOfMaps (mapZero (m + 1)) (inverseZero (m + 1))
    (by
      intro F hF
      apply (mem_part_iff (by omega)).mpr
      simpa only [mapZero, Nat.add_sub_cancel] using
        good_zero_forward hm hδ ((mem_familyD_iff hm).mp hF))
    (by
      intro G hG
      obtain ⟨h, hc⟩ := (mem_part_iff (by omega)).mp hG
      have hc' : G.count m = 0 := by simpa only [Nat.add_sub_cancel] using hc
      apply (mem_familyD_iff hm).mpr
      simpa only [inverseZero, Nat.add_sub_cancel] using good_zero_inverse hm hδ h hc')
    (by
      intro F hF
      have h := (mem_familyD_iff hm).mp hF
      simp only [mapZero, inverseZero, Nat.add_sub_cancel, erase_append]
      exact restore_erase h.1.top_mem)
    (by
      intro G hG
      have h := ((mem_part_iff (by omega)).mp hG).1
      simp only [mapZero, inverseZero, Nat.add_sub_cancel, erase_append]
      exact restore_erase h.1.top_mem)

theorem good_one_forward {δ m : ℕ} {F : Multiset ℕ}
    (h : Good (δ + 1) m F) :
    Good δ (m + 1) (F + {m + 1}) ∧ (F + {m + 1}).count m = 1 := by
  refine ⟨⟨shape_one_forward h.1, ?_⟩, ?_⟩
  · exact (bound_append_iff h.1.top_mem (by omega : m ≤ m + 1)).mpr h.2
  · simp [h.1.top]

theorem good_one_inverse {δ m : ℕ} {G : Multiset ℕ}
    (h : Good δ (m + 1) G) (hc : G.count m = 1) :
    Good (δ + 1) m (G.erase (m + 1)) := by
  have hs := shape_one_inverse h.1 hc
  refine ⟨hs, ?_⟩
  apply (bound_append_iff hs.top_mem (by omega : m ≤ m + 1)).mp
  simpa only [restore_erase h.1.top_mem] using h.2

/-- Append the maximum `m + 1`, reducing the margin by one and producing the one-copy part. -/
def oneEquiv (δ m : ℕ) (hm : 1 ≤ m) :
    ↥(familyD (δ + 1) m) ≃ ↥(part δ (m + 1) 1) :=
  equivOfMaps (mapOneRelaxed (m + 1)) (inverseOneRelaxed (m + 1))
    (by
      intro F hF
      apply (mem_part_iff (by omega)).mpr
      simpa only [mapOneRelaxed, Nat.add_sub_cancel] using
        good_one_forward ((mem_familyD_iff hm).mp hF))
    (by
      intro G hG
      obtain ⟨h, hc⟩ := (mem_part_iff (by omega)).mp hG
      have hc' : G.count m = 1 := by simpa only [Nat.add_sub_cancel] using hc
      exact (mem_familyD_iff hm).mpr (good_one_inverse h hc'))
    (by
      intro F _
      exact erase_append F (m + 1))
    (by
      intro G hG
      exact restore_erase (((mem_part_iff (by omega)).mp hG).1.1.top_mem))

theorem good_two_forward {δ m : ℕ} {F : Multiset ℕ}
    (h : Good (δ + 2) m F) :
    Good δ (m + 1) (F + {m} + {m + 1}) ∧
      (F + {m} + {m + 1}).count m = 2 := by
  refine ⟨⟨shape_two_forward h.1, (bound_two_iff h.1.top_mem).mpr h.2⟩, ?_⟩
  simp [h.1.top]

theorem restore_two {m : ℕ} {G : Multiset ℕ}
    (h : Shape (m + 1) G) (hc : G.count m = 2) :
    (G.erase (m + 1)).erase m + {m} + {m + 1} = G := by
  have hm : m ∈ G.erase (m + 1) := by
    apply Multiset.count_pos.mp
    rw [Multiset.count_erase_of_ne (by omega : m ≠ m + 1), hc]
    decide
  rw [restore_erase hm, restore_erase h.top_mem]

theorem good_two_inverse {δ m : ℕ} {G : Multiset ℕ}
    (h : Good δ (m + 1) G) (hc : G.count m = 2) :
    Good (δ + 2) m ((G.erase (m + 1)).erase m) := by
  have hs := shape_two_inverse h.1 hc
  refine ⟨hs, ?_⟩
  apply (bound_two_iff hs.top_mem).mp
  simpa only [restore_two h.1 hc] using h.2

/-- Append `m` and `m + 1`, reducing the margin by two and producing the two-copy part. -/
def twoEquiv (δ m : ℕ) (hm : 1 ≤ m) :
    ↥(familyD (δ + 2) m) ≃ ↥(part δ (m + 1) 2) :=
  equivOfMaps (fun F => F + {m} + {m + 1})
    (fun G => (G.erase (m + 1)).erase m)
    (by
      intro F hF
      apply (mem_part_iff (by omega)).mpr
      simpa only [Nat.add_sub_cancel] using
        good_two_forward ((mem_familyD_iff hm).mp hF))
    (by
      intro G hG
      obtain ⟨h, hc⟩ := (mem_part_iff (by omega)).mp hG
      have hc' : G.count m = 2 := by simpa only [Nat.add_sub_cancel] using hc
      exact (mem_familyD_iff hm).mpr (good_two_inverse h hc'))
    (by intro F _; simp only [erase_append])
    (by
      intro G hG
      obtain ⟨h, hc⟩ := (mem_part_iff (by omega)).mp hG
      apply restore_two h.1
      simpa only [Nat.add_sub_cancel] using hc)

/-- The six actual partition equivalences, indexed by n = k + 3. -/
def zeroRelaxedEquiv (k : ℕ) :
    ↥(familyD 0 (k + 2)) ≃ ↥(part 0 (k + 3) 0) :=
  zeroEquiv 0 (k + 2) (by omega) (by decide)

/-- The zero-copy part of the strict family at maximum `k + 3`. -/
def zeroStrictEquiv (k : ℕ) :
    ↥(familyD 1 (k + 2)) ≃ ↥(part 1 (k + 3) 0) :=
  zeroEquiv 1 (k + 2) (by omega) (by decide)

/-- The one-copy part of the relaxed family, obtained from the strict family at `k + 2`. -/
def oneRelaxedEquiv (k : ℕ) :
    ↥(familyD 1 (k + 2)) ≃ ↥(part 0 (k + 3) 1) :=
  oneEquiv 0 (k + 2) (by omega)

/-- The one-copy part of the strict family, obtained by shifting the relaxed family at `k + 1`. -/
def oneStrictEquiv (k : ℕ) :
    ↥(familyD 0 (k + 1)) ≃ ↥(part 1 (k + 3) 1) :=
  (shiftEquiv 0 (k + 1) (by omega)).trans (oneEquiv 1 (k + 2) (by omega))

/-- The two-copy part of the relaxed family, obtained from the relaxed family at `k + 1`. -/
def twoRelaxedEquiv (k : ℕ) :
    ↥(familyD 0 (k + 1)) ≃ ↥(part 0 (k + 3) 2) :=
  (shiftEquiv 0 (k + 1) (by omega)).trans (twoEquiv 0 (k + 2) (by omega))

/-- The two-copy part of the strict family, obtained from the strict family at `k + 1`. -/
def twoStrictEquiv (k : ℕ) :
    ↥(familyD 1 (k + 1)) ≃ ↥(part 1 (k + 3) 2) :=
  (shiftEquiv 1 (k + 1) (by omega)).trans (twoEquiv 1 (k + 2) (by omega))

-- Definitional bridges to the original four named forward/inverse maps.
theorem zeroEquiv_val (δ m : ℕ) (hm : 1 ≤ m) (hδ : δ ≤ 1)
    (F : ↥(familyD δ m)) :
    ((zeroEquiv δ m hm hδ) F).val = mapZero (m + 1) F.val := rfl

theorem zeroEquiv_symm_val (δ m : ℕ) (hm : 1 ≤ m) (hδ : δ ≤ 1)
    (G : ↥(part δ (m + 1) 0)) :
    ((zeroEquiv δ m hm hδ).symm G).val = inverseZero (m + 1) G.val := rfl

theorem oneRelaxedEquiv_val (k : ℕ) (F : ↥(familyD 1 (k + 2))) :
    ((oneRelaxedEquiv k) F).val = mapOneRelaxed (k + 3) F.val := rfl

theorem oneRelaxedEquiv_symm_val (k : ℕ) (G : ↥(part 0 (k + 3) 1)) :
    ((oneRelaxedEquiv k).symm G).val = inverseOneRelaxed (k + 3) G.val := rfl

theorem oneStrictEquiv_val (k : ℕ) (F : ↥(familyD 0 (k + 1))) :
    ((oneStrictEquiv k) F).val = mapOneStrict (k + 3) F.val := rfl

theorem oneStrictEquiv_symm_val (k : ℕ) (G : ↥(part 1 (k + 3) 1)) :
    ((oneStrictEquiv k).symm G).val = inverseOneStrict (k + 3) G.val := rfl

theorem twoRelaxedEquiv_val (k : ℕ) (F : ↥(familyD 0 (k + 1))) :
    ((twoRelaxedEquiv k) F).val = mapTwo (k + 3) F.val := rfl

theorem twoRelaxedEquiv_symm_val (k : ℕ) (G : ↥(part 0 (k + 3) 2)) :
    ((twoRelaxedEquiv k).symm G).val = inverseTwo (k + 3) G.val := rfl

theorem twoStrictEquiv_val (k : ℕ) (F : ↥(familyD 1 (k + 1))) :
    ((twoStrictEquiv k) F).val = mapTwo (k + 3) F.val := rfl

theorem twoStrictEquiv_symm_val (k : ℕ) (G : ↥(part 1 (k + 3) 2)) :
    ((twoStrictEquiv k).symm G).val = inverseTwo (k + 3) G.val := rfl

end SchreierQ2
