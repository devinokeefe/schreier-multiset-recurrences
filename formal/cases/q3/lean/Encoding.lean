import SourceBasics
import Compositions
import Mathlib.Data.Multiset.Replicate

namespace SchreierQ3

/-- The ceiling of k / 3, bounding occupied positions for positive cardinalities. -/
def cutoff (k : ℕ) : ℕ := (k + 2) / 3

/-- The final part records the residue of the lower multiplicity sum k - 1. -/
def terminal (k : ℕ) : ℕ := 5 - ((k - 1) % 3)

/-- Encode consecutive multiplicities, retaining a part 3 for each zero. -/
def pack (m : ℕ) : ℕ → Multiset ℕ → List ℕ
  | 0, _ => []
  | l + 1, F => (3 + F.count m) :: pack (m + 1) l F

/-- Decode an initial block into multiplicities at consecutive positions. -/
def unpack (m : ℕ) : List ℕ → Multiset ℕ
  | [] => 0
  | t :: p => Multiset.replicate (t - 3) m + unpack (m + 1) p

/-- Append the cardinality-residue part to the encoded source multiplicities. -/
def encode (n : ℕ) (F : Multiset ℕ) : List ℕ :=
  pack (cutoff F.card) (n - cutoff F.card) F ++ [terminal F.card]

/-- Decode the initial block and append n; inverse laws require family membership. -/
def decode (n : ℕ) (p : List ℕ) : Multiset ℕ :=
  unpack (n - p.dropLast.length) p.dropLast + {n}

theorem cutoff_spec (k : ℕ) (hk : 0 < k) :
    0 < cutoff k ∧ 3 * (cutoff k - 1) < k ∧ k ≤ 3 * cutoff k := by
  unfold cutoff
  omega

theorem cutoff_le_of_size_le {k i : ℕ} (h : k ≤ 3 * i) :
    cutoff k ≤ i := by
  unfold cutoff
  omega

theorem terminal_range (k : ℕ) :
    3 ≤ terminal k ∧ terminal k ≤ 5 := by
  unfold terminal
  omega

theorem card_add_terminal (k : ℕ) (hk : 0 < k) :
    k + terminal k = 3 * cutoff k + 3 := by
  unfold cutoff terminal
  omega

theorem decoded_cardinality (m t : ℕ) (hm : 0 < m)
    (ht3 : 3 ≤ t) (ht5 : t ≤ 5) :
    0 < 3 * m + 3 - t ∧
      cutoff (3 * m + 3 - t) = m ∧
      3 * m + 3 - t ≤ 3 * m := by
  unfold cutoff
  omega

theorem decoded_terminal (m t : ℕ) (hm : 0 < m)
    (ht3 : 3 ≤ t) (ht5 : t ≤ 5) :
    terminal (3 * m + 3 - t) = t := by
  unfold terminal
  omega

theorem cutoff_le_top {n : ℕ} {F : Multiset ℕ}
    (hF : F ∈ family n) : cutoff F.card ≤ n :=
  cutoff_le_of_size_le (source_size_le_top hF)

theorem source_above_cutoff {n i : ℕ} {F : Multiset ℕ}
    (hF : F ∈ family n) (hi : i ∈ F) : cutoff F.card ≤ i := by
  have hs := (schreier3_iff F).mp (mem_family.mp hF).2.2.2 i hi
  exact cutoff_le_of_size_le hs

@[simp] theorem pack_length (m l : ℕ) (F : Multiset ℕ) :
    (pack m l F).length = l := by
  induction l generalizing m with
  | zero => rfl
  | succ l ih => simp [pack, ih]

theorem pack_parts (m l : ℕ) (F : Multiset ℕ) :
    (∀ i, m ≤ i → i < m + l → F.count i ≤ 2) →
    Parts (pack m l F) := by
  induction l generalizing m with
  | zero => intro _; exact parts_nil
  | succ l ih =>
      intro hc
      have h0 := hc m (by omega) (by omega)
      apply parts_cons.mpr
      refine ⟨⟨by omega, by omega⟩, ih (m + 1) ?_⟩
      intro i hi hj
      exact hc i (by omega) (by omega)

theorem unpack_support (m : ℕ) (p : List ℕ) {i : ℕ} :
    i ∈ unpack m p → m ≤ i ∧ i < m + p.length := by
  induction p generalizing m with
  | nil => simp [unpack]
  | cons t p ih =>
      intro hi
      rw [unpack, Multiset.mem_add] at hi
      rcases hi with hi | hi
      · have he := Multiset.eq_of_mem_replicate hi
        subst i
        simp only [List.length_cons]
        omega
      · have hb := ih (m + 1) hi
        simp only [List.length_cons]
        omega

theorem count_unpack_zero (m : ℕ) (p : List ℕ) (i : ℕ)
    (hi : i < m ∨ m + p.length ≤ i) : (unpack m p).count i = 0 := by
  apply Multiset.count_eq_zero.mpr
  intro hmem
  have hb := unpack_support m p hmem
  omega

theorem unpack_count_le_two (m : ℕ) (p : List ℕ) (i : ℕ) :
    Parts p → (unpack m p).count i ≤ 2 := by
  induction p generalizing m with
  | nil => intro _; simp [unpack]
  | cons t p ih =>
      intro hp
      rcases parts_cons.mp hp with ⟨ht, hp⟩
      by_cases hmi : m = i
      · subst i
        have hz := count_unpack_zero (m + 1) p m (Or.inl (by omega))
        simp only [unpack, Multiset.count_add,
          Multiset.count_replicate_self, hz, Nat.add_zero]
        omega
      · have hb := ih (m + 1) hp
        simpa [unpack, Multiset.count_replicate, hmi] using hb

theorem unpack_weight (m : ℕ) (p : List ℕ) :
    (∀ t ∈ p, 3 ≤ t) →
    3 * p.length + (unpack m p).card = p.sum := by
  induction p generalizing m with
  | nil => intro _; simp [unpack]
  | cons t p ih =>
      intro hp
      have ht := hp t (by simp)
      have hp' : ∀ u ∈ p, 3 ≤ u := by
        intro u hu
        exact hp u (by simp [hu])
      have hb := ih (m + 1) hp'
      simp only [List.length_cons, List.sum_cons, unpack,
        Multiset.card_add, Multiset.card_replicate]
      omega

theorem count_unpack_pack (m l : ℕ) (F : Multiset ℕ) (i : ℕ) :
    (unpack m (pack m l F)).count i =
      if m ≤ i ∧ i < m + l then F.count i else 0 := by
  induction l generalizing m with
  | zero => simp [pack, unpack]
  | succ l ih =>
      simp only [pack, unpack, Multiset.count_add,
        Multiset.count_replicate, Nat.add_sub_cancel_left, ih]
      by_cases hmi : m = i
      · subst i
        have hno : ¬(m + 1 ≤ m ∧ m < m + 1 + l) := by omega
        have hyes : m ≤ m ∧ m < m + (l + 1) := by omega
        simp [hno, hyes]
      · have he : (m + 1 ≤ i ∧ i < m + 1 + l) ↔
            (m ≤ i ∧ i < m + (l + 1)) := by omega
        simp [hmi, he]

theorem unpack_pack_restore (m l : ℕ) (F : Multiset ℕ)
    (hs : ∀ i ∈ F, m ≤ i ∧ i ≤ m + l)
    (ht : F.count (m + l) = 1) :
    unpack m (pack m l F) + {m + l} = F := by
  apply Multiset.ext.mpr
  intro i
  rw [Multiset.count_add, count_unpack_pack, Multiset.count_singleton]
  by_cases he : i = m + l
  · subst i
    simp [ht]
  · by_cases hi : m ≤ i ∧ i < m + l
    · simp [hi, he]
    · have hz : F.count i = 0 := by
        apply Multiset.count_eq_zero.mpr
        intro hmem
        have hb := hs i hmem
        omega
      simp [hi, he, hz]

theorem pack_congr (m l : ℕ) (F G : Multiset ℕ) :
    (∀ i, m ≤ i → i < m + l → F.count i = G.count i) →
    pack m l F = pack m l G := by
  induction l generalizing m with
  | zero => intro _; rfl
  | succ l ih =>
      intro h
      have hm := h m (by omega) (by omega)
      simp only [pack, hm]
      apply congrArg (List.cons (3 + G.count m))
      apply ih (m + 1)
      intro i hi hj
      exact h i (by omega) (by omega)

theorem pack_unpack (m : ℕ) (p : List ℕ) :
    (∀ t ∈ p, 3 ≤ t) → pack m p.length (unpack m p) = p := by
  induction p generalizing m with
  | nil => intro _; rfl
  | cons t p ih =>
      intro hp
      have ht := hp t (by simp)
      have hp' : ∀ u ∈ p, 3 ≤ u := by
        intro u hu
        exact hp u (by simp [hu])
      have hz := count_unpack_zero (m + 1) p m (Or.inl (by omega))
      have hhead : (unpack m (t :: p)).count m = t - 3 := by
        simp [unpack, hz]
      have htail :
          pack (m + 1) p.length (unpack m (t :: p)) =
          pack (m + 1) p.length (unpack (m + 1) p) := by
        apply pack_congr
        intro i hi hj
        have hne : m ≠ i := by omega
        simp [unpack, Multiset.count_replicate, hne]
      change (3 + (unpack m (t :: p)).count m) ::
        pack (m + 1) p.length (unpack m (t :: p)) = t :: p
      rw [hhead, htail, ih (m + 1) hp']
      have he : 3 + (t - 3) = t := by omega
      rw [he]

theorem pack_unpack_top (m : ℕ) (p : List ℕ)
    (hp : ∀ t ∈ p, 3 ≤ t) :
    pack m p.length (unpack m p + {m + p.length}) = p := by
  calc
    pack m p.length (unpack m p + {m + p.length}) =
        pack m p.length (unpack m p) := by
      apply pack_congr
      intro i hi hj
      have hne : i ≠ m + p.length := by omega
      simp [Multiset.count_add, hne]
    _ = p := pack_unpack m p hp

end SchreierQ3
