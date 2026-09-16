import SchreierUnified.Multisets
import Mathlib.Tactic

/-!
# General terminal-composition correspondence

The target is a subtype of actual lists of natural numbers, not an image of
an encoding. Its predicate specifies all allowed compositions independently.
The parameter `N` is the word cost, so the multiset maximum is `N + 1`.
-/

namespace SchreierUnified

/-- A nonempty composition, with a separately constrained terminal part. -/
def IsTerminalComposition (q total : ℕ) (c : List ℕ) : Prop :=
  ∃ p : List ℕ, ∃ t : ℕ, c = p ++ [t] ∧
    (∀ a ∈ p, q ≤ a ∧ a ≤ q + 2) ∧ q ≤ t ∧ t < 2 * q ∧ p.sum + t = total

/-- The digits read from the nonterminal parts. -/
def digitOfPart (q a : ℕ) : Fin 3 := ⟨(a - q) % 3, Nat.mod_lt _ (by decide)⟩

theorem shifted_sum (q : ℕ) (w : Word) :
    (w.map (fun d => q + d.val)).sum = q * w.length + weight w := by
  induction w with
  | nil => simp [weight]
  | cons d w ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
      simp only [weight, List.map_cons, List.sum_cons]
      ring

theorem shifted_unshifted (q : ℕ) (p : List ℕ)
    (hp : ∀ a ∈ p, q ≤ a ∧ a ≤ q + 2) :
    ((p.map (digitOfPart q)).map (fun d => q + d.val)) = p := by
  induction p with
  | nil => rfl
  | cons a p ih =>
      have ha := hp a (by simp)
      have ht : ∀ b ∈ p, q ≤ b ∧ b ≤ q + 2 := by
        intro b hb
        exact hp b (by simp [hb])
      simp only [List.map_cons, ih ht]
      congr 1
      dsimp [digitOfPart]
      rw [Nat.mod_eq_of_lt (by omega)]
      omega

theorem unshifted_shifted (q : ℕ) (w : Word) :
    (w.map (fun d => q + d.val)).map (digitOfPart q) = w := by
  induction w with
  | nil => rfl
  | cons d w ih =>
      simp only [List.map_cons, ih]
      congr 1
      apply Fin.ext
      change (q + d.val - q) % 3 = d.val
      simp

theorem append_last_injective {α : Type*} {p s : List α} {t u : α}
    (h : p ++ [t] = s ++ [u]) : p = s ∧ t = u := by
  have hr := congrArg List.reverse h
  simp only [List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.singleton_append] at hr
  have hh := List.cons.inj hr
  exact ⟨List.reverse_injective hh.2, hh.1⟩

theorem terminalComposition_injective (q r : ℕ) :
    Function.Injective (terminalComposition q r) := by
  intro u v h
  have hm := (append_last_injective h).1
  have hi := congrArg (List.map (digitOfPart q)) hm
  simpa only [unshifted_shifted] using hi

/-- Every encoded word has exactly the required total and part restrictions. -/
theorem terminalComposition_mem (q r N : ℕ) (hq : 0 < q) (hr : r < q)
    (w : Word) (hw : cost q r w = N) :
    IsTerminalComposition q (q * (N + 1) + q - 1 - r) (terminalComposition q r w) := by
  let u := (weight w + r) % q
  have hu : u < q := Nat.mod_lt _ hq
  have he := Nat.div_add_mod (weight w + r) q
  have hc : w.length + (weight w + r) / q = N := hw
  refine ⟨w.map (fun d => q + d.val), 2 * q - 1 - u, rfl, ?_, ?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨d, _, rfl⟩ := List.mem_map.mp ha
    have hd := d.isLt
    omega
  · omega
  · omega
  · rw [shifted_sum]
    have hp := congrArg (q * ·) hc
    have huadd := Nat.sub_add_cancel (show u ≤ 2 * q - 1 by omega)
    have hqadd := Nat.sub_add_cancel (show 1 ≤ 2 * q by omega)
    have hsum1 := Nat.sub_add_cancel (show 1 ≤ q * (N + 1) + q by omega)
    have hsum2 := Nat.sub_add_cancel (show r ≤ q * (N + 1) + q - 1 - r + r by omega)
    have hsum3 := Nat.sub_add_cancel (show r ≤ q * (N + 1) + q - 1 by omega)
    dsimp [u] at *
    nlinarith

/-- Every permitted composition is obtained from a word of the specified cost. -/
theorem terminalComposition_surjective (q r N : ℕ) (hq : 0 < q) (hr : r < q)
    (c : List ℕ) (hc : IsTerminalComposition q (q * (N + 1) + q - 1 - r) c) :
    ∃ w : Word, cost q r w = N ∧ terminalComposition q r w = c := by
  obtain ⟨p, t, rfl, hp, ht, ht', htotal⟩ := hc
  let w : Word := p.map (digitOfPart q)
  have hw : w.map (fun d => q + d.val) = p := shifted_unshifted q p hp
  have hs : q * w.length + weight w + t = q * (N + 1) + q - 1 - r := by
    rw [← shifted_sum, hw]
    exact htotal
  have hL : w.length ≤ N := by
    by_contra h
    have hmul := Nat.mul_le_mul_left q (show N + 1 ≤ w.length by omega)
    have htotal_lt : q * (N + 1) + q - 1 - r < q * (N + 1) + q := by omega
    omega
  let u := 2 * q - 1 - t
  have hu : u < q := by dsimp [u]; omega
  have hdecomp : weight w + r = q * (N - w.length) + u := by
    have hsub := Nat.sub_add_cancel hL
    have hmul := congrArg (q * ·) hsub
    have htadd := Nat.sub_add_cancel (show t ≤ 2 * q - 1 by omega)
    have hqadd := Nat.sub_add_cancel (show 1 ≤ 2 * q by omega)
    have hsum1 := Nat.sub_add_cancel (show 1 ≤ q * (N + 1) + q by omega)
    have hsum2 := Nat.sub_add_cancel (show r ≤ q * (N + 1) + q - 1 by omega)
    dsimp [u]
    nlinarith
  have hdiv : (weight w + r) / q = N - w.length := by
    rw [hdecomp, Nat.add_comm, Nat.add_mul_div_left _ _ hq, Nat.div_eq_of_lt hu]
    omega
  have hmod : (weight w + r) % q = u := by
    rw [hdecomp, Nat.add_mod]
    simp [Nat.mod_eq_of_lt hu]
  refine ⟨w, ?_, ?_⟩
  · unfold cost
    rw [hdiv]
    omega
  · unfold terminalComposition
    rw [hw, hmod]
    congr 1
    dsimp [u]
    congr 1
    omega

/-- Words of any cost correspond to all compositions with the terminal constraint. -/
noncomputable def wordTerminalCompositionEquiv (q r N : ℕ)
    (hq : 0 < q) (hr : r < q) :
    {w : Word // cost q r w = N} ≃
      {c : List ℕ // IsTerminalComposition q (q * (N + 1) + q - 1 - r) c} :=
  Equiv.ofBijective
    (fun w => ⟨terminalComposition q r w.val,
      terminalComposition_mem q r N hq hr w.val w.property⟩)
    ⟨by
      intro u v h
      apply Subtype.ext
      exact terminalComposition_injective q r (congrArg Subtype.val h), by
      intro c
      obtain ⟨w, hw, he⟩ := terminalComposition_surjective q r N hq hr c.val c.property
      exact ⟨⟨w, hw⟩, Subtype.ext he⟩⟩

/-- The paper's general theorem, attached to the original multiset family. -/
noncomputable def originalTerminalCompositionEquiv (q r N : ℕ)
    (hq : 0 < q) (hr : r < q) :
    {F // F ∈ family q r (N + 1)} ≃
      {c : List ℕ // IsTerminalComposition q (q * (N + 1) + q - 1 - r) c} :=
  (originalWordEquiv q r N hq).trans (wordTerminalCompositionEquiv q r N hq hr)

#print axioms SchreierUnified.originalTerminalCompositionEquiv

end SchreierUnified
