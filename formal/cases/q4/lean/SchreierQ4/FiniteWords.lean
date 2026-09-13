import SchreierQ4.OriginalBridge

namespace SchreierQ4.WordCounting

open WordModel OriginalBridge

theorem digit_cases (d : Fin 3) : d = 0 ∨ d = 1 ∨ d = 2 := by
  have hd := d.isLt
  have hv : d.val = 0 ∨ d.val = 1 ∨ d.val = 2 := by omega
  rcases hv with h | h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Or.inl (Fin.ext h))
  · exact Or.inr (Or.inr (Fin.ext h))

/-- Independent enumeration of all ternary lists of bounded length. -/
def boundedWords : ℕ → Finset Word
  | 0 => {[]}
  | N + 1 => {[]} ∪
      ((boundedWords N).image (List.cons 0) ∪
       (boundedWords N).image (List.cons 1) ∪
       (boundedWords N).image (List.cons 2))

theorem mem_boundedWords (N : ℕ) (w : Word) :
    w ∈ boundedWords N ↔ w.length ≤ N := by
  induction N generalizing w with
  | zero =>
      cases w with
      | nil => simp [boundedWords]
      | cons d w => simp [boundedWords]
  | succ N ih =>
      cases w with
      | nil => simp [boundedWords]
      | cons d w =>
          rcases digit_cases d with h | h | h
          all_goals subst d
          all_goals simp [boundedWords, Finset.mem_image, ih]

/-- The finite set of words of cost `N` at starting residue `r`. -/
def words (r : Fin 4) (N : ℕ) : Finset Word :=
  (boundedWords N).filter (fun w => cost r w = N)

theorem mem_words (r : Fin 4) (N : ℕ) (w : Word) :
    w ∈ words r N ↔ cost r w = N := by
  rw [words, Finset.mem_filter, mem_boundedWords]
  constructor
  · exact And.right
  · intro h
    refine ⟨?_, h⟩
    have hl := length_le_cost r w
    omega

/-- The cardinality of the words of the specified residue and cost. -/
def wordCount (r : Fin 4) (N : ℕ) : ℕ := (words r N).card

/-- The all-N original-object/independently-enumerated-word count bridge. -/
theorem a_eq_wordCount (N : ℕ) : SchreierQ4.a (N + 1) = wordCount 0 N := by
  unfold SchreierQ4.a wordCount
  symm
  apply Finset.card_bij (fun w _ => decode w)
  · intro w hw
    have hc := (mem_words 0 N w).mp hw
    simpa only [hc] using decode_admissible w
  · intro u hu v hv h
    apply decode_injective_of_cost
    · exact ((mem_words 0 N u).mp hu).trans ((mem_words 0 N v).mp hv).symm
    · exact h
  · intro F hF
    exact ⟨encode N F, (mem_words 0 N _).mpr (encode_cost hF), decode_encode hF⟩

end SchreierQ4.WordCounting
