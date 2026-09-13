import Statement

/-!
Total multiset operations for the partition by next-to-largest multiplicity.
Their restricted domains and inverse identities are proved in
`SchreierQ2.Equivalences`; no unrestricted bijectivity is asserted here.
-/

namespace SchreierQ2

/-- Increase every entry by one. -/
def shiftUp (F : Multiset ℕ) : Multiset ℕ := F.map Nat.succ

/-- Take the predecessor of every entry; inverse laws require positive entries. -/
def shiftDown (F : Multiset ℕ) : Multiset ℕ := F.map Nat.pred

@[simp] theorem shiftUp_card (F : Multiset ℕ) : (shiftUp F).card = F.card := by
  simp [shiftUp]

@[simp] theorem shiftDown_card (F : Multiset ℕ) : (shiftDown F).card = F.card := by
  simp [shiftDown]

@[simp] theorem shiftDown_shiftUp (F : Multiset ℕ) : shiftDown (shiftUp F) = F := by
  simp [shiftDown, shiftUp, Multiset.map_map]

theorem shiftUp_injective : Function.Injective shiftUp := by
  intro F G h
  have h' := congrArg shiftDown h
  simpa only [shiftDown_shiftUp] using h'

/-- Replace the unique old maximum n-1 by n. -/
def mapZero (n : ℕ) (F : Multiset ℕ) : Multiset ℕ :=
  F.erase (n - 1) + {n}

/-- Replace maximum `n` by `n - 1`. -/
def inverseZero (n : ℕ) (G : Multiset ℕ) : Multiset ℕ :=
  G.erase n + {n - 1}

/-- From the strict family at n-1 to the relaxed one-copy class at n. -/
def mapOneRelaxed (n : ℕ) (F : Multiset ℕ) : Multiset ℕ := F + {n}

/-- Remove maximum `n` from the relaxed one-copy part. -/
def inverseOneRelaxed (n : ℕ) (G : Multiset ℕ) : Multiset ℕ := G.erase n

/-- From the relaxed family at n-2 to the strict one-copy class at n. -/
def mapOneStrict (n : ℕ) (F : Multiset ℕ) : Multiset ℕ := shiftUp F + {n}

/-- Remove maximum `n` and shift the remaining entries down by one. -/
def inverseOneStrict (n : ℕ) (G : Multiset ℕ) : Multiset ℕ :=
  shiftDown (G.erase n)

/-- Both slack values use the same two-copy construction. -/
def mapTwo (n : ℕ) (F : Multiset ℕ) : Multiset ℕ :=
  shiftUp F + {n - 1} + {n}

/-- Remove one copy each of `n` and `n - 1`, then shift the remainder down by one. -/
def inverseTwo (n : ℕ) (G : Multiset ℕ) : Multiset ℕ :=
  shiftDown ((G.erase n).erase (n - 1))

end SchreierQ2
