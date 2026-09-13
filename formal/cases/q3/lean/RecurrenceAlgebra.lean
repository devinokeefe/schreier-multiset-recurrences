import Lean.Elab.Tactic.Omega

namespace SchreierQ3

/-- The eight shifted equations give the exact stride-three recurrence. -/
theorem stride_three (u : Nat → Int)
    (h : ∀ k : Nat, u (k + 5) = u (k + 2) + u (k + 1) + u k)
    (m : Nat) :
    u (m + 15) = 3 * u (m + 12) - 3 * u (m + 9) +
      4 * u (m + 6) - 2 * u (m + 3) + u m := by
  -- For R_k = u(k+5) - u(k+2) - u(k+1) - u(k), cancel the combination
  -- R_(m+10) - 2*R_(m+7) + R_(m+6) + R_(m+5) + R_(m+4)
  --   - R_(m+3) - R_(m+1) + R_m.
  have r0 : u (m + 5) = u (m + 2) + u (m + 1) + u m := h m
  have r1 : u (m + 6) = u (m + 3) + u (m + 2) + u (m + 1) := h (m + 1)
  have r3 : u (m + 8) = u (m + 5) + u (m + 4) + u (m + 3) := h (m + 3)
  have r4 : u (m + 9) = u (m + 6) + u (m + 5) + u (m + 4) := h (m + 4)
  have r5 : u (m + 10) = u (m + 7) + u (m + 6) + u (m + 5) := h (m + 5)
  have r6 : u (m + 11) = u (m + 8) + u (m + 7) + u (m + 6) := h (m + 6)
  have r7 : u (m + 12) = u (m + 9) + u (m + 8) + u (m + 7) := h (m + 7)
  have r10 : u (m + 15) = u (m + 12) + u (m + 11) + u (m + 10) := h (m + 10)
  omega

end SchreierQ3
