import Bridge
import RecurrenceAlgebra

namespace SchreierQ3

theorem initialValues : InitialValues := by
  have b1 : a 1 = c 5 := count_bridge (by decide)
  have b2 : a 2 = c 8 := count_bridge (by decide)
  have b3 : a 3 = c 11 := count_bridge (by decide)
  have b4 : a 4 = c 14 := count_bridge (by decide)
  have b5 : a 5 = c 17 := count_bridge (by decide)
  rcases c_selected_values with ⟨h1, h2, h3, h4, h5⟩
  unfold InitialValues
  omega

theorem c_step_int (k : ℕ) :
    (c (k + 5) : ℤ) =
      (c (k + 2) : ℤ) + (c (k + 1) : ℤ) + (c k : ℤ) := by
  have h := c_step k
  omega

theorem recurrence : Recurrence := by
  intro n hn
  rw [count_bridge (n := n) (by omega),
    count_bridge (n := n - 1) (by omega),
    count_bridge (n := n - 2) (by omega),
    count_bridge (n := n - 3) (by omega),
    count_bridge (n := n - 4) (by omega),
    count_bridge (n := n - 5) (by omega)]
  have h := stride_three (fun k => (c k : ℤ)) c_step_int (3 * (n - 5) + 2)
  have e0 : 3 * (n - 5) + 2 + 15 = 3 * n + 2 := by omega
  have e1 : 3 * (n - 5) + 2 + 12 = 3 * (n - 1) + 2 := by omega
  have e2 : 3 * (n - 5) + 2 + 9 = 3 * (n - 2) + 2 := by omega
  have e3 : 3 * (n - 5) + 2 + 6 = 3 * (n - 3) + 2 := by omega
  have e4 : 3 * (n - 5) + 2 + 3 = 3 * (n - 4) + 2 := by omega
  simpa only [e0, e1, e2, e3, e4] using h

theorem main : MainClaim := ⟨initialValues, recurrence⟩

end SchreierQ3
