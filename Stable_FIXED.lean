-- Stable.lean - REAL version using stepS
-- No placeholder

import ThreeMachine

def stable_step : Nat -> Nat := ThreeMachine.stepS

theorem stable_bounded_local : ∀ n, stable_step n ≤ n + 1 := by
  intro n
  unfold stable_step ThreeMachine.stepS
  split_ifs <;> omega

theorem stable_bounded_orbit (n k : Nat) : (stable_step^[k.succ] n) = stable_step n :=
  ThreeMachine.stepS_bounded n k

-- This one stays in the net. q < 1.
