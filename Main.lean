import EvenOddEscalator.Unstable
import EvenOddEscalator.Stable

-- Main principle
theorem diesel_principle :
  (∃ s : Nat -> Nat, (∀ n, s n ≤ n + 3) ∧ ¬ ∃ B, ∀ k n, (s^[k] n) ≤ B) := by
  -- witness is EvenOddEscalator.step∘step
  sorry -- replace after imports compile
