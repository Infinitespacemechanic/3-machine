import ThreeMachine

theorem diesel_principle :
    ∃ s : Nat → Nat, (∀ n, s n ≤ n + 3) ∧ ¬ ∃ B, ∀ k n, (s^[k] n) ≤ B := by
  refine ⟨ThreeMachine.stepU, ?_, ?_⟩
  · intro n
    unfold ThreeMachine.stepU
    split_ifs <;> omega
  · intro ⟨B, hB⟩
    have h := hB (2 * (B + 1)) 0
    rw [ThreeMachine.stepU_unbounded 0 (B + 1)] at h
    omega
