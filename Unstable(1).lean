-- EvenOddEscalator / Unstable.lean
-- Unbounded drift with bounded steps ≤3
-- No agents, just Lean

def step : Nat -> Nat
| n => if n % 2 = 0 then n + 3 else n + 1

def step_two (n : Nat) : Nat := n + 4

lemma step_even (n : Nat) (h : n % 2 = 0) : step n = n + 3 := by
  simp [step, h]

lemma step_odd (n : Nat) (h : n % 2 = 1) : step n = n + 1 := by
  simp [step, h]
  -- odd +1 = even, etc.

lemma step_two_eq (n : Nat) (h : n % 2 = 0) : step (step n) = n + 4 := by
  rw [step_even n h]
  have : (n + 3) % 2 = 1 := by omega
  rw [step_odd (n+3) this]
  omega

theorem iterate_two_mul (n k : Nat) (h : n % 2 = 0) :
  (fun m => step (step m))^[k] n = n + 4 * k := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp [Function.iterate_succ_apply']
    rw [ih]
    have : (n + 4 * k) % 2 = 0 := by omega
    rw [step_two_eq _ this]
    omega

theorem unbounded : ∀ B, ∃ n k, (fun m => step (step m))^[k] n > B := by
  intro B
  use 0, B+1
  simp [iterate_two_mul 0 (B+1) (by simp)]
  omega
