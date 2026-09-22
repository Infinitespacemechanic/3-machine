-- ThreeMachine.lean
-- lake build after you add this to the lib target

namespace ThreeMachine

/-- Unstable: the unpaired +1 stays. Two ticks add 4. -/
def stepU (n : Nat) : Nat :=
  if n % 2 = 0 then n + 3 else n + 1

/-- Stable: use the one only to reach a pair, then stop kicking. -/
def stepS (n : Nat) : Nat :=
  if n % 2 = 0 then n else n + 1

@[simp] theorem stepU_even {n : Nat} (h : n % 2 = 0) :
    stepU n = n + 3 := by simp [stepU, h]

@[simp] theorem stepU_odd {n : Nat} (h : n % 2 = 1) :
    stepU n = n + 1 := by
  have : ¬ n % 2 = 0 := by omega
  simp [stepU, this]

@[simp] theorem stepS_even {n : Nat} (h : n % 2 = 0) :
    stepS n = n := by simp [stepS, h]

@[simp] theorem stepS_odd {n : Nat} (h : n % 2 = 1) :
    stepS n = n + 1 := by
  have : ¬ n % 2 = 0 := by omega
  simp [stepS, this]

/-- Straw that breaks the camel. -/
theorem stepU_two (n : Nat) : stepU (stepU n) = n + 4 := by
  by_cases h : n % 2 = 0
  · have h3 : (n + 3) % 2 = 1 := by omega
    simp [stepU_even h, stepU_odd h3]
  · have h1 : n % 2 = 1 := by omega
    have h2 : (n + 1) % 2 = 0 := by omega
    simp [stepU_odd h1, stepU_even h2]

theorem stepU_unbounded (n : Nat) (k : Nat) :
    (stepU^[2 * k]) n = n + 4 * k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h2 : stepU^[2] n = n + 4 := by
      simpa [Function.iterate_succ, Function.iterate_one] using stepU_two n
    -- iterate 2(k+1) = two more steps after 2k
    calc
      (stepU^[2 * k.succ]) n
          = (stepU^[2 * k + 2]) n := by simp [Nat.mul_succ]
      _ = (stepU^[2] (stepU^[2 * k] n)) := by
            simp [Function.iterate_add]
      _ = (stepU^[2 * k] n) + 4 := by
            simpa [Function.iterate_succ, Function.iterate_one] using
              stepU_two (stepU^[2 * k] n)
      _ = n + 4 * k + 4 := by simp [ih]
      _ = n + 4 * k.succ := by simp [Nat.mul_succ, Nat.add_assoc]

/-- Pair settles. One step lands on even; after that it does not move. -/
theorem stepS_lands_even (n : Nat) : (stepS n) % 2 = 0 := by
  by_cases h : n % 2 = 0
  · simp [stepS_even h, h]
  · have h1 : n % 2 = 1 := by omega
    simp [stepS_odd h1]
    omega

theorem stepS_fixed_on_pair {n : Nat} (h : n % 2 = 0) :
    stepS n = n := stepS_even h

theorem stepS_two_on_pair {n : Nat} (h : n % 2 = 0) :
    stepS (stepS n) = n := by simp [stepS_even h]

/-- After at most one tick you are on a pair and you stay there. -/
theorem stepS_bounded (n : Nat) (k : Nat) :
    (stepS^[k.succ]) n = stepS n := by
  induction k with
  | zero => simp [Function.iterate_succ, Function.iterate_one]
  | succ k ih =>
    have he : (stepS n) % 2 = 0 := stepS_lands_even n
    have : stepS (stepS n) = stepS n := stepS_even he
    simpa [Function.iterate_succ_right, ih, this]

end ThreeMachine
