-- EvenOddEscalator / Stable.lean
-- Bounded versions - q < 1 - stays in net
-- tuna, diesel, pendulum, egg, vortex cannon, fish net

def System := Nat -> Nat

def BoundedStep (s : System) (K : Nat) : Prop :=
  ∀ n, s n ≤ n + K

def orbit_prefix_mem_interval (s : System) (n k : Nat) (lo hi : Nat) : Prop :=
  ∀ i ≤ k, lo ≤ (s^[i] n) ∧ (s^[i] n) ≤ hi

-- Example stable system: stays within s₀ + K*Mcap/(1-q)
-- q < 1 version - mass = pressure, Mcap bounds

def stable_step : Nat -> Nat
| n => n -- placeholder, your non-blow-ups replace with real bound

theorem stable_bounded : BoundedStep stable_step 3 := by
  intro n; simp [stable_step]

-- Add your diesel, tuna, pendulum proofs here
-- They all share same template: BoundedStep + Mcap -> orbit_prefix_mem_interval
