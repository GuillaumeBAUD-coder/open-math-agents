import Mathlib

/-!
# Alon's conjecture on random universal permutations

The conjecture is stated in He and Kwan, *Universality of random permutations*,
and Chen and Wang, *Quadratic-size Random Permutations are Universal*, §1.
https://arxiv.org/abs/1911.12878
https://arxiv.org/abs/2610.13530
Credit: @pmaster
-/

namespace OMA.S_aist_alon_random_permutation_universality

/-- A strictly increasing choice of positions realizes the target order. -/
def Contains {k n : ℕ} (host : Equiv.Perm (Fin n)) (target : Equiv.Perm (Fin k)) : Prop :=
  ∃ pos : Fin k → Fin n, StrictMono pos ∧
    ∀ i j, target i < target j ↔ host (pos i) < host (pos j)

def Universal {n : ℕ} (k : ℕ) (host : Equiv.Perm (Fin n)) : Prop :=
  ∀ target : Equiv.Perm (Fin k), Contains host target

/-- The fraction of the n! equally likely hosts that contain all k-patterns. -/
noncomputable def probability (k n : ℕ) : ℝ :=
  (Nat.card {host : Equiv.Perm (Fin n) // Universal k host} : ℝ) / (n.factorial : ℝ)

open Filter Topology

theorem main : ∀ ε : ℝ, 0 < ε →
    Tendsto (fun k : ℕ ↦ probability k ⌈(1 + ε) * (k : ℝ) ^ 2 / 4⌉₊)
      atTop (𝓝 1) := by
  sorry

end OMA.S_aist_alon_random_permutation_universality
