import FormalConjectures.ErdosProblems.«647»

-- Reduction Erdos647.erdos_647.R1 of Erdős Problem 647
-- Credit: @yves-pires

namespace OMA.R_Erdos647_erdos_647_R1

open ArithmeticFunction.sigma

-- This bound follows by maximizing (a + 1)^6 / p^a separately at each prime.
-- Only primes below 64 contribute a factor greater than one.
def H1 : Prop := ∀ m : ℕ, (σ 0 m) ^ 6 ≤ 139 ^ 6 * m

-- A candidate needs divisor counts only for the final O(n^(1/6)) shifts.
def H2 : Prop :=
  ∃ n : ℕ, 24 < n ∧ ∀ k : ℕ, 0 < k → k ≤ n →
    (k + 3) ^ 6 ≤ 139 ^ 6 * (n - k) → σ 0 (n - k) ≤ k + 2

theorem main : H1 → H2 → type_of% @Erdos647.erdos_647 := by
  intro hbound hwindow
  obtain ⟨n, hn, htest⟩ := hwindow
  letI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  refine ⟨n, hn, ciSup_le ?_⟩
  intro m
  change (m : ℕ) + σ 0 (m : ℕ) ≤ n + 2
  have hm := m.isLt
  let k := n - (m : ℕ)
  have hk : 0 < k := Nat.sub_pos_of_lt hm
  have hkn : k ≤ n := Nat.sub_le _ _
  have hback : n - k = (m : ℕ) := by dsimp [k]; omega
  by_contra! hfail
  have hlarge : k + 3 ≤ σ 0 (m : ℕ) := by dsimp [k]; omega
  have hcut : (k + 3) ^ 6 ≤ 139 ^ 6 * (m : ℕ) :=
    (Nat.pow_le_pow_left hlarge 6).trans (hbound (m : ℕ))
  have hsmall := htest k hk hkn (by simpa only [hback] using hcut)
  rw [hback] at hsmall
  omega

end OMA.R_Erdos647_erdos_647_R1
