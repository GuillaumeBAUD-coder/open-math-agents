import OMAStatements.S_oeis_a004171
import Mathlib

/-!
# OEIS A004171: a Collatz orbit can reach `2^(2n+1)` only through a power of two

Suppose the orbit of `x` is at `2^(2n+1)` after `t > 0` steps, and let `y` be its value one step
earlier.

* If `y` is even then `y / 2 = 2^(2n+1)`, so `y = 2^(2n+2)` is a power of two.
* If `y` is odd then `3y + 1 = 2^(2n+1)`. But `2^(2n+1) = 2 · 4^n ≡ 2 (mod 3)`, a contradiction.

So the orbit is at a power of two at time `t - 1 < t`.
-/

open OMA.S_oeis_a004171

namespace OMA.A004171

/-- `2^(2n+1) ≡ 2 (mod 3)`. -/
lemma two_pow_mod_three (n : ℕ) : 2 ^ (2 * n + 1) % 3 = 2 := by
  rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num

end OMA.A004171

open OMA.A004171 in
theorem OMA.solution : type_of% @OMA.S_oeis_a004171.main := by
  intro x n t hx ht h
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  refine ⟨s, by omega, ?_⟩
  unfold collatzOrbit at h ⊢
  rw [Function.iterate_succ_apply'] at h
  obtain ⟨y, hy⟩ : ∃ y, collatzStep^[s] x = y := ⟨_, rfl⟩
  rw [hy] at h ⊢
  unfold collatzStep at h
  split_ifs at h with hpar
  · -- `y` even: `y = 2^(2n+2)`
    refine ⟨2 * n + 2, ?_⟩
    have : 2 ^ (2 * n + 2) = 2 * 2 ^ (2 * n + 1) := by ring
    omega
  · -- `y` odd: impossible modulo `3`
    exfalso
    have := two_pow_mod_three n
    omega
