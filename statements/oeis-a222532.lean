import Mathlib

/-!
# A222532: the tree of primes under alternating sums of consecutive primes

Source: https://oeis.org/A222532
Credit: @LordMike

a(1)=2; for n >= 1, a(n+1) is the least prime p_m such that a(n)=p_m-p_{m-1}+...+(-1)^{m-k}p_k for some 0<k<m.

Conjecture: For any given prime p, if we define b(1)=p and let b(n+1) be the least prime p_m such that
b(n)=p_m-p_{m-1}+...+(-1)^{m-k}p_k for some 0<k<m, then a(n)=b(n') for some positive integers n and n'.

Reading used here: `Nat.nth Nat.Prime i` is the (i+1)-th prime, so the 1-indexed `p_j` is `Nat.nth Nat.Prime (j-1)`;
shifting both indices by one, `step p` is the least prime `p_m` (`m > k ≥ 0`, so at least two terms) equal to an
alternating sum ending at `p_m` that equals `p`. Then `a(n) = step^[n-1] 2` and `b(n) = step^[n-1] p`.
-/

namespace OMA.S_oeis_a222532

/-- Least prime `p_m` with `p = p_m - p_{m-1} + ... + (-1)^(m-k) p_k` for some `k < m` (0-indexed primes). -/
noncomputable def step (p : ℕ) : ℕ := sInf {q | q.Prime ∧ ∃ k m : ℕ, k < m ∧ q = Nat.nth Nat.Prime m ∧
  (p : ℤ) = ∑ j ∈ Finset.Icc k m, (-1) ^ (m - j) * (Nat.nth Nat.Prime j : ℤ)}

theorem main : ∀ p : ℕ, p.Prime → ∃ n n' : ℕ, (step^[n] 2).Prime ∧ step^[n] 2 = step^[n'] p := by
  sorry

end OMA.S_oeis_a222532
