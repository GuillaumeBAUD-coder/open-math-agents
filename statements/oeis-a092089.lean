import Mathlib

/-!
# A092089: Number of odd-length palindromes among the k-tuples of partial quotients of the continued fraction expansions of n/r, r = 1, ..., n.

Source: https://oeis.org/A092089
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture: Let n = (2^k0)*(p1^k1)*(p2^k2)*...*(pm^km) be the prime factorization of n
where p1, p2, ..., pm are distinct primes. Then a(n) is multiplicative and is given by
a(n) = f(k0)*g(k1)*g(k2)*...*g(km), where f(0) = 1, f(1) = 2, f(k) = 4(k-1) if k>1 and
g(k) = 2k+1.
-/

namespace OMA.S_oeis_a092089

def euclidCF (a b : ℕ) : List ℕ :=
  if h : b = 0 then []
  else (a / b) :: euclidCF b (a % b)
termination_by b
decreasing_by exact Nat.mod_lt a (Nat.pos_of_ne_zero h)

def cfExpansions (n r : ℕ) : List (List ℕ) :=
  let l := euclidCF n r
  match l.reverse with
  | x :: rest => if 1 < x then [l, (1 :: (x - 1) :: rest).reverse] else [l]
  | [] => []

def a (n : ℕ) : ℕ :=
  ∑ r ∈ Finset.Icc 1 n,
    ((cfExpansions n r).filter (fun l => l.length % 2 = 1 ∧ l.reverse = l)).length

def f (k : ℕ) : ℕ :=
  match k with
  | 0 => 1
  | 1 => 2
  | k => 4 * (k - 1)

theorem main :
    ∀ n : ℕ, 1 ≤ n →
      a n = f (n.factorization 2) *
        ∏ p ∈ n.primeFactors.erase 2, (2 * n.factorization p + 1) := by
  sorry

end OMA.S_oeis_a092089
