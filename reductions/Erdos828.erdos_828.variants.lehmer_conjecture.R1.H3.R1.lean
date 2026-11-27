import OMAReductions.R_Erdos828_erdos_828_variants_lehmer_conjecture_R1

-- Reduction Erdos828.erdos_828.variants.lehmer_conjecture.R1.H3.R1
-- of step Erdos828.erdos_828.variants.lehmer_conjecture.R1.H3
-- Credit: @marcusbuffett

/-!
# Lehmer's totient problem: at most six prime factors (Lehmer 1932), and the open rest

The parent step says that no squarefree `n` with at least three prime factors has
`φ(n) ∣ n - 1`.

* `H1` (Lehmer, On Euler's totient function, Bull. Amer. Math. Soc. 38 (1932)): no such `n` has
  at most six prime factors. With `k = (n - 1) / φ(n) ≥ 2` one has `k * ∏ (p - 1) < ∏ p` over the
  primes dividing `n`. If `3 ∣ n` then `k ≡ 1 (mod 3)`, so `k ≥ 4`, which six odd primes cannot
  reach; if `3 ∤ n` the primes are coprime to `6` and
  `(5/4)(7/6)(11/10)(13/12)(17/16)(19/18) < 2`.
* `H2`: seven or more prime factors. This is the open problem and stays open (Cohen and Hagis
  1980 show at least fourteen).
-/

namespace OMA.R_Erdos828_erdos_828_variants_lehmer_conjecture_R1_H3_R1

/-- Three to six prime factors. -/
def H1 : Prop :=
  ∀ n : ℕ, 1 < n → Squarefree n → 3 ≤ n.primeFactors.card → n.primeFactors.card ≤ 6 →
    ¬ n.totient ∣ n - 1

/-- The open part: seven or more prime factors. -/
def H2 : Prop :=
  ∀ n : ℕ, 1 < n → Squarefree n → 7 ≤ n.primeFactors.card → ¬ n.totient ∣ n - 1

theorem main : H1 → H2 → OMA.R_Erdos828_erdos_828_variants_lehmer_conjecture_R1.H3 := by
  intro h1 h2 n hn hsq hc
  by_cases h6 : n.primeFactors.card ≤ 6
  · exact h1 n hn hsq hc h6
  · exact h2 n hn hsq (by omega)

end OMA.R_Erdos828_erdos_828_variants_lehmer_conjecture_R1_H3_R1
