import OMAStatements.S_oeis_a178984

/-!
# Goldbach representations at successors of primes

At every published one-based index n≥3, the nth prime is odd and
greater than 2. A Goldbach decomposition of its successor supplies at
least one candidate. The minimum is attained because the candidates
are natural numbers. The intermediate equivalence also identifies
exactly what is needed at each individual index.

Source: https://oeis.org/A178984. Credit: @Solitude1312
-/

open OMA.S_oeis_a178984

namespace OMA.A178984

lemma local_criterion (n : ℕ) : IsLeast (candidates n) (a n) ↔
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = primeAt n + 1 := by
  constructor
  · intro h
    obtain ⟨hp, hq⟩ := h.1
    have hpos := hq.pos
    exact ⟨a n, primeAt n + 1 - a n, hp, hq, by omega⟩
  · rintro ⟨p, q, hp, hq, hsum⟩
    have hmem : p ∈ candidates n := ⟨hp, by rwa [show primeAt n + 1 - p = q by omega]⟩
    exact ⟨Nat.sInf_mem ⟨p, hmem⟩, fun _ hm => Nat.sInf_le hm⟩

lemma existence (H : binaryGoldbach) (n : ℕ) (hn : 3 ≤ n) : IsLeast (candidates n) (a n) := by
  have hprime : (primeAt n).Prime := Nat.prime_nth_prime _
  have hbound : n - 1 + 2 ≤ primeAt n := Nat.add_two_le_nth_prime _
  obtain ⟨k, hk⟩ := hprime.odd_of_ne_two (by omega)
  apply (local_criterion n).mpr
  exact H (primeAt n + 1) (by omega) ⟨k + 1, by omega⟩

end OMA.A178984

theorem OMA.solution : type_of% @OMA.S_oeis_a178984.main := by
  exact OMA.A178984.existence
