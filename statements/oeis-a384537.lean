import Mathlib

/-!
# Uniqueness of the base of a composite Davis number

Source: https://oeis.org/A384537 (OEIS Foundation, CC BY-SA 4.0).
Use the increasing prime factors of the canonical factorization and place
an exponent immediately after its prime only when the exponent exceeds one.
Every token is written in the same base as the composite number.
-/

namespace OMA.S_oeis_a384537

def factorTokens (n : ℕ) : List ℕ :=
  (n.primeFactors.sort (· ≤ ·)).flatMap fun p =>
    let e := n.factorization p
    if 1 < e then [p, e] else [p]

def concatenate (b : ℕ) (tokens : List ℕ) : ℕ :=
  tokens.foldl (fun acc token => acc * b ^ (Nat.digits b token).length + token) 0

def IsDavisIn (n b : ℕ) : Prop :=
  2 ≤ b ∧ 1 < n ∧ ¬ n.Prime ∧ concatenate b (factorTokens n) = n

theorem main : ∀ n b c : ℕ, IsDavisIn n b → IsDavisIn n c → b = c := by
  sorry

end OMA.S_oeis_a384537
