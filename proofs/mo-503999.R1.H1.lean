import OMAReductions.R_mo_503999_R1

/-!
# Proof of `mo-503999.R1.H1`

Proves that if `p_i * p_{i+1} * p_{i+2}` is a decimal palindrome divisible by `11`, then it
equals `1001`.

Since `11` is prime and divides the product of three consecutive primes, one of them equals
`11 = Nat.nth Nat.Prime 4`, forcing `i ∈ {2, 3, 4}`. Checking the three cases:
- `i = 2`: `5 * 7 * 11 = 385` is not a palindrome;
- `i = 3`: `7 * 11 * 13 = 1001`;
- `i = 4`: `11 * 13 * 17 = 2431` is not a palindrome.
-/

namespace Mo503999R1H1Proof

private lemma count_prime_eq (n c : ℕ) (h : ((Finset.range n).filter Nat.Prime).card = c) :
    Nat.count Nat.Prime n = c := by
  rw [Nat.count_eq_card_filter_range, h]

private lemma nth_prime_eq {k p : ℕ} (hp : p.Prime)
    (hc : ((Finset.range p).filter Nat.Prime).card = k) :
    Nat.nth Nat.Prime k = p := by
  have h1 : Nat.count Nat.Prime p = k := count_prime_eq p k hc
  rw [← h1]
  exact Nat.nth_count hp

private lemma nth_prime_2 : Nat.nth Nat.Prime 2 = 5 :=
  nth_prime_eq (by decide) (by decide)

private lemma nth_prime_3 : Nat.nth Nat.Prime 3 = 7 :=
  nth_prime_eq (by decide) (by decide)

private lemma nth_prime_4 : Nat.nth Nat.Prime 4 = 11 :=
  nth_prime_eq (by decide) (by decide)

private lemma nth_prime_5 : Nat.nth Nat.Prime 5 = 13 :=
  nth_prime_eq (by decide) (by decide)

private lemma nth_prime_6 : Nat.nth Nat.Prime 6 = 17 :=
  nth_prime_eq (by decide) (by decide)

end Mo503999R1H1Proof

theorem OMA.solution : OMA.R_mo_503999_R1.H1 := by
  intro i hpal h11
  have hinf : {n : ℕ | n.Prime}.Infinite := Nat.infinite_setOfPred_prime
  have hp0 : (Nat.nth Nat.Prime i).Prime := Nat.nth_mem_of_infinite hinf i
  have hp1 : (Nat.nth Nat.Prime (i + 1)).Prime := Nat.nth_mem_of_infinite hinf (i + 1)
  have hp2 : (Nat.nth Nat.Prime (i + 2)).Prime := Nat.nth_mem_of_infinite hinf (i + 2)
  have h11p : Nat.Prime 11 := by decide
  have hinj : Function.Injective (Nat.nth Nat.Prime) := (Nat.nth_strictMono hinf).injective
  have hcases : i = 2 ∨ i = 3 ∨ i = 4 := by
    rcases h11p.dvd_mul.mp h11 with h01 | h2
    · rcases h11p.dvd_mul.mp h01 with h0 | h1
      · have heq : 11 = Nat.nth Nat.Prime i := (Nat.prime_dvd_prime_iff_eq h11p hp0).mp h0
        have hi : i = 4 := hinj (heq.symm.trans Mo503999R1H1Proof.nth_prime_4.symm)
        exact Or.inr (Or.inr hi)
      · have heq : 11 = Nat.nth Nat.Prime (i + 1) := (Nat.prime_dvd_prime_iff_eq h11p hp1).mp h1
        have hi : i + 1 = 4 := hinj (heq.symm.trans Mo503999R1H1Proof.nth_prime_4.symm)
        exact Or.inr (Or.inl (by omega))
    · have heq : 11 = Nat.nth Nat.Prime (i + 2) := (Nat.prime_dvd_prime_iff_eq h11p hp2).mp h2
      have hi : i + 2 = 4 := hinj (heq.symm.trans Mo503999R1H1Proof.nth_prime_4.symm)
      exact Or.inl (by omega)
  rcases hcases with rfl | rfl | rfl
  · rw [Mo503999R1H1Proof.nth_prime_2, Mo503999R1H1Proof.nth_prime_3,
      Mo503999R1H1Proof.nth_prime_4] at hpal
    unfold OMA.S_mo_503999.IsPalindrome at hpal
    revert hpal; decide
  · rw [Mo503999R1H1Proof.nth_prime_3, Mo503999R1H1Proof.nth_prime_4,
      Mo503999R1H1Proof.nth_prime_5]
  · rw [Mo503999R1H1Proof.nth_prime_4, Mo503999R1H1Proof.nth_prime_5,
      Mo503999R1H1Proof.nth_prime_6] at hpal
    unfold OMA.S_mo_503999.IsPalindrome at hpal
    revert hpal; decide
