import OMAReductions.R_OeisA69004_conjecture2_variants_without_upper_bound_R1
import Mathlib

/-!
For positive s<n a prime of the form n²+s² has opposite parity and
coprime coordinates. After enforcing those two conditions, only
primes congruent to one modulo four need to be tested as divisors.
-/

open Finset

namespace OMA.SumSquarePrimeSieve

private theorem odd_sum_squares {n s : ℕ} :
    (n^2+s^2)%2 ≠ 0 ↔ n%2 ≠ s%2 := by
  rw [Nat.add_mod (n^2) (s^2) 2,Nat.pow_mod n 2 2,Nat.pow_mod s 2 2]
  have hn := Nat.mod_lt n (by decide : 0 < 2)
  have hs := Nat.mod_lt s (by decide : 0 < 2)
  interval_cases (n%2) <;> interval_cases (s%2) <;> decide

private theorem prime_sieve {n s : ℕ} (hs : 0 < s) (hns : s < n) :
    (n^2+s^2).Prime ↔ n%2 ≠ s%2 ∧ n.Coprime s ∧
      ∀ p ∈ range ((n^2+s^2).sqrt+1), p.Prime → p%4 = 1 → ¬ p ∣ n^2+s^2 := by
  let N := n^2+s^2
  have hn2 : 2 ≤ n := by omega
  have hN : 2 < N := by dsimp [N]; nlinarith
  have hSmall : n < N := by dsimp [N]; nlinarith
  constructor
  · intro h
    have hNPrime : N.Prime := h
    have hNe : ¬ 2 ∣ N := by
      intro hd
      rcases hNPrime.eq_one_or_self_of_dvd 2 hd with hh|hh <;> omega
    refine ⟨odd_sum_squares.mp (fun hn => hNe (Nat.dvd_of_mod_eq_zero hn)),?_,?_⟩
    · by_contra hNo
      obtain ⟨p,hp,hg⟩ := Nat.exists_prime_and_dvd (show n.gcd s ≠ 1 from hNo)
      have hpn := hg.trans (Nat.gcd_dvd_left n s)
      have hps := hg.trans (Nat.gcd_dvd_right n s)
      have hpN : p ∣ N := Nat.dvd_add (dvd_pow hpn (by decide)) (dvd_pow hps (by decide))
      have hpSmall := Nat.le_of_dvd (by omega : 0 < n) hpn
      rcases hNPrime.eq_one_or_self_of_dvd p hpN with hh|hh
      · exact hp.ne_one hh
      · omega
    · intro p hpRange hp _ hDiv
      have hLt : p < N := (Nat.le_of_lt_succ (mem_range.mp hpRange)).trans_lt
        (Nat.sqrt_lt_self (by omega : 1 < N))
      rcases hNPrime.eq_one_or_self_of_dvd p hDiv with h1|hEq
      · exact hp.ne_one h1
      · omega
  · rintro ⟨hParity,hCoprime,hTest⟩
    by_contra hNo
    have hComposite : ¬ N.Prime := hNo
    let p := N.minFac
    have hp : p.Prime := Nat.minFac_prime (by omega : N ≠ 1)
    have hd : p ∣ N := Nat.minFac_dvd _
    have hpsq : p^2 ≤ N := Nat.minFac_sq_le_self (by omega) hComposite
    have hpRange : p ∈ range (N.sqrt+1) :=
      mem_range.mpr (Nat.lt_succ_of_le (Nat.le_sqrt.mpr (by simpa [pow_two] using hpsq)))
    have hp2 : p ≠ 2 := by
      intro hh
      have hd2 : 2 ∣ N := hh ▸ hd
      exact (odd_sum_squares.mpr hParity) (Nat.mod_eq_zero_of_dvd hd2)
    have hOdd := (hp.eq_two_or_odd.resolve_left hp2)
    have hM : p ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hp,hd,by omega⟩
    have hSquare : IsSquare (-1 : ZMod N) :=
      ZMod.isSquare_neg_one_of_eq_sq_add_sq_of_coprime rfl hCoprime
    have hp3 := Nat.mod_four_ne_three_of_mem_primeFactors_of_isSquare_neg_one hM hSquare
    have hp1 : p%4 = 1 := by omega
    exact hTest p hpRange hp hp1 hd

open scoped Classical in
theorem exact_sieve_count (n : ℕ) :
    OeisA69004.a n = ((Ico 1 n).filter (fun s =>
      n%2 ≠ s%2 ∧ n.Coprime s ∧
      ∀ p ∈ range ((n^2+s^2).sqrt+1), p.Prime → p%4 = 1 → ¬ p ∣ n^2+s^2)).card := by
  rw [OeisA69004.a,card_filter]
  apply sum_congr rfl
  intro s hs
  obtain ⟨hs1,hsn⟩ := mem_Ico.mp hs
  have hh := prime_sieve (by omega) hsn
  by_cases h : (n^2+s^2).Prime
  · rw [if_pos h,if_pos (hh.mp h)]
  · rw [if_neg h,if_neg (mt hh.mpr h)]

end OMA.SumSquarePrimeSieve

theorem OMA.solution : OMA.R_OeisA69004_conjecture2_variants_without_upper_bound_R1.H2 :=
  OMA.SumSquarePrimeSieve.exact_sieve_count
