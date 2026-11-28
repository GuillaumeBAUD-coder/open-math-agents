import OMAStatements.S_oeis_a053624
import Mathlib
open OMA.S_oeis_a053624

theorem cardpp {p : ℕ} (hp : p.Prime) (k : ℕ) : (p ^ k).divisors.card = k + 1 := by
  rw [Nat.divisors_prime_pow hp]
  simp

theorem OMA.solution : type_of% @OMA.S_oeis_a053624.main := by
  intro n hT h1 h3 h9
  obtain ⟨hodd, hmin⟩ := hT
  have hn0 : n ≠ 0 := by rintro rfl; exact absurd hodd (by decide)
  by_cases h5 : 5 ∣ n
  · obtain ⟨k, hk⟩ := hodd
    omega
  exfalso
  by_cases hex : ∃ p, p.Prime ∧ p ∣ n ∧ p ≠ 3
  · obtain ⟨p, hp, hpn, hp3⟩ := hex
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hpn)
    have hp5 : p ≠ 5 := by rintro rfl; exact h5 hpn
    have hp7 : 7 ≤ p := by
      have := hp.two_le
      by_contra hlt
      interval_cases p <;> first | omega | norm_num at hp
    set e := n.factorization p with he
    set r := n / p ^ e with hr
    have hnr : p ^ e * r = n := Nat.ordProj_mul_ordCompl_eq_self n p
    have hcop : Nat.Coprime p r := Nat.coprime_ordCompl hp hn0
    have he1 : 1 ≤ e := (hp.dvd_iff_one_le_factorization hn0).mp hpn
    have hr0 : 0 < r := by
      rcases Nat.eq_zero_or_pos r with h | h
      · rw [h] at hnr; omega
      · exact h
    have hrn : r ∣ n := ⟨p ^ e, by rw [← hnr]; ring⟩
    have h5r : ¬ 5 ∣ r := fun h => h5 (dvd_trans h hrn)
    have hcop5 : Nat.Coprime 5 r := 
      (Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr h5r
    have hdn : n.divisors.card = (e + 1) * r.divisors.card := by
      rw [← hnr, Nat.Coprime.card_divisors_mul (Nat.Coprime.pow_left _ hcop), cardpp hp]
    have hd' : (5 ^ e * r).divisors.card = (e + 1) * r.divisors.card := by
      rw [Nat.Coprime.card_divisors_mul (Nat.Coprime.pow_left _ hcop5), cardpp (by norm_num)]
    have hrodd : Odd r := Odd.of_dvd_nat hodd hrn
    have hodd' : Odd (5 ^ e * r) := Odd.mul (Odd.pow (by decide)) hrodd
    have hlt' : 5 ^ e * r < n := by
      rw [← hnr]
      have : 5 ^ e < p ^ e := Nat.pow_lt_pow_left (by omega) (by omega)
      exact Nat.mul_lt_mul_of_pos_right this hr0
    have := hmin _ hodd' hlt'
    omega
  · push Not at hex
    obtain ⟨a, h3p⟩ : ∃ a, n = 3 ^ a :=
      ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd hn0 (fun {d} hd hdn => hex d hd hdn)⟩
    have ha : 3 ≤ a := by
      by_contra hlt
      interval_cases a <;> simp_all
    obtain ⟨b, rfl⟩ : ∃ b, a = b + 3 := ⟨a - 3, by omega⟩
    have hm := hmin (3 ^ (b + 1) * 5) (Odd.mul (Odd.pow (by decide)) (by decide)) (by
      rw [h3p, pow_add 3 (b+1) 2]; have : 0 < 3 ^ (b+1) := by positivity
      omega)
    rw [Nat.Coprime.card_divisors_mul (Nat.Coprime.pow_left _ (by norm_num)), cardpp (by norm_num),
      h3p, cardpp (by norm_num)] at hm
    have : (5 : ℕ).divisors.card = 2 := by decide
    rw [this] at hm
    omega
