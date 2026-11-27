import OMAStatements.S_oeis_a121860
import Mathlib

namespace A121860aux

open OMA.S_oeis_a121860 in
lemma term_dvd (k n d e : ℕ) (hk0 : 0 < k) (hd : 2 ≤ d) (he : 2 ≤ e) (hn : d * e = n)
    (hk : 2 * k + 4 ≤ n) : k ∣ n.factorial / (d.factorial * e.factorial) := by
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 2 := ⟨d - 2, by omega⟩
  obtain ⟨e', rfl⟩ : ∃ e', e = e' + 2 := ⟨e - 2, by omega⟩
  have hexp : n = d' * e' + 2 * d' + 2 * e' + 4 := by
    rw [← hn]
    ring
  generalize d' * e' = P at hexp
  have hde : d' + 2 + (e' + 2) ≤ n := by omega
  have hk' : k ≤ n - (d' + 2) - (e' + 2) := by omega
  have h1 : n.choose (d' + 2) * (d' + 2).factorial * (n - (d' + 2)).factorial = n.factorial :=
    Nat.choose_mul_factorial_mul_factorial (by omega)
  have h2 : (n - (d' + 2)).choose (e' + 2) * (e' + 2).factorial
      * (n - (d' + 2) - (e' + 2)).factorial = (n - (d' + 2)).factorial :=
    Nat.choose_mul_factorial_mul_factorial (by omega)
  have h3 : n.factorial = (d' + 2).factorial * (e' + 2).factorial
      * (n.choose (d' + 2) * (n - (d' + 2)).choose (e' + 2)
        * (n - (d' + 2) - (e' + 2)).factorial) := by
    rw [← h1, ← h2]
    ring
  have hpos : 0 < (d' + 2).factorial * (e' + 2).factorial :=
    Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)
  rw [h3, Nat.mul_div_cancel_left _ hpos]
  exact Dvd.dvd.mul_left (Nat.dvd_factorial hk0 hk') _

end A121860aux

theorem OMA.solution : type_of% @OMA.S_oeis_a121860.main := by
  intro k hk
  refine ⟨2 * k + 4, fun n hn => ?_⟩
  unfold OMA.S_oeis_a121860.value
  have hn0 : n ≠ 0 := by omega
  have h1 : 1 ∈ n.divisors := Nat.one_mem_divisors.mpr hn0
  have hnn : n ∈ (n.divisors).erase 1 :=
    Finset.mem_erase.mpr ⟨by omega, Nat.mem_divisors_self n hn0⟩
  rw [← Finset.add_sum_erase _ _ h1, ← Finset.add_sum_erase _ _ hnn]
  have t1 : OMA.S_oeis_a121860.term n 1 = 1 := by
    unfold OMA.S_oeis_a121860.term
    rw [Nat.div_one, Nat.factorial_one, one_mul]
    exact Nat.div_self (Nat.factorial_pos n)
  have tn : OMA.S_oeis_a121860.term n n = 1 := by
    unfold OMA.S_oeis_a121860.term
    rw [Nat.div_self (by omega), Nat.factorial_one, mul_one]
    exact Nat.div_self (Nat.factorial_pos n)
  have hrest : k ∣ ∑ d ∈ ((n.divisors).erase 1).erase n, OMA.S_oeis_a121860.term n d := by
    apply Finset.dvd_sum
    intro d hd
    rw [Finset.mem_erase, Finset.mem_erase, Nat.mem_divisors] at hd
    obtain ⟨hdn, hd1, hdvd, -⟩ := hd
    unfold OMA.S_oeis_a121860.term
    obtain ⟨e, he⟩ := hdvd
    have hd0 : d ≠ 0 := by
      rintro rfl
      rw [zero_mul] at he
      exact hn0 he
    have hdiv : n / d = e := by
      rw [he]
      exact Nat.mul_div_cancel_left _ (by omega)
    rw [hdiv]
    have he2 : 2 ≤ e := by
      by_contra hlt
      have hcases : e = 0 ∨ e = 1 := by omega
      rcases hcases with rfl | rfl
      · rw [mul_zero] at he
        exact absurd he hn0
      · rw [mul_one] at he
        exact absurd he.symm hdn
    exact A121860aux.term_dvd k n d e (by omega) (by omega) he2 he.symm hn
  rw [t1, tn]
  obtain ⟨c, hc⟩ := hrest
  rw [hc, show 1 + (1 + k * c) = 2 + k * c by ring, Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt (by omega)
