import OMAStatements.S_oeis_a254074
import Mathlib

open OMA.S_oeis_a254074

theorem OMA.solution : type_of% @OMA.S_oeis_a254074.main := by
  intro n ht hdiv
  have hn_ne : n ≠ 0 := by
    intro hz
    simpa [hz] using ht.1.1
  have hnil : Nat.digits 10 n ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hn_ne
  have hheadmem : (Nat.digits 10 n).head! ∈ Nat.digits 10 n := List.head!_mem_self hnil
  have hlasteq : (Nat.digits 10 n).head! = n % 10 := Nat.head!_digits (by decide)
  have hlastmem : n % 10 ∈ Nat.digits 10 n := by
    rwa [hlasteq] at hheadmem
  have hbnd := ht.1.2.2 (n % 10) hlastmem
  have hnmod5 : n % 5 = 0 := Nat.mod_eq_zero_of_dvd hdiv
  have hcases : n % 10 = 0 ∨ n % 10 = 5 := by omega
  rcases hcases with h0 | h5
  · omega
  obtain ⟨q, hq⟩ : ∃ q : ℕ, n = 10 * q + 5 := ⟨n / 10, by omega⟩
  set t : ℕ := q * q + q
  have hsq : n ^ 2 = 100 * t + 25 := by
    rw [hq]
    ring
  have hm1 : n ^ 2 % 10 = 5 := by
    rw [hsq, show 100 * t + 25 = 25 + 10 * (10 * t) by ring,
      Nat.add_mul_mod_self_left]
  have hsqdiv : n ^ 2 / 10 = 10 * t + 2 := by
    rw [hsq, show 100 * t + 25 = 5 + 10 * (10 * t + 2) by ring,
      Nat.add_mul_div_left 5 (10 * t + 2) (by decide : 0 < 10)]
    norm_num
  have hm2 : (n ^ 2 / 10) % 10 = 2 := by
    rw [hsqdiv, show 10 * t + 2 = 2 + 10 * t by ring,
      Nat.add_mul_mod_self_left]
  have hsq_ne : n ^ 2 ≠ 0 := by rw [hsq]; omega
  have hdiv_ne : n ^ 2 / 10 ≠ 0 := by rw [hsqdiv]; omega
  have hd1 := Nat.digits_eq_cons_digits_div (b := 10) (n := n ^ 2) (by decide) hsq_ne
  have hd2 := Nat.digits_eq_cons_digits_div (b := 10) (n := n ^ 2 / 10) (by decide) hdiv_ne
  rw [hm1] at hd1
  rw [hm2] at hd2
  have h2mem : 2 ∈ Nat.digits 10 (n ^ 2) := by
    rw [hd1, hd2]
    simp
  have hbnd2 := ht.2.2.2 2 h2mem
  omega
