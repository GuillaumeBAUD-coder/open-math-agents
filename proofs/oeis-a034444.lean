import OMAStatements.S_oeis_a034444
import Mathlib
open OMA.S_oeis_a034444

namespace OMA.P_oeis_a034444

theorem mem_unitary' {n d : ℕ} (hn : 0 < n) :
    d ∈ OMA.S_oeis_a034444.unitary n ↔ ∃ c, n = d * c ∧ Nat.Coprime d c := by
  unfold OMA.S_oeis_a034444.unitary
  rw [Finset.mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hd, -⟩, hc⟩
    exact ⟨n / d, (Nat.mul_div_cancel' hd).symm, hc⟩
  · rintro ⟨c, rfl, hc⟩
    have hd : 0 < d := Nat.pos_of_mul_pos_right hn
    refine ⟨⟨dvd_mul_right d c, hn.ne'⟩, ?_⟩
    rwa [Nat.mul_div_cancel_left c hd]

theorem odd_struct {e m d : ℕ} (hm : Odd m) (he : 0 < e) (hd : d ∈ OMA.S_oeis_a034444.unitary (2 ^ e * m))
    (hodd : Odd d) : d * 2 ^ e ∈ OMA.S_oeis_a034444.unitary (2 ^ e * m) ∧ ¬ Odd (d * 2 ^ e) := by
  have hn : 0 < 2 ^ e * m := Nat.mul_pos (by positivity) hm.pos
  obtain ⟨c, hc, hdc⟩ := (mem_unitary' hn).1 hd
  have hd2 : Nat.Coprime d (2 ^ e) := Nat.Coprime.pow_right e (Nat.coprime_two_right.2 hodd)
  have hdm : d ∣ m := hd2.dvd_of_dvd_mul_left ⟨c, hc⟩
  obtain ⟨c', rfl⟩ := hdm
  have hdpos : 0 < d := hodd.pos
  have hcc : c = 2 ^ e * c' := by
    apply Nat.eq_of_mul_eq_mul_left hdpos
    rw [← hc]; ring
  subst hcc
  have hc'odd : Odd c' := Nat.Odd.of_mul_right hm
  have h1 : Nat.Coprime d c' := Nat.Coprime.coprime_dvd_right (dvd_mul_left c' _) hdc
  have h2 : Nat.Coprime (2 ^ e) c' := Nat.Coprime.pow_left e (Nat.coprime_two_left.2 hc'odd)
  refine ⟨(mem_unitary' hn).2 ⟨c', by ring, Nat.Coprime.mul_left h1 h2⟩, ?_⟩
  rw [Nat.not_odd_iff_even, Nat.even_mul]
  right
  exact (Nat.even_pow' he.ne').2 even_two

theorem even_struct {e m d : ℕ} (hm : Odd m) (hd : d ∈ OMA.S_oeis_a034444.unitary (2 ^ e * m))
    (hev : ¬ Odd d) : ∃ d', d = d' * 2 ^ e ∧ d' ∈ OMA.S_oeis_a034444.unitary (2 ^ e * m) ∧ Odd d' := by
  have hn : 0 < 2 ^ e * m := Nat.mul_pos (by positivity) hm.pos
  obtain ⟨c, hc, hdc⟩ := (mem_unitary' hn).1 hd
  have h2d : 2 ∣ d := even_iff_two_dvd.1 (Nat.not_odd_iff_even.1 hev)
  have h2c : Nat.Coprime 2 c := Nat.Coprime.coprime_dvd_left h2d hdc
  have hec : Nat.Coprime (2 ^ e) c := Nat.Coprime.pow_left e h2c
  have hed : 2 ^ e ∣ d := hec.dvd_of_dvd_mul_right ⟨m, hc.symm⟩
  obtain ⟨d', rfl⟩ := hed
  have hm' : m = d' * c := by
    apply Nat.eq_of_mul_eq_mul_left (show 0 < 2 ^ e by positivity)
    rw [hc]; ring
  subst hm'
  have hd'odd : Odd d' := Nat.Odd.of_mul_left hm
  have hcodd : Odd c := Nat.Odd.of_mul_right hm
  have h1 : Nat.Coprime d' (2 ^ e) := Nat.Coprime.pow_right e (Nat.coprime_two_right.2 hd'odd)
  have h3 : Nat.Coprime d' c := Nat.Coprime.coprime_dvd_left (dvd_mul_left d' _) hdc
  refine ⟨d', by ring, (mem_unitary' hn).2 ⟨2 ^ e * c, by ring, Nat.Coprime.mul_right h1 h3⟩, hd'odd⟩

end OMA.P_oeis_a034444

open OMA.P_oeis_a034444 in
theorem OMA.solution : type_of% @OMA.S_oeis_a034444.main := by
  intro n hn k
  obtain ⟨e, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hn.ne'
  rcases Nat.eq_zero_or_pos e with he | he
  · subst he
    rw [Finset.filter_true_of_mem]
    intro d hd
    have hn' : 0 < 2 ^ 0 * m := hn
    obtain ⟨c, hc, -⟩ := (mem_unitary' hn').1 hd
    exact Nat.Odd.of_mul_left (by rw [← hc]; simpa using hm)
  · rw [← Finset.sum_filter_add_sum_filter_not (OMA.S_oeis_a034444.unitary (2 ^ e * m)) Odd]
    have key : ∑ d ∈ (OMA.S_oeis_a034444.unitary (2 ^ e * m)).filter (fun d => ¬ Odd d), d ^ k
        = ∑ d ∈ (OMA.S_oeis_a034444.unitary (2 ^ e * m)).filter Odd, (d * 2 ^ e) ^ k := by
      apply Finset.sum_nbij' (fun d => d / 2 ^ e) (fun d => d * 2 ^ e)
      · intro d hd
        rw [Finset.mem_filter] at hd
        obtain ⟨d', rfl, h1, h2⟩ := even_struct hm hd.1 hd.2
        rw [Finset.mem_filter, Nat.mul_div_cancel _ (by positivity)]
        exact ⟨h1, h2⟩
      · intro d hd
        rw [Finset.mem_filter] at hd
        rw [Finset.mem_filter]
        exact odd_struct hm he hd.1 hd.2
      · intro d hd
        rw [Finset.mem_filter] at hd
        obtain ⟨d', rfl, h1, h2⟩ := even_struct hm hd.1 hd.2
        rw [Nat.mul_div_cancel _ (by positivity)]
      · intro d hd
        rw [Nat.mul_div_cancel _ (by positivity)]
      · intro d hd
        rw [Finset.mem_filter] at hd
        obtain ⟨d', rfl, h1, h2⟩ := even_struct hm hd.1 hd.2
        rw [Nat.mul_div_cancel _ (by positivity)]
    rw [key]
    simp only [mul_pow, ← Finset.sum_mul]
    exact dvd_add dvd_rfl (dvd_mul_right _ _)
