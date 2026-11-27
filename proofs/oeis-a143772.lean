import OMAStatements.S_oeis_a143772
import Mathlib

namespace OMA.P_oeis_a143772

open OMA.S_oeis_a143772

theorem modeq_of_eq {a b n t : ℕ} (h : a = b + n * t) : a ≡ b [MOD n] := by
  subst h
  simp [Nat.ModEq, Nat.add_mul_mod_self_left]

theorem dvd_of_modeq {a b n d : ℕ} (h : a ≡ b [MOD n]) (hd : d ∣ n) (ha : d ∣ a) : d ∣ b :=
  Nat.modEq_zero_iff_dvd.mp ((h.of_dvd hd).symm.trans (Nat.modEq_zero_iff_dvd.mpr ha))

theorem coprime_of_modeq {a b n : ℕ} (h : a ≡ b [MOD n]) (hb : Nat.Coprime b n) :
    Nat.Coprime a n := by
  unfold Nat.Coprime
  rw [h.gcd_eq]
  exact hb

theorem divisors_pq {p q d : ℕ} (hp : p.Prime) (hq : q.Prime) (hd : d ∣ p * q) :
    d = 1 ∨ d = p ∨ d = q ∨ d = p * q := by
  obtain ⟨a, b, ha, hb, rfl⟩ := dvd_mul.mp hd
  rcases (Nat.dvd_prime hp).mp ha with rfl | rfl <;>
    rcases (Nat.dvd_prime hq).mp hb with rfl | rfl <;> simp

theorem value_pq (p q g M : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hM : p * (p + q) = (1 + p * q) + M) (hgM : g ∣ M) (hmod : p + q ≡ g [MOD M]) :
    value (p * q) = g := by
  have hpq0 : p * q ≠ 0 := Nat.mul_ne_zero hp.ne_zero hq.ne_zero
  apply Nat.dvd_antisymm
  · have h1 : value (p * q) ∣ 1 + p * q / 1 :=
      Finset.gcd_dvd (Nat.mem_divisors.mpr ⟨one_dvd _, hpq0⟩)
    have h2 : value (p * q) ∣ p + p * q / p :=
      Finset.gcd_dvd (Nat.mem_divisors.mpr ⟨dvd_mul_right p q, hpq0⟩)
    rw [Nat.div_one] at h1
    rw [Nat.mul_div_cancel_left q hp.pos] at h2
    have h3 : value (p * q) ∣ M := by
      have : value (p * q) ∣ p * (p + q) := dvd_mul_of_dvd_right h2 p
      rw [hM] at this
      exact (Nat.dvd_add_right h1).mp this
    exact dvd_of_modeq hmod h3 h2
  · apply Finset.dvd_gcd
    intro d hd
    have hgB : g ∣ p + q := dvd_of_modeq hmod.symm hgM dvd_rfl
    have hgA : g ∣ 1 + p * q := by
      have : g ∣ (1 + p * q) + M := hM ▸ dvd_mul_of_dvd_right hgB p
      exact (Nat.dvd_add_left hgM).mp this
    rcases divisors_pq hp hq (Nat.dvd_of_mem_divisors hd) with rfl | rfl | rfl | rfl
    · simpa using hgA
    · rwa [Nat.mul_div_cancel_left q hp.pos]
    · rw [Nat.mul_div_cancel p hq.pos, add_comm]; exact hgB
    · rw [Nat.div_self (Nat.pos_of_ne_zero hpq0), add_comm]; exact hgA

theorem even_case (k : ℕ) : ∃ m, 1 < m ∧ ¬ m.Prime ∧ value m = 2 * k + 2 := by
  have cop1 : Nat.Coprime (1 + (k + 1) * (2 * k + 2) * (2 * k + 3)) (2 * k + 2) :=
    coprime_of_modeq (modeq_of_eq (t := (k + 1) * (2 * k + 3)) (by ring)) (Nat.coprime_one_left _)
  have cop2 : Nat.Coprime (1 + (k + 1) * (2 * k + 2) * (2 * k + 3)) (2 * k + 3) :=
    coprime_of_modeq (modeq_of_eq (t := (k + 1) * (2 * k + 2)) (by ring)) (Nat.coprime_one_left _)
  have two3 : Nat.Coprime 2 (2 * k + 3) := Nat.coprime_two_left.mpr ⟨k + 1, by ring⟩
  have two1 : Nat.Coprime 2 (2 * k + 1) := Nat.coprime_two_left.mpr ⟨k, by ring⟩
  have cop3 : Nat.Coprime (1 + (k + 1) * (2 * k + 2) * (2 * k + 3)) (2 * k + 1) :=
    coprime_of_modeq (b := 2)
      (modeq_of_eq (t := 2 * (k + 1) ^ 2 + 2 * (k + 1) + 1) (by ring)) two1
  have hcL := Nat.Coprime.mul_right (Nat.Coprime.mul_right cop1 cop2) cop3
  obtain ⟨p, -, hp, hpc⟩ := Nat.forall_exists_prime_gt_and_modEq 0 (by positivity) hcL
  have e1 : p ≡ 1 [MOD 2 * k + 2] :=
    ((hpc.of_mul_right _).of_mul_right _).trans
      (modeq_of_eq (t := (k + 1) * (2 * k + 3)) (by ring))
  have e2 : p ≡ 1 [MOD 2 * k + 3] :=
    ((hpc.of_mul_right _).of_mul_left _).trans
      (modeq_of_eq (t := (k + 1) * (2 * k + 2)) (by ring))
  have e3 : p ≡ 2 [MOD 2 * k + 1] :=
    (hpc.of_mul_left _).trans
      (modeq_of_eq (t := 2 * (k + 1) ^ 2 + 2 * (k + 1) + 1) (by ring))
  obtain ⟨s, rfl⟩ : ∃ s, p = s + 2 := ⟨p - 2, by have := hp.two_le; omega⟩
  have hg : 2 * k + 2 ∣ s + 1 := by
    apply Nat.modEq_zero_iff_dvd.mp
    exact Nat.ModEq.add_right_cancel' 1 e1
  have hc1 : Nat.Coprime (2 * k + 1) (s + 1) := by
    have : s + 1 ≡ 1 [MOD 2 * k + 1] := Nat.ModEq.add_right_cancel' 1 e3
    exact (coprime_of_modeq this (Nat.coprime_one_left _)).symm
  have hc2 : Nat.Coprime (2 * k + 3) (s + 3) := by
    have : s + 3 ≡ 2 [MOD 2 * k + 3] := Nat.ModEq.add_right 1 e2
    exact (coprime_of_modeq this two3).symm
  have hr1 : Nat.Coprime ((2 * k + 1) + (s + 1) * (s + 2)) (s + 1) :=
    coprime_of_modeq (modeq_of_eq rfl) hc1
  have hr2 : Nat.Coprime ((2 * k + 1) + (s + 1) * (s + 2)) (s + 3) :=
    coprime_of_modeq (b := 2 * k + 3) (modeq_of_eq (t := s) (by ring)) hc2
  have hrM := Nat.Coprime.mul_right hr1 hr2
  obtain ⟨q, hqgt, hq, hqr⟩ := Nat.forall_exists_prime_gt_and_modEq (s + 2) (by positivity) hrM
  refine ⟨(s + 2) * q, ?_, Nat.not_prime_mul (by omega) hq.ne_one, ?_⟩
  · have := hq.two_le
    nlinarith
  · apply value_pq (s + 2) q (2 * k + 2) ((s + 1) * (s + 3)) hp hq (by ring)
      (Dvd.dvd.mul_right hg _)
    exact (Nat.ModEq.add_left (s + 2) hqr).trans (modeq_of_eq (t := 1) (by ring))

theorem val4 : value 4 = 1 := by decide

theorem val8 : value 8 = 3 := by decide

end OMA.P_oeis_a143772

theorem OMA.solution : type_of% @OMA.S_oeis_a143772.main := by
  intro g hg
  constructor
  · rintro ⟨m, hm1, -, hv⟩
    by_cases he : Even g
    · exact Or.inl he
    right
    have hm0 : m ≠ 0 := by omega
    have hme : Even m := by
      by_contra hmo
      rw [Nat.not_even_iff_odd] at hmo
      apply he
      rw [← hv, even_iff_two_dvd]
      apply Finset.dvd_gcd
      intro d hd
      have hdm := Nat.dvd_of_mem_divisors hd
      have hd_odd : Odd d := Odd.of_dvd_nat hmo hdm
      have hq_odd : Odd (m / d) := Odd.of_dvd_nat hmo (Nat.div_dvd_of_dvd hdm)
      exact (hd_odd.add_odd hq_odd).two_dvd
    have h1 : g ∣ 1 + m / 1 := hv ▸ Finset.gcd_dvd (Nat.mem_divisors.mpr ⟨one_dvd _, hm0⟩)
    have h2 : g ∣ 2 + m / 2 :=
      hv ▸ Finset.gcd_dvd (Nat.mem_divisors.mpr ⟨even_iff_two_dvd.mp hme, hm0⟩)
    obtain ⟨t, rfl⟩ := hme
    have e1 : (t + t) / 1 = t + t := Nat.div_one _
    have e2 : (t + t) / 2 = t := by omega
    rw [e1] at h1
    rw [e2] at h2
    have h3 : g ∣ 3 := by
      have : g ∣ 2 * (2 + t) := dvd_mul_of_dvd_right h2 2
      rw [show 2 * (2 + t) = 3 + (1 + (t + t)) by ring] at this
      exact (Nat.dvd_add_left h1).mp this
    have : g ≤ 3 := Nat.le_of_dvd (by norm_num) h3
    interval_cases g
    · exact Or.inl rfl
    · exact absurd even_two he
    · exact Or.inr rfl
  · rintro (he | rfl | rfl)
    · obtain ⟨h, rfl⟩ := he
      obtain ⟨k, rfl⟩ : ∃ k, h = k + 1 := ⟨h - 1, by omega⟩
      rw [show k + 1 + (k + 1) = 2 * k + 2 by ring]
      exact OMA.P_oeis_a143772.even_case k
    · exact ⟨4, by norm_num, by norm_num, OMA.P_oeis_a143772.val4⟩
    · exact ⟨8, by norm_num, by norm_num, OMA.P_oeis_a143772.val8⟩
