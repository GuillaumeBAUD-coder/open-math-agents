import OMAStatements.S_oeis_a369871
import Mathlib

namespace A369871
open OMA.S_oeis_a369871

lemma cop_of_eq (m b x y : ℕ) (h : x * m = y * b + 1) : Nat.Coprime m b := by
  have hd : Nat.gcd m b ∣ 1 := by
    have h1 : Nat.gcd m b ∣ x * m := Dvd.dvd.mul_left (Nat.gcd_dvd_left m b) x
    have h2 : Nat.gcd m b ∣ y * b := Dvd.dvd.mul_left (Nat.gcd_dvd_right m b) y
    rw [h] at h1
    exact (Nat.dvd_add_right h2).mp h1
  exact Nat.eq_one_of_dvd_one hd

lemma msl_odd (p q : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hq : q.Prime) (hpq : 3 * p < q) :
    MultiShortLeg (p * q) := by
  have hpodd : p % 2 = 1 := (hp.eq_two_or_odd).resolve_left hp2
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hqodd : q % 2 = 1 := (hq.eq_two_or_odd).resolve_left (by omega)
  obtain ⟨d, rfl⟩ : ∃ d, q = p + 2 * d := ⟨(q - p) / 2, by omega⟩
  have hd : p < d := by omega
  have hmodd : (p * (p + 2 * d)) % 2 = 1 := by
    have h2 : (p + 2 * d) % 2 = 1 := by omega
    rw [Nat.mul_mod, hpodd, h2]
  obtain ⟨k, hk⟩ : ∃ k, p * (p + 2 * d) = 2 * k + 1 := ⟨(p * (p + 2 * d)) / 2, by omega⟩
  have hk1 : 1 ≤ k := by
    have h9 : 3 * 3 ≤ p * (p + 2 * d) := Nat.mul_le_mul hp3 (by omega)
    omega
  have hk2 : 1 * k ≤ k * k := Nat.mul_le_mul_right k hk1
  refine ⟨2 * k ^ 2 + 2 * k, 2 * k ^ 2 + 2 * k + 1, 2 * d * (p + d),
    p ^ 2 + 2 * p * d + 2 * d ^ 2, ?_, ?_, ?_⟩
  · unfold IsPPT
    rw [hk]
    refine ⟨by omega, ?_, by ring, ?_⟩
    · nlinarith [hk2]
    · exact cop_of_eq _ _ (2 * k + 1) 2 (by ring)
  · unfold IsPPT
    refine ⟨Nat.mul_pos (by omega) (by omega), ?_, by ring, ?_⟩
    · have h1 : p * p < d * d := Nat.mul_self_lt_mul_self hd
      nlinarith [h1, Nat.zero_le (d * d)]
    · apply Nat.Coprime.mul_left
      · rw [Nat.Prime.coprime_iff_not_dvd hp]
        intro hdv
        have hpd : ¬ p ∣ d := by
          intro h
          have h' : p ∣ p + 2 * d := Dvd.dvd.add (dvd_refl p) (Dvd.dvd.mul_left h 2)
          have := (Nat.prime_dvd_prime_iff_eq hp hq).mp h'
          omega
        rcases (Nat.Prime.dvd_mul hp).mp hdv with h | h
        · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
          · have := Nat.le_of_dvd (by norm_num) h
            omega
          · exact hpd h
        · exact hpd ((Nat.dvd_add_right (dvd_refl p)).mp h)
      · rw [Nat.Prime.coprime_iff_not_dvd hq]
        intro hdv
        rcases (Nat.Prime.dvd_mul hq).mp hdv with h | h
        · rcases (Nat.Prime.dvd_mul hq).mp h with h | h
          · have := Nat.le_of_dvd (by norm_num) h
            omega
          · have := Nat.le_of_dvd (by omega) h
            omega
        · have := Nat.le_of_dvd (by omega) h
          omega
  · intro hb
    have h1 : (p * (p + 2 * d)) ^ 2 = 2 * (2 * k ^ 2 + 2 * k) + 1 := by
      rw [hk]
      ring
    rw [hb] at h1
    have h2 : p ^ 2 * ((p + 2 * d) ^ 2 + 1) = (p + 2 * d) ^ 2 + 1 := by
      nlinarith [h1]
    have h3 : 9 ≤ p ^ 2 := by nlinarith [hp3]
    have h4 := Nat.mul_le_mul_right ((p + 2 * d) ^ 2 + 1) h3
    rw [h2] at h4
    generalize (p + 2 * d) ^ 2 = Q at h4
    omega

lemma msl_two (q : ℕ) (hq : q.Prime) (hq5 : 5 ≤ q) : MultiShortLeg (4 * q) := by
  have hqodd : q % 2 = 1 := (hq.eq_two_or_odd).resolve_left (by omega)
  have hqq : 5 * q ≤ q * q := Nat.mul_le_mul_right q hq5
  have hsqodd : (q * q) % 2 = 1 := by
    rw [Nat.mul_mod, hqodd]
  obtain ⟨w, hw⟩ : ∃ w, 4 * (q * q) = w + 1 := ⟨4 * (q * q) - 1, by omega⟩
  obtain ⟨v, hv⟩ : ∃ v, q * q = v + 4 := ⟨q * q - 4, by omega⟩
  refine ⟨w, w + 2, v, v + 8, ?_, ?_, ?_⟩
  · unfold IsPPT
    refine ⟨by omega, by omega, ?_, ?_⟩
    · have e : (4 * q) ^ 2 = 4 * (w + 1) := by
        rw [← hw]
        ring
      rw [e]
      ring
    · exact cop_of_eq _ _ q 1 (by rw [one_mul, ← hw]; ring)
  · unfold IsPPT
    refine ⟨by omega, by omega, ?_, ?_⟩
    · have e : (4 * q) ^ 2 = 16 * (v + 4) := by
        rw [← hv]
        ring
      rw [e]
      ring
    · apply Nat.Coprime.mul_left
      · have hvodd : v % 2 = 1 := by omega
        have h2 : Nat.Coprime (2 ^ 2) v :=
          Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr (Nat.odd_iff.mpr hvodd))
        exact h2
      · rw [Nat.Prime.coprime_iff_not_dvd hq]
        intro h
        have h' : q ∣ v + 4 := by
          rw [← hv]
          exact Dvd.intro q rfl
        have h4 : q ∣ 4 := (Nat.dvd_add_right h).mp h'
        have := Nat.le_of_dvd (by norm_num) h4
        omega
  · omega

lemma minFac_mul (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p < q) :
    (p * q).minFac = p := by
  have h1 : (p * q).minFac ≤ p := Nat.minFac_le_of_dvd hp.two_le (Dvd.intro q rfl)
  have hne : p * q ≠ 1 := by
    have := Nat.mul_le_mul hp.two_le hq.two_le
    omega
  have h2 : ((p * q).minFac).Prime := Nat.minFac_prime hne
  have h3 : (p * q).minFac ∣ p * q := Nat.minFac_dvd (p * q)
  rcases (Nat.Prime.dvd_mul h2).mp h3 with h | h
  · exact (Nat.prime_dvd_prime_iff_eq h2 hp).mp h
  · have := (Nat.prime_dvd_prime_iff_eq h2 hq).mp h
    omega

lemma exists_family (p : ℕ) (hp : p.Prime) :
    ∃ g : ℕ → ℕ, Function.Injective g ∧
      ∀ q : ℕ, q.Prime → 3 * p < q → MultiShortLeg (g q) ∧ (g q).minFac = p := by
  by_cases h2 : p = 2
  · subst h2
    refine ⟨fun q => 4 * q, ?_, ?_⟩
    · intro x y hxy
      have h' : 4 * x = 4 * y := hxy
      omega
    · intro q hq hlt
      refine ⟨msl_two q hq (by omega), ?_⟩
      show (4 * q).minFac = 2
      rw [Nat.minFac_eq_two_iff]
      exact Dvd.intro (2 * q) (by ring)
  · refine ⟨fun q => p * q, ?_, ?_⟩
    · intro x y hxy
      have h' : p * x = p * y := hxy
      exact Nat.eq_of_mul_eq_mul_left hp.pos h'
    · intro q hq hlt
      exact ⟨msl_odd p q hp h2 hq hlt, minFac_mul p q hp hq (by omega)⟩

end A369871

theorem OMA.solution : type_of% @OMA.S_oeis_a369871.main := by
  intro p hp
  classical
  obtain ⟨g, hg_inj, hg⟩ := A369871.exists_family p hp
  have hS : {q : ℕ | q.Prime ∧ 3 * p < q}.Infinite := by
    apply Set.infinite_of_forall_exists_gt
    intro x
    obtain ⟨q, hq1, hq2⟩ := Nat.exists_infinite_primes (x + 3 * p + 1)
    exact ⟨q, ⟨hq2, by omega⟩, by omega⟩
  have hinj : Set.InjOn (fun q => Nat.count OMA.S_oeis_a369871.MultiShortLeg (g q) + 1)
      {q : ℕ | q.Prime ∧ 3 * p < q} := by
    intro q1 h1 q2 h2 h
    have hc : Nat.count OMA.S_oeis_a369871.MultiShortLeg (g q1) =
        Nat.count OMA.S_oeis_a369871.MultiShortLeg (g q2) := Nat.succ_injective h
    exact hg_inj (Nat.count_injective (hg q1 h1.1 h1.2).1 (hg q2 h2.1 h2.2).1 hc)
  apply Set.Infinite.mono _ (hS.image hinj)
  rintro n ⟨q, hq, rfl⟩
  refine ⟨Nat.succ_le_succ (Nat.zero_le _), ?_⟩
  show OMA.S_oeis_a369871.a (Nat.count OMA.S_oeis_a369871.MultiShortLeg (g q) + 1) = p
  unfold OMA.S_oeis_a369871.a
  rw [Nat.add_sub_cancel, Nat.nth_count (hg q hq.1 hq.2).1]
  exact (hg q hq.1 hq.2).2
