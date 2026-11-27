import OMAStatements.S_oeis_a058764
import Mathlib

namespace A058764
open OMA.S_oeis_a058764

lemma odd_key (m c : ℕ) (hm : m % 2 = 1) (h : 2 * m - Nat.totient m = 2 ^ c) :
    2 * m ≤ 3 * Nat.totient m := by
  by_cases h1 : m = 1
  · subst h1
    simp
  have hm2 : 3 ≤ m := by omega
  have hpp : (m.minFac).Prime := Nat.minFac_prime h1
  have hpm : m.minFac ∣ m := Nat.minFac_dvd m
  obtain ⟨e, m', hm', hmeq⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (by omega : m ≠ 0) m.minFac hpp.ne_one
  generalize m.minFac = p at hpp hpm hm' hmeq
  have hpodd : p % 2 = 1 := by
    rcases hpp.eq_two_or_odd with h2 | h2
    · rw [h2] at hpm
      omega
    · exact h2
  have hp3 : 3 ≤ p := by
    have := hpp.two_le
    omega
  obtain ⟨f, rfl⟩ : ∃ f, e = f + 1 := by
    rcases Nat.eq_zero_or_pos e with he | he
    · exfalso
      rw [he, pow_zero, one_mul] at hmeq
      rw [hmeq] at hpm
      exact hm' hpm
    · exact ⟨e - 1, by omega⟩
  have hcop : Nat.Coprime (p ^ (f + 1)) m' :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hpp).mpr hm')
  have htot : Nat.totient m = p ^ f * (p - 1) * Nat.totient m' := by
    rw [hmeq, Nat.totient_mul hcop, Nat.totient_prime_pow_succ hpp]
  obtain ⟨t, rfl⟩ : ∃ t, p = t + 3 := ⟨p - 3, by omega⟩
  have e1 : t + 3 - 1 = t + 2 := by omega
  rw [e1] at htot
  by_cases hm1 : m' = 1
  · rw [htot, hmeq, hm1, Nat.totient_one]
    have hpos : 0 < (t + 3) ^ f := by positivity
    have e2 : 2 * ((t + 3) ^ (f + 1) * 1) = (t + 3) ^ f * (2 * (t + 3)) := by ring
    have e3 : 3 * ((t + 3) ^ f * (t + 2) * 1) = (t + 3) ^ f * (3 * (t + 2)) := by ring
    rw [e2, e3]
    exact Nat.mul_le_mul_left _ (by omega)
  · exfalso
    have hm'0 : m' ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hmeq
      omega
    have hm'odd : m' % 2 = 1 := by
      by_contra hc
      have h2 : 2 ∣ m' := by omega
      have h3 : 2 ∣ m := by
        rw [hmeq]
        exact Dvd.dvd.mul_left h2 _
      omega
    have hev : Even (Nat.totient m') := Nat.totient_even (by omega)
    obtain ⟨r, hr⟩ := hev
    have ht2 : t % 2 = 0 := by omega
    obtain ⟨s, hs⟩ : ∃ s, t + 2 = 2 * s := ⟨(t + 2) / 2, by omega⟩
    have h4 : Nat.totient m = 4 * ((t + 3) ^ f * s * r) := by
      rw [htot, hs, hr]
      ring
    have hle := Nat.totient_le m
    rcases Nat.lt_or_ge c 2 with hc | hc
    · have hc' : c = 0 ∨ c = 1 := by omega
      rcases hc' with rfl | rfl
      · simp at h
        omega
      · simp at h
        omega
    · obtain ⟨d, rfl⟩ : ∃ d, c = d + 2 := ⟨c - 2, by omega⟩
      have e4 : 2 ^ (d + 2) = 4 * 2 ^ d := by ring
      rw [e4] at h
      omega

lemma lower (n x : ℕ) (hn : 1 < n) (hx : x - Nat.totient x = 2 ^ n) : 3 * 2 ^ (n - 1) ≤ x := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  have e1 : k + 2 - 1 = k + 1 := by omega
  rw [e1]
  have hpow : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by ring
  have hpos : 0 < 2 ^ (k + 1) := by positivity
  rw [hpow] at hx
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
  obtain ⟨a, m, hmodd, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hx0
  have hm : m % 2 = 1 := Nat.odd_iff.mp hmodd
  suffices hs : 2 ^ a * m ≤ 3 * Nat.totient (2 ^ a * m) by
    have := Nat.totient_le (2 ^ a * m)
    omega
  rcases Nat.eq_zero_or_pos a with ha | ha
  · exfalso
    rw [ha, pow_zero, one_mul] at hx
    have hm1 : m ≠ 1 := by
      rintro rfl
      rw [Nat.totient_one] at hx
      omega
    have hev : Even (Nat.totient m) := Nat.totient_even (by omega)
    obtain ⟨r, hr⟩ := hev
    have hle := Nat.totient_le m
    omega
  · obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
    have hcop : Nat.Coprime (2 ^ (b + 1)) m :=
      Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hmodd)
    have htot : Nat.totient (2 ^ (b + 1) * m) = 2 ^ b * Nat.totient m := by
      rw [Nat.totient_mul hcop, Nat.totient_prime_pow_succ Nat.prime_two]
      simp
    rw [htot] at hx ⊢
    have e2 : 2 ^ (b + 1) * m = 2 ^ b * (2 * m) := by ring
    rw [e2] at hx ⊢
    rw [← Nat.mul_sub] at hx
    have hdvd : (2 * m - Nat.totient m) ∣ 2 ^ (k + 2) := by
      rw [hpow, ← hx]
      exact Dvd.intro_left _ rfl
    obtain ⟨c, _, hc⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    have hk := odd_key m c hm hc
    have e3 : 3 * (2 ^ b * Nat.totient m) = 2 ^ b * (3 * Nat.totient m) := by ring
    rw [e3]
    exact Nat.mul_le_mul_left _ hk

lemma mem (k : ℕ) : cototient (3 * 2 ^ (k + 1)) = 2 ^ (k + 2) := by
  unfold cototient
  have hcop : Nat.Coprime 3 (2 ^ (k + 1)) := Nat.Coprime.pow_right _ (by decide)
  rw [Nat.totient_mul hcop, Nat.totient_prime_pow_succ Nat.prime_two,
    Nat.totient_prime Nat.prime_three]
  have e1 : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
  have e2 : 2 ^ (k + 2) = 4 * 2 ^ k := by ring
  rw [e1, e2]
  have hpos : 0 < 2 ^ k := by positivity
  simp only [Nat.add_one_sub_one, mul_one]
  omega

end A058764

theorem OMA.solution : type_of% @OMA.S_oeis_a058764.main := by
  intro n hn
  unfold OMA.S_oeis_a058764.a
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  have e1 : k + 2 - 1 = k + 1 := by omega
  have hmem : 3 * 2 ^ (k + 1) ∈ {x | OMA.S_oeis_a058764.cototient x = 2 ^ (k + 2)} :=
    A058764.mem k
  apply le_antisymm
  · rw [e1]
    exact Nat.sInf_le hmem
  · apply le_csInf ⟨_, hmem⟩
    intro x hx
    exact A058764.lower (k + 2) x hn hx
