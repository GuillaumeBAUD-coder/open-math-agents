import OMAStatements.S_oeis_a349958
import Mathlib

namespace OMA.A349958Proof

open OMA.S_oeis_a349958

theorem dvd_choose_two (N A B : ℕ) (hcop : Nat.Coprime (2 * A) B)
    (h1 : 2 * A ∣ N * (N - 1)) (h2 : B ∣ N * (N - 1)) : A * B ∣ N.choose 2 := by
  have h := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop h1 h2
  obtain ⟨t, ht⟩ := h
  rw [Nat.choose_two_right, ht]
  refine ⟨t, ?_⟩
  rw [show 2 * A * B * t = 2 * (A * B * t) by ring]
  exact Nat.mul_div_cancel_left _ (by norm_num)

theorem key (A B : ℕ) (hA : 2 ≤ A) (hB : 2 ≤ B) (hBodd : Odd B) (hcop : Nat.Coprime A B) :
    ∃ r < A * B, containsMultiple (A * B) r := by
  have h2B : Nat.Coprime 2 B := (Nat.coprime_two_left).mpr hBodd
  have hXB : Nat.Coprime (2 * A) B := Nat.Coprime.mul h2B hcop
  set N := (Nat.chineseRemainder hXB 0 1 : ℕ) with hNdef
  have hNlt : N < 2 * A * B := Nat.chineseRemainder_lt_mul hXB 0 1 (by omega) (by omega)
  have hm0 : N ≡ 0 [MOD 2 * A] := (Nat.chineseRemainder hXB 0 1).2.1
  have hm1 : N ≡ 1 [MOD B] := (Nat.chineseRemainder hXB 0 1).2.2
  have hXN : 2 * A ∣ N := (Nat.modEq_zero_iff_dvd).mp hm0
  have hN1 : 1 ≤ N := by
    by_contra hc
    have : N = 0 := by omega
    rw [this] at hm1
    have := (Nat.modEq_iff_dvd' (Nat.zero_le 1)).mp hm1
    have : B ∣ 1 := by simpa using this
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have hBN : B ∣ N - 1 := (Nat.modEq_iff_dvd' hN1).mp hm1.symm
  have hN2 : 2 ≤ N := by
    by_contra hc
    have : N = 1 := by omega
    rw [this] at hXN
    have := Nat.le_of_dvd (by norm_num) hXN
    omega
  by_cases hlt : N < A * B
  · refine ⟨N, hlt, 2, hN2, ?_⟩
    exact dvd_choose_two N A B hXB (Dvd.dvd.mul_right hXN _) (Dvd.dvd.mul_left hBN _)
  · have hne : N ≠ A * B := by
      intro he
      rw [he, show A * B = A * B * 1 by ring, show 2 * A = A * 2 by ring] at hXN
      have := Nat.dvd_of_mul_dvd_mul_left (by omega : 0 < A) (by simpa [mul_assoc] using hXN)
      exact (Nat.not_even_iff_odd.mpr hBodd) (even_iff_two_dvd.mpr (by simpa using this))
    have hne1 : N ≠ A * B + 1 := by
      intro he
      rw [he] at hXN
      have hA1 : A ∣ A * B + 1 := Dvd.dvd.trans (Dvd.intro_left 2 rfl) hXN
      have : A ∣ 1 := (Nat.dvd_add_right (Dvd.intro B rfl)).mp hA1
      have := Nat.le_of_dvd (by norm_num) this
      omega
    have hNlt' : N < 2 * (A * B) := by rw [← mul_assoc]; exact hNlt
    refine ⟨2 * (A * B) + 1 - N, by omega, 2, by omega, ?_⟩
    apply dvd_choose_two _ A B hXB
    · apply Dvd.dvd.mul_left
      rw [show 2 * (A * B) + 1 - N - 1 = 2 * (A * B) - N by omega]
      exact Nat.dvd_sub (by rw [← mul_assoc]; exact Dvd.intro B rfl) hXN
    · apply Dvd.dvd.mul_right
      rw [show 2 * (A * B) + 1 - N = 2 * (A * B) - (N - 1) by omega]
      exact Nat.dvd_sub (by rw [← mul_assoc]; exact Dvd.intro_left (2 * A) rfl) hBN

theorem nonpp (n : ℕ) (hn : 1 < n) (hnp : ¬ IsPrimePow n) :
    ∃ r < n, containsMultiple n r := by
  have hn0 : n ≠ 0 := by omega
  have hp : n.minFac.Prime := Nat.minFac_prime (by omega)
  obtain ⟨p, hpdef⟩ : ∃ p, p = n.minFac := ⟨_, rfl⟩
  rw [← hpdef] at hp
  obtain ⟨A, hAdef⟩ : ∃ A, A = p ^ n.factorization p := ⟨_, rfl⟩
  obtain ⟨B, hBdef⟩ : ∃ B, B = n / A := ⟨_, rfl⟩
  have hAB : A * B = n := by rw [hBdef, hAdef]; exact Nat.ordProj_mul_ordCompl_eq_self n p
  have hcopB : Nat.Coprime p B := by rw [hBdef, hAdef]; exact Nat.coprime_ordCompl hp hn0
  have hcop : Nat.Coprime A B := by rw [hAdef]; exact Nat.Coprime.pow_left _ hcopB
  have hfac : 0 < n.factorization p :=
    hp.factorization_pos_of_dvd hn0 (by rw [hpdef]; exact Nat.minFac_dvd n)
  have hA : 2 ≤ A := by
    have h1 : p ^ 1 ≤ p ^ n.factorization p := Nat.pow_le_pow_right hp.pos hfac
    have := hp.two_le
    rw [pow_one, ← hAdef] at h1
    omega
  have hB0 : B ≠ 0 := by
    intro h; rw [h, mul_zero] at hAB; omega
  have hB1 : B ≠ 1 := by
    intro h
    apply hnp
    rw [isPrimePow_nat_iff]
    exact ⟨p, n.factorization p, hp, hfac, by rw [← hAdef, ← hAB, h, mul_one]⟩
  have hBodd : Odd B := by
    rcases Nat.even_or_odd B with he | ho
    · exfalso
      have h2B : 2 ∣ B := even_iff_two_dvd.mp he
      have h2n : 2 ∣ n := by rw [← hAB]; exact Dvd.dvd.mul_left h2B A
      have hp2 : p ≤ 2 := by rw [hpdef]; exact Nat.minFac_le_of_dvd (le_refl 2) h2n
      have hp2' : p = 2 := by have := hp.two_le; omega
      rw [hp2'] at hcopB
      have := Nat.Coprime.eq_one_of_dvd hcopB h2B
      omega
    · exact ho
  obtain ⟨r, hr, hc⟩ := key A B hA (by omega) hBodd hcop
  rw [hAB] at hr hc
  exact ⟨r, hr, hc⟩

theorem pp (n : ℕ) (h : IsPrimePow n) : IsLeast {row : ℕ | containsMultiple n row} n := by
  rw [isPrimePow_nat_iff] at h
  obtain ⟨p, k, hp, hk, rfl⟩ := h
  refine ⟨⟨1, Nat.one_le_pow _ _ hp.pos, by simp⟩, ?_⟩
  intro r hr
  obtain ⟨j, hj, hd⟩ := hr
  by_contra hlt
  push Not at hlt
  have hC : r.choose j ≠ 0 := (Nat.choose_pos hj).ne'
  have h1 := (hp.pow_dvd_iff_le_factorization hC).mp hd
  have h2 : (r.choose j).factorization p ≤ Nat.log p r := Nat.factorization_choose_le_log
  have h3 : Nat.log p r < k := Nat.log_lt_of_lt_pow' (by omega) hlt
  omega

end OMA.A349958Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a349958.main := by
  intro n hn
  constructor
  · intro h
    by_contra hnp
    by_cases h1 : n = 1
    · subst h1
      have : (0 : ℕ) ∈ {row : ℕ | OMA.S_oeis_a349958.containsMultiple 1 row} :=
        ⟨0, le_refl 0, one_dvd _⟩
      have := h.2 this
      omega
    · obtain ⟨r, hr, hc⟩ := OMA.A349958Proof.nonpp n (by omega) hnp
      have := h.2 hc
      omega
  · exact OMA.A349958Proof.pp n
