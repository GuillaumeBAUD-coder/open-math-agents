import OMAStatements.S_oeis_a182532

-- Problem: A182532: Carmichael numbers divisible by 7 and 17.
-- Upstream: statements/oeis-a182532.lean (declaration OMA.S_oeis_a182532.main)
-- Credit: Daniel Whorlow (@draonbioetl)

namespace OMA_A182532

open OMA.S_oeis_a182532

private lemma carmichael_base_modEq {C p g : ℕ} (hC : IsCarmichael C) (hp : p.Prime)
    (hpC : p ∣ C) (hg : g.Coprime p) : g ^ (C - 1) ≡ 1 [MOD p] := by
  have : Fact p.Prime := ⟨hp⟩
  have hCpos : 0 < C := by have := hC.1; omega
  set k := padicValNat p C
  have hk_pos : 1 ≤ k := by
    have : p ^ 1 ∣ C := by simpa using hpC
    exact (padicValNat_dvd_iff_le hCpos.ne').mp this
  have hpk_dvd : p ^ k ∣ C := pow_padicValNat_dvd
  set m := C / p ^ k
  have hCm : p ^ k * m = C := Nat.mul_div_cancel' hpk_dvd
  have hp_ndvd_m : ¬ p ∣ m := by
    intro hpm
    have h1 : p ^ (k + 1) ∣ C := by
      rw [← hCm, pow_succ]
      exact mul_dvd_mul_left (p ^ k) hpm
    have h2 : k + 1 ≤ k := (padicValNat_dvd_iff_le hCpos.ne').mp h1
    omega
  have hcop_pm : (p ^ k).Coprime m :=
    (hp.coprime_iff_not_dvd.mpr hp_ndvd_m).pow_left k
  let crt := Nat.chineseRemainder hcop_pm g 1
  set b := crt.val
  have hb_pk : b ≡ g [MOD p ^ k] := crt.property.1
  have hb_m : b ≡ 1 [MOD m] := crt.property.2
  have hp_dvd_pk : p ∣ p ^ k := dvd_pow_self p (by omega)
  have hb_p : b ≡ g [MOD p] := hb_pk.of_dvd hp_dvd_pk
  have hcop_bp : b.Coprime p := by
    rw [Nat.Coprime, Nat.ModEq.gcd_eq hb_p]
    exact hg
  have hcop_bm : b.Coprime m := by
    rw [Nat.Coprime, Nat.ModEq.gcd_eq hb_m]
    exact Nat.gcd_one_left m
  have hcop_bC : b.Coprime C := by
    rw [← hCm]
    exact (hcop_bp.pow_right k).mul_right hcop_bm
  have hpowC : b ^ (C - 1) ≡ 1 [MOD C] := hC.2.2 b hcop_bC
  have hpowp : b ^ (C - 1) ≡ 1 [MOD p] := hpowC.of_dvd hpC
  exact (hb_p.symm.pow (C - 1)).trans hpowp

private lemma mod_six_of_pow_three {n : ℕ} (h : 3 ^ n ≡ 1 [MOD 7]) : n % 6 = 0 := by
  have hpow : 3 ^ (n % 6) ≡ 1 [MOD 7] := by
    have h6 : 3 ^ 6 ≡ 1 [MOD 7] := by decide
    have hsplit : 3 ^ n = (3 ^ 6) ^ (n / 6) * 3 ^ (n % 6) := by
      rw [← pow_mul, ← pow_add, Nat.div_add_mod]
    have h1 : (3 ^ 6) ^ (n / 6) * 3 ^ (n % 6) ≡ 1 ^ (n / 6) * 3 ^ (n % 6) [MOD 7] :=
      (h6.pow (n / 6)).mul_right _
    rw [one_pow, one_mul, ← hsplit] at h1
    exact h1.symm.trans h
  have hlt : n % 6 < 6 := Nat.mod_lt n (by decide)
  interval_cases hmod : n % 6 <;> simp_all [Nat.ModEq]

private lemma mod_sixteen_of_pow_three {n : ℕ} (h : 3 ^ n ≡ 1 [MOD 17]) : n % 16 = 0 := by
  have hpow : 3 ^ (n % 16) ≡ 1 [MOD 17] := by
    have h16 : 3 ^ 16 ≡ 1 [MOD 17] := by decide
    have hsplit : 3 ^ n = (3 ^ 16) ^ (n / 16) * 3 ^ (n % 16) := by
      rw [← pow_mul, ← pow_add, Nat.div_add_mod]
    have h1 : (3 ^ 16) ^ (n / 16) * 3 ^ (n % 16) ≡ 1 ^ (n / 16) * 3 ^ (n % 16) [MOD 17] :=
      (h16.pow (n / 16)).mul_right _
    rw [one_pow, one_mul, ← hsplit] at h1
    exact h1.symm.trans h
  have hlt : n % 16 < 16 := Nat.mod_lt n (by decide)
  interval_cases hmod : n % 16 <;> simp_all [Nat.ModEq]

theorem main_proof :
    ∀ C : ℕ, IsCarmichael C → 7 ∣ C → 17 ∣ C →
      (C % 10 = 1 → ∃ n : ℕ, C = 7 * 17 * (120 * n + 119)) ∧
      (C % 10 = 5 → ∃ n : ℕ, C = 7 * 17 * (120 * n + 95)) ∧
      (C % 10 = 3 → ∃ n : ℕ, C = 7 * 17 * (120 * n + 47)) ∧
      (C % 10 = 9 → ∃ n : ℕ, C = 7 * 17 * (120 * n + 71)) := by
  intro C hC h7 h17
  have hC1 : 1 < C := hC.1
  have h6 : (C - 1) % 6 = 0 :=
    mod_six_of_pow_three (carmichael_base_modEq hC (by decide) h7 (by decide))
  have h16 : (C - 1) % 16 = 0 :=
    mod_sixteen_of_pow_three (carmichael_base_modEq hC (by decide) h17 (by decide))
  have h119 : 7 * 17 ∣ C :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide) h7 h17
  rcases h119 with ⟨q, rfl⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h10; exact ⟨q / 120, by omega⟩
  · intro h10; exact ⟨q / 120, by omega⟩
  · intro h10; exact ⟨q / 120, by omega⟩
  · intro h10; exact ⟨q / 120, by omega⟩

end OMA_A182532

theorem OMA.solution : type_of% @OMA.S_oeis_a182532.main := OMA_A182532.main_proof
