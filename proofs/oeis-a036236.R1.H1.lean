import OMAReductions.R_oeis_a036236_R1
import Mathlib.NumberTheory.LSeries.PrimesInAP

/-!
# Proof of `oeis-a036236.R1.H1`

Proves that for every `j ≥ 1`, there are infinitely many positive integers `k` such that
`2 ^ k % k = 2 ^ j`.

Write `j = 2 ^ v * m` with `m` odd. By Dirichlet's theorem on primes in arithmetic progressions
(`Nat.forall_exists_prime_gt_and_modEq`), for any bound `B` there exists a prime
`p > max B (2 ^ j + j)` with `p ≡ 1 [MOD m.totient]`. Set `k = j * p > B`. Then:
1. `2 ^ (j * p) ≡ 2 ^ j [MOD p]` by Fermat's little theorem;
2. `2 ^ (j * p) ≡ 2 ^ j [MOD 2 ^ v]` because both are divisible by `2 ^ v` (since `v ≤ j ≤ j * p`);
3. `2 ^ (j * p) ≡ 2 ^ j [MOD m]` by Euler's theorem since `m.totient ∣ p - 1 ∣ j * (p - 1)` and
   `Nat.Coprime 2 m`.
Since `p`, `2 ^ v`, and `m` are pairwise coprime, `2 ^ k ≡ 2 ^ j [MOD k]`, and since `2 ^ j < k`,
`2 ^ k % k = 2 ^ j`.
-/

namespace OeisA036236R1H1Proof

private lemma le_two_pow (v : ℕ) : v ≤ 2 ^ v := by
  induction v with
  | zero => simp
  | succ v ih =>
    rw [pow_succ]
    have := Nat.one_le_two_pow (n := v)
    omega

end OeisA036236R1H1Proof

theorem OMA.solution : OMA.R_oeis_a036236_R1.H1 := by
  intro j hj
  apply Set.infinite_of_forall_exists_gt
  intro B
  obtain ⟨v, m, hm_odd, hj_eq⟩ := Nat.exists_eq_two_pow_mul_odd (by omega : j ≠ 0)
  have hm_pos : 0 < m := by
    by_contra h0
    have : m = 0 := by omega
    subst this; simp at hm_odd
  have htot_ne : m.totient ≠ 0 := (Nat.totient_pos.mpr hm_pos).ne'
  obtain ⟨p, hp_gt, hp_prime, hp_mod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq (max B (2 ^ j + j)) htot_ne (Nat.coprime_one_left m.totient)
  set k := j * p
  have hp_gtB : B < p := lt_of_le_of_lt (le_max_left _ _) hp_gt
  have hp_gt2j : 2 ^ j + j < p := lt_of_le_of_lt (le_max_right _ _) hp_gt
  have hk_gtB : B < k := by
    dsimp [k]
    calc B < p := hp_gtB
      _ = 1 * p := (one_mul p).symm
      _ ≤ j * p := Nat.mul_le_mul_right p hj
  have hk_pos : 0 < k := Nat.mul_pos (by omega) hp_prime.pos
  have h2j_lt_k : 2 ^ j < k := by
    dsimp [k]
    calc 2 ^ j < 2 ^ j + j := by omega
      _ < p := hp_gt2j
      _ = 1 * p := (one_mul p).symm
      _ ≤ j * p := Nat.mul_le_mul_right p hj
  -- Step 1: 2 ^ (j * p) ≡ 2 ^ j [MOD p]
  have hmod_p : 2 ^ k ≡ 2 ^ j [MOD p] := by
    dsimp [k]
    rw [pow_mul]
    have : Fact p.Prime := ⟨hp_prime⟩
    have hflt : ((2 ^ j : ℕ) : ZMod p) ^ p = ((2 ^ j : ℕ) : ZMod p) := ZMod.pow_card _
    rw [← ZMod.natCast_eq_natCast_iff]
    simp [Nat.cast_pow, hflt]
  -- Step 2: 2 ^ (j * p) ≡ 2 ^ j [MOD 2 ^ v]
  have hv_le_j : v ≤ j := by
    calc v ≤ 2 ^ v := OeisA036236R1H1Proof.le_two_pow v
      _ = 2 ^ v * 1 := (mul_one _).symm
      _ ≤ 2 ^ v * m := Nat.mul_le_mul_left _ hm_pos
      _ = j := hj_eq.symm
  have hv_le_k : v ≤ k := le_trans hv_le_j (Nat.le_mul_of_pos_right j hp_prime.pos)
  have hmod_2v : 2 ^ k ≡ 2 ^ j [MOD 2 ^ v] := by
    have h1 : 2 ^ k ≡ 0 [MOD 2 ^ v] := Nat.modEq_zero_iff_dvd.mpr (Nat.pow_dvd_pow 2 hv_le_k)
    have h2 : 2 ^ j ≡ 0 [MOD 2 ^ v] := Nat.modEq_zero_iff_dvd.mpr (Nat.pow_dvd_pow 2 hv_le_j)
    exact h1.trans h2.symm
  -- Step 3: 2 ^ (j * p) ≡ 2 ^ j [MOD m]
  have hmod_m : 2 ^ k ≡ 2 ^ j [MOD m] := by
    have hp1 : 1 ≤ p := hp_prime.one_le
    have htot_dvd : m.totient ∣ p - 1 := (Nat.modEq_iff_dvd' hp1).mp hp_mod.symm
    obtain ⟨t, ht⟩ := htot_dvd
    have hk_split : k = j + m.totient * (j * t) := by
      dsimp [k]
      have : p = 1 + m.totient * t := by omega
      rw [this]; ring
    rw [hk_split, pow_add, pow_mul]
    have hcop2m : Nat.Coprime 2 m := Nat.coprime_two_left.mpr hm_odd
    have heul : 2 ^ m.totient ≡ 1 [MOD m] := Nat.ModEq.pow_totient hcop2m
    have hpow : (2 ^ m.totient) ^ (j * t) ≡ 1 [MOD m] := by
      simpa using heul.pow (j * t)
    simpa using (Nat.ModEq.refl (2 ^ j)).mul hpow
  -- Combine via coprimality of 2 ^ v, m, p
  have hcop_2v_m : (2 ^ v).Coprime m := (Nat.coprime_two_left.mpr hm_odd).pow_left v
  have hmod_j : 2 ^ k ≡ 2 ^ j [MOD j] := by
    have h1 : 2 ^ k ≡ 2 ^ j [MOD 2 ^ v * m] :=
      (Nat.modEq_and_modEq_iff_modEq_mul hcop_2v_m).mp ⟨hmod_2v, hmod_m⟩
    rwa [← hj_eq] at h1
  have hcop_j_p : j.Coprime p := by
    have hnot : ¬ (p ∣ j) := by
      intro hd
      have hle : p ≤ j := Nat.le_of_dvd (by omega) hd
      have hlt : j < p := lt_of_le_of_lt (Nat.le_add_left j (2 ^ j)) hp_gt2j
      omega
    exact (hp_prime.coprime_iff_not_dvd.mpr hnot).symm
  have hmod_k : 2 ^ k ≡ 2 ^ j [MOD k] :=
    (Nat.modEq_and_modEq_iff_modEq_mul hcop_j_p).mp ⟨hmod_j, hmod_p⟩
  refine ⟨k, ⟨hk_pos, ?_⟩, hk_gtB⟩
  rw [Nat.ModEq, Nat.mod_eq_of_lt h2j_lt_k] at hmod_k
  exact hmod_k
