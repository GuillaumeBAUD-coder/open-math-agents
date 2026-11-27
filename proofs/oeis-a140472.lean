import OMAStatements.S_oeis_a140472
import Mathlib

namespace OMA.S_oeis_a140472

private def g (n : ℕ) : ℕ :=
  if n = 0 then 0 else (n + 2 ^ padicValNat 2 n) / 2

private lemma pow_padicValNat_le {m : ℕ} (hm : 0 < m) : 2 ^ padicValNat 2 m ≤ m :=
  Nat.le_of_dvd hm pow_padicValNat_dvd

private lemma two_mul_g {m : ℕ} (hm : 0 < m) : 2 * g m = m + 2 ^ padicValNat 2 m := by
  have hm0 : m ≠ 0 := by omega
  simp only [g, if_neg hm0]
  have hdvd : 2 ∣ m + 2 ^ padicValNat 2 m := by
    by_cases h2 : 2 ∣ m
    · have hpos : 1 ≤ padicValNat 2 m := one_le_padicValNat_of_dvd hm0 h2
      have hpow : 2 ∣ 2 ^ padicValNat 2 m := dvd_pow_self 2 (by omega)
      exact dvd_add h2 hpow
    · have hv0 : padicValNat 2 m = 0 := padicValNat.eq_zero_of_not_dvd h2
      rw [hv0, pow_zero]
      omega
  exact Nat.mul_div_cancel' hdvd

private lemma g_pos {m : ℕ} (hm : 0 < m) : 1 ≤ g m := by
  have h1 := two_mul_g hm
  have h2 : 1 ≤ 2 ^ padicValNat 2 m := Nat.one_le_pow _ _ (by omega)
  omega

private lemma g_odd {m : ℕ} (hodd : ¬ 2 ∣ m) : g m = (m + 1) / 2 := by
  have hm0 : m ≠ 0 := by
    intro h; subst h; exact hodd (dvd_zero 2)
  have hv0 : padicValNat 2 m = 0 := padicValNat.eq_zero_of_not_dvd hodd
  simp only [g, if_neg hm0, hv0, pow_zero]

private lemma g_two_mul {k : ℕ} (hk : 0 < k) : g (2 * k) = k + 2 ^ padicValNat 2 k := by
  have h1 := two_mul_g (m := 2 * k) (by omega)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hv : padicValNat 2 (2 * k) = padicValNat 2 k + 1 := by
    rw [padicValNat.mul (by norm_num) (by omega), padicValNat.self (by norm_num), add_comm]
  rw [hv, pow_succ] at h1
  omega

private lemma even_sub_pow_padicValNat {k : ℕ} (hk : 0 < k) : 2 ∣ k - 2 ^ padicValNat 2 k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set v : ℕ := padicValNat 2 k with hv
  rcases (show 2 ^ v ∣ k from pow_padicValNat_dvd) with ⟨q, hq⟩
  have hnot : ¬ 2 ∣ q := by
    intro h2q
    rcases h2q with ⟨r, hr⟩
    have hdvd : 2 ^ (v + 1) ∣ k := by
      refine ⟨r, ?_⟩
      rw [hq, hr, pow_succ]
      ring
    exact pow_succ_padicValNat_not_dvd (by omega) (hv ▸ hdvd)
  have hqpos : 1 ≤ q := by
    rcases Nat.eq_zero_or_pos q with rfl | hpos
    · simp at hq; omega
    · exact hpos
  have hqeven : 2 ∣ q - 1 := by omega
  rcases hqeven with ⟨r, hr⟩
  refine ⟨2 ^ v * r, ?_⟩
  have h1 : k - 2 ^ v = 2 ^ v * (q - 1) := by
    rw [hq, Nat.mul_sub_left_distrib, mul_one]
  rw [h1, hr]
  ring

private lemma g_isA140472 : IsA140472 g := by
  refine ⟨by simp [g], ?_, ?_⟩
  · simp [g]
  · intro n hn
    rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
    · have hkpos : 0 < k := by omega
      have hn_eq : n = 2 * k := by omega
      subst hn_eq
      have hsub1 : ¬ 2 ∣ (2 * k - 1) := by omega
      have hgm1 : g (2 * k - 1) = k := by
        rw [g_odd hsub1]
        omega
      rw [hgm1, show 2 * k - k = k by omega, show 2 * k / 2 = k by omega]
      have h1 := g_two_mul hkpos
      have h2 := two_mul_g hkpos
      omega
    · have hkpos : 0 < k := by omega
      subst hk
      have hn_sub : 2 * k + 1 - 1 = 2 * k := by omega
      rw [hn_sub, g_two_mul hkpos, show (2 * k + 1) / 2 = k by omega]
      have hle : 2 ^ padicValNat 2 k ≤ k := pow_padicValNat_le hkpos
      have heven : 2 ∣ k - 2 ^ padicValNat 2 k := even_sub_pow_padicValNat hkpos
      set m : ℕ := 2 * k + 1 - (k + 2 ^ padicValNat 2 k)
      have hm_eq : m = (k - 2 ^ padicValNat 2 k) + 1 := by omega
      have hm_odd : ¬ 2 ∣ m := by
        rcases heven with ⟨r, hr⟩
        omega
      have hgm : g m = (m + 1) / 2 := g_odd hm_odd
      have hg2k1 : g (2 * k + 1) = k + 1 := by
        rw [g_odd (by omega)]
        omega
      have hgk := two_mul_g hkpos
      have hm_even2 : 2 ∣ m + 1 := by omega
      have h2gm : 2 * g m = m + 1 := by
        rw [hgm]
        exact Nat.mul_div_cancel' hm_even2
      omega

private lemma eq_g_of_isA140472 {f : ℕ → ℕ} (hf : IsA140472 f) : ∀ n : ℕ, f n = g n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 => rw [hf.1]; simp [g]
    | 1 => rw [hf.2.1]; simp [g]
    | m + 2 =>
      rw [hf.2.2 (m + 2) (by omega), g_isA140472.2.2 (m + 2) (by omega)]
      have h1 : f (m + 1) = g (m + 1) := ih (m + 1) (by omega)
      have hpos : 1 ≤ g (m + 1) := g_pos (by omega)
      have h2 : f (m + 2 - g (m + 1)) = g (m + 2 - g (m + 1)) := ih _ (by omega)
      have h3 : f ((m + 2) / 2) = g ((m + 2) / 2) := ih _ (by omega)
      rw [show m + 2 - 1 = m + 1 by omega, h1, h2, h3]

private lemma main_proof : (∃ f : ℕ → ℕ, IsA140472 f) ∧
    ∀ f : ℕ → ℕ, IsA140472 f → ∀ n : ℕ, 0 < n → f n = (n + 2 ^ padicValNat 2 n) / 2 := by
  refine ⟨⟨g, g_isA140472⟩, ?_⟩
  intro f hf n hn
  rw [eq_g_of_isA140472 hf n]
  simp only [g, if_neg (by omega : n ≠ 0)]

end OMA.S_oeis_a140472

theorem OMA.solution : type_of% @OMA.S_oeis_a140472.main :=
  OMA.S_oeis_a140472.main_proof
