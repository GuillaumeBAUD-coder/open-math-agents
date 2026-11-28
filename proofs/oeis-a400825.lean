import OMAStatements.S_oeis_a400825
import Mathlib

-- Problem oeis-a400825: for k >= 1 and N = (2^k - 1) * 2^(k+4) + 1, if 2^((N-1)/4) = -1 (mod N) then N is prime.
-- Upstream: statements/oeis-a400825.lean (declaration OMA.S_oeis_a400825.main)
-- Credit: @cclyles (the owner of the agent is credited as the solver)
--
-- Proof (a Proth / Pocklington argument): let r be the least prime factor of N; it is odd. Modulo r we have
-- 2^e = -1 with e = (N-1)/4 = (2^k - 1) * 2^(k+2), so the order d of 2 divides 2e but not e, which forces
-- 2^(k+3) | d. Since d | r - 1, r >= 2^(k+3) + 1, hence r^2 > 2^(2k+6) > N. A composite N would have r^2 <= N.

open OMA.S_oeis_a400825

private lemma two_pow_dvd_a400825 (d m j : ℕ) (h1 : d ∣ m * 2 ^ (j + 1)) (h2 : ¬ d ∣ m * 2 ^ j) :
    2 ^ (j + 1) ∣ d := by
  have hd0 : d ≠ 0 := by
    rintro rfl
    apply h2
    have h0 := Nat.eq_zero_of_zero_dvd h1
    have hm : m = 0 := by
      rcases Nat.mul_eq_zero.mp h0 with h | h
      · exact h
      · exact absurd h (pow_ne_zero _ (by norm_num))
    subst hm
    simp
  obtain ⟨a, b, hb, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hd0
  by_contra hcon
  have haj : a ≤ j := by
    by_contra h
    apply hcon
    exact Dvd.dvd.mul_right (pow_dvd_pow 2 (by omega)) b
  have hbdvd : b ∣ m * 2 ^ (j + 1) := dvd_trans (dvd_mul_left b (2 ^ a)) h1
  have hcop : Nat.Coprime b (2 ^ (j + 1)) := Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hb)
  have hbm : b ∣ m := hcop.dvd_of_dvd_mul_right hbdvd
  apply h2
  rw [mul_comm m]
  exact Nat.mul_dvd_mul (pow_dvd_pow 2 haj) hbm

theorem OMA.solution : type_of% @OMA.S_oeis_a400825.main := by
  intro k hk h
  by_contra hnp
  have h2k : 2 ^ 1 ≤ 2 ^ k := Nat.pow_le_pow_right (Nat.succ_pos 1) hk
  obtain ⟨t, ht⟩ : ∃ t, 2 ^ k = t + 2 := ⟨2 ^ k - 2, by omega⟩
  have e4 : 2 ^ (k + 4) = 16 * 2 ^ k := by ring
  have e3 : 2 ^ (k + 2 + 1) = 8 * 2 ^ k := by ring
  have e2 : 2 ^ (k + 2) = 4 * 2 ^ k := by ring
  have hN : N k = (t + 1) * (16 * (t + 2)) + 1 := by
    unfold N
    rw [e4, ht]
    rfl
  have hN1 : N k ≠ 1 := by
    rw [hN]
    have : 0 < (t + 1) * (16 * (t + 2)) := by positivity
    omega
  have hNpos : 0 < N k := by
    rw [hN]
    omega
  obtain ⟨r, hrdef⟩ : ∃ r, r = (N k).minFac := ⟨_, rfl⟩
  have hr : r.Prime := hrdef ▸ Nat.minFac_prime hN1
  have hrd : r ∣ N k := hrdef ▸ Nat.minFac_dvd _
  have hsq : r ^ 2 ≤ N k := hrdef ▸ Nat.minFac_sq_le_self hNpos hnp
  have hfact : Fact r.Prime := ⟨hr⟩
  have hr2 : r ≠ 2 := by
    intro h2r
    have hd : 2 ∣ N k := h2r ▸ hrd
    rw [hN] at hd
    have hd' : 2 ∣ (t + 1) * (16 * (t + 2)) := ⟨(t + 1) * (8 * (t + 2)), by ring⟩
    omega
  have h2ne : (2 : ZMod r) ≠ 0 := by
    intro h0
    have h0' : ((2 : ℕ) : ZMod r) = 0 := by exact_mod_cast h0
    have hdvd : r ∣ 2 := (ZMod.natCast_eq_zero_iff 2 r).mp h0'
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp hdvd)
  have he : (N k - 1) / 4 = (t + 1) * 2 ^ (k + 2) := by
    rw [hN, Nat.add_sub_cancel, e2, ht]
    have : (t + 1) * (16 * (t + 2)) = (t + 1) * (4 * (t + 2)) * 4 := by ring
    rw [this, Nat.mul_div_cancel _ (by norm_num : 0 < 4)]
  have h2' : (2 : ZMod r) ^ ((t + 1) * 2 ^ (k + 2)) = -1 := by
    have hc := congrArg (ZMod.castHom hrd (ZMod r)) h
    rw [he, map_pow, map_neg, map_one, map_ofNat] at hc
    exact hc
  have hd1 : orderOf (2 : ZMod r) ∣ (t + 1) * 2 ^ (k + 2 + 1) := by
    rw [orderOf_dvd_iff_pow_eq_one, pow_succ, ← mul_assoc, pow_mul, h2']
    norm_num
  have hd2 : ¬ orderOf (2 : ZMod r) ∣ (t + 1) * 2 ^ (k + 2) := by
    rw [orderOf_dvd_iff_pow_eq_one, h2']
    intro hneg
    apply h2ne
    linear_combination (-1 : ZMod r) * hneg
  have hpow : 2 ^ (k + 2 + 1) ∣ orderOf (2 : ZMod r) := two_pow_dvd_a400825 _ _ _ hd1 hd2
  have hfer : orderOf (2 : ZMod r) ∣ r - 1 :=
    orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one h2ne)
  have hr1 : 0 < r - 1 := by
    have := hr.two_le
    omega
  have hle : 2 ^ (k + 2 + 1) ≤ r - 1 := Nat.le_of_dvd hr1 (dvd_trans hpow hfer)
  rw [e3, ht] at hle
  have hr9 : 8 * (t + 2) + 1 ≤ r := by omega
  have hrr : (8 * (t + 2) + 1) * (8 * (t + 2) + 1) ≤ r * r := Nat.mul_le_mul hr9 hr9
  rw [hN, pow_two] at hsq
  nlinarith [hrr, hsq]
