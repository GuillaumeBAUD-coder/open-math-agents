import OMAStatements.S_oeis_a341522
import Mathlib

namespace OMA.P_oeis_a341522

private theorem main_proved :
    ∀ (primeShift doudna invDoudna : ℕ → ℕ),
      primeShift 1 = 1 →
      (∀ x : ℕ, primeShift (2 * x) = 3 * primeShift x) →
      doudna 1 = 1 →
      (∀ k : ℕ, 1 ≤ k → doudna (2 * k) = 2 * doudna k) →
      (∀ k : ℕ, doudna (2 * k + 1) = primeShift (doudna (k + 1))) →
      (∀ m : ℕ, 1 ≤ m → invDoudna (doudna m) = m - 1) →
      ∀ n : ℕ,
        invDoudna (3 * doudna (n + 1)) = 1 + 2 * n + 2 ^ padicValNat 2 (n + 1) := by
  intro primeShift doudna invDoudna _ hshift2 _ hd_even hd_odd hinv n
  have hd_pow2 : ∀ (v r : ℕ), 1 ≤ r → doudna (2 ^ v * r) = 2 ^ v * doudna r := by
    intro v
    induction v with
    | zero => intro r _; simp
    | succ v ih =>
      intro r hr
      have h1 : 2 ^ (v + 1) * r = 2 * (2 ^ v * r) := by rw [pow_succ']; ring
      have hpos : 1 ≤ 2 ^ v * r := Nat.one_le_iff_ne_zero.mpr (by positivity)
      rw [h1, hd_even _ hpos, ih r hr, pow_succ']; ring
  set v := padicValNat 2 (n + 1)
  have hdvd : 2 ^ v ∣ (n + 1) := pow_padicValNat_dvd
  obtain ⟨q, hq⟩ := hdvd
  have hq_odd : ¬(2 ∣ q) := by
    intro h2q
    have hdvd1 : 2 ^ (v + 1) ∣ (n + 1) := by
      obtain ⟨r, hr⟩ := h2q
      exact ⟨r, by rw [hq, hr, pow_succ']; ring⟩
    have hle : v + 1 ≤ padicValNat 2 (n + 1) := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact (padicValNat_dvd_iff_le (Nat.succ_ne_zero n)).mp hdvd1
    omega
  obtain ⟨k, hk⟩ : ∃ k, q = 2 * k + 1 := ⟨q / 2, by omega⟩
  have h3d : 3 * doudna (n + 1) = doudna (2 ^ v * (4 * k + 3)) := by
    rw [hq, hk, hd_pow2 v (2 * k + 1) (by omega), hd_odd k]
    calc 3 * (2 ^ v * primeShift (doudna (k + 1)))
        = 2 ^ v * (3 * primeShift (doudna (k + 1))) := by ring
      _ = 2 ^ v * primeShift (2 * doudna (k + 1)) := by rw [← hshift2]
      _ = 2 ^ v * primeShift (doudna (2 * (k + 1))) := by rw [← hd_even (k + 1) (by omega)]
      _ = 2 ^ v * doudna (2 * (2 * k + 1) + 1) := by
            rw [show 2 * (k + 1) = 2 * k + 1 + 1 by omega, ← hd_odd (2 * k + 1)]
      _ = doudna (2 ^ v * (4 * k + 3)) := by
            rw [show 2 * (2 * k + 1) + 1 = 4 * k + 3 by omega, ← hd_pow2 v (4 * k + 3) (by omega)]
  have hpos : 1 ≤ 2 ^ v * (4 * k + 3) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  rw [h3d, hinv _ hpos]
  have hval : 2 ^ v * (4 * k + 3) = 2 * (n + 1) + 2 ^ v := by
    rw [hq, hk]; ring
  rw [hval]
  omega

end OMA.P_oeis_a341522

theorem OMA.solution : type_of% @OMA.S_oeis_a341522.main :=
  OMA.P_oeis_a341522.main_proved
