import OMAStatements.S_oeis_a341723
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Tactic

namespace OMA.P_oeis_a341723

open OMA.S_oeis_a341723

private lemma two_pow_dvd_choose_odd (m k : ℕ) (hk0 : 0 < k) (hklt : k < 2 ^ m) (hodd : Odd k) :
    2 ^ m ∣ Nat.choose (2 ^ m) k := by
  have hm_pos : 0 < 2 ^ m := pow_pos (by decide) m
  have habs : k * Nat.choose (2 ^ m) k = 2 ^ m * Nat.choose (2 ^ m - 1) (k - 1) := by
    obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    obtain ⟨N, hN⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : 2 ^ m ≠ 0)
    rw [hN, show N + 1 - 1 = N by omega, show k' + 1 - 1 = k' by omega]
    have h := Nat.add_one_mul_choose_eq N k'
    linarith
  have hcop : Nat.Coprime (2 ^ m) k := (Nat.coprime_two_left.mpr hodd).pow_left m
  have hdvd : 2 ^ m ∣ k * Nat.choose (2 ^ m) k := ⟨Nat.choose (2 ^ m - 1) (k - 1), habs⟩
  exact hcop.dvd_of_dvd_mul_left hdvd

private lemma prove_main :
    (∀ p k : ℕ, p.Prime → 0 < k → k < p → (p : ℤ) ∣ a341723 p k) ∧
    (∀ m k : ℕ, 0 < k → k < 2 ^ m → Odd k → ((2 ^ m : ℕ) : ℤ) ∣ a341723 (2 ^ m) k) := by
  refine ⟨?_, ?_⟩
  · intro p k hp hk0 hkp
    unfold a341723
    have hd : p ∣ Nat.choose p k := hp.dvd_choose_self (by omega) hkp
    have hdz : (p : ℤ) ∣ (Nat.choose p k : ℤ) := Int.natCast_dvd_natCast.mpr hd
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hdz _) _
  · intro m k hk0 hklt hodd
    unfold a341723
    have hd : 2 ^ m ∣ Nat.choose (2 ^ m) k := two_pow_dvd_choose_odd m k hk0 hklt hodd
    have hdz : ((2 ^ m : ℕ) : ℤ) ∣ (Nat.choose (2 ^ m) k : ℤ) := Int.natCast_dvd_natCast.mpr hd
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hdz _) _

end OMA.P_oeis_a341723

theorem OMA.solution : type_of% @OMA.S_oeis_a341723.main :=
  OMA.P_oeis_a341723.prove_main
