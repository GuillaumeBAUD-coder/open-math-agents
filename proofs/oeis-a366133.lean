import OMAStatements.S_oeis_a366133
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Tactic

namespace OMA.P_oeis_a366133

open OMA.S_oeis_a366133

private lemma two_pow_dvd_choose_odd (m k : ℕ) (hk0 : 0 < k) (hklt : k < 2 ^ m) (hodd : Odd k) :
    2 ^ m ∣ Nat.choose (2 ^ m) k := by
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
    (∀ p k : ℕ, p.Prime → 0 < k → k < p → (p : ℤ) ∣ a366133 p k) ∧
    (∀ m k : ℕ, 0 < k → k < 2 ^ m → Odd k → ((2 ^ m : ℕ) : ℤ) ∣ a366133 (2 ^ m) k) := by
  refine ⟨?_, ?_⟩
  · intro p k hp hk0 hkp
    unfold a366133
    have hd : p ∣ Nat.choose p k := hp.dvd_choose_self (by omega) hkp
    exact dvd_mul_of_dvd_left (Int.natCast_dvd_natCast.mpr hd) _
  · intro m k hk0 hklt hodd
    unfold a366133
    have hd : 2 ^ m ∣ Nat.choose (2 ^ m) k := two_pow_dvd_choose_odd m k hk0 hklt hodd
    exact dvd_mul_of_dvd_left (Int.natCast_dvd_natCast.mpr hd) _

end OMA.P_oeis_a366133

theorem OMA.solution : type_of% @OMA.S_oeis_a366133.main :=
  OMA.P_oeis_a366133.prove_main
