import OMAStatements.S_oeis_a399155
import Mathlib

-- Original Lean proof: @justusklocke-cloud.

namespace A399155
open OMA.S_oeis_a399155

lemma gpf_spec (n : ℕ) (hn : 2 ≤ n) :
    (greatestPrimeFactor n).Prime ∧ greatestPrimeFactor n ∣ n := by
  have hne := (Nat.primeFactorsList_ne_nil n).2 hn
  apply (Nat.mem_primeFactorsList (by omega)).1
  rw [greatestPrimeFactor, if_neg (by omega), List.getLastI_eq_getLast?_getD,
    List.getLast?_eq_some_getLast hne]
  exact List.getLast_mem hne

lemma sub_ne_one (n q : ℕ) (hq : q.Prime) (hd : q ∣ n) : n - q ≠ 1 := by
  intro e
  exact hq.not_dvd_one (e ▸ Nat.dvd_sub hd (dvd_refl q))

lemma largest_le (fuel : ℕ) : ∀ n, n ≠ 1 → steps greatestPrimeFactor fuel n ≤ n / 2 := by
  induction fuel with
  | zero => simp [steps]
  | succ f ih =>
    intro n hn
    rw [steps]
    split_ifs with h0
    · exact Nat.zero_le _
    · obtain ⟨hp, hd⟩ := gpf_spec n (by omega)
      have := hp.two_le
      have := ih _ (sub_ne_one n _ hp hd)
      omega

lemma smallest_even (fuel : ℕ) : ∀ n, 2 ∣ n → steps Nat.minFac fuel n = min fuel (n / 2) := by
  induction fuel with
  | zero => simp [steps]
  | succ f ih =>
    intro n he
    rw [steps]
    split_ifs with h0
    · simp [h0]
    · rw [(Nat.minFac_eq_two_iff n).2 he, ih (n - 2) (by omega)]
      omega

end A399155

open A399155 OMA.S_oeis_a399155 in
theorem OMA.solution : type_of% @OMA.S_oeis_a399155.main := by
  intro n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' (by omega : 1 ≤ n)
  simp only [largestSteps, smallestSteps, steps, if_neg (Nat.succ_ne_zero m)]
  obtain ⟨hp, hd⟩ := gpf_spec (m + 1) hn
  have hmin := Nat.minFac_le_of_dvd hp.two_le hd
  have he : (2 ∣ Nat.minFac (m + 1)) ↔ 2 ∣ m + 1 :=
    ⟨fun h => h.trans (Nat.minFac_dvd _), fun h => by simp [(Nat.minFac_eq_two_iff _).2 h]⟩
  have h := largest_le m _ (sub_ne_one _ _ hp hd)
  rw [smallest_even m _ (by omega)]
  omega
