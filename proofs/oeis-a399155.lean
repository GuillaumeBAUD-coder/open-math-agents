import OMAStatements.S_oeis_a399155
import Mathlib

namespace A399155
open OMA.S_oeis_a399155

lemma gpf_spec (n : ℕ) (hn : 2 ≤ n) :
    (greatestPrimeFactor n).Prime ∧ greatestPrimeFactor n ∣ n := by
  have hne : n.primeFactorsList ≠ [] := (Nat.primeFactorsList_ne_nil n).2 (by omega)
  have hmem : greatestPrimeFactor n ∈ n.primeFactorsList := by
    unfold greatestPrimeFactor
    rw [if_neg (by omega), List.getLastI_eq_getLast?_getD, List.getLast?_eq_some_getLast hne]
    simp only [Option.getD_some]
    exact List.getLast_mem hne
  exact (Nat.mem_primeFactorsList (by omega)).1 hmem

lemma sub_ne_one (n q : ℕ) (hq : q.Prime) (hd : q ∣ n) : n - q ≠ 1 := by
  intro h1
  have h2 : q ∣ n - q := Nat.dvd_sub hd (dvd_refl _)
  rw [h1] at h2
  have h3 := Nat.le_of_dvd one_pos h2
  have h4 := hq.two_le
  omega

lemma largest_le (fuel : ℕ) : ∀ n, n ≠ 1 → steps greatestPrimeFactor fuel n ≤ n / 2 := by
  induction fuel with
  | zero =>
    intro n _
    rw [steps]
    exact Nat.zero_le _
  | succ f ih =>
    intro n hn
    rw [steps]
    split_ifs with h0
    · exact Nat.zero_le _
    · have hn2 : 2 ≤ n := by omega
      obtain ⟨hp, hd⟩ := gpf_spec n hn2
      have hq2 := hp.two_le
      have hqn := Nat.le_of_dvd (by omega) hd
      have h5 := ih _ (sub_ne_one n _ hp hd)
      omega

lemma smallest_ge (fuel : ℕ) : ∀ n, n ≤ fuel → 2 ∣ n → n / 2 ≤ steps Nat.minFac fuel n := by
  induction fuel with
  | zero =>
    intro n hn _
    have h0 : n = 0 := by omega
    subst h0
    exact Nat.zero_le _
  | succ f ih =>
    intro n hn h2
    rw [steps]
    split_ifs with h0
    · subst h0
      exact Nat.zero_le _
    · have hm : Nat.minFac n = 2 := (Nat.minFac_eq_two_iff n).2 h2
      rw [hm]
      have h5 := ih (n - 2) (by omega) (by omega)
      omega

end A399155

theorem OMA.solution : type_of% @OMA.S_oeis_a399155.main := by
  intro n hn
  unfold OMA.S_oeis_a399155.largestSteps OMA.S_oeis_a399155.smallestSteps
  by_cases he : 2 ∣ n
  · have h1 := A399155.largest_le n n (by omega)
    have h2 := A399155.smallest_ge n n le_rfl he
    omega
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [OMA.S_oeis_a399155.steps, OMA.S_oeis_a399155.steps]
    rw [if_neg (by omega), if_neg (by omega)]
    obtain ⟨hp, hd⟩ := A399155.gpf_spec (m + 1) hn
    have hmp : (Nat.minFac (m + 1)).Prime := Nat.minFac_prime (by omega)
    have hmd : Nat.minFac (m + 1) ∣ m + 1 := Nat.minFac_dvd _
    have hle : Nat.minFac (m + 1) ≤ OMA.S_oeis_a399155.greatestPrimeFactor (m + 1) :=
      Nat.minFac_le_of_dvd hp.two_le hd
    have hne := A399155.sub_ne_one (m + 1) _ hp hd
    have hpodd : ¬ 2 ∣ Nat.minFac (m + 1) := fun h => he (dvd_trans h hmd)
    have hp2 := hmp.two_le
    have hpn := Nat.le_of_dvd (by omega) hmd
    have hqn := Nat.le_of_dvd (by omega) hd
    have h1 := A399155.largest_le m (m + 1 - OMA.S_oeis_a399155.greatestPrimeFactor (m + 1)) hne
    have h2 := A399155.smallest_ge m (m + 1 - Nat.minFac (m + 1)) (by omega) (by omega)
    omega
