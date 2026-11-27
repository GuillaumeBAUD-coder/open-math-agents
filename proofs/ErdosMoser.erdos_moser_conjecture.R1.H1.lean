import OMAReductions.R_ErdosMoser_erdos_moser_conjecture_R1
import Mathlib.Tactic

/-!
# Moser's parity/pairing argument for odd exponents in the Erdős–Moser equation
-/

private lemma add_dvd_pow_add_pow_odd (a b : ℕ) {k : ℕ} (hk : Odd k) :
    (a + b) ∣ a ^ k + b ^ k := by
  rcases hk with ⟨t, rfl⟩
  rw [← Int.ofNat_dvd]
  push_cast
  induction t with
  | zero =>
    simp
  | succ t ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨(a : ℤ) ^ 2 * c + (b : ℤ) ^ (2 * t + 1) * ((b : ℤ) - (a : ℤ)), ?_⟩
    have hexp : 2 * (t + 1) + 1 = (2 * t + 1) + 2 := by omega
    rw [hexp, pow_add, pow_add]
    linear_combination (a : ℤ) ^ 2 * hc

private lemma one_add_two_pow_lt_three_pow : ∀ k : ℕ, 2 ≤ k → 1 + 2 ^ k < 3 ^ k := by
  intro k hk
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  induction d with
  | zero =>
    norm_num
  | succ d ih =>
    have hprev : 1 + 2 ^ (2 + d) < 3 ^ (2 + d) := ih (Nat.le_add_right 2 d)
    have hpow : 0 < 2 ^ (2 + d) := by positivity
    calc 1 + 2 ^ (2 + (d + 1))
        = 1 + 2 * 2 ^ (2 + d) := by ring
      _ < 3 * (1 + 2 ^ (2 + d)) := by omega
      _ < 3 * 3 ^ (2 + d) := Nat.mul_lt_mul_of_pos_left hprev (by norm_num)
      _ = 3 ^ (2 + (d + 1)) := by ring

theorem prove_ErdosMoser_H1 :
    ∀ k m : ℕ, 0 < k → 0 < m → Odd k → ErdosMoser.powerSum k m = m ^ k → k = 1 ∧ m = 3 := by
  intro k m hk hm hodd heq
  rcases m with _ | _ | _ | _ | m'
  · omega
  · simp [ErdosMoser.powerSum] at heq
  · have hps : ErdosMoser.powerSum k 2 = 1 := by
      simp [ErdosMoser.powerSum]
    rw [hps] at heq
    change 1 = 2 ^ k at heq
    have h2 : 2 ≤ 2 ^ k := by
      simpa using Nat.pow_le_pow_right (by norm_num : 0 < 2) hk
    omega
  · have hps : ErdosMoser.powerSum k 3 = 1 + 2 ^ k := by
      have hico : Finset.Ico 1 3 = ({1, 2} : Finset ℕ) := by decide
      rw [ErdosMoser.powerSum, hico]
      simp
    rw [hps] at heq
    rcases eq_or_ne k 1 with rfl | hkne
    · exact ⟨rfl, rfl⟩
    · exfalso
      have hk2 : 2 ≤ k := by omega
      exact (one_add_two_pow_lt_three_pow k hk2).ne heq
  · exfalso
    set n : ℕ := m' + 3
    have hn3 : 3 ≤ n := by omega
    have hm_eq : m' + 4 = n + 1 := by omega
    rw [hm_eq] at heq
    let S : ℕ := ∑ i ∈ Finset.range (n + 1), i ^ k
    have hS_eq : S = ErdosMoser.powerSum k (n + 1) := by
      have hrange : Finset.range (n + 1) = insert 0 (Finset.Ico 1 (n + 1)) := by
        ext x
        simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]
        omega
      unfold S ErdosMoser.powerSum
      rw [hrange, Finset.sum_insert (by simp), Nat.zero_pow hk, zero_add]
    have hrefl : ∑ i ∈ Finset.range (n + 1), (n - i) ^ k = S := by
      simpa [Nat.add_sub_cancel] using
        (Finset.sum_range_reflect (fun i => i ^ k) (n + 1))
    have h2S : 2 * S = ∑ i ∈ Finset.range (n + 1), (i ^ k + (n - i) ^ k) := by
      calc 2 * S = S + S := two_mul S
        _ = (∑ i ∈ Finset.range (n + 1), i ^ k) + (∑ i ∈ Finset.range (n + 1), (n - i) ^ k) := by
            rw [hrefl]
        _ = ∑ i ∈ Finset.range (n + 1), (i ^ k + (n - i) ^ k) :=
            (Finset.sum_add_distrib).symm
    have hdvd_2S : n ∣ 2 * S := by
      rw [h2S]
      refine Finset.dvd_sum (fun i hi => ?_)
      have hi_le : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have hsum_i : i + (n - i) = n := Nat.add_sub_of_le hi_le
      simpa [hsum_i] using add_dvd_pow_add_pow_odd i (n - i) hodd
    rw [hS_eq, heq, mul_comm] at hdvd_2S
    have hcop : Nat.Coprime n ((n + 1) ^ k) :=
      (Nat.coprime_self_add_right.mpr (Nat.gcd_one_right n)).pow_right k
    have hdvd2 : n ∣ 2 := hcop.dvd_of_dvd_mul_left hdvd_2S
    have hle2 : n ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd2
    omega

theorem OMA.solution : OMA.R_ErdosMoser_erdos_moser_conjecture_R1.H1 :=
  prove_ErdosMoser_H1
