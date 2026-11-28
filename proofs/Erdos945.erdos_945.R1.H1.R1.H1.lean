import OMAReductions.R_Erdos945_erdos_945_R1_H1_R1

/-!
# Proof of Step H1 of Erdos945.erdos_945.R1.H1

Elementary union bound over all `d ∈ Icc 2 (H / 8)` showing that at most `7 * H / 8`
integers in `(n, n + H]` are divisible by the square of a prime `p ≤ H / 8`.
-/

-- Step Erdos945.erdos_945.R1.H1.R1.H1: hypothesis H1 of reduction Erdos945.erdos_945.R1.H1.R1
-- Credit: @ignacio-rocco

open Finset

private lemma card_multiples_Ioc (n H b : ℕ) (hb : 0 < b) :
    ((Ioc n (n + H)).filter fun q => b ∣ q).card ≤ H / b + 1 := by
  have hsub : ((Ioc n (n + H)).filter fun q => b ∣ q).card ≤
      (Ioc (n / b) ((n + H) / b)).card := by
    refine Finset.card_le_card_of_injOn (fun q => q / b) ?_ ?_
    · intro q hq
      obtain ⟨hI, hd⟩ := mem_filter.mp (Finset.mem_coe.mp hq)
      obtain ⟨hlo, hhi⟩ := mem_Ioc.mp hI
      simp only [Finset.mem_coe, mem_Ioc]
      refine ⟨?_, Nat.div_le_div_right hhi⟩
      rcases hd with ⟨k, rfl⟩
      rw [Nat.mul_div_cancel_left k hb]
      exact (Nat.div_lt_iff_lt_mul hb).mpr (by rwa [Nat.mul_comm])
    · intro q₁ hq₁ q₂ hq₂ heq
      dsimp only at heq
      obtain ⟨_, hd₁⟩ := mem_filter.mp (Finset.mem_coe.mp hq₁)
      obtain ⟨_, hd₂⟩ := mem_filter.mp (Finset.mem_coe.mp hq₂)
      have h1 := Nat.mul_div_cancel' hd₁
      have h2 := Nat.mul_div_cancel' hd₂
      rw [← h1, ← h2, heq]
  calc ((Ioc n (n + H)).filter fun q => b ∣ q).card
      ≤ (Ioc (n / b) ((n + H) / b)).card := hsub
    _ = (n + H) / b - n / b := by simp
    _ ≤ H / b + 1 := by
      rw [Nat.add_div hb]
      generalize n / b = q1, H / b = q2
      split <;> omega

private lemma div_sq_le_sub (H d : ℕ) (hd : 2 ≤ d) :
    H / (d * d) ≤ H / (d - 1) - H / d := by
  rw [← Nat.div_div_eq_div_mul]
  apply Nat.le_sub_of_add_le
  apply (Nat.le_div_iff_mul_le (by omega : 0 < d - 1)).2
  have h1 : (H / d / d) * (d - 1) ≤ H / d :=
    le_trans (Nat.mul_le_mul_left _ (Nat.sub_le d 1)) (Nat.div_mul_le_self (H / d) d)
  have h2 : (H / d) * (d - 1) + H / d = (H / d) * d := by
    have : d - 1 + 1 = d := by omega
    calc (H / d) * (d - 1) + H / d = (H / d) * (d - 1 + 1) := by ring
      _ = (H / d) * d := by rw [this]
  rw [Nat.add_mul]
  calc (H / d / d) * (d - 1) + (H / d) * (d - 1)
      ≤ H / d + (H / d) * (d - 1) := Nat.add_le_add_right h1 _
    _ = (H / d) * (d - 1) + H / d := Nat.add_comm _ _
    _ = (H / d) * d := h2
    _ ≤ H := Nat.div_mul_le_self H d

private lemma sum_div_sq_Icc (H M : ℕ) (hM : 2 ≤ M) :
    ∑ d ∈ Icc 3 M, (H / (d * d)) ≤ H / 2 - H / M := by
  induction M, hM using Nat.le_induction with
  | base =>
    simp
  | succ k hk ih =>
    have hsplit : Icc 3 (k + 1) = insert (k + 1) (Icc 3 k) := by
      ext x
      simp only [mem_Icc, mem_insert]
      omega
    rw [hsplit, sum_insert (by simp only [mem_Icc]; omega)]
    have hstep : H / ((k + 1) * (k + 1)) ≤ H / k - H / (k + 1) := by
      simpa [Nat.add_sub_cancel] using div_sq_le_sub H (k + 1) (by omega)
    have hmono1 : H / (k + 1) ≤ H / k := Nat.div_le_div_left (by omega) (by omega)
    have hmono2 : H / k ≤ H / 2 := Nat.div_le_div_left hk (by omega)
    omega

theorem OMA.solution : OMA.R_Erdos945_erdos_945_R1_H1_R1.H1 := by
  intro n H hH
  classical
  set M := H / 8
  have hM : 2 ≤ M := by omega
  have hcov : ((Ioc n (n + H)).filter fun q =>
      ∃ p : ℕ, p.Prime ∧ p ≤ M ∧ p * p ∣ q) ⊆
      (Icc 2 M).biUnion (fun d => (Ioc n (n + H)).filter fun q => d * d ∣ q) := by
    intro q hq
    obtain ⟨hI, p, hp, hpM, hdvd⟩ := mem_filter.mp hq
    exact mem_biUnion.mpr ⟨p, mem_Icc.mpr ⟨hp.two_le, hpM⟩, mem_filter.mpr ⟨hI, hdvd⟩⟩
  have h1 : ((Ioc n (n + H)).filter fun q =>
      ∃ p : ℕ, p.Prime ∧ p ≤ M ∧ p * p ∣ q).card ≤
      ∑ d ∈ Icc 2 M, ((Ioc n (n + H)).filter fun q => d * d ∣ q).card :=
    (card_le_card hcov).trans card_biUnion_le
  have h2 : ∑ d ∈ Icc 2 M, ((Ioc n (n + H)).filter fun q => d * d ∣ q).card ≤
      ∑ d ∈ Icc 2 M, (H / (d * d) + 1) := by
    refine sum_le_sum fun d hd => ?_
    have hd2 : 2 ≤ d := (mem_Icc.mp hd).1
    exact card_multiples_Ioc n H (d * d) (by nlinarith)
  have hsplit : Icc 2 M = insert 2 (Icc 3 M) := by
    ext x
    simp only [mem_Icc, mem_insert]
    omega
  have hsum : ∑ d ∈ Icc 2 M, (H / (d * d) + 1) ≤ H / 4 + H / 2 + M := by
    rw [sum_add_distrib]
    have hones : ∑ _d ∈ Icc 2 M, (1 : ℕ) = M - 1 := by
      simp only [sum_const, Nat.card_Icc, smul_eq_mul, mul_one]
      omega
    rw [hones, hsplit, sum_insert (by simp only [mem_Icc]; omega)]
    have htail : ∑ d ∈ Icc 3 M, (H / (d * d)) ≤ H / 2 :=
      (sum_div_sq_Icc H M hM).trans (Nat.sub_le _ _)
    have h22 : 2 * 2 = 4 := rfl
    rw [h22]
    omega
  have hfinal : H / 4 + H / 2 + M ≤ 7 * H / 8 := by
    dsimp [M]
    omega
  exact h1.trans (h2.trans (hsum.trans hfinal))
