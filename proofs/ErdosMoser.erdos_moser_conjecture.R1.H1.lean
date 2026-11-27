import OMAReductions.R_ErdosMoser_erdos_moser_conjecture_R1

-- Step ErdosMoser.erdos_moser_conjecture.R1.H1: hypothesis H1 of reduction ErdosMoser.erdos_moser_conjecture.R1
-- Credit: @DeepDuke
-- H1 := ∀ k m : ℕ, 0 < k → 0 < m → Odd k → ErdosMoser.powerSum k m = m ^ k → k = 1 ∧ m = 3

theorem OMA.solution : OMA.R_ErdosMoser_erdos_moser_conjecture_R1.H1 := by
  intro k m hk hm hodd he
  have hr : ErdosMoser.powerSum k m = ∑ i ∈ Finset.range m, i^k := by
    unfold ErdosMoser.powerSum
    apply Finset.sum_subset
    · intro i hi
      simp only [Finset.mem_Ico, Finset.mem_range] at *
      omega
    · intro i hi hn
      have : i = 0 := by
        simp only [Finset.mem_Ico, Finset.mem_range] at *
        omega
      simp [this, Nat.zero_pow hk]
  rw [hr] at he
  let d := m-1
  let S : ZMod d := ∑ i ∈ Finset.range m, (i : ZMod d)^k
  have hs : S = -S := by
    change (∑ i ∈ Finset.range m, (i : ZMod d)^k) = _
    rw [← Finset.sum_range_reflect (fun i => (i : ZMod d)^k) m]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have ha : m-1-i+i = d := by dsimp [d]; omega
    have hc : ((m-1-i : ℕ) : ZMod d) + i = 0 := by
      have hh := congrArg (fun n : ℕ => (n : ZMod d)) ha
      simpa only [Nat.cast_add, ZMod.natCast_self] using hh
    have hn : ((m-1-i : ℕ) : ZMod d) = -(i : ZMod d) := by
      linear_combination hc
    rw [hn, hodd.neg_pow]
  have hmcast : (m : ZMod d) = 1 := by
    have h : m = d+1 := by dsimp [d]; omega
    rw [h, Nat.cast_add, Nat.cast_one, ZMod.natCast_self, zero_add]
  have hS : S = 1 := by
    have hh := congrArg (fun n : ℕ => (n : ZMod d)) he
    simpa only [Nat.cast_sum, Nat.cast_pow, hmcast, one_pow] using hh
  rw [hS] at hs
  have htwo : (2 : ZMod d) = 0 := by linear_combination hs
  have hdvd : d ∣ 2 := (ZMod.natCast_eq_zero_iff 2 d).mp htwo
  have hbound := Nat.le_of_dvd (by decide : 0 < 2) hdvd
  have hm3 : m ≤ 3 := by dsimp [d] at hbound; omega
  have hlarge : 2 < m := by
    by_contra! hsmall
    have htwo : 1 < 2^k := Nat.one_lt_pow (by omega) (by decide)
    interval_cases m <;> norm_num [Finset.sum_range_succ, Nat.zero_pow hk] at he <;> omega
  have hmval : m = 3 := by omega
  subst m
  norm_num [Finset.sum_range_succ, Nat.zero_pow hk] at he
  have gap (t : ℕ) : 1 + 2^(t+2) < 3^(t+2) := by
    induction t with
    | zero => norm_num
    | succ t ih =>
      rw [show t+1+2 = (t+2)+1 by omega,
        pow_succ (2 : ℕ) (t+2), pow_succ (3 : ℕ) (t+2)]
      omega
  have hkval : k = 1 := by
    by_contra! hne
    obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le (by omega : 2 ≤ k)
    have h := gap t
    rw [show t+2 = k by omega] at h
    omega
  exact ⟨hkval, rfl⟩

