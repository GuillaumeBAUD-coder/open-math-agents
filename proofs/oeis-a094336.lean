import OMAStatements.S_oeis_a094336

namespace OMA.A094336Proof

open Finset Nat OMA.S_oeis_a094336

private def low (n : ℕ) : ℕ := n * (n - 1) / 2 + 1

private theorem block_lower (n : ℕ) : low n ^ n ≤ blockProd n := by
  calc
    low n ^ n = ∏ _ ∈ range n, low n := by simp
    _ ≤ blockProd n := by
      unfold blockProd
      apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
      intro i _
      exact Nat.le_add_right _ _

private theorem low_pos (n : ℕ) : 0 < low n := by unfold low; omega

private theorem block_pos (n : ℕ) : 0 < blockProd n :=
  (pow_pos (low_pos n) n).trans_le (block_lower n)

private theorem factorial_too_small {n k : ℕ} (hn : 128 ≤ n) (hk : 2 * k ≤ 3 * n) :
    k.factorial < blockProd n := by
  have hq : 42 ≤ n / 3 := by omega
  have hnq : n ≤ 3 * (n / 3) + 2 := by omega
  have hq2 : 8 * n < (n / 3) ^ 2 := by
    nlinarith [Nat.mul_le_mul_right (n / 3) hq]
  have hlower : n * (n / 3) ≤ low n := by
    unfold low
    have hmul : n * (n / 3) * 2 ≤ n * (n - 1) := by
      rw [Nat.mul_assoc]
      exact Nat.mul_le_mul_left _ (by omega)
    have hb := (Nat.le_div_iff_mul_le (by decide : 0 < 2)).2 hmul
    omega
  have hg : (2 * n) ^ 3 < low n ^ 2 := by
    calc
      (2 * n) ^ 3 = n ^ 2 * (8 * n) := by ring
      _ < n ^ 2 * (n / 3) ^ 2 := Nat.mul_lt_mul_of_pos_left hq2 (by positivity)
      _ = (n * (n / 3)) ^ 2 := by ring
      _ ≤ low n ^ 2 := Nat.pow_le_pow_left hlower 2
  have hb : (2 * n) ^ (3 * n) < blockProd n ^ 2 := by
    calc
      (2 * n) ^ (3 * n) = ((2 * n) ^ 3) ^ n := by rw [pow_mul]
      _ < (low n ^ 2) ^ n := Nat.pow_lt_pow_left hg (by omega)
      _ = (low n ^ n) ^ 2 := by rw [← pow_mul, ← pow_mul, Nat.mul_comm 2 n]
      _ ≤ blockProd n ^ 2 := Nat.pow_le_pow_left (block_lower n) 2
  have hf : k.factorial ^ 2 ≤ (2 * n) ^ (3 * n) := by
    calc
      k.factorial ^ 2 ≤ (k ^ k) ^ 2 := Nat.pow_le_pow_left (Nat.factorial_le_pow k) 2
      _ ≤ ((2 * n) ^ k) ^ 2 := Nat.pow_le_pow_left
        (Nat.pow_le_pow_left (by omega) k) 2
      _ = (2 * n) ^ (2 * k) := by rw [← pow_mul, Nat.mul_comm k 2]
      _ ≤ (2 * n) ^ (3 * n) := Nat.pow_le_pow_right (by omega) hk
  by_contra! bad
  exact (not_lt_of_ge (Nat.pow_le_pow_left bad 2)) (hf.trans_lt hb)

private theorem small_log_bound (n : ℕ) (hn : 128 ≤ n) : n ^ 2 < 2 ^ (n / 4) := by
  have hstep : ∀ t : ℕ, 32 ≤ t → (4 * t + 3) ^ 2 < 2 ^ t := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => decide
    | succ t ht iht =>
      calc
        (4 * (t + 1) + 3) ^ 2 ≤ 2 * (4 * t + 3) ^ 2 := by
          nlinarith [Nat.mul_le_mul_right t ht]
        _ < 2 * 2 ^ t := Nat.mul_lt_mul_of_pos_left iht (by decide)
        _ = 2 ^ (t + 1) := (pow_succ' 2 t).symm
  exact (Nat.pow_le_pow_left (show n ≤ 4 * (n / 4) + 3 by omega) 2).trans_lt
    (hstep (n / 4) (by omega))

private theorem block_eq_choose (n : ℕ) :
    blockProd n = n.factorial * (low n + n - 1).choose n := by
  unfold blockProd low
  rw [← Nat.ascFactorial_eq_prod_range, Nat.ascFactorial_eq_factorial_mul_choose']

private theorem upper_le_square (n : ℕ) (hn : 0 < n) : low n + n - 1 ≤ n ^ 2 := by
  have hmul : n * (n - 1) + n = n ^ 2 := by
    calc
      n * (n - 1) + n = n * (n - 1 + 1) := by ring
      _ = n ^ 2 := by rw [Nat.sub_add_cancel hn, pow_two]
  have hd := Nat.div_le_self (n * (n - 1)) 2
  unfold low
  omega

private theorem factorial_val_lower {n k : ℕ} (hk : n ≤ k) :
    k / 2 - n / 2 ≤ k.factorial.factorization 2 - n.factorial.factorization 2 := by
  let b := Nat.log 2 k + 2
  have hb : Nat.log 2 k < b := by dsimp [b]; omega
  have hnb : Nat.log 2 n < b := (Nat.log_mono_right hk).trans_lt hb
  rw [Nat.factorization_factorial Nat.prime_two hb, Nat.factorization_factorial Nat.prime_two hnb,
    ← Finset.sum_tsub_distrib _ (fun i _ => Nat.div_le_div_right hk)]
  have h1 : 1 ∈ Ico 1 b := by simp [b]
  have h := Finset.single_le_sum (f := fun i => k / 2 ^ i - n / 2 ^ i)
    (fun _ _ => Nat.zero_le _) h1
  simpa using h

private theorem block_not_factorial_large {n k : ℕ} (hn : 128 ≤ n) :
    blockProd n ≠ k.factorial := by
  intro heq
  have hbig : 3 * n < 2 * k := by
    by_contra! h
    exact (_root_.ne_of_lt (factorial_too_small hn h)) heq.symm
  have hnk : n ≤ k := by omega
  let m := low n + n - 1
  have hm : n ≤ m := by dsimp [m]; have := low_pos n; omega
  have hvalEq : k.factorial.factorization 2 =
      n.factorial.factorization 2 + (m.choose n).factorization 2 := by
    rw [← heq, block_eq_choose]
    exact congrArg (fun f : ℕ →₀ ℕ => f 2)
      (Nat.factorization_mul n.factorial_ne_zero (Nat.choose_ne_zero hm))
  have hvalLow := factorial_val_lower hnk
  have hvalUp : (m.choose n).factorization 2 ≤ Nat.log 2 m := Nat.factorization_choose_le_log
  have hlog : Nat.log 2 m < n / 4 :=
    (Nat.log_lt_iff_lt_pow (by decide : 1 < 2) (by omega : m ≠ 0)).2
      ((upper_le_square n (by omega)).trans_lt (small_log_bound n hn))
  omega

private def smallBounds : List ℕ := [0, 0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26, 28, 30, 32, 34, 36, 38, 40, 42, 44, 46, 48, 50, 52, 54, 56, 58, 60, 62, 64, 66, 68, 70, 72, 74, 76, 78, 80, 82, 84, 86, 88, 90, 92, 94, 96, 98, 100, 102, 104, 106, 108, 110, 112, 114, 116, 118, 120, 122, 124, 126, 128, 130, 132, 134, 136, 138, 140, 142, 144, 146, 148, 150, 152, 154, 156, 158, 160, 162, 164, 166, 168, 169, 171, 173, 175, 177, 179, 181, 183, 185, 187, 189, 191, 193, 195, 197, 199, 201, 203, 205, 207, 209, 211, 213, 215, 217, 219, 221, 223, 225, 227, 229, 231, 233, 235, 237, 239, 241, 243, 245, 247, 249, 251]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 12000 in
private theorem small_certificate :
    ∀ n : Fin 128, 4 < n.val →
      (smallBounds.getD n.val 0).factorial < blockProd n.val ∧
      blockProd n.val < (smallBounds.getD n.val 0 + 1).factorial := by
  decide

private theorem block_not_factorial {n k : ℕ} (hn : 4 < n) : blockProd n ≠ k.factorial := by
  by_cases h : 128 ≤ n
  · exact block_not_factorial_large h
  · obtain ⟨hlo, hhi⟩ := small_certificate ⟨n, by omega⟩ hn
    intro heq
    rw [heq] at hlo hhi
    have h₁ : smallBounds.getD n 0 < k := by
      by_contra! hle
      exact (not_le_of_gt hlo) (Nat.factorial_le hle)
    have h₂ : k < smallBounds.getD n 0 + 1 :=
      lt_of_not_ge fun hle => (not_le_of_gt hhi) (Nat.factorial_le hle)
    omega

end OMA.A094336Proof

open OMA.S_oeis_a094336 in
theorem OMA.solution : type_of% @OMA.S_oeis_a094336.main := by
  intro n hn
  have hp := OMA.A094336Proof.block_pos n
  have hne : {k : ℕ | k.factorial ∣ blockProd n}.Nonempty := ⟨0, by simp⟩
  have hb : BddAbove {k : ℕ | k.factorial ∣ blockProd n} := by
    refine ⟨blockProd n, ?_⟩
    intro k h
    exact (Nat.self_le_factorial k).trans (Nat.le_of_dvd hp h)
  have hd : (largestFact n).factorial ∣ blockProd n := Nat.sSup_mem hne hb
  have hl : (largestFact n).factorial < blockProd n :=
    lt_of_le_of_ne (Nat.le_of_dvd hp hd)
      (Ne.symm (OMA.A094336Proof.block_not_factorial hn))
  obtain ⟨q, hq⟩ := hd
  unfold a
  rw [hq, Nat.mul_div_cancel_left _ (Nat.factorial_pos _)]
  by_contra! hc
  exact (not_le_of_gt hl) (hq.trans_le (by simpa using Nat.mul_le_mul_left (largestFact n).factorial hc))
