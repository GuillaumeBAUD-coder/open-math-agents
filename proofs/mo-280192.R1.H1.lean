import OMAReductions.R_mo_280192_R1

/-!
Proof of `mo-280192.R1.H1`: for every `k ∈ {2, ..., 4096}`, with `m = (3^k - 1) / 2^k + 1`,
we have `3^k + m ≤ 2^k * m`.

Since `3^k` is odd and `2^k` is even for `k ≥ 1`, `2^k` does not divide `3^k`, so
`(3^k - 1) / 2^k = 3^k / 2^k`, and the inequality is equivalent to
`3^k % 2^k + 3^k / 2^k + 1 ≤ 2^k`. We verify all `4096` values `k = 2, ..., 4097`
via a balanced binary-tree kernel evaluator of depth 6 over blocks of 64 steps, using
repeated squaring for block jumps so no large exponentiation occurs.
-/

namespace OMAmo280192H1

private def checkStep (p3 p2 : ℕ) : Bool :=
  Nat.ble (p3 % p2 + p3 / p2 + 1) p2

private def checkBlock : ℕ → ℕ → ℕ → Bool
  | 0, _, _ => true
  | n + 1, p3, p2 => checkStep p3 p2 && checkBlock n (3 * p3) (2 * p2)

private def sqPow : ℕ → ℕ → ℕ
  | 0, a => a
  | d + 1, a =>
    let x := sqPow d a
    x * x

private def checkTree : ℕ → ℕ → ℕ → Bool
  | 0, p3, p2 => checkBlock 64 p3 p2
  | d + 1, p3, p2 =>
    checkTree d p3 p2 && checkTree d (p3 * sqPow d (3 ^ 64)) (p2 * sqPow d (2 ^ 64))

private lemma sqPow_eq (d a : ℕ) : sqPow d a = a ^ (2 ^ d) := by
  induction d with
  | zero => simp [sqPow]
  | succ d ih =>
    simp only [sqPow, ih]
    rw [pow_succ, pow_mul, sq]

private lemma checkBlock_sound (n k : ℕ) (h : checkBlock n (3 ^ k) (2 ^ k) = true) :
    ∀ j < n, 3 ^ (k + j) % 2 ^ (k + j) + 3 ^ (k + j) / 2 ^ (k + j) + 1 ≤ 2 ^ (k + j) := by
  induction n generalizing k with
  | zero => intro j hj; omega
  | succ n ih =>
    simp only [checkBlock, Bool.and_eq_true] at h
    obtain ⟨h0, hrest⟩ := h
    have hnext : checkBlock n (3 ^ (k + 1)) (2 ^ (k + 1)) = true := by
      simpa only [pow_succ'] using hrest
    intro j hj
    cases j with
    | zero =>
      simp only [Nat.add_zero]
      exact Nat.le_of_ble_eq_true h0
    | succ j =>
      have h1 := ih (k + 1) hnext j (by omega)
      have heq : k + (j + 1) = k + 1 + j := by omega
      rw [heq]
      exact h1

private lemma checkTree_sound (d k : ℕ) (h : checkTree d (3 ^ k) (2 ^ k) = true) :
    ∀ j < 64 * 2 ^ d,
      3 ^ (k + j) % 2 ^ (k + j) + 3 ^ (k + j) / 2 ^ (k + j) + 1 ≤ 2 ^ (k + j) := by
  induction d generalizing k with
  | zero =>
    simpa [checkTree] using checkBlock_sound 64 k h
  | succ d ih =>
    simp only [checkTree, Bool.and_eq_true, sqPow_eq, ← pow_mul] at h
    obtain ⟨hl, hr⟩ := h
    have hr' : checkTree d (3 ^ (k + 64 * 2 ^ d)) (2 ^ (k + 64 * 2 ^ d)) = true := by
      simpa only [pow_add] using hr
    intro j hj
    by_cases hlt : j < 64 * 2 ^ d
    · exact ih k hl j hlt
    · have hj' : j - 64 * 2 ^ d < 64 * 2 ^ d := by
        rw [pow_succ] at hj
        omega
      have h2 := ih (k + 64 * 2 ^ d) hr' (j - 64 * 2 ^ d) hj'
      have heq : k + j = k + 64 * 2 ^ d + (j - 64 * 2 ^ d) := by omega
      rw [heq]
      exact h2

set_option maxHeartbeats 4000000 in
private lemma cert_4096 : checkTree 6 (3 ^ 2) (2 ^ 2) = true := by
  decide

private lemma odd_three_pow (k : ℕ) : 3 ^ k % 2 = 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ]
    omega

private lemma div_sub_one_eq (k : ℕ) (hk : 1 ≤ k) : (3 ^ k - 1) / 2 ^ k = 3 ^ k / 2 ^ k := by
  have hodd : 3 ^ k % 2 = 1 := odd_three_pow k
  have h2dvd : 2 ∣ 2 ^ k := dvd_pow_self 2 (by omega)
  have hrem_ne : 3 ^ k % 2 ^ k ≠ 0 := by
    intro h0
    have hdvd : 2 ∣ 3 ^ k := dvd_trans h2dvd (Nat.dvd_of_mod_eq_zero h0)
    omega
  have hpos : 0 < 3 ^ k % 2 ^ k := Nat.pos_of_ne_zero hrem_ne
  have h2pos : 0 < 2 ^ k := Nat.pow_pos (by decide)
  have hdm : 2 ^ k * (3 ^ k / 2 ^ k) + 3 ^ k % 2 ^ k = 3 ^ k := Nat.div_add_mod (3 ^ k) (2 ^ k)
  have hsub : 3 ^ k - 1 = (3 ^ k % 2 ^ k - 1) + 2 ^ k * (3 ^ k / 2 ^ k) := by omega
  rw [hsub, Nat.add_mul_div_left _ _ h2pos]
  have hlt : 3 ^ k % 2 ^ k - 1 < 2 ^ k := by
    have := Nat.mod_lt (3 ^ k) h2pos
    omega
  rw [Nat.div_eq_of_lt hlt, Nat.zero_add]

end OMAmo280192H1

theorem OMA.solution : OMA.R_mo_280192_R1.H1 := by
  intro i
  dsimp only
  have hbound := OMAmo280192H1.checkTree_sound 6 2 OMAmo280192H1.cert_4096 i.val (by omega)
  have hk : 1 ≤ i.val + 2 := by omega
  have heq_k : 2 + i.val = i.val + 2 := by omega
  rw [heq_k] at hbound
  rw [OMAmo280192H1.div_sub_one_eq (i.val + 2) hk]
  have hdm : 2 ^ (i.val + 2) * (3 ^ (i.val + 2) / 2 ^ (i.val + 2)) + 3 ^ (i.val + 2) % 2 ^ (i.val + 2)
      = 3 ^ (i.val + 2) := Nat.div_add_mod _ _
  rw [Nat.mul_add, Nat.mul_one]
  omega
