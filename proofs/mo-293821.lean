import OMAStatements.S_mo_293821

-- Problem: MathOverflow 293821: a recursion for the total number of 1's in the binary expansions
-- of 0, ..., n.
-- Proof: with s(i) the binary digit sum and T(m) = Σ_{i<m} s(i), complementing bits gives
-- s(i) + s(2^k - 1 - i) = k for i < 2^k. Summing gives T(2^k) = k 2^(k-1) and
-- T(m) = T(2^k - m) + k (m - 2^(k-1)) for 2^(k-1) < m ≤ 2^k, which is the recursion.
-- The recursion determines a, so a = T by strong induction.

namespace OMA.Proof_mo_293821

def s (i : ℕ) : ℕ := (Nat.digits 2 i).sum

def T (m : ℕ) : ℕ := ∑ i ∈ Finset.range m, s i

lemma s_eq (n : ℕ) : s n = n % 2 + s (n / 2) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [s]
  · unfold s
    rw [Nat.digits_def' (by norm_num) hn, List.sum_cons]

lemma s_compl (k : ℕ) : ∀ i, i < 2 ^ k → s i + s (2 ^ k - 1 - i) = k := by
  induction k with
  | zero =>
    intro i hi
    have : i = 0 := by simpa using hi
    subst this; simp [s]
  | succ k ih =>
    intro i hi
    have hp : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
    have hpos : 0 < 2 ^ k := pow_pos (by norm_num) k
    rw [s_eq i, s_eq (2 ^ (k + 1) - 1 - i)]
    have h1 : i / 2 < 2 ^ k := by omega
    have h2 : (2 ^ (k + 1) - 1 - i) / 2 = 2 ^ k - 1 - i / 2 := by omega
    have h3 : i % 2 + (2 ^ (k + 1) - 1 - i) % 2 = 1 := by omega
    rw [h2]
    have := ih (i / 2) h1
    omega

lemma T_pow (k : ℕ) : 2 * T (2 ^ k) = k * 2 ^ k := by
  have h := Finset.sum_range_reflect s (2 ^ k)
  unfold T
  have hsum : ∑ i ∈ Finset.range (2 ^ k), (s i + s (2 ^ k - 1 - i)) = k * 2 ^ k := by
    rw [Finset.sum_congr rfl (fun i hi => s_compl k i (Finset.mem_range.mp hi))]
    simp [mul_comm]
  rw [Finset.sum_add_distrib, h] at hsum
  omega

lemma T_split (k m : ℕ) (hm : m ≤ 2 ^ k) :
    T (2 ^ k) + T (2 ^ k - m) = T m + k * (2 ^ k - m) := by
  set L := 2 ^ k - m with hL
  have hmL : 2 ^ k = m + L := by omega
  have e1 : T (2 ^ k) = T m + ∑ j ∈ Finset.range L, s (m + j) := by
    unfold T; rw [hmL, Finset.sum_range_add]
  have e2 : ∑ j ∈ Finset.range L, s (m + j) = ∑ j ∈ Finset.range L, s (2 ^ k - 1 - j) := by
    rw [← Finset.sum_range_reflect]
    apply Finset.sum_congr rfl
    intro j hj
    have := Finset.mem_range.mp hj
    congr 1; omega
  have e3 : ∑ j ∈ Finset.range L, s (2 ^ k - 1 - j) + T L = k * L := by
    unfold T
    rw [← Finset.sum_add_distrib,
      Finset.sum_congr rfl (fun j hj => (show s (2 ^ k - 1 - j) + s j = k by
        rw [add_comm]; exact s_compl k j (by have := Finset.mem_range.mp hj; omega)))]
    simp [mul_comm]
  omega

lemma T_rec (k m : ℕ) (hk : 1 ≤ k) (h1 : 2 ^ (k - 1) < m) (h2 : m ≤ 2 ^ k) :
    T m = T (2 ^ k - m) + k * (m - 2 ^ (k - 1)) := by
  have hp : 2 ^ k = 2 * 2 ^ (k - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hs := T_split k m h2
  have ht := T_pow k
  rw [hp] at hs ht
  set K := 2 ^ (k - 1)
  have hTK : T (2 * K) = k * K := by nlinarith
  rw [hTK] at hs
  have e : k * (2 * K - m) + k * (m - K) = k * K := by
    rw [← mul_add]; congr 1; omega
  rw [hp]
  linarith

end OMA.Proof_mo_293821

open OMA.Proof_mo_293821 in
theorem OMA.solution : type_of% @OMA.S_mo_293821.main := by
  intro a h0 h1 h2 hrec
  have key : ∀ m, a m = T m := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      rcases Nat.lt_or_ge m 2 with hm | hm
      · interval_cases m
        · simp [h0, T]
        · simp [h1, T, s]
      · set k := Nat.log 2 (m - 1) + 1 with hk
        have hlo : 2 ^ (k - 1) ≤ m - 1 := by
          rw [hk, Nat.add_sub_cancel]; exact Nat.pow_log_le_self 2 (by omega)
        have hhi : m - 1 < 2 ^ k := Nat.lt_pow_succ_log_self (by norm_num) _
        have hlt : 2 ^ (k - 1) < m := by omega
        have hle : m ≤ 2 ^ k := by omega
        rw [hrec k m (by omega) hlt hle, T_rec k m (by omega) hlt hle]
        congr 1
        apply ih
        have : 2 ^ k = 2 * 2 ^ (k - 1) := by
          rw [← pow_succ']; exact congrArg (2 ^ ·) (by omega)
        omega
  intro n
  rw [key]; rfl
