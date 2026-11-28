import OMAStatements.S_oeis_a161580

-- Problem: A161580: Positions n such that A010060(n) + A010060(n+3) = 1.
-- Upstream: formal-conjectures statements/oeis-a161580.lean:0 (declaration OMA.S_oeis_a161580.main)
-- Credit: @oceancheol (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
--
-- Proof. Let t = A010060 (Thue-Morse), u(n) = 1 - 2 t(n) and S(N) = sum_{j<N} u(j).
-- As t(2m) + t(2m+1) = 1, S(2m) = 0 and S(2m+1) is 1 or -1; so for odd k, S(a) - S(a+k) is
-- 1 or -1 for every a (S_sub). Put f(j) = u(j) - u(j+k): f(j) = 2 u(j) if t(j) + t(j+k) = 1 and
-- f(j) = 0 otherwise. For consecutive solutions n < m, the sum of f over n <= j <= m is
-- 2 u(n) + 2 u(m), and by telescoping (tele) it is (S(m+1) - S(m+1+k)) - (S(n) - S(n+k)),
-- which lies in {-2, 0, 2}. Hence u(n) + u(m) = 0, that is t(m) != t(n).
-- Remark: this is Shevelev's conjecture from the OEIS entry (2009). I did not find a proof in
-- the literature, but did not search it exhaustively.

namespace OMA.A161580

open Finset OMA.S_oeis_a161580

/-- The binary digit sum. -/
def s (n : ℕ) : ℕ := (Nat.digits 2 n).sum

lemma s_double (m : ℕ) : s (2 * m) = s m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [s]
  · unfold s
    rw [Nat.digits_def' (by norm_num) (by omega)]
    have h1 : 2 * m % 2 = 0 := by omega
    have h2 : 2 * m / 2 = m := by omega
    rw [h1, h2, List.sum_cons]
    omega

lemma s_double_add_one (m : ℕ) : s (2 * m + 1) = s m + 1 := by
  unfold s
  rw [Nat.digits_def' (by norm_num) (by omega)]
  have h1 : (2 * m + 1) % 2 = 1 := by omega
  have h2 : (2 * m + 1) / 2 = m := by omega
  rw [h1, h2, List.sum_cons]
  omega

lemma t_eq (n : ℕ) : A010060 n = s n % 2 := rfl

lemma t_lt (n : ℕ) : A010060 n < 2 := by
  rw [t_eq]
  omega

lemma t_pair (m : ℕ) : A010060 (2 * m) + A010060 (2 * m + 1) = 1 := by
  rw [t_eq, t_eq, s_double, s_double_add_one]
  omega

/-- The Thue-Morse sequence with values 1 and -1. -/
def u (n : ℕ) : ℤ := 1 - 2 * (A010060 n : ℤ)

/-- Partial sums of u. -/
def S (N : ℕ) : ℤ := ∑ j ∈ range N, u j

lemma S_even (m : ℕ) : S (2 * m) = 0 := by
  induction m with
  | zero => simp [S]
  | succ m ih =>
    have e : 2 * (m + 1) = 2 * m + 1 + 1 := by ring
    rw [e]
    unfold S at ih ⊢
    rw [sum_range_succ, sum_range_succ, ih]
    have h := t_pair m
    have hz : (A010060 (2 * m) : ℤ) + (A010060 (2 * m + 1) : ℤ) = 1 := by exact_mod_cast h
    unfold u
    linarith

lemma S_odd (m : ℕ) : S (2 * m + 1) = 1 ∨ S (2 * m + 1) = -1 := by
  have h0 := S_even m
  unfold S at h0 ⊢
  rw [sum_range_succ, h0]
  have h := t_lt (2 * m)
  unfold u
  have h01 : A010060 (2 * m) = 0 ∨ A010060 (2 * m) = 1 := by omega
  rcases h01 with h1 | h1 <;> rw [h1] <;> norm_num

lemma S_sub (k a : ℕ) (hk : k % 2 = 1) : S a - S (a + k) = 1 ∨ S a - S (a + k) = -1 := by
  rcases Nat.even_or_odd' a with ⟨x, hx | hx⟩
  · obtain ⟨y, hy⟩ : ∃ y, a + k = 2 * y + 1 := ⟨(a + k) / 2, by omega⟩
    rw [hy, hx, S_even]
    rcases S_odd y with h | h <;> rw [h] <;> norm_num
  · obtain ⟨y, hy⟩ : ∃ y, a + k = 2 * y := ⟨(a + k) / 2, by omega⟩
    rw [hy, hx, S_even]
    rcases S_odd x with h | h <;> rw [h] <;> norm_num

lemma tele (k a b : ℕ) (hab : a ≤ b) :
    ∑ j ∈ Ico a b, (u j - u (j + k)) = (S b - S a) - (S (b + k) - S (a + k)) := by
  unfold S
  rw [sum_sub_distrib, sum_Ico_eq_sub _ hab, sum_Ico_add' u a b k, sum_Ico_eq_sub _ (by omega)]

end OMA.A161580

open Finset OMA.S_oeis_a161580 OMA.A161580 in
theorem OMA.solution : type_of% @OMA.S_oeis_a161580.main := by
  intro k hk n m hnm hn hm hmid
  have hf_n : u n - u (n + k) = 2 * u n := by
    have hz : (A010060 n : ℤ) + (A010060 (n + k) : ℤ) = 1 := by exact_mod_cast hn
    unfold u
    linarith
  have hf_m : u m - u (m + k) = 2 * u m := by
    have hz : (A010060 m : ℤ) + (A010060 (m + k) : ℤ) = 1 := by exact_mod_cast hm
    unfold u
    linarith
  have hmid0 : ∑ j ∈ Ico (n + 1) m, (u j - u (j + k)) = 0 := by
    apply sum_eq_zero
    intro j hj
    rw [mem_Ico] at hj
    have h1 := hmid j (by omega) (by omega)
    have h2 := t_lt j
    have h3 := t_lt (j + k)
    have h4 : A010060 j = A010060 (j + k) := by omega
    unfold u
    rw [h4]
    ring
  have hsum : ∑ j ∈ Ico n (m + 1), (u j - u (j + k)) = 2 * u n + 2 * u m := by
    rw [sum_Ico_succ_top (by omega), sum_eq_sum_Ico_succ_bot hnm, hmid0, hf_n, hf_m]
    ring
  have htele := tele k n (m + 1) (by omega)
  rw [hsum] at htele
  have hX := S_sub k (m + 1) hk
  have hY := S_sub k n hk
  intro heq
  have hu : u m = u n := by
    unfold u
    rw [heq]
  have htn := t_lt n
  have hun : u n = 1 ∨ u n = -1 := by
    unfold u
    have h01 : A010060 n = 0 ∨ A010060 n = 1 := by omega
    rcases h01 with h | h <;> rw [h] <;> norm_num
  rw [hu] at htele
  rcases hX with hX | hX <;> rcases hY with hY | hY <;> rcases hun with h | h <;>
    rw [h] at htele <;> linarith
