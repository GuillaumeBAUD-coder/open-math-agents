import OMAStatements.S_oeis_a299154

-- Complete proof of OEIS A299154 via Dirichlet's theorem on primes in arithmetic progressions
-- Author: Paul Roulleau (@Solfanbtc) via Antigravity NEON-SWARM FACTORY v3

open OMA.S_oeis_a299154

private lemma digitSum_mod_nine (n : ℕ) : (Nat.digits 10 n).sum % 9 = n % 9 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · subst hn; simp
    · rw [Nat.digits_def' (by decide : 1 < 10) (Nat.pos_of_ne_zero hn), List.sum_cons]
      have hlt : n / 10 < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide)
      have hih := ih (n / 10) hlt
      omega

private lemma digitSum_le (n : ℕ) : (Nat.digits 10 n).sum ≤ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · subst hn; simp
    · rw [Nat.digits_def' (by decide : 1 < 10) (Nat.pos_of_ne_zero hn), List.sum_cons]
      have hlt : n / 10 < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide)
      have hih := ih (n / 10) hlt
      omega

private lemma digitSum_lt_of_ge_ten {n : ℕ} (hn : 10 ≤ n) : (Nat.digits 10 n).sum < n := by
  rw [Nat.digits_def' (by decide : 1 < 10) (by omega), List.sum_cons]
  have hle := digitSum_le (n / 10)
  omega

private lemma digitSum_pos {n : ℕ} (hn : 0 < n) : 0 < (Nat.digits 10 n).sum := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [Nat.digits_def' (by decide : 1 < 10) hn, List.sum_cons]
    by_cases hr : 0 < n % 10
    · omega
    · have hdiv : 0 < n / 10 := by omega
      have hlt : n / 10 < n := Nat.div_lt_self hn (by decide)
      have hih := ih (n / 10) hlt hdiv
      omega

private lemma digitSum_of_lt_ten {n : ℕ} (hn : n < 10) : (Nat.digits 10 n).sum = n := by
  by_cases h0 : n = 0
  · subst h0; simp
  · rw [Nat.digits_of_lt 10 n h0 hn]
    simp

private lemma iterate_digitSum_fixed {m : ℕ} (hm : m < 10) (k : ℕ) :
    (fun x => (Nat.digits 10 x).sum)^[k] m = m := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, digitSum_of_lt_ten hm]

private lemma iterate_digitSum_mod_nine (k n : ℕ) :
    (fun x => (Nat.digits 10 x).sum)^[k] n % 9 = n % 9 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', digitSum_mod_nine, ih]

private lemma iterate_digitSum_pos (k n : ℕ) (hn : 0 < n) :
    0 < (fun x => (Nat.digits 10 x).sum)^[k] n := by
  induction k with
  | zero => exact hn
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact digitSum_pos ih

private lemma iterate_digitSum_lt_ten (k n : ℕ) (hk : n ≤ k) :
    (fun x => (Nat.digits 10 x).sum)^[k] n < 10 := by
  induction k generalizing n with
  | zero =>
    have hn0 : n = 0 := by omega
    subst hn0; simp
  | succ k ih =>
    by_cases h10 : n < 10
    · rw [iterate_digitSum_fixed h10]
      exact h10
    · rw [Function.iterate_succ_apply]
      have hlt : (Nat.digits 10 n).sum < n := digitSum_lt_of_ge_ten (by omega)
      exact ih ((Nat.digits 10 n).sum) (by omega)

private lemma digitalRoot_eq_mod_nine {n : ℕ} (hn : 0 < n) (hmod : n % 9 ≠ 0) :
    digitalRoot n = n % 9 := by
  unfold digitalRoot
  have hpos : 0 < (fun x => (Nat.digits 10 x).sum)^[n] n := iterate_digitSum_pos n n hn
  have hlt : (fun x => (Nat.digits 10 x).sum)^[n] n < 10 := iterate_digitSum_lt_ten n n le_rfl
  have hm : (fun x => (Nat.digits 10 x).sum)^[n] n % 9 = n % 9 := iterate_digitSum_mod_nine n n
  omega

theorem OMA.solution : type_of% @OMA.S_oeis_a299154.main := by
  intro d hd
  have hd_props : d.Coprime 9 ∧ d < 9 ∧ d ≠ 0 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  obtain ⟨hcop, hd_lt, hd_ne0⟩ := hd_props
  refine Set.infinite_of_forall_exists_gt ?_
  intro N
  obtain ⟨p, hp_gt, hp_prime, hp_mod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq N (q := 9) (a := d) (by decide) hcop
  refine ⟨p, ⟨hp_prime, ?_⟩, hp_gt⟩
  have hpm : p % 9 = d := by
    rw [Nat.ModEq, Nat.mod_eq_of_lt hd_lt] at hp_mod
    exact hp_mod
  rw [digitalRoot_eq_mod_nine hp_prime.pos (by omega), hpm]
