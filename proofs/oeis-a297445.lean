import OMAStatements.S_oeis_a297445

namespace OMA.S_oeis_a297445




/-- The explicit solution: b(n+2) = 9 b(n) + 2, base-3 digits 1 0 2 0 2 ... or 1 2 0 2 .... -/
def b : ℕ → ℕ
  | 0 => 1
  | 1 => 5
  | n + 2 => 9 * b n + 2

lemma a_eq_b (n : ℕ) : a n = b n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => rfl
    | 1, _ => rfl
    | 2, _ => rfl
    | n + 3, ih =>
      rw [a, ih (n + 2) (by omega), ih (n + 1) (by omega), ih n (by omega)]
      simp only [b]
      push_cast
      ring

lemma b_succ_succ (n : ℕ) : b (n + 2) = 9 * b n + 2 := rfl

lemma b_pos (n : ℕ) : 1 ≤ b n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | n
    · simp [b]
    · simp [b]
    · rw [b_succ_succ]; omega

lemma b_lt_succ (n : ℕ) : b n < b (n + 1) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | n
    · simp [b]
    · simp [b]
    · have := ih n (by omega)
      rw [b_succ_succ, show n + 2 + 1 = (n + 1) + 2 by omega, b_succ_succ]
      omega

lemma b_mono {i j : ℕ} (h : i ≤ j) : b i ≤ b j :=
  (strictMono_nat_of_lt_succ b_lt_succ).monotone h

/-- Up-variation of 3q + r in terms of q. -/
lemma upVar_step (q r : ℕ) (hq : 1 ≤ q) (hr : r < 3) : upVar (3 * q + r) = (r - q % 3) + upVar q := by
  unfold upVar
  have h1 : Nat.digits 3 (3 * q + r) = r :: Nat.digits 3 q := by
    rw [Nat.digits_def' (by norm_num) (by omega)]
    congr 2 <;> omega
  have h2 : Nat.digits 3 q = q % 3 :: Nat.digits 3 (q / 3) := Nat.digits_def' (by norm_num) (by omega)
  rw [h1, h2, upv]

lemma upVar_small (m : ℕ) (h1 : 1 ≤ m) (h3 : m < 3) : upVar m = 0 := by
  unfold upVar
  rw [Nat.digits_def' (by norm_num) (by omega), Nat.div_eq_of_lt h3]
  simp [upv]

lemma upVar_b (n : ℕ) : upVar (b n) = n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | n
    · decide
    · decide
    · have hb := b_pos n
      rw [b_succ_succ, show 9 * b n + 2 = 3 * (3 * b n) + 2 by ring,
        upVar_step _ _ (by omega) (by norm_num), show 3 * b n = 3 * b n + 0 by ring,
        upVar_step _ _ hb (by norm_num), ih n (by omega)]
      have h0 : (3 * b n + 0) % 3 = 0 := by omega
      rw [h0]
      omega

/-- The least m with up-variation n and last digit d (as shown by the invariant below). -/
def E (n d : ℕ) : ℕ :=
  if d = 0 then 3 * b n
  else if d = 1 then (if n = 0 then 1 else min (3 * b n + 1) (9 * b (n - 1) + 1))
  else (if n = 0 then 2 else b n)

lemma E0 (n : ℕ) : E n 0 = 3 * b n := by simp [E]
lemma E1z : E 0 1 = 1 := by simp [E]
lemma E1s (n : ℕ) : E (n + 1) 1 = min (3 * b (n + 1) + 1) (9 * b n + 1) := by simp [E]
lemma E2z : E 0 2 = 2 := by simp [E]
lemma E2s (n : ℕ) : E (n + 1) 2 = b (n + 1) := by simp [E]

lemma b_le_E (n d : ℕ) (hd : d < 3) : b n ≤ E n d := by
  interval_cases d
  · rw [E0]; omega
  · rcases n with _ | n
    · rw [E1z]; simp [b]
    · rw [E1s]
      apply le_min (by omega)
      rcases n with _ | k
      · simp [b]
      · rw [b_succ_succ]
        have := b_lt_succ k
        omega
  · rcases n with _ | n
    · rw [E2z]; simp [b]
    · rw [E2s]

lemma E_step (k d r : ℕ) (hd : d < 3) (hr : r < 3) : E (k + (r - d)) r ≤ 3 * E k d + r := by
  have hbk := b_le_E k d hd
  interval_cases r
  · rw [show k + (0 - d) = k by omega, E0]
    omega
  · interval_cases d
    · rw [show k + (1 - 0) = k + 1 by omega, E1s, E0]
      omega
    · rw [show k + (1 - 1) = k by omega]
      omega
    · rw [show k + (1 - 2) = k by omega]
      rcases k with _ | k
      · rw [E1z]; omega
      · rw [E1s, E2s]; omega
  · interval_cases d
    · rw [show k + (2 - 0) = (k + 1) + 1 by omega, E2s, show k + 1 + 1 = k + 2 by omega,
        b_succ_succ, E0]
      omega
    · rw [show k + (2 - 1) = k + 1 by omega, E2s]
      rcases k with _ | j
      · rw [E1z]; simp [b]
      · rw [E1s, show j + 1 + 1 = j + 2 by omega, b_succ_succ]
        have h2 := b_lt_succ j
        omega
    · rw [show k + (2 - 2) = k by omega]
      omega

/-- The invariant: every m >= 1 is at least E(UV(m), m mod 3). -/
lemma E_le (m : ℕ) (hm : 1 ≤ m) : E (upVar m) (m % 3) ≤ m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases Nat.lt_or_ge m 3 with h3 | h3
    · rw [upVar_small m hm h3]
      interval_cases m <;> decide
    · have hq : 1 ≤ m / 3 := by omega
      have hr : m % 3 < 3 := Nat.mod_lt _ (by norm_num)
      have hm' : m = 3 * (m / 3) + m % 3 := by omega
      have ih' := ih (m / 3) (by omega) hq
      have hs := E_step (upVar (m / 3)) ((m / 3) % 3) (m % 3) (Nat.mod_lt _ (by norm_num)) hr
      rw [hm', upVar_step _ _ hq hr, show (3 * (m / 3) + m % 3) % 3 = m % 3 by omega, add_comm]
      calc E (upVar (m / 3) + (m % 3 - m / 3 % 3)) (m % 3)
          ≤ 3 * E (upVar (m / 3)) (m / 3 % 3) + m % 3 := hs
        _ ≤ 3 * (m / 3) + m % 3 := by omega

/-- Kimberling's conjecture: a(n) is the least positive integer whose base-3 up-variation is n. -/
theorem conjecture (n : ℕ) :
    ∃ m : ℕ, (m : ℤ) = a n ∧ IsLeast {k : ℕ | 0 < k ∧ upVar k = n} m := by
  refine ⟨b n, (a_eq_b n).symm, ⟨b_pos n, upVar_b n⟩, ?_⟩
  rintro k ⟨hk, hkn⟩
  have h1 := E_le k hk
  rw [hkn] at h1
  exact (b_le_E n (k % 3) (Nat.mod_lt _ (by norm_num))).trans h1

/-- Controls: a(0..6) = 1, 5, 11, 47, 101, 425, 911 as in the entry. -/
lemma controls : (List.range 7).map a = [1, 5, 11, 47, 101, 425, 911] := by decide

end OMA.S_oeis_a297445

theorem OMA.solution : type_of% @OMA.S_oeis_a297445.main :=
  fun n => OMA.S_oeis_a297445.conjecture n
