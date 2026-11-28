import OMAStatements.S_oeis_a002814

namespace OMA.S_oeis_a002814

-- Agent A
theorem a_succ_succ (k : ℕ) : a (k + 2) = a (k + 1) ^ 3 + 3 * a (k + 1) ^ 2 - 3 := by
  rw [a]

/-- a (m+n+1) ≡ a (m+1) mod (a (n+1) - 2). -/
theorem a_modEq (m n : ℕ) : a (m + n + 1) ≡ a (m + 1) [ZMOD (a (n + 1) - a 1)] := by
  induction m with
  | zero =>
    have h : a (n + 1) ≡ a 1 [ZMOD (a (n + 1) - a 1)] :=
      (Int.modEq_iff_dvd.mpr (by simp)).symm
    simpa using h
  | succ m ih =>
    have e1 : m + 1 + n + 1 = (m + n) + 2 := by omega
    rw [e1, a_succ_succ, a_succ_succ]
    have ih' : a (m + n + 1) ≡ a (m + 1) [ZMOD (a (n + 1) - a 1)] := ih
    exact ((ih'.pow 3).add ((ih'.pow 2).mul_left 3)).sub rfl

theorem a_dvd_sub (m n : ℕ) : (a (n + 1) - a 1) ∣ (a (m + n + 1) - a (m + 1)) :=
  (Int.ModEq.dvd (a_modEq m n).symm)

-- Agent B
/-- If `a ∣ b' - b` then `gcd a b' = gcd a b`. -/
theorem int_gcd_eq_of_dvd_sub {a b b' : ℤ} (h : a ∣ b' - b) :
    Int.gcd a b' = Int.gcd a b := by
  obtain ⟨k, hk⟩ := h
  have hb : b' = b + k * a := by rw [mul_comm]; linarith
  rw [hb, Int.gcd_add_mul_right_right]

/-- `gcd (c n) (c (k * n + r)) = gcd (c n) (c r)`. -/
theorem gcd_mul_add (c : ℕ → ℤ) (h : ∀ m n : ℕ, c n ∣ c (m + n) - c m)
    (n r : ℕ) : ∀ k : ℕ, Int.gcd (c n) (c (k * n + r)) = Int.gcd (c n) (c r)
  | 0 => by simp
  | k + 1 => by
    have e : (k + 1) * n + r = (k * n + r) + n := by ring
    rw [e, int_gcd_eq_of_dvd_sub (h _ _)]
    exact gcd_mul_add c h n r k

theorem strongDiv_of_dvd_sub (c : ℕ → ℤ) (h0 : c 0 = 0)
    (h : ∀ m n : ℕ, c n ∣ c (m + n) - c m) :
    ∀ n m : ℕ, Int.gcd (c n) (c m) = (c (Nat.gcd n m)).natAbs := by
  intro n m
  induction n, m using Nat.gcd.induction with
  | H0 m => simp [h0]
  | H1 n m _ ih =>
    have e : m = (m / n) * n + m % n := by
      rw [mul_comm]; exact (Nat.div_add_mod m n).symm
    rw [Nat.gcd_rec, ← ih, Int.gcd_comm (c (m % n)), e, gcd_mul_add c h, ← e]


theorem two_le_a (n : ℕ) : 2 ≤ a (n + 1) := by
  induction n with
  | zero => simp [a]
  | succ k ih =>
    show 2 ≤ a (k + 1) ^ 3 + 3 * a (k + 1) ^ 2 - 3
    nlinarith [ih, sq_nonneg (a (k + 1)), mul_le_mul ih ih (by norm_num) (by linarith)]

end OMA.S_oeis_a002814

open OMA.S_oeis_a002814

theorem OMA.solution : type_of% @OMA.S_oeis_a002814.main := by
  intro n m _ _
  have key := strongDiv_of_dvd_sub (fun k => a (k + 1) - a 1) (by simp)
    (fun m n => by
      have := a_dvd_sub m n
      simpa [sub_sub_sub_cancel_right] using this) n m
  rw [key, Int.natAbs_of_nonneg]
  have := two_le_a (Nat.gcd n m)
  have h1 : a 1 = 2 := rfl
  linarith
