import OMAStatements.S_oeis_a007091
import Mathlib

-- Problem: A007091: Numbers in base 5.
-- Upstream: formal-conjectures statements/oeis-a007091.lean:0 (declaration OMA.S_oeis_a007091.main)
-- Credit: @Solfanbtc (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

private lemma digits_sum_eq_mod_add_div {b : ℕ} (hb : 1 < b) (x : ℕ) :
    (Nat.digits b x).sum = x % b + (Nat.digits b (x / b)).sum := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [Nat.digits_eq_cons_digits_div hb hx, List.sum_cons]

private lemma digits_sum_succ_le {b : ℕ} (hb : 1 < b) (k : ℕ) :
    (Nat.digits b (k + 1)).sum ≤ (Nat.digits b k).sum + 1 := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    rw [digits_sum_eq_mod_add_div hb (k + 1), digits_sum_eq_mod_add_div hb k]
    by_cases hmod : k % b + 1 < b
    · have h1 : (k + 1) % b = k % b + 1 := by
        rw [Nat.add_mod, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hmod]
      have h2 : (k + 1) / b = k / b := by
        have hk : k = b * (k / b) + k % b := (Nat.div_add_mod k b).symm
        calc (k + 1) / b
            = (b * (k / b) + (k % b + 1)) / b := by rw [← Nat.add_assoc, ← hk]
          _ = k / b + (k % b + 1) / b := Nat.mul_add_div (Nat.zero_lt_of_lt hb) (k / b) (k % b + 1)
          _ = k / b := by rw [Nat.div_eq_of_lt hmod, Nat.add_zero]
      rw [h1, h2]
      omega
    · have hkb : k % b + 1 = b := by
        have := Nat.mod_lt k (Nat.zero_lt_of_lt hb)
        omega
      have hk_pos : 0 < k := by
        by_contra h0
        have hk0 : k = 0 := by omega
        rw [hk0, Nat.zero_mod] at hkb
        omega
      have h1 : (k + 1) % b = 0 := by
        rw [Nat.add_mod, Nat.mod_eq_of_lt hb, hkb, Nat.mod_self]
      have h2 : (k + 1) / b = k / b + 1 := by
        have hk : k = b * (k / b) + k % b := (Nat.div_add_mod k b).symm
        calc (k + 1) / b
            = (b * (k / b) + (k % b + 1)) / b := by rw [← Nat.add_assoc, ← hk]
          _ = (b * (k / b) + b * 1) / b := by rw [hkb, Nat.mul_one]
          _ = (b * (k / b + 1)) / b := by rw [← Nat.mul_add]
          _ = k / b + 1 := Nat.mul_div_right (k / b + 1) (Nat.zero_lt_of_lt hb)
      have hdiv_lt : k / b < k := Nat.div_lt_self hk_pos hb
      have hih := ih (k / b) hdiv_lt
      rw [h1, h2]
      omega

private lemma digits_ten_sum_two_mul_le (n : ℕ) :
    (Nat.digits 10 (2 * n)).sum ≤ 2 * (Nat.digits 10 n).sum := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · have h10 : 1 < 10 := by decide
      rw [digits_sum_eq_mod_add_div h10 (2 * n), digits_sum_eq_mod_add_div h10 n]
      have hdiv_lt : n / 10 < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn) h10
      have hih := ih (n / 10) hdiv_lt
      have hn_eq : n = 10 * (n / 10) + n % 10 := (Nat.div_add_mod n 10).symm
      have hmod_lt : n % 10 < 10 := Nat.mod_lt n (by decide)
      by_cases hr : n % 10 < 5
      · have h1 : (2 * n) % 10 = 2 * (n % 10) := by omega
        have h2 : (2 * n) / 10 = 2 * (n / 10) := by omega
        rw [h1, h2]
        omega
      · have h1 : (2 * n) % 10 = 2 * (n % 10) - 10 := by omega
        have h2 : (2 * n) / 10 = 2 * (n / 10) + 1 := by omega
        have hstep := digits_sum_succ_le h10 (2 * (n / 10))
        rw [h1, h2]
        omega

private lemma all_digits_lt_five_iff (n : ℕ) :
    (∀ d ∈ Nat.digits 10 n, d < 5) ↔
      2 * (Nat.digits 10 n).sum = (Nat.digits 10 (2 * n)).sum := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · have h10 : 1 < 10 := by decide
      have hdig : Nat.digits 10 n = (n % 10) :: Nat.digits 10 (n / 10) :=
        Nat.digits_eq_cons_digits_div h10 hn
      have hdiv_lt : n / 10 < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn) h10
      have hih := ih (n / 10) hdiv_lt
      have hn_eq : n = 10 * (n / 10) + n % 10 := (Nat.div_add_mod n 10).symm
      have hmod_lt : n % 10 < 10 := Nat.mod_lt n (by decide)
      by_cases hr : n % 10 < 5
      · have h1 : (2 * n) % 10 = 2 * (n % 10) := by omega
        have h2 : (2 * n) / 10 = 2 * (n / 10) := by omega
        have hsum_2n : (Nat.digits 10 (2 * n)).sum =
            2 * (n % 10) + (Nat.digits 10 (2 * (n / 10))).sum := by
          rw [digits_sum_eq_mod_add_div h10 (2 * n), h1, h2]
        have hsum_n : (Nat.digits 10 n).sum = n % 10 + (Nat.digits 10 (n / 10)).sum := by
          rw [hdig, List.sum_cons]
        have hforall : (∀ d ∈ Nat.digits 10 n, d < 5) ↔
            (∀ d ∈ Nat.digits 10 (n / 10), d < 5) := by
          rw [hdig]
          constructor
          · intro h d hd
            exact h d (List.mem_cons_of_mem _ hd)
          · intro h d hd
            rcases List.mem_cons.mp hd with rfl | hd
            · exact hr
            · exact h d hd
        rw [hforall, hih, hsum_2n, hsum_n]
        omega
      · have h1 : (2 * n) % 10 = 2 * (n % 10) - 10 := by omega
        have h2 : (2 * n) / 10 = 2 * (n / 10) + 1 := by omega
        have hsum_2n : (Nat.digits 10 (2 * n)).sum =
            (2 * (n % 10) - 10) + (Nat.digits 10 (2 * (n / 10) + 1)).sum := by
          rw [digits_sum_eq_mod_add_div h10 (2 * n), h1, h2]
        have hsum_n : (Nat.digits 10 n).sum = n % 10 + (Nat.digits 10 (n / 10)).sum := by
          rw [hdig, List.sum_cons]
        have hstep := digits_sum_succ_le h10 (2 * (n / 10))
        have hle := digits_ten_sum_two_mul_le (n / 10)
        constructor
        · intro h
          exfalso
          apply hr
          exact h (n % 10) (by rw [hdig]; exact List.mem_cons_self)
        · intro heq
          exfalso
          omega

theorem OMA.solution : type_of% @OMA.S_oeis_a007091.main := by
  intro n
  rw [← all_digits_lt_five_iff n]
  constructor
  · rintro ⟨m, rfl⟩ d hd
    have hdig : Nat.digits 10 (OMA.S_oeis_a007091.a m) = Nat.digits 5 m := by
      unfold OMA.S_oeis_a007091.a
      apply Nat.digits_ofDigits 10 (by decide) (Nat.digits 5 m)
      · intro l hl
        exact (Nat.digits_lt_base (by decide) hl).trans (by decide)
      · intro hne
        exact Nat.getLast_digit_ne_zero 5 (Nat.digits_ne_nil_iff_ne_zero.mp hne)
    rw [hdig] at hd
    exact Nat.digits_lt_base (by decide) hd
  · intro hlt
    refine ⟨Nat.ofDigits 5 (Nat.digits 10 n), ?_⟩
    unfold OMA.S_oeis_a007091.a
    have hdig : Nat.digits 5 (Nat.ofDigits 5 (Nat.digits 10 n)) = Nat.digits 10 n := by
      apply Nat.digits_ofDigits 5 (by decide) (Nat.digits 10 n) hlt
      intro hne
      exact Nat.getLast_digit_ne_zero 10 (Nat.digits_ne_nil_iff_ne_zero.mp hne)
    rw [hdig, Nat.ofDigits_digits]
