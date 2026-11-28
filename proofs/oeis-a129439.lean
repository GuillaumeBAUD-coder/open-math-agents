import OMAStatements.S_oeis_a129439

open Finset OMA.S_oeis_a129439

private lemma ext_range (a n : ℕ) (h : a ≤ n) :
    ∏ d ∈ Icc 1 a, d ^ (a / d) = ∏ d ∈ Icc 1 n, d ^ (a / d) := by
  refine prod_subset (Icc_subset_Icc_right h) fun d hd hnd => ?_
  rw [mem_Icc] at hd hnd
  rw [Nat.div_eq_of_lt (by omega), pow_zero]

private lemma D_eq (n : ℕ) : D n = ∏ d ∈ Icc 1 n, d ^ (n / d) := by
  induction n with
  | zero => simp [D]
  | succ n ih =>
    have hD : D (n+1) = D n * ∏ d ∈ (n+1).divisors, d := by
      unfold D; rw [prod_range_succ]
    have hdiv : (n+1).divisors = (Icc 1 (n+1)).filter (· ∣ n+1) := by
      ext d
      rw [Nat.mem_divisors, mem_filter, mem_Icc]
      constructor
      · rintro ⟨h, _⟩
        exact ⟨⟨Nat.pos_of_dvd_of_pos h (by omega), Nat.le_of_dvd (by omega) h⟩, h⟩
      · rintro ⟨_, h⟩
        exact ⟨h, by omega⟩
    rw [hD, ih, ext_range n (n+1) (by omega), hdiv, prod_filter, ← prod_mul_distrib]
    refine prod_congr rfl fun d _ => ?_
    rw [Nat.succ_div]
    split_ifs <;> simp [pow_succ]

theorem OMA.solution : type_of% @OMA.S_oeis_a129439.main := by
  intro n k hk
  rw [D_eq (n-k), D_eq k, D_eq n, ext_range (n-k) n (by omega), ext_range k n hk,
    ← prod_mul_distrib]
  refine prod_dvd_prod_of_dvd _ _ fun d _ => ?_
  rw [← pow_add]
  refine pow_dvd_pow d ?_
  have h := Nat.add_div_le_add_div (n-k) k d
  rwa [Nat.sub_add_cancel hk] at h
