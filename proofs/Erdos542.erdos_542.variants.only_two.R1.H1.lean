import OMAReductions.R_Erdos542_erdos_542_variants_only_two_R1

/-! # The numerical inequality for the case `3 ∈ A`

Harmonic sums over `(a, b]` are squeezed between logarithms:
`log (b + 1) - log (a + 1) ≤ ∑ 1/k ≤ log (2b + 1) - log (2a + 1)`.
Removing the multiples of `3` subtracts a third of a harmonic sum over `(a/3, b/3]`.
For `n ≥ 50` this leaves a polynomial inequality against `exp 4`;
for `12 ≤ n < 50` the sums are computed exactly over `ℚ`. -/

namespace OMA.Erdos542OnlyTwoH1

open Finset

lemma recip_le_log (m : ℕ) (hm : 1 ≤ m) :
    (1 : ℝ) / m ≤ Real.log (2 * m + 1) - Real.log (2 * m - 1) := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  set x : ℝ := 1 / (2 * m) with hx
  have hx0 : 0 ≤ x := by positivity
  have hx1 : |x| < 1 := by
    rw [abs_of_nonneg hx0, hx, div_lt_one (by positivity)]
    linarith
  have hs := Real.hasSum_log_sub_log_of_abs_lt_one hx1
  have h0 := le_hasSum hs 0 (fun j _ => by positivity)
  have e1 : 1 + x = (2 * m + 1) / (2 * m) := by rw [hx]; field_simp
  have e2 : 1 - x = (2 * m - 1) / (2 * m) := by rw [hx]; field_simp
  rw [e1, e2, Real.log_div (by positivity) (by positivity),
    Real.log_div (by linarith) (by positivity)] at h0
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have e3 : 2 * (1 / (2 * ((0 : ℕ) : ℝ) + 1)) * x ^ (2 * 0 + 1) = 1 / m := by
    rw [hx]
    push_cast
    ring
  linarith

lemma log_le_recip (k : ℕ) (hk : 1 ≤ k) :
    Real.log (k + 1) - Real.log k ≤ (1 : ℝ) / k := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  rw [← Real.log_div (by positivity) (by positivity)]
  have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (k + 1) / k by positivity)
  have e : ((k : ℝ) + 1) / k - 1 = 1 / k := by field_simp; ring
  linarith

lemma harm_upper (a b : ℕ) (hab : a ≤ b) :
    ∑ m ∈ Ioc a b, (1 : ℝ) / m ≤ Real.log (2 * b + 1) - Real.log (2 * a + 1) := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hb ih =>
    rw [Finset.sum_Ioc_succ_top hb]
    have := recip_le_log (b + 1) (by omega)
    push_cast at this ⊢
    have e : (2 * ((b : ℝ) + 1) - 1) = 2 * b + 1 := by ring
    have e' : (2 * ((b : ℝ) + 1) + 1) = 2 * (b + 1) + 1 := by ring
    rw [e] at this
    linarith

lemma harm_lower (a b : ℕ) (hab : a ≤ b) :
    Real.log (b + 1) - Real.log (a + 1) ≤ ∑ m ∈ Ioc a b, (1 : ℝ) / m := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hb ih =>
    rw [Finset.sum_Ioc_succ_top hb]
    have := log_le_recip (b + 1) (by omega)
    push_cast at this ⊢
    linarith

lemma sum_not_three (a b : ℕ) :
    ∑ m ∈ (Ioc a b).filter (fun m => m % 3 ≠ 0), (1 : ℝ) / m =
      ∑ m ∈ Ioc a b, (1 : ℝ) / m - 1 / 3 * ∑ k ∈ Ioc (a / 3) (b / 3), (1 : ℝ) / k := by
  have hsplit := Finset.sum_filter_add_sum_filter_not (Ioc a b) (fun m => m % 3 ≠ 0)
    (fun m => (1 : ℝ) / m)
  have hthree : ∑ m ∈ (Ioc a b).filter (fun m => ¬ (m % 3 ≠ 0)), (1 : ℝ) / m =
      ∑ k ∈ Ioc (a / 3) (b / 3), 1 / 3 * ((1 : ℝ) / k) := by
    apply Finset.sum_nbij' (fun m => m / 3) (fun k => 3 * k)
    · intro m hm
      simp only [mem_filter, mem_Ioc] at hm ⊢
      omega
    · intro k hk
      simp only [mem_filter, mem_Ioc] at hk ⊢
      omega
    · intro m hm
      simp only [mem_filter, mem_Ioc] at hm
      omega
    · intro k hk
      omega
    · intro m hm
      simp only [mem_filter, mem_Ioc] at hm
      have h3 : m = 3 * (m / 3) := by omega
      conv_lhs => rw [h3]
      push_cast
      rw [one_div_mul_one_div]
  rw [← Finset.mul_sum] at hthree
  linarith

lemma set_one (n : ℕ) :
    (Icc 1 n).filter (fun m => n < 2 * m ∧ m % 3 ≠ 0) =
      (Ioc (n / 2) n).filter (fun m => m % 3 ≠ 0) := by
  ext m
  simp only [mem_filter, mem_Icc, mem_Ioc]
  omega

lemma set_two (n : ℕ) :
    (Icc 1 n).filter (fun b => n < 3 * b ∧ 2 * b ≤ n ∧ b % 3 ≠ 0) =
      (Ioc (n / 3) (n / 2)).filter (fun m => m % 3 ≠ 0) := by
  ext m
  simp only [mem_filter, mem_Icc, mem_Ioc]
  omega

lemma exp_four : (51 : ℝ) ≤ Real.exp 4 := by
  have h := Real.exp_one_gt_d9
  have e : Real.exp 4 = Real.exp 1 ^ 4 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [e]
  have h1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith
  calc (51 : ℝ) ≤ 2.7 ^ 4 := by norm_num
    _ ≤ Real.exp 1 ^ 4 := by gcongr

lemma poly (n : ℝ) (hn : 50 ≤ n) :
    (2 * n + 1) ^ 6 * ((n + 6) / 6) * ((n + 9) / 9) ≤
      51 * (n ^ 3 * ((2 * n - 1) / 3) ^ 3 * ((n + 1) / 3) ^ 2) := by
  obtain ⟨t, ht, rfl⟩ : ∃ t : ℝ, 0 ≤ t ∧ n = t + 50 := ⟨n - 50, by linarith, by ring⟩
  have key : 51 * ((t + 50) ^ 3 * ((2 * (t + 50) - 1) / 3) ^ 3 * ((t + 50 + 1) / 3) ^ 2) -
      (2 * (t + 50) + 1) ^ 6 * ((t + 50 + 6) / 6) * ((t + 50 + 9) / 9) =
      (19440 * t ^ 8 + 6969240 * t ^ 7 + 1073557476 * t ^ 6 + 92251835226 * t ^ 5 +
        4789967248368 * t ^ 4 + 151270002051930 * t ^ 3 + 2740409737275591 * t ^ 2 +
        23789374209100773 * t + 49606017082271784) / 39366 := by
    ring
  have : 0 ≤ (19440 * t ^ 8 + 6969240 * t ^ 7 + 1073557476 * t ^ 6 + 92251835226 * t ^ 5 +
        4789967248368 * t ^ 4 + 151270002051930 * t ^ 3 + 2740409737275591 * t ^ 2 +
        23789374209100773 * t + 49606017082271784) / 39366 := by positivity
  linarith

lemma large (n : ℕ) (hn : 50 ≤ n) :
    ∑ m ∈ (Icc 1 n).filter (fun m => n < 2 * m ∧ m % 3 ≠ 0), (1 : ℝ) / m +
      ∑ b ∈ (Icc 1 n).filter (fun b => n < 3 * b ∧ 2 * b ≤ n ∧ b % 3 ≠ 0),
        (1 : ℝ) / (2 * b) ≤ 2 / 3 := by
  have hhalf : ∑ b ∈ (Icc 1 n).filter (fun b => n < 3 * b ∧ 2 * b ≤ n ∧ b % 3 ≠ 0),
      (1 : ℝ) / (2 * b) = 1 / 2 * ∑ b ∈ (Icc 1 n).filter
        (fun b => n < 3 * b ∧ 2 * b ≤ n ∧ b % 3 ≠ 0), (1 : ℝ) / b := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [one_div_mul_one_div]
  rw [hhalf, set_one, set_two, sum_not_three, sum_not_three]
  have u1 := harm_upper (n / 2) n (Nat.div_le_self n 2)
  have u2 := harm_upper (n / 3) (n / 2) (Nat.div_le_div_left (by norm_num) (by norm_num))
  have l1 := harm_lower (n / 2 / 3) (n / 3) (by omega)
  have l2 := harm_lower (n / 3 / 3) (n / 2 / 3) (by omega)
  set a : ℝ := ((n / 2 : ℕ) : ℝ) with ha
  set b : ℝ := ((n / 3 : ℕ) : ℝ) with hb
  set c : ℝ := ((n / 2 / 3 : ℕ) : ℝ) with hc
  set d : ℝ := ((n / 3 / 3 : ℕ) : ℝ) with hd
  set x : ℝ := (n : ℝ) with hx
  have hx50 : (50 : ℝ) ≤ x := by rw [hx]; exact_mod_cast hn
  have ha1 : x ≤ 2 * a + 1 := by
    rw [hx, ha]; exact_mod_cast (show n ≤ 2 * (n / 2) + 1 by omega)
  have hb1 : x ≤ 3 * b + 2 := by
    rw [hx, hb]; exact_mod_cast (show n ≤ 3 * (n / 3) + 2 by omega)
  have hc1 : 6 * c ≤ x := by
    rw [hx, hc]; exact_mod_cast (show 6 * (n / 2 / 3) ≤ n by omega)
  have hd1 : 9 * d ≤ x := by
    rw [hx, hd]; exact_mod_cast (show 9 * (n / 3 / 3) ≤ n by omega)
  have hc0 : 0 ≤ c := by positivity
  have hd0 : 0 ≤ d := by positivity
  have hb0 : 0 ≤ b := by positivity
  have ha0 : 0 ≤ a := by positivity
  -- the key logarithmic inequality
  have hP : 0 < (2 * x + 1) ^ 6 * (c + 1) * (d + 1) := by positivity
  have hQ : 0 < (2 * a + 1) ^ 3 * (2 * b + 1) ^ 3 * (b + 1) ^ 2 := by positivity
  have hPQ : (2 * x + 1) ^ 6 * (c + 1) * (d + 1) ≤
      Real.exp 4 * ((2 * a + 1) ^ 3 * (2 * b + 1) ^ 3 * (b + 1) ^ 2) := by
    have p1 : (2 * x + 1) ^ 6 * (c + 1) * (d + 1) ≤
        (2 * x + 1) ^ 6 * ((x + 6) / 6) * ((x + 9) / 9) := by
      gcongr
      · linarith
      · linarith
    have p2 : x ^ 3 * ((2 * x - 1) / 3) ^ 3 * ((x + 1) / 3) ^ 2 ≤
        (2 * a + 1) ^ 3 * (2 * b + 1) ^ 3 * (b + 1) ^ 2 := by
      have q1 : 0 ≤ (2 * x - 1) / 3 := by linarith
      have q2 : 0 ≤ (x + 1) / 3 := by linarith
      gcongr
      · linarith
      · linarith
    have p3 := poly x hx50
    have p4 := exp_four
    have p5 : 0 ≤ x ^ 3 * ((2 * x - 1) / 3) ^ 3 * ((x + 1) / 3) ^ 2 := by
      have q1 : 0 ≤ (2 * x - 1) / 3 := by linarith
      positivity
    calc (2 * x + 1) ^ 6 * (c + 1) * (d + 1)
        ≤ 51 * (x ^ 3 * ((2 * x - 1) / 3) ^ 3 * ((x + 1) / 3) ^ 2) := p1.trans p3
      _ ≤ 51 * ((2 * a + 1) ^ 3 * (2 * b + 1) ^ 3 * (b + 1) ^ 2) := by gcongr
      _ ≤ Real.exp 4 * ((2 * a + 1) ^ 3 * (2 * b + 1) ^ 3 * (b + 1) ^ 2) := by gcongr
  have hlog := Real.log_le_log hP hPQ
  have eP : Real.log ((2 * x + 1) ^ 6 * (c + 1) * (d + 1)) =
      6 * Real.log (2 * x + 1) + Real.log (c + 1) + Real.log (d + 1) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_pow]
    push_cast
    ring
  have eQ : Real.log (Real.exp 4 * ((2 * a + 1) ^ 3 * (2 * b + 1) ^ 3 * (b + 1) ^ 2)) =
      4 + 3 * Real.log (2 * a + 1) + 3 * Real.log (2 * b + 1) + 2 * Real.log (b + 1) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_exp,
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow, Real.log_pow]
    push_cast
    ring
  rw [eP, eQ] at hlog
  linarith

def checkQ (n : ℕ) : Bool :=
  decide (∑ m ∈ (Icc 1 n).filter (fun m => n < 2 * m ∧ m % 3 ≠ 0), (1 : ℚ) / m +
      ∑ b ∈ (Icc 1 n).filter (fun b => n < 3 * b ∧ 2 * b ≤ n ∧ b % 3 ≠ 0),
        (1 : ℚ) / ((2 * b : ℕ) : ℚ) ≤ 2 / 3)

lemma checkQ_all : ∀ n < 50, 12 ≤ n → checkQ n = true := by decide +kernel

lemma small (n : ℕ) (h1 : 12 ≤ n) (h2 : n < 50) :
    ∑ m ∈ (Icc 1 n).filter (fun m => n < 2 * m ∧ m % 3 ≠ 0), (1 : ℝ) / m +
      ∑ b ∈ (Icc 1 n).filter (fun b => n < 3 * b ∧ 2 * b ≤ n ∧ b % 3 ≠ 0),
        (1 : ℝ) / (2 * b) ≤ 2 / 3 := by
  have h := checkQ_all n h2 h1
  simp only [checkQ, decide_eq_true_eq] at h
  have h' := (Rat.cast_le (K := ℝ)).mpr h
  push_cast at h'
  exact h'

end OMA.Erdos542OnlyTwoH1

theorem OMA.solution : OMA.R_Erdos542_erdos_542_variants_only_two_R1.H1 := by
  intro n hn
  rcases lt_or_ge n 50 with h | h
  · exact OMA.Erdos542OnlyTwoH1.small n hn h
  · exact OMA.Erdos542OnlyTwoH1.large n h
