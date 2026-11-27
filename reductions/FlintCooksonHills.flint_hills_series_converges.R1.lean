import FormalConjectures.Wikipedia.FlintCooksonHills

-- Reduction FlintCooksonHills.flint_hills_series_converges.R1 of Convergence of the Flint Hills and Cookson Hills series — flint hills series converges
-- Credit: @senamakel
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

-- H1 is the open input: the irrationality exponent of pi is 2, in the form that for every
-- nu > 2 the bound |pi - p/q| >= q^(-nu) holds for all large q.
-- H2 is a classical dyadic-spacing lemma for an arbitrary real alpha: a uniform bound
-- ||q alpha|| >= c q^(1-nu) with nu < 5/2 makes the series of 1/(q^3 ||q alpha||^2) converge.
-- main carries the rest: the uniform bound for pi from H1, the transfer from |sin n| to
-- ||q pi|| (q the nearest multiple index), and the reindexing.
-- Adapted from the Apache-2.0 Lean files of openai/math (PiExponent analysis) and
-- conjectures-lean cookson-hills.

namespace OMA.R_FlintCooksonHills_flint_hills_series_converges_R1

def H1 : Prop :=
  ∀ ν : ℝ, 2 < ν → ∃ Q : ℕ, 2 ≤ Q ∧
    ∀ (p : ℤ) (q : ℕ), Q ≤ q → (q : ℝ) ^ (-ν) ≤ |Real.pi - (p : ℝ) / (q : ℝ)|

def H2 : Prop :=
  ∀ α c ν : ℝ, 0 < c → 1 < ν → ν < 5 / 2 →
    (∀ q : ℕ, 0 < q →
      c * (q : ℝ) ^ (1 - ν) ≤ |(q : ℝ) * α - (round ((q : ℝ) * α) : ℝ)|) →
    Summable (fun q : ℕ =>
      1 / ((q : ℝ) ^ 3 * |(q : ℝ) * α - (round ((q : ℝ) * α) : ℝ)| ^ 2))

theorem dist_mul_pos {α : ℝ} (hα : Irrational α) {q : ℕ}
    (hq : 0 < q) : 0 < |(q : ℝ) * α - (round ((q : ℝ) * α) : ℝ)| := by
  exact abs_pos.mpr (sub_ne_zero.mpr ((hα.natCast_mul hq.ne').ne_int _))

theorem finite_relative_lower_bound (f g : ℕ → ℝ)
    (hf : ∀ n, 0 < f n) (hg : ∀ n, 0 < g n) (N : ℕ) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ n < N, c * g n ≤ f n := by
  induction N with
  | zero => exact ⟨1, zero_lt_one, le_rfl, by simp⟩
  | succ N ih =>
    rcases ih with ⟨c, hc, hc1, hbound⟩
    refine ⟨min c (f N / g N), lt_min hc (div_pos (hf N) (hg N)),
      (min_le_left _ _).trans hc1, ?_⟩
    intro n hn
    rcases Nat.lt_succ_iff_lt_or_eq.mp hn with hn | rfl
    · exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (hg n).le).trans (hbound n hn)
    · exact (le_div_iff₀ (hg n)).mp (min_le_right _ _)

theorem uniform_relative_lower_bound (f g : ℕ → ℝ)
    (hf : ∀ n, 0 < f n) (hg : ∀ n, 0 < g n)
    (htail : ∃ N : ℕ, ∀ n, N ≤ n → g n ≤ f n) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ n, c * g n ≤ f n := by
  rcases htail with ⟨N, hN⟩
  rcases finite_relative_lower_bound f g hf hg N with ⟨c, hc, hc1, hbound⟩
  refine ⟨c, hc, hc1, fun n => ?_⟩
  by_cases hn : n < N
  · exact hbound n hn
  · exact (mul_le_of_le_one_left (hg n).le hc1).trans (hN n (Nat.le_of_not_gt hn))

theorem dist_lower_bound {α ν : ℝ} {q : ℕ} (hq : 0 < q)
    (h : ∀ p : ℤ, (q : ℝ) ^ (-ν) ≤ |α - p / (q : ℝ)|) :
    (q : ℝ) ^ (1 - ν) ≤ |(q : ℝ) * α - (round ((q : ℝ) * α) : ℝ)| := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hh := mul_le_mul_of_nonneg_left (h (round ((q : ℝ) * α))) hqR.le
  have heq : (q : ℝ) * |α - (round ((q : ℝ) * α) : ℝ) / q| =
      |(q : ℝ) * α - (round ((q : ℝ) * α) : ℝ)| := by
    calc
      _ = |(q : ℝ) * (α - (round ((q : ℝ) * α) : ℝ) / q)| := by
        rw [abs_mul, abs_of_pos hqR]
      _ = _ := by
        congr 1
        field_simp
  rw [heq] at hh
  simpa only [sub_eq_add_neg, Real.rpow_add hqR, Real.rpow_one] using hh

theorem uniform_dist_lower_bound {α ν : ℝ} (hα : Irrational α)
    (h : ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q → 0 < q →
      ∀ p : ℤ, (q : ℝ) ^ (-ν) ≤ |α - p / (q : ℝ)|) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ q : ℕ, 0 < q →
      c * (q : ℝ) ^ (1 - ν) ≤ |(q : ℝ) * α - (round ((q : ℝ) * α) : ℝ)| := by
  let f : ℕ → ℝ := fun n =>
    |((n + 1 : ℕ) : ℝ) * α - (round (((n + 1 : ℕ) : ℝ) * α) : ℝ)|
  let g : ℕ → ℝ := fun n => ((n + 1 : ℕ) : ℝ) ^ (1 - ν)
  have hf : ∀ n, 0 < f n := fun n => dist_mul_pos hα (Nat.succ_pos n)
  have hg : ∀ n, 0 < g n := fun n => Real.rpow_pos_of_pos (by positivity) _
  have htail : ∃ N : ℕ, ∀ n, N ≤ n → g n ≤ f n := by
    rcases h with ⟨Q, hQ⟩
    exact ⟨Q, fun n hn => dist_lower_bound (Nat.succ_pos n)
      (hQ (n + 1) (Nat.le_trans hn (Nat.le_succ n)) (Nat.succ_pos n))⟩
  rcases uniform_relative_lower_bound f g hf hg htail with ⟨c, hc, hc1, hbound⟩
  refine ⟨c, hc, hc1, ?_⟩
  rintro (_ | q) hq
  · exact False.elim (Nat.not_lt_zero _ hq)
  · exact hbound q

theorem round_div_pi_nonneg (n : ℕ) : 0 ≤ round ((n : ℝ) / Real.pi) := by
  have h := sub_half_lt_round ((n : ℝ) / Real.pi)
  have hn : (0 : ℝ) ≤ (n : ℝ) / Real.pi := by positivity
  have hh : (-1 : ℝ) < (round ((n : ℝ) / Real.pi) : ℝ) := by linarith
  have : (-1 : ℤ) < round ((n : ℝ) / Real.pi) := by exact_mod_cast hh
  omega

theorem grp_cast (n : ℕ) :
    (((round ((n : ℝ) / Real.pi)).toNat : ℕ) : ℝ) = round ((n : ℝ) / Real.pi) := by
  rw [← Int.cast_natCast, Int.toNat_of_nonneg (round_div_pi_nonneg n)]

theorem grp_distance (n : ℕ) :
    |(n : ℝ) - ((round ((n : ℝ) / Real.pi)).toNat : ℝ) * Real.pi| ≤ Real.pi / 2 := by
  have hh := mul_le_mul_of_nonneg_right (abs_sub_round ((n : ℝ) / Real.pi)) Real.pi_pos.le
  rw [grp_cast]
  calc
    |(n : ℝ) - (round ((n : ℝ) / Real.pi) : ℝ) * Real.pi| =
        |(n : ℝ) / Real.pi - (round ((n : ℝ) / Real.pi) : ℝ)| * Real.pi := by
      calc
        _ = |((n : ℝ) / Real.pi - (round ((n : ℝ) / Real.pi) : ℝ)) * Real.pi| := by
          congr 1
          field_simp
        _ = _ := by rw [abs_mul, abs_of_pos Real.pi_pos]
    _ ≤ Real.pi / 2 := by linarith

theorem grp_pos {n : ℕ} (hn : 2 ≤ n) : 0 < (round ((n : ℝ) / Real.pi)).toNat := by
  have hh := grp_distance n
  have hlow := (abs_le.mp hh).2
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  by_contra h
  have hz : (round ((n : ℝ) / Real.pi)).toNat = 0 := Nat.eq_zero_of_not_pos h
  rw [hz] at hlow
  norm_num at hlow
  linarith [Real.pi_lt_four]

theorem grp_lower {n : ℕ} (hn : 2 ≤ n) :
    Real.pi * ((round ((n : ℝ) / Real.pi)).toNat : ℝ) / 2 ≤ n := by
  have hh := (abs_le.mp (grp_distance n)).1
  have hq : (1 : ℝ) ≤ ((round ((n : ℝ) / Real.pi)).toNat : ℝ) := by
    exact_mod_cast grp_pos hn
  nlinarith [Real.pi_pos]

theorem abs_sin_lower_dist (n : ℕ) :
    (2 / Real.pi) * |((round ((n : ℝ) / Real.pi)).toNat : ℝ) * Real.pi -
      (round (((round ((n : ℝ) / Real.pi)).toNat : ℝ) * Real.pi) : ℝ)| ≤
      |Real.sin n| := by
  have hs := Real.mul_abs_le_abs_sin (grp_distance n)
  have hd := round_le (((round ((n : ℝ) / Real.pi)).toNat : ℝ) * Real.pi) (n : ℤ)
  have heq : |Real.sin ((n : ℝ) - ((round ((n : ℝ) / Real.pi)).toNat : ℝ) * Real.pi)| =
      |Real.sin n| := by
    rw [Real.sin_sub_nat_mul_pi, abs_mul, abs_pow]
    norm_num
  rw [heq] at hs
  have : |((round ((n : ℝ) / Real.pi)).toNat : ℝ) * Real.pi -
      (round (((round ((n : ℝ) / Real.pi)).toNat : ℝ) * Real.pi) : ℝ)| ≤
      |(n : ℝ) - ((round ((n : ℝ) / Real.pi)).toNat : ℝ) * Real.pi| := by
    simpa only [Int.cast_natCast, abs_sub_comm] using hd
  exact (mul_le_mul_of_nonneg_left this (by positivity)).trans hs

theorem grp_residue_injective : Function.Injective
    (fun n : ℕ => ((round ((n : ℝ) / Real.pi)).toNat,
      (⟨n % 4, Nat.mod_lt n (by norm_num)⟩ : Fin 4))) := by
  intro a b hab
  have hg : (round ((a : ℝ) / Real.pi)).toNat = (round ((b : ℝ) / Real.pi)).toNat :=
    congrArg Prod.fst hab
  have hm : a % 4 = b % 4 := congrArg (fun x : ℕ × Fin 4 => (x.2 : ℕ)) hab
  have ha := abs_le.mp (grp_distance a)
  have hb := abs_le.mp (grp_distance b)
  rw [hg] at ha
  have habR : (a : ℝ) - b < 4 := by linarith [Real.pi_lt_four]
  have hbaR : (b : ℝ) - a < 4 := by linarith [Real.pi_lt_four]
  have habN : a < b + 4 := by exact_mod_cast (show (a : ℝ) < b + 4 by linarith)
  have hbaN : b < a + 4 := by exact_mod_cast (show (b : ℝ) < a + 4 by linarith)
  omega

theorem flint_term_le_dist_term {n : ℕ} (hn : 2 ≤ n) :
    1 / ((n : ℝ) ^ 3 * Real.sin n ^ 2) ≤
      4 / (((round ((n : ℝ) / Real.pi)).toNat : ℝ) ^ 3 *
        |((round ((n : ℝ) / Real.pi)).toNat : ℝ) * Real.pi -
          (round (((round ((n : ℝ) / Real.pi)).toNat : ℝ) * Real.pi) : ℝ)| ^ 2) := by
  set m : ℕ := (round ((n : ℝ) / Real.pi)).toNat with hmdef
  set D : ℝ := |(m : ℝ) * Real.pi - (round ((m : ℝ) * Real.pi) : ℝ)| with hDdef
  have hqN : 0 < m := grp_pos hn
  have hq : (0 : ℝ) < m := by exact_mod_cast hqN
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hd : 0 < D := dist_mul_pos irrational_pi hqN
  have hlow : (2 / Real.pi) * D ≤ |Real.sin n| := abs_sin_lower_dist n
  have h2 : D ≤ 2 * |Real.sin n| := by
    have hp : 0 < Real.pi := Real.pi_pos
    have hm := (div_le_iff₀ hp).mp (show 2 * D / Real.pi ≤ |Real.sin n| by
      simpa only [div_mul_eq_mul_div] using hlow)
    nlinarith [Real.pi_lt_four]
  have hs : 0 < Real.sin n ^ 2 := by
    have : Real.sin n ≠ 0 := by
      intro hzero
      rw [hzero, abs_zero, mul_zero] at h2
      linarith
    exact sq_pos_of_ne_zero this
  have hqle : (m : ℝ) ≤ n := by
    have h := grp_lower hn
    nlinarith [Real.pi_gt_three]
  have hcube := pow_le_pow_left₀ hq.le hqle 3
  have hd2 : D ^ 2 ≤ 4 * Real.sin n ^ 2 := by
    nlinarith [sq_abs (Real.sin n), sq_nonneg (2 * |Real.sin n| - D)]
  have hp : (m : ℝ) ^ 3 * D ^ 2 ≤ 4 * ((n : ℝ) ^ 3 * Real.sin n ^ 2) := by
    calc
      _ ≤ (m : ℝ) ^ 3 * (4 * Real.sin n ^ 2) :=
        mul_le_mul_of_nonneg_left hd2 (by positivity)
      _ ≤ (n : ℝ) ^ 3 * (4 * Real.sin n ^ 2) :=
        mul_le_mul_of_nonneg_right hcube (by positivity)
      _ = _ := by ring
  exact (div_le_div_iff₀ (mul_pos (pow_pos hnR 3) hs)
    (mul_pos (pow_pos hq 3) (sq_pos_of_pos hd))).mpr (by simpa using hp)

theorem summable_grp_comp {f : ℕ → ℝ} (hf0 : ∀ n, 0 ≤ f n)
    (hf : Summable f) :
    Summable (fun n : ℕ => f (round ((n : ℝ) / Real.pi)).toNat) := by
  have hp : Summable (fun p : ℕ × Fin 4 => f p.1) := by
    apply (summable_prod_of_nonneg (fun p => hf0 p.1)).mpr
    constructor
    · intro n
      exact Summable.of_finite
    · simpa using hf.mul_left 4
  exact hp.comp_injective grp_residue_injective

theorem flint_of_dist_summable
    (h : Summable (fun q : ℕ =>
      1 / ((q : ℝ) ^ 3 * |(q : ℝ) * Real.pi - (round ((q : ℝ) * Real.pi) : ℝ)| ^ 2))) :
    Summable (fun n : ℕ => 1 / ((n : ℝ) ^ 3 * Real.sin n ^ 2)) := by
  have hh : Summable (fun q : ℕ =>
      4 / ((q : ℝ) ^ 3 * |(q : ℝ) * Real.pi - (round ((q : ℝ) * Real.pi) : ℝ)| ^ 2)) := by
    simpa only [mul_one_div] using h.mul_left 4
  have hcomp := summable_grp_comp (fun q => by positivity) hh
  have htail := (summable_nat_add_iff 2).mpr hcomp
  apply (summable_nat_add_iff 2).mp
  exact Summable.of_nonneg_of_le (fun n => by positivity)
    (fun n => flint_term_le_dist_term (show 2 ≤ n + 2 by omega)) htail

theorem flint_of_H1_H2 (h1 : H1) (h2 : H2) :
    Summable (fun n : ℕ => 1 / ((((n + 1) : ℝ)^3) * (Real.sin (n + 1)^2))) := by
  have hν : (2 : ℝ) < 9 / 4 := by norm_num
  obtain ⟨Q, _, hbound⟩ := h1 (9 / 4) hν
  obtain ⟨c, hc, _, hlow⟩ :=
    uniform_dist_lower_bound (ν := 9 / 4) irrational_pi ⟨Q, fun q hq _ p => hbound p q hq⟩
  have hd := h2 Real.pi c (9 / 4) hc (by norm_num) (by norm_num) hlow
  have hf := flint_of_dist_summable hd
  have := (summable_nat_add_iff (f := fun n : ℕ => 1 / ((n : ℝ) ^ 3 * Real.sin n ^ 2)) 1).mpr hf
  simpa only [Nat.cast_add, Nat.cast_one] using this

theorem main : H1 → H2 → type_of% @FlintCooksonHills.flint_hills_series_converges := by
  intro h1 h2
  exact flint_of_H1_H2 h1 h2

end OMA.R_FlintCooksonHills_flint_hills_series_converges_R1
