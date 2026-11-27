import OMAReductions.R_FlintCooksonHills_flint_hills_series_converges_R1
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-! A dyadic block has separated signed rounding errors. Binning by that separation
compares its sum with the integer p-series of exponent two. -/

private noncomputable def err (a : ℝ) (n : ℕ) : ℝ := n*a - (round (n*a) : ℝ)

private lemma sep (a : ℝ) (m n : ℕ) (h : m < n) :
    |err a (n-m)| ≤ |err a n - err a m| := by
  have hh := round_le (((n-m : ℕ) : ℝ)*a) (round ((n : ℝ)*a)-round ((m : ℝ)*a))
  unfold err
  have eqn : (↑(n-m : ℕ) : ℝ)*a - ↑(round ((n : ℝ)*a)-round ((m : ℝ)*a)) =
      ((n:ℝ)*a - ↑(round ((n:ℝ)*a))) - ((m:ℝ)*a - ↑(round ((m:ℝ)*a))) := by
    rw [Nat.cast_sub h.le, Int.cast_sub]
    ring
  rwa [eqn] at hh

private lemma floor_bounds (x d : ℝ) (hd : 0 < d) :
    (⌊x/d⌋ : ℝ)*d ≤ x ∧ x < ((⌊x/d⌋ : ℝ)+1)*d := by
  exact ⟨(le_div_iff₀ hd).mp (Int.floor_le _),
    (div_lt_iff₀ hd).mp (Int.lt_floor_add_one _)⟩

private lemma weight (ν c : ℝ) (hc : 0 < c) (hν : ν < 5/2) :
    Summable (fun j : ℕ => 4 / (((2:ℝ)^j)^3 * (c*((2:ℝ)^(j+1))^(1-ν))^2)) := by
  let s := (2:ℝ)^(1-ν)
  have hs : 0 < s := Real.rpow_pos_of_pos (by norm_num) _
  have hr : 1 < 8*s^2 := by
    have he : (2:ℝ)^(5-2*ν) = 8*s^2 := by
      rw [show 5-2*ν = 3+(1-ν)*(2:ℕ) by push_cast; ring, Real.rpow_add (by norm_num),
        Real.rpow_mul_natCast (by norm_num)]
      norm_num [s]
    rw [← he]
    exact Real.one_lt_rpow (by norm_num) (by linarith)
  have hg := (summable_geometric_of_lt_one (by positivity : 0 ≤ 1/(8*s^2))
    ((div_lt_one (by positivity)).mpr hr)).mul_left (4/(c*s)^2)
  apply hg.congr
  intro j
  have hj : ((2:ℝ)^(j+1))^(1-ν) = s^j*s := by
    rw [pow_succ, Real.mul_rpow (by positivity) (by norm_num), ← Real.rpow_natCast_mul (by norm_num),
      mul_comm (j:ℝ), Real.rpow_mul_natCast (by norm_num)]
  rw [hj, div_pow, mul_pow, one_pow]
  have hp : ((2:ℝ)^j)^3 = 8^j := by rw [← pow_mul, Nat.mul_comm, pow_mul]; norm_num
  rw [hp, mul_pow, ← pow_mul, Nat.mul_comm 2 j, pow_mul]
  field_simp

theorem OMA.solution : OMA.R_FlintCooksonHills_flint_hills_series_converges_R1.H2 := by
  intro a c ν hc hν htop hh
  let d := fun j : ℕ => c*((2:ℝ)^(j+1))^(1-ν)
  have hd (j) : 0 < d j := by dsimp [d]; positivity
  have lower (j m : ℕ) (hm : 0 < m) (hmax : m ≤ 2^(j+1)) : d j ≤ |err a m| := by
    apply le_trans _ (hh m hm)
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hm)
      (by exact_mod_cast hmax) (by linarith)) hc.le
  let block (n : ℕ) := Nat.log 2 (n+1)
  have upper (n : ℕ) : n+1 < 2^(block n+1) := Nat.lt_pow_succ_log_self (by decide) _
  let code (n : ℕ) : ℕ × ℤ := (block n, ⌊err a (n+1) / d (block n)⌋)
  have unequal (m n : ℕ) (hmn : m < n) : code m ≠ code n := by
    intro he
    have hb : block m = block n := congrArg Prod.fst he
    have hz : ⌊err a (m+1)/d (block m)⌋ = ⌊err a (n+1)/d (block n)⌋ := congrArg Prod.snd he
    rw [hb] at hz
    have hm' := floor_bounds (err a (m+1)) _ (hd (block n))
    rw [hz] at hm'
    have hn' := floor_bounds (err a (n+1)) _ (hd (block n))
    have hdist := (lower (block n) ((n+1)-(m+1)) (by omega)
      (by have := upper n; omega)).trans (sep a (m+1) (n+1) (by omega))
    rcases le_total (err a (m+1)) (err a (n+1)) with h | h
    · rw [abs_of_nonneg (sub_nonneg.mpr h)] at hdist
      linarith [hm'.1, hn'.2]
    · rw [abs_of_nonpos (sub_nonpos.mpr h)] at hdist
      linarith [hm'.2, hn'.1]
  have hinj : Function.Injective code := by
    intro m n h
    exact le_antisymm (le_of_not_gt fun h' => unequal n m h' h.symm)
      (le_of_not_gt fun h' => unequal m n h' h)
  have prodSum := (weight ν c hc htop).mul_of_nonneg
    (Real.summable_one_div_int_pow.mpr (by decide : 1 < 2)) (by intro j; positivity)
    (by intro z; positivity)
  apply (summable_nat_add_iff 1).mp
  apply (prodSum.comp_injective hinj).of_nonneg_of_le
  · intro n; positivity
  intro n
  let j := block n
  let z := (code n).2
  let e := err a (n+1)
  let N := (2:ℝ)^j
  have hn : N ≤ (n+1:ℕ) := by
    dsimp [N, j, block]
    exact_mod_cast Nat.pow_log_le_self 2 (Nat.succ_ne_zero n)
  have hN : 0 < N := by dsimp [N]; positivity
  have hD := hd j
  have he : d j ≤ |e| := lower j (n+1) (by omega) (upper n).le
  have hz : (z:ℝ)*d j ≤ e ∧ e < ((z:ℝ)+1)*d j := floor_bounds e _ hD
  have hz0 : (z:ℝ) ≠ 0 := by
    intro h
    rw [h] at hz
    have he' : 0 ≤ e := by linarith [hz.1]
    rw [abs_of_nonneg he'] at he
    linarith [hz.2]
  have hz' : |(z:ℝ)| *d j ≤ 2*|e| := by
    rcases le_total 0 (z:ℝ) with h | h
    · rw [abs_of_nonneg h]; linarith [hz.1, le_abs_self e, abs_nonneg e]
    · rw [abs_of_nonpos h]; linarith [hz.2, neg_abs_le e]
  have hs := pow_le_pow_left₀ (mul_nonneg (abs_nonneg _) hD.le) hz' 2
  rw [mul_pow, sq_abs, mul_pow] at hs
  have hnp := pow_le_pow_left₀ hN.le hn 3
  change 1/(((n+1:ℕ):ℝ)^3*|e|^2) ≤ (4/(N^3*(d j)^2))*(1/(z:ℝ)^2)
  have he0 := lt_of_lt_of_le hD he
  have hq := lt_of_lt_of_le hN hn
  have hz2 := sq_pos_of_ne_zero hz0
  rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith only [mul_le_mul_of_nonneg_left hs (pow_nonneg hN.le 3),
    mul_le_mul_of_nonneg_right hnp (by positivity : 0 ≤ 4*|e|^2)]
