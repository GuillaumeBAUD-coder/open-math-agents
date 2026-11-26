import FormalConjectures.ErdosProblems.«945»

open Filter Asymptotics Erdos945

theorem OMA.solution : type_of% @Erdos945.erdos_945.variants.equivalence := by
  constructor
  · rintro ⟨g, hg, hF⟩
    obtain ⟨B, hB⟩ := hg.isBigOWith
    let C : ℝ := max B 1
    have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    have hbound : ∀ᶠ x : ℝ in atTop, (F x : ℝ) ≤ Real.log x ^ C := by
      filter_upwards [hB.bound, hF, Real.tendsto_log_atTop.eventually_ge_atTop 1] with x hb hf hx
      have hb' : |g x| ≤ B := by simpa [Real.norm_eq_abs] using hb
      have hgc : g x ≤ C := (le_abs_self _).trans (hb'.trans (le_max_left _ _))
      exact hf.trans (Real.rpow_le_rpow_of_exponent_le hx hgc)
    refine ⟨C + 2, by linarith, ?_⟩
    have hsublinear : ∀ᶠ x : ℝ in atTop, Real.log x ^ (C + 2) ≤ x := by
      filter_upwards [(isLittleO_log_rpow_rpow_atTop (C + 2) zero_lt_one).bound
        (by norm_num : (0 : ℝ) < 1), eventually_ge_atTop (1 : ℝ)] with x hx hx1
      simpa [Real.rpow_one, Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ x by linarith),
        abs_of_nonneg (Real.rpow_nonneg (Real.log_nonneg hx1) _)] using hx
    have hFtwo := ((tendsto_const_mul_atTop_of_pos (by norm_num : (0 : ℝ) < 2)).2
      (tendsto_id : Tendsto id atTop atTop)).eventually hbound
    filter_upwards [hsublinear, hFtwo, eventually_ge_atTop (2 : ℝ),
      Real.tendsto_log_atTop.eventually_ge_atTop (2 ^ C + 2)] with x hsub hxF hx hlog
    let L := Real.log x
    let y := x + L ^ (C + 2)
    let n := ⌈x⌉₊ - 1
    let k := ⌊y⌋₊ - n
    have hL : 2 ≤ L := le_trans (le_add_of_nonneg_left (Real.rpow_nonneg (by norm_num) _)) hlog
    have hn : (n : ℝ) < x := by
      have hceil := Nat.ceil_lt_add_one (show 0 ≤ x by linarith)
      have hpos : 1 ≤ ⌈x⌉₊ := by
        have := Nat.le_ceil x
        exact_mod_cast (show (1 : ℝ) ≤ (⌈x⌉₊ : ℝ) by linarith)
      simpa [n, Nat.cast_sub hpos] using (show (⌈x⌉₊ : ℝ) - 1 < x by linarith)
    have hy : x ≤ y := le_add_of_nonneg_right (Real.rpow_nonneg (by linarith) _)
    have hnk : n + k = ⌊y⌋₊ := Nat.add_sub_of_le (Nat.le_floor (by linarith))
    have hend : ((n + k : ℕ) : ℝ) ≤ y := hnk ▸ Nat.floor_le (by linarith)
    have hmem : ∀ a ∈ Set.Ioc n (n + k), (a : ℝ) ∈ Set.Icc x y := by
      intro a ha
      refine ⟨(Nat.le_ceil x).trans ?_, ?_⟩
      · exact_mod_cast (show ⌈x⌉₊ ≤ a by dsimp [n] at ha; have := ha.1; omega)
      · exact (Nat.cast_le.mpr ha.2).trans hend
    by_contra h
    have hinj : (Set.Ioc n (n + k)).InjOn τ := by
      intro a ha b hb heq
      by_contra hab
      exact h ⟨a, b, hab, hmem a ha, hmem b hb, heq⟩
    have hrun : k ≤ F (2 * x) := by
      unfold F
      apply le_csSup
      · refine ⟨⌊2 * x⌋₊, ?_⟩
        rintro j ⟨m, hm, _⟩
        exact Nat.le_floor (by push_cast at hm; linarith)
      · exact ⟨n, by push_cast; push_cast at hend; dsimp [y, L] at hend; linarith, hinj⟩
    have hlogTwo : Real.log (2 * x) ≤ 2 * L := by
      rw [Real.log_mul (by norm_num) (by linarith)]
      have := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hx
      dsimp [L]
      linarith
    have hupper : (k : ℝ) ≤ 2 ^ C * L ^ C := by
      calc
        (k : ℝ) ≤ F (2 * x) := by exact_mod_cast hrun
        _ ≤ Real.log (2 * x) ^ C := hxF
        _ ≤ (2 * L) ^ C := Real.rpow_le_rpow (Real.log_nonneg (by linarith)) hlogTwo hC.le
        _ = _ := Real.mul_rpow (by norm_num) (by linarith)
    have hfloor := Nat.lt_floor_add_one y
    rw [← hnk, Nat.cast_add] at hfloor
    have hk : L ^ (C + 2) < (k : ℝ) + 1 := by dsimp [y] at hfloor; linarith
    have hrpow : L ^ (2 : ℝ) = L ^ (2 : ℕ) := Real.rpow_natCast L 2
    rw [Real.rpow_add (by linarith), hrpow] at hk
    have hpow : 1 ≤ L ^ C := by
      simpa using Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) (show 1 ≤ L by linarith) hC.le
    have hsq : 2 ^ C + 1 ≤ L ^ 2 := by nlinarith
    have hmul := mul_le_mul_of_nonneg_right hsq (show 0 ≤ L ^ C by linarith)
    nlinarith
  · rintro ⟨C, hC, h⟩
    obtain ⟨T, hT⟩ := eventually_atTop.1 h
    let A := max T 1
    refine ⟨fun _ => C + 1, Asymptotics.isBigO_const_const _ one_ne_zero _, ?_⟩
    filter_upwards [eventually_ge_atTop A, Real.tendsto_log_atTop.eventually_ge_atTop (A + 2)] with x hx hlog
    let L := Real.log x
    have hA : 1 ≤ A := le_max_right _ _
    have hL : 0 < L := by linarith
    have hpow : 1 ≤ L ^ C := by
      simpa using Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) (show 1 ≤ L by linarith) hC.le
    have haux : A + 1 + L ^ C ≤ L ^ (C + 1) := by
      rw [Real.rpow_add_one hL.ne']
      have := mul_le_mul_of_nonneg_right hlog (show 0 ≤ L ^ C by linarith)
      have := mul_le_mul_of_nonneg_left hpow (show 0 ≤ A + 1 by linarith)
      nlinarith
    have hf : F x ≤ ⌊L ^ (C + 1)⌋₊ := by
      unfold F
      apply csSup_le'
      rintro k ⟨n, hnk, hi⟩
      apply Nat.le_floor
      by_contra hk
      have hk := lt_of_not_ge hk
      let y : ℝ := max A ((n : ℝ) + 1)
      have hy0 : 1 ≤ y := hA.trans (le_max_left _ _)
      have hyT : T ≤ y := (le_max_left T 1).trans (le_max_left _ _)
      have hyN : (n : ℝ) + 1 ≤ y := le_max_right _ _
      have hyB : y ≤ (n : ℝ) + A + 1 := max_le (by linarith) (by linarith)
      push_cast at hnk
      have hyX : y ≤ x := by linarith
      have hp : Real.log y ^ C ≤ L ^ C :=
        Real.rpow_le_rpow (Real.log_nonneg hy0)
          (Real.strictMonoOn_log.monotoneOn (by simpa using (show 0 < y by linarith))
            (by simpa using (show 0 < x by linarith)) hyX) hC.le
      obtain ⟨a, b, hab, ha, hb, ht⟩ := hT y hyT
      have hmem : ∀ z : ℕ, (z : ℝ) ∈ Set.Icc y (y + Real.log y ^ C) →
          z ∈ Set.Ioc n (n + k) := by
        intro z hz
        have hz1 := hz.1
        have hz2 := hz.2
        constructor
        · exact_mod_cast (show (n : ℝ) < z by linarith)
        · exact_mod_cast (show (z : ℝ) ≤ (n : ℝ) + k by linarith)
      exact hab (hi (hmem a ha) (hmem b hb) ht)
    exact (Nat.cast_le.mpr hf).trans (Nat.floor_le (Real.rpow_nonneg hL.le _))
