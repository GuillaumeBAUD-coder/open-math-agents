import FormalConjectures.ErdosProblems.«652»

/-! Place the remaining points on the unit circle around the origin. -/

open scoped EuclideanGeometry

theorem OMA.solution : type_of% @Erdos652.erdos_652.variants.first := by
  classical
  let : DecidableEq ℝ² := Classical.decEq _
  let : DecidableEq ℝ := Classical.decEq _
  intro n hn
  let t (i : Fin (n - 1)) : ℝ := i.val / (n : ℝ)
  let p (i : Fin (n - 1)) : ℝ² := WithLp.toLp 2 ![t i, Real.sqrt (1 - t i ^ 2)]
  have hn' : 0 < (n : ℝ) := by positivity
  have hi : Function.Injective p := by
    intro i j h
    apply Fin.ext
    exact_mod_cast (div_left_inj' hn'.ne').mp (congrArg (fun x : ℝ² => x 0) h)
  have hd (i) : dist (p i) 0 = 1 := by
    have ht : t i ≤ 1 := (div_le_one hn').2 (by exact_mod_cast (show i.val ≤ n by omega))
    have ht' : 0 ≤ t i := by dsimp [t]; positivity
    have hs : 0 ≤ 1 - t i ^ 2 := by nlinarith [mul_nonneg (sub_nonneg.mpr ht) ht']
    rw [dist_zero_right, ← sq_eq_sq₀ (norm_nonneg _) zero_le_one,
      EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
    change t i ^ 2 + Real.sqrt (1 - t i ^ 2) ^ 2 = 1 ^ 2
    rw [Real.sq_sqrt hs]
    ring
  let s := Finset.univ.map ⟨p, hi⟩
  have hc : s.card = n - 1 := by simp [s]
  have h (x) (hx : x ∈ s) : dist x 0 = 1 := by
    obtain ⟨i, -, rfl⟩ := Finset.mem_map.mp hx
    exact hd i
  have h0 : (0 : ℝ²) ∉ s := fun hx => by simpa using h 0 hx
  refine ⟨insert 0 s, ?_, 0, Finset.mem_insert_self _ _, ?_⟩
  · rw [Finset.card_insert_of_notMem h0, hc]; omega
  · rw [distinctDistancesFrom, Finset.erase_insert h0,
      Finset.image_congr h, Finset.image_const (Finset.card_pos.mp (by omega))]
    simp
