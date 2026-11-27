import OMAReductions.R_Borsuk_borsuk_conjecture_not_of_nine_le_R1

-- Step Borsuk.borsuk_conjecture.not_of_nine_le.R1.H2: hypothesis H2 of reduction Borsuk.borsuk_conjecture.not_of_nine_le.R1

/-!
Embed `ℝ⁹` as the first nine coordinates of `ℝ^(9+k)`. In the last `k` coordinates put
`q i = e_i + t (1, …, 1)` with `k t² + 2 t = 1/4`, that is `t = (√(1 + k/4) - 1) / k`. Then
`‖q i‖² = 1 + 2 t + k t² = 5/4`, so a point `x` with `‖x‖² = 3/4` is at squared distance
`3/4 + 5/4 = 2` from `q i`, and `‖q i - q j‖² = ‖e_i - e_j‖² = 2` for `i ≠ j`.
-/

namespace OMA

/-- Squared distance of two points given by blocks of coordinates. -/
theorem dist_sq_append (k : ℕ) (u u' : Fin 9 → ℝ) (v v' : Fin k → ℝ) :
    dist (WithLp.toLp 2 (Fin.append u v) : EuclideanSpace ℝ (Fin (9 + k)))
        (WithLp.toLp 2 (Fin.append u' v')) ^ 2 =
      ∑ a, (u a - u' a) ^ 2 + ∑ l, (v l - v' l) ^ 2 := by
  rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_add]
  simp only [PiLp.toLp_apply, Fin.append_left, Fin.append_right, Real.dist_eq, sq_abs]

theorem sum_delta_sq (k : ℕ) (i j : Fin k) (hij : i ≠ j) (t : ℝ) :
    ∑ l : Fin k, (((if l = i then (1 : ℝ) else 0) + t) - ((if l = j then (1 : ℝ) else 0) + t)) ^ 2
      = 2 := by
  have h : ∀ l : Fin k,
      (((if l = i then (1 : ℝ) else 0) + t) - ((if l = j then (1 : ℝ) else 0) + t)) ^ 2 =
        (if l = i then (1 : ℝ) else 0) + (if l = j then (1 : ℝ) else 0) := by
    intro l
    by_cases h1 : l = i
    · have h2 : ¬ l = j := fun h => hij (h1.symm.trans h)
      rw [if_pos h1, if_neg h2]
      ring
    · by_cases h2 : l = j
      · rw [if_neg h1, if_pos h2]
        ring
      · rw [if_neg h1, if_neg h2]
        ring
  rw [Finset.sum_congr rfl (fun l _ => h l), Finset.sum_add_distrib]
  simp
  norm_num

theorem sum_delta_t (k : ℕ) (i : Fin k) (t : ℝ) :
    ∑ l : Fin k, ((0 : ℝ) - ((if l = i then (1 : ℝ) else 0) + t)) ^ 2 =
      1 + 2 * t + (k : ℝ) * t ^ 2 := by
  have h : ∀ l : Fin k, ((0 : ℝ) - ((if l = i then (1 : ℝ) else 0) + t)) ^ 2 =
      (if l = i then (1 + 2 * t : ℝ) else 0) + t ^ 2 := by
    intro l
    by_cases h1 : l = i
    · rw [if_pos h1, if_pos h1]
      ring
    · rw [if_neg h1, if_neg h1]
      ring
  rw [Finset.sum_congr rfl (fun l _ => h l), Finset.sum_add_distrib]
  simp

theorem t_eq (k : ℕ) (hk : 0 < k) :
    (k : ℝ) * ((Real.sqrt (1 + (k : ℝ) / 4) - 1) / (k : ℝ)) ^ 2 +
      2 * ((Real.sqrt (1 + (k : ℝ) / 4) - 1) / (k : ℝ)) = 1 / 4 := by
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hs : Real.sqrt (1 + (k : ℝ) / 4) ^ 2 = 1 + (k : ℝ) / 4 :=
    Real.sq_sqrt (by positivity)
  generalize Real.sqrt (1 + (k : ℝ) / 4) = s at hs
  have e : (k : ℝ) * ((s - 1) / (k : ℝ)) ^ 2 + 2 * ((s - 1) / (k : ℝ)) =
      (s ^ 2 - 1) / (k : ℝ) := by
    field_simp
    ring
  rw [e, hs]
  field_simp
  ring

end OMA

theorem OMA.solution : OMA.R_Borsuk_borsuk_conjecture_not_of_nine_le_R1.H2 := by
  unfold OMA.R_Borsuk_borsuk_conjecture_not_of_nine_le_R1.H2
  intro k
  refine ⟨fun x => WithLp.toLp 2 (Fin.append (fun a => x a) (fun _ => (0 : ℝ))),
    fun i => WithLp.toLp 2 (Fin.append (fun _ => (0 : ℝ))
      (fun l => (if l = i then (1 : ℝ) else 0) +
        (Real.sqrt (1 + (k : ℝ) / 4) - 1) / (k : ℝ))), ?_, ?_, ?_⟩
  · apply Isometry.of_dist_eq
    intro x y
    have h : dist (WithLp.toLp 2 (Fin.append (fun a => x a) (fun _ => (0 : ℝ))) :
          EuclideanSpace ℝ (Fin (9 + k)))
        (WithLp.toLp 2 (Fin.append (fun a => y a) (fun _ => (0 : ℝ)))) ^ 2 = dist x y ^ 2 := by
      rw [OMA.dist_sq_append, EuclideanSpace.dist_sq_eq]
      simp only [Real.dist_eq, sq_abs]
      simp
    exact (pow_left_inj₀ dist_nonneg dist_nonneg two_ne_zero).mp h
  · intro i j hij
    have h := OMA.dist_sq_append k (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ))
      (fun l => (if l = i then (1 : ℝ) else 0) + (Real.sqrt (1 + (k : ℝ) / 4) - 1) / (k : ℝ))
      (fun l => (if l = j then (1 : ℝ) else 0) + (Real.sqrt (1 + (k : ℝ) / 4) - 1) / (k : ℝ))
    rw [OMA.sum_delta_sq k i j hij] at h
    simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      Finset.sum_const_zero, zero_add] at h
    rw [← Real.sqrt_sq (dist_nonneg (α := EuclideanSpace ℝ (Fin (9 + k)))), h]
  · intro x hx i
    have hk : 0 < k := Fin.pos i
    have h := OMA.dist_sq_append k (fun a => x a) (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ))
      (fun l => (if l = i then (1 : ℝ) else 0) + (Real.sqrt (1 + (k : ℝ) / 4) - 1) / (k : ℝ))
    rw [OMA.sum_delta_t k i] at h
    have hn : ∑ a : Fin 9, (x a - 0) ^ 2 = 3 / 4 := by
      rw [← hx, EuclideanSpace.real_norm_sq_eq]
      simp
    have ht := OMA.t_eq k hk
    rw [hn] at h
    have h2 : dist (WithLp.toLp 2 (Fin.append (fun a => x a) (fun _ => (0 : ℝ))) :
          EuclideanSpace ℝ (Fin (9 + k)))
        (WithLp.toLp 2 (Fin.append (fun _ => (0 : ℝ))
          (fun l => (if l = i then (1 : ℝ) else 0) +
            (Real.sqrt (1 + (k : ℝ) / 4) - 1) / (k : ℝ)))) ^ 2 = 2 := by
      rw [h]
      linarith
    rw [← Real.sqrt_sq (dist_nonneg (α := EuclideanSpace ℝ (Fin (9 + k)))), h2]
