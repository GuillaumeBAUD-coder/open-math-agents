import OMAReductions.R_Borsuk_borsuk_conjecture_not_of_nine_le_R1
import Mathlib

-- Explicit construction: f x = (x, 0) and q i = (0, e_i + t * 1) with k t^2 + 2 t = 1/4.

namespace BorP2

lemma dsq {m : ℕ} (v w : Fin m → ℝ) :
    dist (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin m)) (WithLp.toLp 2 w) ^ 2 = ∑ l, (v l - w l) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  simp [Real.dist_eq, sq_abs]

lemma of_sq {d : ℝ} (hd : 0 ≤ d) (h : d ^ 2 = 2) : d = Real.sqrt 2 := by
  rw [← h, Real.sqrt_sq hd]

theorem t_eq (k : ℕ) : let t : ℝ := 1 / (2 * (2 + Real.sqrt (4 + k)));
    (k : ℝ) * t ^ 2 + 2 * t = 1 / 4 := by
  intro t
  have hr : Real.sqrt (4 + k) ^ 2 = 4 + k := Real.sq_sqrt (by positivity)
  have hpos : 0 < 2 + Real.sqrt (4 + k) := by positivity
  simp only [t]
  field_simp
  nlinarith [hr]

end BorP2

open BorP2 in
theorem OMA.solution : OMA.R_Borsuk_borsuk_conjecture_not_of_nine_le_R1.H2 := by
  unfold OMA.R_Borsuk_borsuk_conjecture_not_of_nine_le_R1.H2
  intro k
  set t : ℝ := 1 / (2 * (2 + Real.sqrt (4 + k))) with ht
  have htk : (k : ℝ) * t ^ 2 + 2 * t = 1 / 4 := t_eq k
  refine ⟨fun x => WithLp.toLp 2 (Fin.append (fun l => x l) (0 : Fin k → ℝ)),
    fun i => WithLp.toLp 2 (Fin.append (0 : Fin 9 → ℝ) (fun l => (if l = i then 1 else 0) + t)),
    ?_, ?_, ?_⟩
  · apply Isometry.of_dist_eq
    intro x y
    have h1 := dsq (Fin.append (fun l => x l) (0 : Fin k → ℝ)) (Fin.append (fun l => y l) (0 : Fin k → ℝ))
    rw [Fin.sum_univ_add] at h1
    simp only [Fin.append_left, Fin.append_right, Pi.zero_apply, sub_zero, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero, add_zero] at h1
    have h2 : dist x y ^ 2 = ∑ l, (x l - y l) ^ 2 := by
      rw [EuclideanSpace.dist_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
      simp [Real.dist_eq, sq_abs]
    rw [← h2] at h1
    rw [← Real.sqrt_sq (dist_nonneg (x := x)), ← h1, Real.sqrt_sq dist_nonneg]
  · intro i j hij
    apply of_sq dist_nonneg
    rw [dsq, Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, Pi.zero_apply, sub_zero, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero, zero_add]
    have : ∀ l : Fin k, ((if l = i then (1:ℝ) else 0) + t - ((if l = j then 1 else 0) + t)) ^ 2
        = (if l = i then 1 else 0) + (if l = j then 1 else 0) := by
      intro l
      by_cases hi : l = i <;> by_cases hj : l = j
      · exact absurd (hi.symm.trans hj) hij
      all_goals simp [hi, hj, hij, Ne.symm hij]
    rw [Finset.sum_congr rfl (fun l _ => this l), Finset.sum_add_distrib]
    simp
    norm_num
  · intro x hx i
    apply of_sq dist_nonneg
    rw [dsq, Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, Pi.zero_apply, sub_zero, zero_sub, neg_sq]
    have hx' : ∑ l, x l ^ 2 = 3 / 4 := by
      rw [← hx, EuclideanSpace.real_norm_sq_eq]
    rw [hx']
    have : ∀ l : Fin k, ((if l = i then (1:ℝ) else 0) + t) ^ 2
        = (if l = i then 1 + 2 * t else 0) + t ^ 2 := by
      intro l
      by_cases hi : l = i
      · simp [hi]; ring
      · simp [hi]
    rw [Finset.sum_congr rfl (fun l _ => this l), Finset.sum_add_distrib]
    simp
    linarith

