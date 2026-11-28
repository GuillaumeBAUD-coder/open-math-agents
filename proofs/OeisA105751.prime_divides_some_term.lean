import FormalConjectures.OEIS.«105751»

-- Shorter proof of OeisA105751.prime_divides_some_term via GaussianInt pairing
-- Credit: @B221393

open Finset

theorem OMA.solution : type_of% @OeisA105751.prime_divides_some_term := by
  intro p hp
  rcases hp.eq_two_or_odd' with rfl | ⟨m, hm⟩
  · exact ⟨4, by rw [OeisA105751.a_4]; norm_num⟩
  let g : ℕ → GaussianInt := fun k => ⟨1, k⟩
  have ha : ∀ n, OeisA105751.a n = (∏ k ∈ range (n + 1), g k).im := fun n => by
    have h : (∏ k ∈ range (n + 1), (1 + (k : ℂ) * Complex.I)) =
        GaussianInt.toComplex (∏ k ∈ range (n + 1), g k) := by
      rw [map_prod]; refine prod_congr rfl fun k _ => ?_
      rw [GaussianInt.toComplex_def']; push_cast; ring
    simp only [OeisA105751.a]; rw [h, ← GaussianInt.intCast_im, Int.floor_intCast]
  set Z : GaussianInt := ∏ k ∈ range p, g k with hZdef
  have hpair : Z = ∏ k ∈ range m, (g (k + 1) * g (m + (m - 1 - k) + 1)) := by
    rw [hZdef, hm, prod_range_succ', two_mul, prod_range_add,
      ← prod_range_reflect (fun k => g (m + k + 1)) m, ← prod_mul_distrib,
      show g 0 = 1 by ext <;> simp [g], mul_one]
  have hdvd : ∀ n ≤ m, (p : ℤ) ∣ (∏ k ∈ range n, g (k + 1) * g (m + (m - 1 - k) + 1)).im := by
    intro n; induction n with
    | zero => simp
    | succ n ih =>
      intro hn; rw [prod_range_succ, Zsqrtd.im_mul]
      exact dvd_add (dvd_mul_of_dvd_right ⟨1, by simp [g]; omega⟩ _) ((ih (by omega)).mul_right _)
  by_cases him : Z.im = 0
  · have hZ : Z ≠ 0 := prod_ne_zero_iff.2 fun k _ h => by simpa [g] using congrArg Zsqrtd.re h
    have hre : Z.re ≠ 0 := fun h => hZ (Zsqrtd.ext h him)
    have ha' : OeisA105751.a p = Z.re * p := by
      rw [ha, prod_range_succ, ← hZdef, Zsqrtd.im_mul, him]; simp [g]
    exact ⟨p, by simp [ha', hre, hp.ne_zero], by simp [ha']⟩
  · exact ⟨2 * m, by rw [ha, ← hm, ← hZdef]; exact him,
      by rw [ha, ← hm, ← hZdef, hpair]; exact hdvd m le_rfl⟩
