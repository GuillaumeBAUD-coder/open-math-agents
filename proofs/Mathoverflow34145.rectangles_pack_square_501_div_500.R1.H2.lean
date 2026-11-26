import OMAReductions.R_Mathoverflow34145_rectangles_pack_square_501_div_500_R1

/-! # Dyadic shelves for the infinite rectangle tail -/
-- Credit: @steveDOTdigital

namespace OMA.Shelves

open Mathoverflow34145 Set

private def level (n : ℕ) := (n+1).log2
private def base (n : ℕ) : ℝ := 2 ^ level n
private noncomputable def left (n : ℕ) : ℝ := ((n : ℝ) + 1 - base n) / base n
private noncomputable def bottom (n : ℕ) : ℝ := 1 + 1/512 - 2/base n

private theorem pos (n : ℕ) : 0 < base n := pow_pos (by norm_num) _

private theorem extent (n : ℕ) : base n ≤ (n : ℝ)+1 ∧ (n : ℝ)+2 ≤ 2*base n := by
  have lo := Nat.log2_self_le (Nat.succ_ne_zero n)
  have hi := Nat.lt_log2_self (n := n+1)
  rw [pow_succ] at hi
  have hi' : n+2 ≤ 2 * 2^(level n) := by
    unfold level
    rw [Nat.mul_comm]
    omega
  unfold base level at *
  constructor
  · exact_mod_cast lo
  · exact_mod_cast hi'

private noncomputable def cfg : Configuration where
  rect n := ⟨1/(n+1), 1/(n+2), (left n, bottom n), 0⟩
  rect_width _ := rfl
  rect_height _ := rfl

-- Every rectangle in a shelf fits inside its own square cell.
private theorem cell (n : ℕ) : (cfg.rect n).toSet ⊆
    Icc (left n) (left n + 1/base n) ×ˢ Icc (bottom n) (bottom n + 1/base n) := by
  have coord {z w t : ℝ} (w0 : 0 ≤ w) (hw : w ≤ 1/base n) (ht : t ∈ Icc 0 1) :
      z + w*t ∈ Icc z (z+1/base n) :=
    ⟨le_add_of_nonneg_right (mul_nonneg w0 ht.1),
      add_le_add_right ((mul_le_of_le_one_right w0 ht.2).trans hw) z⟩
  rintro _ ⟨_, ⟨p, hp, rfl⟩, rfl⟩
  change 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1 at hp
  simp only [cfg, rigidMotion, scale, Real.Angle.cos_zero, Real.Angle.sin_zero,
    mul_one, mul_zero, sub_zero, add_zero]
  exact ⟨coord (by positivity) (one_div_le_one_div_of_le (pos n) (extent n).1) ⟨hp.1,hp.2.1⟩,
    coord (by positivity) (one_div_le_one_div_of_le (pos n) (by linarith [(extent n).1])) hp.2.2⟩

private theorem whole (n : ℕ) (hn : 1023 ≤ n) :
    (cfg.rect n).toSet ⊆ Icc 0 1 ×ˢ Icc 1 (501/500) := by
  have bpos := pos n
  have lev : 10 ≤ level n := (Nat.le_log2 (Nat.succ_ne_zero n)).2 (by norm_num; omega)
  have big : (1024 : ℝ) ≤ base n := calc
    1024 = (2 : ℝ)^10 := by norm_num
    _ ≤ _ := pow_le_pow_right₀ (by norm_num) lev
  have x0 : 0 ≤ left n := div_nonneg (sub_nonneg.2 (extent n).1) bpos.le
  have x1 : left n + 1/base n ≤ 1 := by
    rw [left, ← add_div, div_le_one bpos]
    linarith [(extent n).2]
  have y0 : 1 ≤ bottom n := by
    have : 2/base n ≤ 1/512 := (div_le_iff₀ bpos).2 (by linarith)
    unfold bottom
    linarith
  have y1 : bottom n + 1/base n ≤ 501/500 := by
    unfold bottom
    linarith [show 0 < 1/base n from one_div_pos.2 bpos, show 2/base n = 2*(1/base n) by ring]
  intro p hp
  obtain ⟨hx,hy⟩ := cell n hp
  exact ⟨⟨x0.trans hx.1, hx.2.trans x1⟩, ⟨y0.trans hy.1, hy.2.trans y1⟩⟩

private theorem separate {m n : ℕ} (hmn : m < n) :
    interior (cfg.rect m).toSet ∩ interior (cfg.rect n).toSet = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.2
  intro p hp
  have hm := interior_mono (cell m) hp.1
  have hn := interior_mono (cell n) hp.2
  simp only [interior_prod_eq, interior_Icc] at hm hn
  have order : level m ≤ level n := (Nat.le_log2 (Nat.succ_ne_zero n)).2
    ((Nat.log2_self_le (Nat.succ_ne_zero m)).trans (by omega))
  rcases order.eq_or_lt with eq | lt
  · have same : base m = base n := by simp [base,eq]
    have dx : (m : ℝ)+1 ≤ n := by exact_mod_cast hmn
    have sep : left m + 1/base m ≤ left n := by
      rw [left, left, same, ← add_div]
      apply div_le_div_of_nonneg_right _ (pos n).le
      linarith
    exact hn.1.1.not_ge (hm.1.2.le.trans sep)
  · have twice : 2*base m ≤ base n := calc
      2*base m = 2^(level m + 1) := by simp [base,pow_succ,mul_comm]
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) lt
    have inv : 2/base n ≤ 1/base m := (div_le_div_iff₀ (pos n) (pos m)).2 (by linarith)
    have sep : bottom m + 1/base m ≤ bottom n := by
      unfold bottom
      linarith [show 2/base m = 2*(1/base m) by ring]
    exact hn.2.1.not_ge (hm.2.2.le.trans sep)

end OMA.Shelves

theorem OMA.solution : OMA.R_Mathoverflow34145_rectangles_pack_square_501_div_500_R1.H2 := by
  refine ⟨OMA.Shelves.cfg, OMA.Shelves.whole, ?_⟩
  intro m _ n _ hmn
  rcases lt_or_gt_of_ne hmn with h | h
  · exact OMA.Shelves.separate h
  · rw [Set.inter_comm]
    exact OMA.Shelves.separate h
