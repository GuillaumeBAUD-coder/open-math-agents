import OMAStatements.S_mo_106117
import Mathlib

open Filter
open OMA.S_mo_106117

namespace DehanCounterexample

open Classical in
noncomputable def f (k : ℕ) : ℝ :=
  if ∃ m : ℕ, k = m ^ 2 then 1 / 2 else min (1 / 2) (2 / (k : ℝ))

lemma f_nonneg (k : ℕ) : 0 ≤ f k := by
  classical
  unfold f
  split
  · norm_num
  · exact le_min (by norm_num) (by positivity)

lemma f_le (k : ℕ) : f k ≤ 1 / 2 := by
  classical
  unfold f
  split
  · rfl
  · exact min_le_left _ _

lemma f_sq (m : ℕ) : f (m ^ 2) = 1 / 2 := by
  classical
  exact if_pos ⟨m, rfl⟩

lemma f_lower {k : ℕ} (hk : 4 ≤ k) : 2 / (k : ℝ) ≤ f k := by
  classical
  have hkr : (4 : ℝ) ≤ k := by exact_mod_cast hk
  have hp : (0 : ℝ) < k := by linarith
  have h : 2 / (k : ℝ) ≤ 1 / 2 := by
    rw [div_le_iff₀ hp]
    linarith
  unfold f
  split
  · exact h
  · exact le_min h le_rfl

lemma no_square {m k : ℕ} (hlo : m ^ 2 < k) (hhi : k ≤ m ^ 2 + m) :
    ¬ ∃ d : ℕ, k = d ^ 2 := by
  rintro ⟨d, rfl⟩
  have hmd : m + 1 ≤ d := by
    by_contra! h
    have hdm : d ≤ m := by omega
    exact (not_le_of_gt hlo) (by gcongr)
  have hs : (m + 1) ^ 2 ≤ d ^ 2 := by gcongr
  nlinarith

lemma prod_bounds (m t : ℕ) :
    0 ≤ (∏ l ∈ Finset.Icc (m ^ 2) (m ^ 2 + t), (1 - f l)) ∧
    (∏ l ∈ Finset.Icc (m ^ 2) (m ^ 2 + t), (1 - f l)) ≤ 1 / 2 := by
  let s := Finset.Icc (m ^ 2) (m ^ 2 + t)
  have hj : m ^ 2 ∈ s := Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
  constructor
  · exact Finset.prod_nonneg fun l _ => by linarith [f_le l]
  · change (∏ l ∈ s, (1 - f l)) ≤ _
    rw [← Finset.mul_prod_erase s (fun l => 1 - f l) hj, f_sq]
    have hp : (∏ l ∈ s.erase (m ^ 2), (1 - f l)) ≤ 1 :=
      Finset.prod_le_one (fun l _ => by linarith [f_le l])
        (fun l _ => by linarith [f_nonneg l])
    nlinarith

lemma term_nonneg (m t : ℕ) : 0 ≤ dehanTerm f (m ^ 2) t := by
  exact div_nonneg (prod_bounds m t).1 (sq_nonneg _)

lemma term_lower {m t : ℕ} (hm : 8 ≤ m) (ht : t < m) :
    1 / 4 ≤ dehanTerm f (m ^ 2) t := by
  classical
  let j := m ^ 2
  let s := Finset.Icc j (j + t)
  let a : ℝ := 1 - 2 / (j : ℝ)
  have hj : j ∈ s := Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
  have hr : (8 : ℝ) ≤ m := by exact_mod_cast hm
  have htr : (t : ℝ) ≤ m := by exact_mod_cast ht.le
  have hcast : (j : ℝ) = (m : ℝ) ^ 2 := by simp [j]
  have hjp : (0 : ℝ) < j := by rw [hcast]; positivity
  have hfrac : (2 : ℝ) / j ≤ 1 := by
    rw [div_le_iff₀ hjp, hcast]
    nlinarith
  have ha : 0 ≤ a := sub_nonneg.mpr hfrac
  have hc : (s.erase j).card = t := by
    rw [Finset.card_erase_of_mem hj]
    simp [s, Nat.card_Icc]
    omega
  have hpow : (3 : ℝ) / 4 ≤ a ^ t := by
    have hb := one_add_mul_sub_le_pow (a := a) (by linarith) t
    have hratio : (t : ℝ) * (2 / (j : ℝ)) ≤ 1 / 4 := by
      rw [← mul_div_assoc, div_le_iff₀ hjp, hcast]
      nlinarith [mul_nonneg (show 0 ≤ (m : ℝ) by positivity) (sub_nonneg.mpr hr)]
    have heq : a - 1 = -(2 / (j : ℝ)) := by dsimp [a]; ring
    rw [heq, mul_neg] at hb
    linarith
  have hlower : (∏ l ∈ s.erase j, a) ≤ ∏ l ∈ s.erase j, (1 - f l) := by
    apply Finset.prod_le_prod (fun l _ => ha)
    intro l hl
    have hn := (Finset.mem_erase.mp hl).1
    obtain ⟨hle, hge⟩ := Finset.mem_Icc.mp (Finset.mem_erase.mp hl).2
    have hs := no_square (lt_of_le_of_ne hle (Ne.symm hn)) (by dsimp [j] at hge ⊢; omega)
    have hleR : (j : ℝ) ≤ l := by exact_mod_cast hle
    have hdiv : (2 : ℝ) / l ≤ 2 / j := div_le_div_of_nonneg_left (by norm_num) hjp hleR
    have hfl : f l ≤ 2 / (l : ℝ) := by
      unfold f
      rw [if_neg hs]
      exact min_le_right _ _
    exact sub_le_sub_left (hfl.trans hdiv) 1
  simp only [Finset.prod_const, hc] at hlower
  let A : ℝ := ∏ l ∈ s, (1 - f l)
  have hA : 1 / 4 ≤ A := by
    change 1 / 4 ≤ ∏ l ∈ s, (1 - f l)
    rw [← Finset.mul_prod_erase s (fun l => 1 - f l) hj]
    change 1 / 4 ≤ (1 - f (m ^ 2)) * _
    rw [f_sq]
    linarith [hpow.trans hlower]
  have hu : A ≤ 1 / 2 := (prod_bounds m t).2
  have hd : 0 < (1 - A) ^ 2 := pow_pos (by linarith) _
  change 1 / 4 ≤ A / (1 - A) ^ 2
  rw [le_div_iff₀ hd]
  have hb : (1 - A) ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg (show 0 ≤ A by linarith) (show 0 ≤ 2 - A by linarith)]
  linarith

end DehanCounterexample

theorem OMA.disproof :
    ¬ (∀ (f : ℕ → ℝ) (α c : ℝ), 1 < α → c < 1 →
      (∀ᶠ j : ℕ in atTop, α / (j : ℝ) ≤ f j ∧ f j ≤ c) →
      ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
        ∀ᶠ j : ℕ in atTop, ∃ π : ℝ, HasSum (dehanTerm f j) π ∧
          C₁ / (f j) ^ 2 ≤ π ∧ π ≤ C₂ / (f j) ^ 2) := by
  open DehanCounterexample in
  intro h
  have hf : ∀ᶠ j : ℕ in atTop, 2 / (j : ℝ) ≤ f j ∧ f j ≤ 1 / 2 :=
    eventually_atTop.mpr ⟨4, fun j hj => ⟨f_lower hj, f_le j⟩⟩
  obtain ⟨C₁, C₂, -, -, he⟩ := h f 2 (1 / 2) (by norm_num) (by norm_num) hf
  obtain ⟨N, hN⟩ := eventually_atTop.mp he
  obtain ⟨M, hM⟩ := exists_nat_gt (16 * C₂)
  let m := N + M + 8
  have hm : 8 ≤ m := by dsimp [m]; omega
  have hNm : N ≤ m ^ 2 := by
    have h : N ≤ m := by dsimp [m]; omega
    exact h.trans (by nlinarith [show 1 ≤ m by omega])
  have hMr : (M : ℝ) ≤ m := by exact_mod_cast (show M ≤ m by dsimp [m]; omega)
  obtain ⟨π, hs, -, hu⟩ := hN (m ^ 2) hNm
  have hsum : (∑ t ∈ Finset.range m, dehanTerm f (m ^ 2) t) ≤ π :=
    sum_le_hasSum (Finset.range m) (fun t _ => term_nonneg m t) hs
  have hl : (m : ℝ) / 4 ≤ ∑ t ∈ Finset.range m, dehanTerm f (m ^ 2) t := by
    calc
      (m : ℝ) / 4 = ∑ _t ∈ Finset.range m, (1 / 4 : ℝ) := by simp [div_eq_mul_inv]
      _ ≤ _ := Finset.sum_le_sum fun t ht => term_lower hm (Finset.mem_range.mp ht)
  rw [f_sq] at hu
  norm_num at hu
  linarith [hl.trans hsum]