import OMAReductions.R_Erdos1099_erdos_1099_variants_factorial_R1
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Nat.Nth

/-!
The logarithms of the divisors form a partition symmetric about half the
logarithm of the integer. Cut the lower half at the logarithms of the
square roots of the earlier terms of the divisibility sequence. On each
piece, admissibility bounds the derivative of the gap cost by the
specified coefficient. Summing the piece lengths proves Tenenbaum's
Theorem 2 for power costs.
-/

-- Credit: @dk8827

open Finset Real
open scoped BigOperators

namespace OMA.DivisorGaps

private noncomputable def clip (a b x : ℝ) : ℝ := max a (min b x)

private theorem clip_mono (a b : ℝ) : Monotone (clip a b) :=
  fun _ _ h => max_le_max le_rfl (min_le_min le_rfl h)

private theorem clip_bounds {a b : ℝ} (hab : a ≤ b) (x : ℝ) :
    a ≤ clip a b x ∧ clip a b x ≤ b :=
  ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩

private theorem clip_reflect {a b : ℝ} (hab : a ≤ b) (M x : ℝ) :
    clip (M - b) (M - a) (M - x) = M - clip a b x := by
  rcases le_or_gt x a with hxa | hax
  · have hxb : x ≤ b := hxa.trans hab
    have hax' : M - a ≤ M - x := sub_le_sub_left hxa _
    have hba' : M - b ≤ M - a := sub_le_sub_left hab _
    simp [clip, min_eq_right hxb, min_eq_left hax', max_eq_right hba', max_eq_left hxa]
  · rcases le_or_gt b x with hbx | hxb
    · have hxb' : M - x ≤ M - b := sub_le_sub_left hbx _
      have hxa' : M - x ≤ M - a := hxb'.trans (sub_le_sub_left hab _)
      simp [clip, min_eq_left hbx, min_eq_right hxa', max_eq_left hxb', max_eq_right hab]
    · have hxa' : M - x ≤ M - a := sub_le_sub_left hax.le _
      have hbx' : M - b ≤ M - x := sub_le_sub_left hxb.le _
      simp [clip, min_eq_right hxb.le, min_eq_right hxa', max_eq_right hbx',
        max_eq_right hax.le]

private theorem clip_hinge {a b : ℝ} (hab : a ≤ b) (x : ℝ) :
    clip a b x - a = max 0 (x - a) - max 0 (x - b) := by
  by_cases hxa : x ≤ a
  · have hxb := hxa.trans hab
    simp [clip, min_eq_right hxb, max_eq_left hxa, max_eq_left (sub_nonpos.2 hxa),
      max_eq_left (sub_nonpos.2 hxb)]
  · have hax : a < x := lt_of_not_ge hxa
    by_cases hxb : x ≤ b
    · simp [clip, min_eq_right hxb, max_eq_right hax.le, max_eq_right (sub_nonneg.2 hax.le),
        max_eq_left (sub_nonpos.2 hxb)]
    · have hbx := (lt_of_not_ge hxb).le
      rw [clip, min_eq_left hbx, max_eq_right hab, max_eq_right (sub_nonneg.2 hax.le),
        max_eq_right (sub_nonneg.2 hbx)]
      ring

private theorem sum_differences (f : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ range n, (f (i + 1) - f i)) = f n - f 0 := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih]; ring

private theorem sum_clip {A : ℕ → ℝ} {m : ℕ} (hA : ∀ i < m, A i ≤ A (i + 1))
    {x y : ℝ} (hx : A 0 ≤ x) (hxm : x ≤ A m) (hy : A 0 ≤ y) (hym : y ≤ A m) :
    (∑ i ∈ range m, (clip (A i) (A (i + 1)) y - clip (A i) (A (i + 1)) x)) = y - x := by
  have key (u : ℝ) (hu : A 0 ≤ u) (hum : u ≤ A m) :
      (∑ i ∈ range m, (clip (A i) (A (i + 1)) u - A i)) = u - A 0 := by
    calc
      _ = ∑ i ∈ range m, (max 0 (u - A i) - max 0 (u - A (i + 1))) := by
        exact sum_congr rfl (fun i hi => clip_hinge (hA i (mem_range.1 hi)) u)
      _ = max 0 (u - A 0) - max 0 (u - A m) := by
        simpa only [neg_sub_neg] using (sum_differences (fun i => -(max 0 (u - A i))) m)
      _ = _ := by simp [max_eq_right (sub_nonneg.2 hu), max_eq_left (sub_nonpos.2 hum)]
  calc
    _ = (∑ i ∈ range m, (clip (A i) (A (i + 1)) y - A i)) -
          (∑ i ∈ range m, (clip (A i) (A (i + 1)) x - A i)) := by
        rw [← sum_sub_distrib]
        exact sum_congr rfl (fun i _ => by ring)
    _ = _ := by rw [key _ hy hym, key _ hx hxm]; ring

private noncomputable def score (α d : ℝ) : ℝ := (Real.exp d - 1) ^ α

private theorem score_superadditive {α x y : ℝ} (hα : 1 ≤ α) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    score α x + score α y ≤ score α (x + y) := by
  have ex : 0 ≤ Real.exp x - 1 := sub_nonneg.2 (Real.one_le_exp hx)
  have ey : 0 ≤ Real.exp y - 1 := sub_nonneg.2 (Real.one_le_exp hy)
  calc
    _ ≤ ((Real.exp x - 1) + (Real.exp y - 1)) ^ α := Real.add_rpow_le_rpow_add ex ey hα
    _ ≤ _ := Real.rpow_le_rpow (add_nonneg ex ey) (by
      rw [Real.exp_add]
      nlinarith only [mul_nonneg ex ey]) (by linarith)

private theorem reflected_gap {α a b M : ℝ} (hα : 1 ≤ α) (hab : a ≤ b) :
    score α (b - a) ≤
      (score α (b - a) - score α (b - clip a b (M / 2))) +
        (score α ((M - a) - (M - b)) -
          score α ((M - a) - clip (M - b) (M - a) (M / 2))) := by
  have hmid : M - M / 2 = M / 2 := by ring
  have he := clip_reflect hab M (M / 2)
  rw [hmid] at he
  rw [he]
  have he₁ : (M - a) - (M - b) = b - a := by ring
  have he₂ : (M - a) - (M - clip a b (M / 2)) = clip a b (M / 2) - a := by ring
  rw [he₁, he₂]
  have h := score_superadditive hα
    (sub_nonneg.2 (clip_bounds hab (M / 2)).2) (sub_nonneg.2 (clip_bounds hab (M / 2)).1)
  rw [show (b - clip a b (M / 2)) + (clip a b (M / 2) - a) = b - a by ring] at h
  linarith only [h]

private theorem shell_bound {α a b u v ε : ℝ}
    (hα : 1 < α) (hab : a ≤ b) (huv : u ≤ v) (hε : 0 < ε)
    (hclose : ∀ x : ℝ, u < x → x < v → a < x → x < b → Real.exp (b - x) ≤ 1 + ε) :
    score α (b - clip a b u) - score α (b - clip a b v) ≤
      (1 + ε) * (α * ε ^ (α - 1)) * (clip a b v - clip a b u) := by
  let x := clip a b u
  let y := clip a b v
  have hxy : x ≤ y := clip_mono a b huv
  rcases eq_or_lt_of_le hxy with h | h
  · simp [show clip a b u = clip a b v from h]
  have hxu : u ≤ x := by
    have hub : u ≤ b := by
      by_contra! hub
      have he : x = b := by simp [x, clip, min_eq_left hub.le, max_eq_right hab]
      have hyb : y ≤ b := (clip_bounds hab v).2
      rw [← he] at hyb
      exact (not_lt_of_ge hyb) h
    exact (min_eq_right hub ▸ le_max_right a (min b u))
  have hyv : y ≤ v := by
    apply max_le _ (min_le_right _ _)
    by_contra! hva
    have he : y = a := by
      have : min b v ≤ a := (min_le_right _ _).trans hva.le
      simp [y, clip, max_eq_left this]
    have hax : a ≤ x := (clip_bounds hab u).1
    rw [← he] at hax
    exact (not_lt_of_ge hax) h
  let f (t : ℝ) := score α (b - t)
  let f' (t : ℝ) := -Real.exp (b - t) * (α * (Real.exp (b - t) - 1) ^ (α - 1))
  have hbase : Differentiable ℝ (fun t : ℝ => Real.exp (b - t) - 1) := by fun_prop
  have hf : ContinuousOn f (Set.Icc x y) :=
    (hbase.rpow_const (fun _ => Or.inr hα.le)).continuous.continuousOn
  have hf' (t : ℝ) (_ : t ∈ Set.Ioo x y) : HasDerivAt f (f' t) t := by
    have hlin := (hasDerivAt_const t b).sub (hasDerivAt_id t)
    have hexp := ((Real.hasDerivAt_exp (b - t)).comp t hlin).sub_const 1
    have hd := (Real.hasDerivAt_rpow_const (p := α)
      (x := Real.exp (b - t) - 1) (Or.inr hα.le)).comp t hexp
    convert hd using 1 <;> first
    | rfl
    | simp [f', mul_comm, mul_left_comm]
  obtain ⟨t, ht, hderiv⟩ := exists_hasDerivAt_eq_slope f f' h hf hf'
  have hnear : Real.exp (b - t) ≤ 1 + ε :=
    hclose t (hxu.trans_lt ht.1) (ht.2.trans_le hyv)
      ((clip_bounds hab u).1.trans_lt ht.1) (ht.2.trans_le (clip_bounds hab v).2)
  have hnonneg : 0 ≤ Real.exp (b - t) - 1 :=
    sub_nonneg.2 (Real.one_le_exp (sub_nonneg.2 (ht.2.trans_le (clip_bounds hab v).2).le))
  have hpow : (Real.exp (b - t) - 1) ^ (α - 1) ≤ ε ^ (α - 1) :=
    Real.rpow_le_rpow hnonneg (by linarith only [hnear]) (by linarith)
  have hmul : Real.exp (b - t) * (α * (Real.exp (b - t) - 1) ^ (α - 1)) ≤
      (1 + ε) * (α * ε ^ (α - 1)) := by
    have hα0 : 0 < α := by linarith
    apply mul_le_mul hnear (mul_le_mul_of_nonneg_left hpow hα0.le)
      (mul_nonneg hα0.le (Real.rpow_nonneg hnonneg _))
      (by linarith)
  have hfv := (eq_div_iff (sub_pos.2 h).ne').1 hderiv
  change _ ≤ _ * (y - x)
  have hstep := mul_le_mul_of_nonneg_right hmul (sub_nonneg.2 h.le)
  dsimp only [f', f] at hfv
  linarith only [hfv, hstep]


theorem partition_bound (α : ℝ) (hα : 1 < α)
    (A S : ℕ → ℝ) (m r : ℕ) (ε : ℕ → ℝ)
    (hA : MonotoneOn A (Set.Iic m)) (hA0 : A 0 = 0)
    (hR : ∀ i ≤ m, A (m - i) = A m - A i)
    (hs : Monotone S) (hs0 : S 0 = 0) (hsr : S r = A m / 2)
    (hε : ∀ j < r, 0 < ε j)
    (hclose : ∀ i < m, ∀ j < r, ∀ x : ℝ,
      S j < x → x < S (j + 1) → A i < x → x < A (i + 1) →
      Real.exp (A (i + 1) - x) ≤ 1 + ε j) :
    (∑ i ∈ range m, score α (A (i + 1) - A i)) ≤
      2 * ∑ j ∈ range r, (1 + ε j) * (α * (ε j) ^ (α - 1)) * (S (j + 1) - S j) := by
  let H (i : ℕ) := score α (A (i + 1) - A i)
  let G (i : ℕ) := H i - score α (A (i + 1) - clip (A i) (A (i + 1)) (A m / 2))
  have hA' (i : ℕ) (hi : i < m) : A i ≤ A (i + 1) :=
    hA (by exact hi.le) (by exact hi) (Nat.le_succ _)
  have hmid (i : ℕ) (hi : i < m) : H i ≤ G i + G (m - 1 - i) := by
    have hlo : A (m - 1 - i) = A m - A (i + 1) := by
      rw [show m - 1 - i = m - (i + 1) by omega]
      exact hR _ (by omega)
    have hhi : A (m - 1 - i + 1) = A m - A i := by
      rw [show m - 1 - i + 1 = m - i by omega]
      exact hR i hi.le
    dsimp only [H, G]
    rw [hlo, hhi]
    exact reflected_gap hα.le (hA' i hi)
  have hsymmetric : (∑ i ∈ range m, H i) ≤ 2 * ∑ i ∈ range m, G i := by
    calc
      _ ≤ ∑ i ∈ range m, (G i + G (m - 1 - i)) :=
        sum_le_sum (fun i hi => hmid i (mem_range.1 hi))
      _ = _ := by rw [sum_add_distrib, sum_range_reflect G m, two_mul]
  let C (i j : ℕ) := clip (A i) (A (i + 1)) (S j)
  let L (i j : ℕ) := score α (A (i + 1) - C i j)
  let K (j : ℕ) := (1 + ε j) * (α * (ε j) ^ (α - 1))
  have hsplit (i : ℕ) (hi : i < m) :
      G i = ∑ j ∈ range r, (L i j - L i (j + 1)) := by
    have h := sum_differences (fun j => -(L i j)) r
    simp only [neg_sub_neg] at h
    have hleft : C i 0 = A i := by
      have hAi : 0 ≤ A i := by
        rw [← hA0]
        exact hA (by exact Nat.zero_le _) (by exact hi.le) (Nat.zero_le _)
      have hBi := hAi.trans (hA' i hi)
      simp [C, clip, hs0, min_eq_right hBi, max_eq_left hAi]
    have hright : C i r = clip (A i) (A (i + 1)) (A m / 2) := by simp [C, hsr]
    simpa only [G, L, H, hleft, hright] using h.symm
  have hterm (i : ℕ) (hi : i < m) (j : ℕ) (hj : j < r) :
      L i j - L i (j + 1) ≤ K j * (C i (j + 1) - C i j) :=
    shell_bound hα (hA' i hi) (hs (Nat.le_succ _)) (hε j hj) (hclose i hi j hj)
  have hC (j : ℕ) (hj : j < r) :
      (∑ i ∈ range m, (C i (j + 1) - C i j)) = S (j + 1) - S j := by
    have hAm : 0 ≤ A m := by rw [← hA0]; exact hA (by exact Nat.zero_le _) (by exact Nat.le_refl _) (Nat.zero_le _)
    have upper (k : ℕ) (hk : k ≤ r) : S k ≤ A m := by
      have h := hs hk
      rw [hsr] at h
      linarith only [h, hAm]
    have lower (k : ℕ) : A 0 ≤ S k := by
      rw [hA0, ← hs0]
      exact hs (Nat.zero_le _)
    exact sum_clip hA' (lower j) (upper j hj.le) (lower _) (upper _ hj)
  apply hsymmetric.trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  calc
    (∑ i ∈ range m, G i) = ∑ i ∈ range m, ∑ j ∈ range r, (L i j - L i (j + 1)) :=
      sum_congr rfl (fun i hi => hsplit i (mem_range.1 hi))
    _ ≤ ∑ i ∈ range m, ∑ j ∈ range r, K j * (C i (j + 1) - C i j) :=
      sum_le_sum (fun i hi => sum_le_sum (fun j hj => hterm i (mem_range.1 hi) j (mem_range.1 hj)))
    _ = ∑ j ∈ range r, ∑ i ∈ range m, K j * (C i (j + 1) - C i j) := Finset.sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro j hj
      rw [← mul_sum, hC j (mem_range.1 hj)]

private theorem sorted_divisors (M : ℕ) :
    M.divisorsAntidiagonalList.map Prod.fst = M.divisors.sort := by
  apply Nat.sortedLT_map_fst_divisorsAntidiagonalList.eq_of_mem_iff (sortedLT_sort _)
  intro d
  simp only [List.mem_map, mem_sort, Nat.mem_divisorsAntidiagonalList, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨a, b⟩, ⟨he, hM⟩, rfl⟩
    exact ⟨⟨b, he.symm⟩, hM⟩
  · rintro ⟨hD, hM⟩
    obtain ⟨q, hq⟩ := hD
    exact ⟨(d, q), ⟨hq.symm, hM⟩, rfl⟩

private theorem divisor_finite {M : ℕ} (hM : M ≠ 0) :
    (Set.ofPred (fun k : ℕ => k ∣ M)).Finite :=
  M.divisors.finite_toSet.subset (fun _ h => Nat.mem_divisors.2 ⟨h, hM⟩)

private theorem divisors_toFinset {M : ℕ} (hM : M ≠ 0) :
    (divisor_finite hM).toFinset = M.divisors := by
  ext x
  simp [Nat.mem_divisors, hM]

private theorem reciprocal_nth {M i : ℕ} (hM : M ≠ 0) (hi : i < M.divisors.card) :
    Nat.nth (· ∣ M) (M.divisors.card - 1 - i) * Nat.nth (· ∣ M) i = M := by
  let L := M.divisorsAntidiagonalList
  have hsort : L.map Prod.fst = M.divisors.sort := sorted_divisors M
  have hlen : L.length = M.divisors.card := by
    simpa using congrArg List.length hsort
  have hiL : i < L.length := by rwa [hlen]
  have hrev : i < L.reverse.length := by simpa using hiL
  have hit (j : ℕ) (hj : j < L.length) : Nat.nth (· ∣ M) j = L[j].1 := by
    rw [Nat.nth_eq_getD_sort (divisor_finite hM), divisors_toFinset hM, ← hsort]
    rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map]
  have himap : i < (L.map Prod.swap).length := by simpa using hiL
  have hflip : L[L.length - 1 - i] = L[i].swap := by
    calc
      _ = L.reverse[i] := (List.getElem_reverse hrev).symm
      _ = (L.map Prod.swap)[i] :=
        List.getElem_of_eq (Nat.reverse_divisorsAntidiagonalList M) hrev
      _ = _ := by rw [List.getElem_map]
  have hprod : L[i].1 * L[i].2 = M :=
    (Nat.mem_divisorsAntidiagonalList.1 (List.getElem_mem hiL)).1
  rw [← hlen, hit i hiL, hit (L.length - 1 - i) (by omega)]
  exact (by rw [hflip]; simpa [mul_comm] using hprod)

end OMA.DivisorGaps

set_option maxHeartbeats 1000000 in
theorem OMA.solution : OMA.R_Erdos1099_erdos_1099_variants_factorial_R1.H2 := by
  classical
  intro α hα N ε hN0 hN1 hNpos hdiv hε hadm n
  by_cases hn0 : n = 0
  · subst n
    rw [hN0]
    unfold Erdos1099.h
    rw [Nat.divisors_one, Finset.card_singleton, Nat.sub_self, Fin.sum_univ_zero]
    simp
  have hn : 1 ≤ n := Nat.pos_of_ne_zero hn0
  let M := N n
  have hM : M ≠ 0 := (hNpos n).ne'
  let m := M.divisors.card - 1
  let d : ℕ → ℕ := Nat.nth (· ∣ M)
  let A (i : ℕ) := Real.log (d i : ℝ)
  let hf := OMA.DivisorGaps.divisor_finite hM
  have hfin : hf.toFinset = M.divisors := OMA.DivisorGaps.divisors_toFinset hM
  have hcard : 0 < M.divisors.card :=
    card_pos.2 ⟨1, Nat.mem_divisors.2 ⟨one_dvd M, hM⟩⟩
  have hidx (i : ℕ) (hi : i ≤ m) : i < hf.toFinset.card := by
    rw [hfin]
    dsimp only [m] at hi
    omega
  have hdvd (i : ℕ) (hi : i ≤ m) : d i ∣ M := Nat.nth_mem_of_lt_card hf (hidx i hi)
  have hdpos (i : ℕ) (hi : i ≤ m) : (0 : ℝ) < d i := by
    exact_mod_cast Nat.pos_of_mem_divisors (Nat.mem_divisors.2 ⟨hdvd i hi, hM⟩)
  have dmono (i j : ℕ) (hij : i ≤ j) (hj : j ≤ m) : d i ≤ d j :=
    Nat.nth_le_nth_of_lt_card hf hij (hidx j hj)
  have hd0 : d 0 = 1 := by
    refine le_antisymm ?_ (by exact_mod_cast hdpos 0 (Nat.zero_le _))
    exact (Nat.isLeast_nth_of_lt_card hf (hidx 0 (Nat.zero_le _))).2
      ⟨one_dvd M, fun k hk => (Nat.not_lt_zero _ hk).elim⟩
  have hdm : d m = M := by
    refine le_antisymm (Nat.le_of_dvd (hNpos n) (hdvd m le_rfl)) ?_
    obtain ⟨i, hi, he⟩ := Nat.exists_lt_card_finite_nth_eq hf (dvd_refl M)
    rw [hfin] at hi
    have him : i ≤ m := by dsimp only [m]; omega
    have hm := dmono i m him le_rfl
    change d i = M at he
    rwa [he] at hm
  have hA : MonotoneOn A (Set.Iic m) := by
    intro i hi j hj hij
    exact Real.log_le_log (hdpos i hi) (by exact_mod_cast dmono i j hij hj)
  have hA0 : A 0 = 0 := by simp [A, hd0]
  have hAm : A m = Real.log (M : ℝ) := by simp [A, hdm]
  have hR (i : ℕ) (hi : i ≤ m) : A (m - i) = A m - A i := by
    have hi' : i < M.divisors.card := by
      have := hidx i hi
      rwa [hfin] at this
    have he : d (m - i) * d i = M := OMA.DivisorGaps.reciprocal_nth hM hi'
    have hcast : (d (m - i) : ℝ) * (d i : ℝ) = (M : ℝ) := by exact_mod_cast he
    have hlog := congrArg Real.log hcast
    rw [Real.log_mul (hdpos _ (Nat.sub_le _ _)).ne' (hdpos _ hi).ne'] at hlog
    change A (m - i) + A i = Real.log (M : ℝ) at hlog
    linarith only [hlog, hAm]
  have hDvd (i j : ℕ) (hij : i ≤ j) : N i ∣ N j := by
    induction hij with
    | refl => exact dvd_refl _
    | step _ ih => exact ih.trans (hdiv _)
  have hNmono : Monotone N := fun i j hij => Nat.le_of_dvd (hNpos j) (hDvd i j hij)
  let S (j : ℕ) := Real.log (N (j + 1) : ℝ) / 2
  let r := n - 1
  have hs : Monotone S := by
    intro i j hij
    apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 2)
    exact Real.log_le_log (by exact_mod_cast hNpos (i + 1))
      (by exact_mod_cast hNmono (Nat.add_le_add_right hij 1))
  have hs0 : S 0 = 0 := by simp [S, hN1]
  have hsr : S r = A m / 2 := by
    change Real.log (N (n - 1 + 1) : ℝ) / 2 = _
    rw [Nat.sub_add_cancel hn, hAm]
  have es (j : ℕ) : Real.exp (S j) = √((N (j + 1) : ℕ) : ℝ) := by
    have hpositive : 0 < √((N (j + 1) : ℕ) : ℝ) :=
      Real.sqrt_pos.2 (by exact_mod_cast hNpos (j + 1))
    rw [show S j = Real.log (√((N (j + 1) : ℕ) : ℝ)) by
      rw [Real.log_sqrt (by positivity)], Real.exp_log hpositive]
  have eA (i : ℕ) (hi : i ≤ m) : Real.exp (A i) = (d i : ℝ) :=
    Real.exp_log (hdpos i hi)
  have hclose : ∀ i < m, ∀ j < r, ∀ x : ℝ,
      S j < x → x < S (j + 1) → A i < x → x < A (i + 1) →
      Real.exp (A (i + 1) - x) ≤ 1 + ε (j + 2) := by
    intro i hi j hj x hjs hxj hix _hx
    have hjn : j + 2 ≤ n := by dsimp only [r] at hj; omega
    have hjpred : j + 2 - 1 = j + 1 := by omega
    have hleft : √((N (j + 2 - 1) : ℕ) : ℝ) < Real.exp x := by
      rw [hjpred, ← es j]
      exact Real.exp_lt_exp.2 hjs
    have hright : Real.exp x ≤ √((N (j + 2) : ℕ) : ℝ) := by
      rw [← es (j + 1)]
      exact (Real.exp_lt_exp.2 hxj).le
    obtain ⟨b, hb, hxb, hub⟩ := hadm (j + 2) (by omega) (Real.exp x) hleft hright
    have hbM : b ∣ M := hb.trans (hDvd _ _ hjn)
    have hdb : d i < b := by
      have ht := Real.exp_lt_exp.2 hix
      rw [eA i hi.le] at ht
      exact_mod_cast ht.trans hxb
    have hnext : d (i + 1) ≤ b :=
      (Nat.isLeast_nth_of_lt_card hf (hidx _ hi)).2
        ⟨hbM, fun k hk => (dmono k i (by omega) hi.le).trans_lt hdb⟩
    rw [Real.exp_sub, eA _ hi]
    apply (div_le_iff₀ (Real.exp_pos x)).2
    exact (show (d (i + 1) : ℝ) ≤ (b : ℝ) by exact_mod_cast hnext).trans hub
  let W (k : ℕ) := (1 + ε k) * (α * (ε k) ^ (α - 1))
  have hscore (i : ℕ) (hi : i < m) :
      OMA.DivisorGaps.score α (A (i + 1) - A i) =
        ((d (i + 1) : ℝ) / (d i : ℝ) - 1) ^ α := by
    unfold OMA.DivisorGaps.score
    rw [Real.exp_sub, eA _ hi, eA _ hi.le]
  have hpart := OMA.DivisorGaps.partition_bound α hα A S m r (fun j => ε (j + 2))
    hA hA0 hR hs hs0 hsr (fun j _ => hε (j + 2) (by omega)) hclose
  calc
    Erdos1099.h α (N n) = ∑ i ∈ range m, OMA.DivisorGaps.score α (A (i + 1) - A i) := by
      change (∑ i : Fin m, ((d ((i : ℕ) + 1) : ℝ) / (d i : ℝ) - 1) ^ α) = _
      rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => ((d (i + 1) : ℝ) / (d i : ℝ) - 1) ^ α)]
      apply sum_congr rfl
      intro i hi
      exact (hscore i (mem_range.1 hi)).symm
    _ ≤ 2 * ∑ j ∈ range r, W (j + 2) * (S (j + 1) - S j) := hpart
    _ = ∑ k ∈ Icc 2 n, W k * Real.log ((N k : ℝ) / (N (k - 1) : ℝ)) := by
      have hI : Icc 2 n = Ico 2 (r + 2) := by
        ext k
        simp only [mem_Icc, mem_Ico]
        dsimp only [r]
        omega
      rw [hI, ← Finset.sum_Ico_add' (fun k => W k * Real.log ((N k : ℝ) / (N (k - 1) : ℝ))) 0 r
        (c := 2), Nat.Ico_zero_eq_range, mul_sum]
      apply sum_congr rfl
      intro j _
      rw [Real.log_div (by exact_mod_cast (hNpos (j + 2)).ne')
        (by exact_mod_cast (hNpos (j + 2 - 1)).ne')]
      have hj : j + 2 - 1 = j + 1 := by omega
      rw [hj]
      dsimp only [S]
      ring
