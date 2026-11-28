import OMAStatements.S_mo_442949

/-!
MvG proposed sorting the segment lengths by projection in the discussion
of Mathematics Stack Exchange question 221764. Here strict improvement
under a transposition controls every maximizer, including a possible tie
in the projections. Concavity on the arc of headings gives unimodality.
The final transposition verifies the endpoint observation made by Arthur
Queiroz Moura in MathOverflow question 442949.
-/

namespace SegmentChain

open Finset OMA.S_mo_442949

private def coord {ι : Type*} [Fintype ι] (l f : ι → ℝ) : ℝ := ∑ i, l i * f i

private theorem coordinate_formula {n : ℕ} (l : Fin (n+1) → ℝ) (t : Fin n → ℝ) :
    endpointSquared l t = (coord l (fun i => Real.cos (headingAngle t i)))^2 +
      (coord l (fun i => Real.sin (headingAngle t i)))^2 := by
  simp [endpointSquared, Complex.normSq_apply, Complex.re_sum, Complex.im_sum,
    Complex.mul_re, Complex.mul_im, coord, pow_two]

private theorem swap_coord {ι : Type*} [Fintype ι] [DecidableEq ι] (l f : ι → ℝ)
    {i j : ι} (h : i ≠ j) :
    coord (l ∘ Equiv.swap i j) f = coord l f + (l j - l i) * (f i - f j) := by
  have at_index (u : ι) :
      l (Equiv.swap i j u) * f u = l u * f u +
        (if u = i then (l j-l i)*f i else 0) + (if u = j then (l i-l j)*f j else 0) := by
    by_cases hu : u=i
    · subst u
      simp [h]
      ring
    by_cases hv : u=j
    · subst u
      simp [h.symm]
      ring
    simp [Equiv.swap_apply_of_ne_of_ne hu hv, hu, hv]
  simp only [coord, Function.comp_apply, at_index, sum_add_distrib]
  simp
  ring

private theorem headings {n : ℕ} {t : Fin n → ℝ} (ht : ∀ j, 0 < t j)
    (hπ : ∑ j, t j ≤ Real.pi/2) :
    StrictMono (headingAngle t) ∧ ∀ i, headingAngle t i ∈ Set.Icc 0 (Real.pi/2) := by
  let A (i : Fin (n+1)) := univ.filter (fun j : Fin n => j.val < i.val)
  have subset {i j : Fin (n+1)} (h : i ≤ j) : A i ⊆ A j := by
    intro u hu
    simp only [A, mem_filter, mem_univ, true_and] at hu ⊢
    exact lt_of_lt_of_le hu h
  constructor
  · intro i j hij
    let u : Fin n := ⟨i.val, by omega⟩
    have hu : u ∈ A j := by simpa [A,u] using hij
    have hn : u ∉ A i := by simp [A,u]
    exact sum_lt_sum_of_subset (subset hij.le) hu hn (ht u) (fun k _ _ => (ht k).le)
  · intro i
    constructor
    · exact sum_nonneg (fun j _ => (ht j).le)
    · exact (sum_le_sum_of_subset_of_nonneg (subset_univ (A i)) (fun j _ _ => (ht j).le)).trans hπ

private theorem concave_score {X Y : ℝ} (hx : 0 ≤ X) (hy : 0 ≤ Y) :
    ConcaveOn ℝ (Set.Icc 0 (Real.pi/2)) (fun a => X*Real.cos a + Y*Real.sin a) := by
  have c : ConcaveOn ℝ (Set.Icc 0 (Real.pi/2)) Real.cos :=
    strictConcaveOn_cos_Icc.concaveOn.subset
      (fun x h => ⟨by linarith [h.1, Real.pi_pos], h.2⟩) (convex_Icc ..)
  have s : ConcaveOn ℝ (Set.Icc 0 (Real.pi/2)) Real.sin :=
    strictConcaveOn_sin_Icc.concaveOn.subset
      (fun x h => ⟨h.1, by linarith [h.2, Real.pi_pos]⟩) (convex_Icc ..)
  exact (c.smul hx).add (s.smul hy)

private theorem swap_bound {n : ℕ} {l : Fin (n+1) → ℝ} {t : Fin n → ℝ}
    (opt : IsOptimal l t) {i j : Fin (n+1)} (ne : i ≠ j) :
    let C := fun k => Real.cos (headingAngle t k)
    let S := fun k => Real.sin (headingAngle t k)
    let d := l j-l i
    (coord l C + d*(C i-C j))^2 + (coord l S + d*(S i-S j))^2 ≤
      (coord l C)^2 + (coord l S)^2 := by
  have h := opt (Equiv.swap i j) (Equiv.refl _)
  change endpointSquared (l ∘ Equiv.swap i j) t ≤ endpointSquared l t at h
  simpa only [coordinate_formula, swap_coord l _ ne] using h

private theorem score_order {ι : Type*} [Fintype ι] {l c s : ι → ℝ} {i j : ι}
    (len : l i < l j) (diff : c i ≠ c j)
    (bound : (coord l c+(l j-l i)*(c i-c j))^2 + (coord l s+(l j-l i)*(s i-s j))^2 ≤
      (coord l c)^2 + (coord l s)^2) :
    coord l c * c i + coord l s * s i < coord l c * c j + coord l s * s j := by
  let d := l j-l i
  let X := coord l c
  let Y := coord l s
  have hd : 0 < d := sub_pos.mpr len
  change (X+d*(c i-c j))^2+(Y+d*(s i-s j))^2 ≤ X^2+Y^2 at bound
  change X*c i+Y*s i < X*c j+Y*s j
  by_contra! h
  have hp : 0 ≤ 2*d*((X*c i+Y*s i)-(X*c j+Y*s j)) :=
    mul_nonneg (by positivity) (sub_nonneg.mpr h)
  have hq : 0 < d^2*((c i-c j)^2+(s i-s j)^2) :=
    mul_pos (sq_pos_of_pos hd) (add_pos_of_pos_of_nonneg
      (sq_pos_of_ne_zero (sub_ne_zero.mpr diff)) (sq_nonneg _))
  linarith only [bound,hp,hq]

private theorem unimodal {n : ℕ} {l : Fin (n+1) → ℝ} {t : Fin n → ℝ}
    (hl : ∀ i, 0 < l i) (ht : ∀ j, 0 < t j) (hπ : ∑ j, t j ≤ Real.pi/2)
    (opt : IsOptimal l t) {i j k : Fin (n+1)} (ij : i<j) (jk : j<k) :
    min (l i) (l k) ≤ l j := by
  let θ := headingAngle t
  let C := fun u => Real.cos (θ u)
  let S := fun u => Real.sin (θ u)
  let X := coord l C
  let Y := coord l S
  obtain ⟨incr,bounds⟩ := headings ht hπ
  have dec : StrictAnti C := fun a b h =>
    Real.cos_lt_cos_of_nonneg_of_le_pi_div_two (bounds a).1 (bounds b).2 (incr h)
  have hx : 0 ≤ X := sum_nonneg (fun u _ => mul_nonneg (hl u).le
    (Real.cos_nonneg_of_mem_Icc ⟨by linarith [(bounds u).1, Real.pi_pos],(bounds u).2⟩))
  have hy : 0 ≤ Y := sum_nonneg (fun u _ => mul_nonneg (hl u).le
    (Real.sin_nonneg_of_nonneg_of_le_pi (bounds u).1 (by linarith [(bounds u).2, Real.pi_pos])))
  let q := fun a => X*Real.cos a + Y*Real.sin a
  have valley : min (q (θ i)) (q (θ k)) ≤ q (θ j) :=
    (concave_score hx hy).min_le_of_mem_Icc (bounds i) (bounds k)
      ⟨(incr ij).le,(incr jk).le⟩
  by_contra! h
  obtain ⟨hji,hjk⟩ := lt_min_iff.mp h
  have a : q (θ j) < q (θ i) := score_order (c:=C) (s:=S) hji
    (dec.injective.ne ij.ne.symm) (swap_bound opt ij.ne.symm)
  have b : q (θ j) < q (θ k) := score_order (c:=C) (s:=S) hjk
    (dec.injective.ne jk.ne) (swap_bound opt jk.ne)
  exact (not_lt_of_ge valley) (lt_min a b)

private theorem descending {n : ℕ} {l : Fin (n+1) → ℝ} {t : Fin n → ℝ}
    (hl : ∀ i, 0 < l i) (ht : ∀ j, 0 < t j) (hπ : ∑ j, t j ≤ Real.pi/2)
    (hn : 2 ≤ n) (anti : StrictAnti l) (opt : IsOptimal l t) : False := by
  let i : Fin (n+1) := ⟨0,by omega⟩
  let j : Fin (n+1) := ⟨1,by omega⟩
  let k : Fin (n+1) := ⟨2,by omega⟩
  have ij : i < j := by change (0 : ℕ) < 1; decide
  have ne := ij.ne
  let R : Finset (Fin (n+1)) := (univ.erase j).erase i
  have nonempty : R.Nonempty := ⟨k,by simp [R,k,j,i, Fin.ext_iff]⟩
  let θ := headingAngle t
  let C := fun u => Real.cos (θ u)
  let S := fun u => Real.sin (θ u)
  obtain ⟨incr,bounds⟩ := headings ht hπ
  have positive (u : Fin (n+1)) (hu : u ∈ R) :
      0 < C u*(C j-C i) + S u*(S j-S i) := by
    have ui := (mem_erase.mp hu).1
    have uj := (mem_erase.mp (mem_erase.mp hu).2).1
    have v0 : u.val ≠ 0 := fun h => ui (Fin.ext h)
    have v1 : u.val ≠ 1 := fun h => uj (Fin.ext h)
    have ju : j < u := by change 1 < u.val; omega
    have h₁ : θ i < θ j := incr ij
    have h₂ : θ j < θ u := incr ju
    have h₃ : 0 ≤ θ i := (bounds i).1
    have h₄ : θ u ≤ Real.pi/2 := (bounds u).2
    have cmp := Real.cos_lt_cos_of_nonneg_of_le_pi_div_two
      (show 0 ≤ θ u-θ j by linarith) (show θ u-θ i ≤ Real.pi/2 by linarith)
      (show θ u-θ j < θ u-θ i by linarith)
    rw [Real.cos_sub, Real.cos_sub] at cmp
    change 0 < Real.cos (θ u)*(Real.cos (θ j)-Real.cos (θ i))+
      Real.sin (θ u)*(Real.sin (θ j)-Real.sin (θ i))
    linarith only [cmp]
  have splitCoord (f : Fin (n+1) → ℝ) :
      coord l f = (∑ u ∈ R, l u * f u) + l i*f i + l j*f j := by
    have hi : i ∈ (univ.erase j : Finset (Fin (n+1))) := by simp [ne]
    exact ((congrArg (fun a : ℝ => a + l j*f j)
      (sum_erase_add (univ.erase j) (fun u => l u*f u) hi)).trans
      (sum_erase_add univ (fun u => l u*f u) (mem_univ j))).symm
  let X := coord l C
  let Y := coord l S
  have tail_pos : 0 < (X-l i*C i-l j*C j)*(C j-C i)+(Y-l i*S i-l j*S j)*(S j-S i) := by
    have eqn : (X-l i*C i-l j*C j)*(C j-C i)+(Y-l i*S i-l j*S j)*(S j-S i) =
        ∑ u ∈ R, l u*(C u*(C j-C i)+S u*(S j-S i)) := by
      calc
        _ = (∑ u ∈ R, l u*C u)*(C j-C i) + (∑ u ∈ R, l u*S u)*(S j-S i) := by
          dsimp only [X,Y]
          rw [splitCoord C,splitCoord S]
          ring
        _ = _ := by
          rw [sum_mul, sum_mul, ←sum_add_distrib]
          exact sum_congr rfl (fun u _ => by ring)
    rw [eqn]
    exact sum_pos (fun u hu => mul_pos (hl u) (positive u hu)) nonempty
  have unit (u : Fin (n+1)) : C u ^ 2 + S u ^ 2 = 1 := Real.cos_sq_add_sin_sq _
  have gain :
      (X+(l j-l i)*(C i-C j))^2+(Y+(l j-l i)*(S i-S j))^2-(X^2+Y^2) =
      2*(l i-l j)*((X-l i*C i-l j*C j)*(C j-C i)+(Y-l i*S i-l j*S j)*(S j-S i)) := by
    linear_combination (l i^2-l j^2)*(unit j - unit i)
  have inc := mul_pos (mul_pos (by norm_num : (0:ℝ)<2) (sub_pos.mpr (anti ij))) tail_pos
  have contradiction := swap_bound opt ne
  change (X+(l j-l i)*(C i-C j))^2+(Y+(l j-l i)*(S i-S j))^2 ≤ X^2+Y^2 at contradiction
  linarith only [inc, contradiction, gain]

theorem result : type_of% @OMA.S_mo_442949.main := by
  intro n l t hl _ ht _ hπ
  exact ⟨fun opt _ _ _ ij jk => unimodal hl ht hπ opt ij jk,
    fun hn ha opt => descending hl ht hπ hn ha opt⟩

end SegmentChain

theorem OMA.solution : type_of% @OMA.S_mo_442949.main := SegmentChain.result
