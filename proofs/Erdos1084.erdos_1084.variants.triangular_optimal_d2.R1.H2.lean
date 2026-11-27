import OMAReductions.R_Erdos1084_erdos_1084_variants_triangular_optimal_d2_R1

/-!
One nearest-neighbor direction gives one contact per lattice point except
at the terminal point of each row. Two lattice symmetries give the same count
in the other directions. The patch count below removes two congruent corners. In the upper corner the map
`(x,y) ↦ (n-y,x)` identifies the deleted points with strictly ordered pairs
from `[0,n]`. Credit to @marcusbuffett for the hexagonal-patch reduction.
-/

namespace OMA.HexagonalPatchContacts

open Finset

private def upperCornerEquiv (n : ℤ) : (ℤ × ℤ) ≃ (ℤ × ℤ) where
  toFun p := (n - p.2, p.1)
  invFun p := (p.2, n - p.1)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp

private def oppositeEquiv : (ℤ × ℤ) ≃ (ℤ × ℤ) where
  toFun p := (-p.1, -p.2)
  invFun p := (-p.1, -p.2)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp

private theorem card_patch (n : ℕ) :
    let I := Icc (-(n : ℤ)) (n : ℤ)
    ((I ×ˢ I).filter (fun p => p.1 + p.2 ∈ I)).card = 3 * n^2 + 3 * n + 1 := by
  classical
  let I := Icc (-(n : ℤ)) (n : ℤ)
  let J := Icc (0 : ℤ) (n : ℤ)
  let box := I ×ˢ I
  let upper := box.filter fun p => (n : ℤ) < p.1 + p.2
  let lower := box.filter fun p => p.1 + p.2 < -(n : ℤ)
  let patch := box.filter fun p => p.1 + p.2 ∈ I
  change patch.card = _
  have hI : I.card = 2 * n + 1 := by
    simp only [I, Int.card_Icc]
    omega
  have hJ : J.card = n + 1 := by
    simp only [J, Int.card_Icc]
    omega
  have hu : upper.card = (n + 1).choose 2 := by
    calc
      upper.card = ((J ×ˢ J).filter fun p => p.1 < p.2).card := by
        apply card_equiv (upperCornerEquiv (n : ℤ))
        rintro ⟨x, y⟩
        simp only [upper, box, I, J, mem_filter, mem_product, mem_Icc,
          upperCornerEquiv, Equiv.coe_fn_mk]
        omega
      _ = (n + 1).choose 2 := by rw [card_product_filter_lt, hJ]
  have hl : lower.card = upper.card := by
    apply card_equiv oppositeEquiv
    rintro ⟨x, y⟩
    simp only [lower, upper, box, I, mem_filter, mem_product, mem_Icc,
      oppositeEquiv, Equiv.coe_fn_mk]
    omega
  have hmiss : (box.filter fun p => p.1 + p.2 ∉ I) = upper ∪ lower := by
    ext p
    by_cases hp : p ∈ box
    · simp only [upper, lower, mem_union, mem_filter, hp, true_and, I, mem_Icc]
      omega
    · simp [upper, lower, hp]
  have hdisj : Disjoint upper lower := by
    refine disjoint_left.mpr ?_
    intro p hp hq
    have hp' := (mem_filter.mp hp).2
    have hq' := (mem_filter.mp hq).2
    omega
  have hpart := card_filter_add_card_filter_not (s := box) (fun p => p.1 + p.2 ∈ I)
  change patch.card + _ = _ at hpart
  rw [hmiss, card_union_of_disjoint hdisj, hl, hu] at hpart
  have hbox : box.card = (2 * n + 1)^2 := by
    dsimp [box]
    rw [card_product, hI, pow_two]
  rw [hbox] at hpart
  have hchoose : 2 * (n + 1).choose 2 = (n + 1) * n := by
    rw [mul_comm 2, Nat.choose_two_right, Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self (n + 1))]
    simp
  nlinarith only [hpart, hchoose]


open scoped EuclideanGeometry
open OMA.R_Erdos1084_erdos_1084_variants_triangular_optimal_d2_R1 (lattice_sep)

private def interval (n : ℕ) : Finset ℤ := Icc (-(n : ℤ)) (n : ℤ)

private def patch (n : ℕ) : Finset (ℤ × ℤ) :=
  (interval n ×ˢ interval n).filter fun p => p.1 + p.2 ∈ interval n

private theorem mem_patch (n : ℕ) (p : ℤ × ℤ) :
    p ∈ patch n ↔ -(n : ℤ) ≤ p.1 ∧ p.1 ≤ n ∧
      -(n : ℤ) ≤ p.2 ∧ p.2 ≤ n ∧ -(n : ℤ) ≤ p.1 + p.2 ∧ p.1 + p.2 ≤ n := by
  simp [patch, interval, and_assoc]

private def step (d : Fin 3) : ℤ × ℤ := ![(1, 0), (0, 1), (1, -1)] d

private def good (n : ℕ) (d : Fin 3) : Finset (ℤ × ℤ) :=
  (patch n).filter fun p => p + step d ∈ patch n

private def rightBorder (n : ℕ) : Finset (ℤ × ℤ) :=
  (patch n).filter fun p => p + step 0 ∉ patch n

private theorem mem_rightBorder (n : ℕ) (p : ℤ × ℤ) :
    p ∈ rightBorder n ↔ p.2 ∈ interval n ∧ p.1 = min (n : ℤ) (n - p.2) := by
  simp only [rightBorder, step, mem_filter, mem_patch, interval, mem_Icc, Prod.fst_add,
    Prod.snd_add, Matrix.cons_val_zero, add_zero]
  rcases le_total (0 : ℤ) p.2 with h | h
  · rw [min_eq_right (by omega)]
    omega
  · rw [min_eq_left (by omega)]
    omega

private theorem card_rightBorder (n : ℕ) : (rightBorder n).card = 2 * n + 1 := by
  let endpoint : ℤ ↪ (ℤ × ℤ) :=
    ⟨fun y => (min (n : ℤ) (n - y), y), fun _ _ h => congrArg Prod.snd h⟩
  have hborder : rightBorder n = (interval n).map endpoint := by
    ext p
    rw [mem_rightBorder, mem_map]
    constructor
    · rintro ⟨h, hx⟩
      exact ⟨p.2, h, Prod.ext hx.symm rfl⟩
    · rintro ⟨y, h, rfl⟩
      exact ⟨h, rfl⟩
  rw [hborder, card_map, interval, Int.card_Icc]
  omega

private def swapCoords : (ℤ × ℤ) ≃ (ℤ × ℤ) := Equiv.prodComm ℤ ℤ

private def diagonalCoords : (ℤ × ℤ) ≃ (ℤ × ℤ) where
  toFun p := (p.1, -p.1 - p.2)
  invFun p := (p.1, -p.1 - p.2)
  left_inv p := Prod.ext rfl (by change -p.1 - (-p.1 - p.2) = p.2; omega)
  right_inv p := Prod.ext rfl (by change -p.1 - (-p.1 - p.2) = p.2; omega)

private theorem card_good (n : ℕ) (d : Fin 3) : (good n d).card = 3 * n^2 + n := by
  have hcount := card_patch n
  change (patch n).card = _ at hcount
  have hsplit := card_filter_add_card_filter_not (s := patch n) (fun p => p + step 0 ∈ patch n)
  change (good n 0).card + (rightBorder n).card = (patch n).card at hsplit
  rw [card_rightBorder, hcount] at hsplit
  have hhorizontal : (good n 0).card = 3 * n^2 + n := by omega
  have hvert : (good n 0).card = (good n 1).card := by
    apply card_equiv swapCoords
    intro p
    simp [good, swapCoords, mem_patch, step]
    omega
  have hdiag : (good n 0).card = (good n 2).card := by
    apply card_equiv diagonalCoords
    intro p
    simp [good, diagonalCoords, mem_patch, step]
    omega
  fin_cases d
  · exact hhorizontal
  · exact hvert.symm.trans hhorizontal
  · exact hdiag.symm.trans hhorizontal

private noncomputable def point (p : ℤ × ℤ) : ℝ² :=
  !₂[(p.1 : ℝ) + (p.2 : ℝ) / 2, Real.sqrt 3 * (p.2 : ℝ) / 2]

private theorem point_injective : Function.Injective point := by
  intro p q h
  by_contra hne
  have hsep := lattice_sep p q hne
  change 1 ≤ dist (point p) (point q) at hsep
  rw [h, dist_self] at hsep
  norm_num at hsep

private theorem dist_step (p : ℤ × ℤ) (d : Fin 3) : dist (point p) (point (p + step d)) = 1 := by
  rw [dist_eq_norm]
  have hsq : ‖point p - point (p + step d)‖^2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
    change ((p.1 : ℝ) + (p.2 : ℝ) / 2 - (((p + step d).1 : ℝ) + ((p + step d).2 : ℝ) / 2))^2 +
      (Real.sqrt 3 * (p.2 : ℝ) / 2 - Real.sqrt 3 * ((p + step d).2 : ℝ) / 2)^2 = 1
    fin_cases d <;> simp [step] <;> ring_nf <;> norm_num [Real.sq_sqrt]
  nlinarith [norm_nonneg (point p - point (p + step d))]

private theorem step_injective : Function.Injective step := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [step]

private theorem steps_not_opposite (i j : Fin 3) : step i + step j ≠ 0 := by
  fin_cases i <;> fin_cases j <;> norm_num [step, Prod.ext_iff]

private noncomputable def edge (e : Σ _ : Fin 3, ℤ × ℤ) : Sym2 ℝ² :=
  s(point e.2, point (e.2 + step e.1))

private theorem edge_injective : Function.Injective edge := by
  rintro ⟨i,p⟩ ⟨j,q⟩ h
  rcases Sym2.eq_iff.mp h with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
  · obtain rfl := point_injective h₁
    obtain rfl := step_injective (add_left_cancel (point_injective h₂))
    rfl
  · have h₁' := point_injective h₁
    have h₂' := point_injective h₂
    have hsum : q + (step j + step i) = q + 0 := by
      rw [← add_assoc, ← h₁', h₂', add_zero]
    exact (steps_not_opposite j i (add_left_cancel hsum)).elim

private theorem out_dist (a b : ℝ²) : dist (s(a,b)).out.1 (s(a,b)).out.2 = dist a b := by
  have h : s((s(a,b)).out.1, (s(a,b)).out.2) = s(a,b) := (s(a,b)).out_eq
  rcases Sym2.eq_iff.mp h with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
  · rw [h₁, h₂]
  · rw [h₁, h₂, dist_comm]

theorem contacts (n : ℕ) : 9 * n^2 + 3 * n ≤ unitDistNum ((patch n).image point) := by
  classical
  let oriented := (univ : Finset (Fin 3)).sigma (good n)
  have hcard : oriented.card = 9 * n^2 + 3 * n := by
    simp [oriented, card_sigma, card_good]
    ring
  rw [← hcard, ← card_image_of_injective oriented edge_injective, unitDistNum]
  apply card_le_card
  intro e he
  rcases mem_image.mp he with ⟨⟨d,p⟩, hp, rfl⟩
  have hgood : p ∈ good n d := (mem_sigma.mp hp).2
  obtain ⟨hp₁,hp₂⟩ := mem_filter.mp hgood
  refine mem_filter.mpr ⟨?_, ?_⟩
  · change s(point p, point (p + step d)) ∈ ((patch n).image point).sym2
    exact mk_mem_sym2_iff.mpr ⟨mem_image_of_mem _ hp₁, mem_image_of_mem _ hp₂⟩
  · change dist (s(point p, point (p + step d))).out.1
      (s(point p, point (p + step d))).out.2 = 1
    rw [out_dist, dist_step]

end OMA.HexagonalPatchContacts

theorem OMA.solution : OMA.R_Erdos1084_erdos_1084_variants_triangular_optimal_d2_R1.H2 :=
  OMA.HexagonalPatchContacts.contacts
