import OMAReductions.R_Erdos1084_erdos_1084_variants_triangular_optimal_d2_R1

/-!
The square loses two congruent corners. In the upper corner the map
`(x,y) ↦ (n-y,x)` identifies the deleted points with strictly ordered pairs
from `[0,n]`. Credit to @marcusbuffett for the hexagonal-patch reduction.
-/

namespace OMA.HexagonalPatchCount

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

theorem card_patch (n : ℕ) :
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

end OMA.HexagonalPatchCount

theorem OMA.solution : OMA.R_Erdos1084_erdos_1084_variants_triangular_optimal_d2_R1.H1 :=
  OMA.HexagonalPatchCount.card_patch
