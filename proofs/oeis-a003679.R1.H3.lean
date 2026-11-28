import OMAReductions.R_oeis_a003679_R1

/-! A kernel-checked search. If 33066 = pent a + pent b + pent c, sort so that a ≤ b ≤ c. Since
`pent` is monotone, c ≤ 148 (pent 149 = 33227), pent b + pent c ≤ 33066 ≤ 3 · pent c. The
Boolean `chk` runs over every such sorted triple and finds no solution. -/

namespace OMA.A003679

open OMA.S_oeis_a003679

def chk : Bool :=
  (List.range 149).all fun c =>
    !(Nat.ble 33066 (3 * pent c)) ||
    (List.range (c + 1)).all fun b =>
      !(Nat.ble (pent b + pent c) 33066) ||
      (List.range (b + 1)).all fun a => !(Nat.beq (pent a + pent b + pent c) 33066)

set_option maxRecDepth 100000 in
theorem chk_eq : chk = true := by decide +kernel

theorem pent_mono {x y : ℕ} (h : x ≤ y) : pent x ≤ pent y := by
  unfold pent
  apply Nat.div_le_div_right
  exact Nat.mul_le_mul h (Nat.sub_le_sub_right (Nat.mul_le_mul_left 3 h) 1)

theorem sorted (a b c : ℕ) (hab : a ≤ b) (hbc : b ≤ c) (h : pent a + pent b + pent c = 33066) :
    False := by
  have hb : ∀ x y : Bool, (!x || y) = true → x = true → y = true := by decide
  have hc : c < 149 := by
    by_contra hc
    push Not at hc
    have h1 := pent_mono hc
    have h149 : pent 149 = 33227 := by unfold pent; norm_num
    omega
  have m1 := pent_mono hab
  have m2 := pent_mono hbc
  have s := chk_eq
  unfold chk at s
  have s1 := hb _ _ (List.all_eq_true.1 s c (List.mem_range.2 hc)) (by simp; omega)
  have s2 := hb _ _ (List.all_eq_true.1 s1 b (List.mem_range.2 (by omega))) (by simp; omega)
  have s3 := List.all_eq_true.1 s2 a (List.mem_range.2 (by omega))
  rw [h] at s3
  simp at s3

end OMA.A003679

theorem OMA.solution : OMA.R_oeis_a003679_R1.H3 := by
  show ¬ ∃ a b c : ℕ, 33066 = OMA.S_oeis_a003679.pent a + OMA.S_oeis_a003679.pent b +
    OMA.S_oeis_a003679.pent c
  rintro ⟨a, b, c, h⟩
  rcases le_total a b with hab | hab <;> rcases le_total b c with hbc | hbc <;>
    rcases le_total a c with hac | hac
  all_goals first
    | exact OMA.A003679.sorted a b c (by omega) (by omega) (by omega)
    | exact OMA.A003679.sorted a c b (by omega) (by omega) (by omega)
    | exact OMA.A003679.sorted b a c (by omega) (by omega) (by omega)
    | exact OMA.A003679.sorted b c a (by omega) (by omega) (by omega)
    | exact OMA.A003679.sorted c a b (by omega) (by omega) (by omega)
    | exact OMA.A003679.sorted c b a (by omega) (by omega) (by omega)
