import OMAReductions.R_oeis_a000952_R1
import Mathlib

open Finset OMA.S_oeis_a000952

private theorem correlation {p : ℕ} [Fact p.Prime] (hodd : ringChar (ZMod p) ≠ 2)
    (a b : ZMod p) (hab : a ≠ b) :
    ∑ x : ZMod p, quadraticChar _ (x-a) * quadraticChar _ (x-b) = -1 := by
  let χ := quadraticChar (ZMod p)
  let d := b-a
  have hd : d ≠ 0 := sub_ne_zero.mpr hab.symm
  let e : ZMod p ≃ ZMod p := (Equiv.mulLeft₀ d hd).trans (Equiv.addRight a)
  rw [← e.sum_comp]
  have hs (x : ZMod p) : χ (e x - a) * χ (e x - b) =
      χ (-1) * (χ x * χ (1-x)) := by
    change χ (d*x+a-a) * χ (d*x+a-b) = _
    rw [show d*x+a-a = d*x by ring, show d*x+a-b = (-1)*d*(1-x) by dsimp [d]; ring]
    simp only [map_mul]
    have hh := quadraticChar_sq_one (F := ZMod p) hd
    change χ d ^ 2 = 1 at hh
    linear_combination χ (-1) * χ x * χ (1-x) * hh
  change ∑ x, χ (e x-a) * χ (e x-b) = _
  simp_rw [hs]
  rw [← mul_sum]
  change χ (-1) * jacobiSum χ χ = -1
  have hj := jacobiSum_nontrivial_inv (quadraticChar_ne_one hodd)
  rw [(quadraticChar_isQuadratic _).inv] at hj
  change jacobiSum χ χ = -χ (-1) at hj
  rw [hj]
  have := quadraticChar_sq_one (F := ZMod p) (neg_ne_zero.mpr one_ne_zero)
  change χ (-1)^2 = 1 at this
  linarith [show χ (-1)* -χ (-1) = -(χ (-1)^2) by ring]

private def entry {p : ℕ} [Fact p.Prime] : Option (ZMod p) → Option (ZMod p) → ℤ
  | none, none => 0
  | some _, none | none, some _ => 1
  | some a, some b => quadraticChar _ (b-a)

theorem OMA.solution : OMA.R_oeis_a000952_R1.H1 := by
  classical
  intro p hp h4
  let : Fact p.Prime := ⟨hp⟩
  have ho : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; omega
  let χ := quadraticChar (ZMod p)
  have hneg : χ (-1) = 1 := by
    change quadraticChar _ (-1) = 1
    rw [quadraticChar_neg_one ho, ZMod.card, ZMod.χ₄_nat_eq_if_mod_four]
    simp [h4, show p % 2 = 1 by omega]
  have hsum (a : ZMod p) : ∑ x : ZMod p, χ (x-a) = 0 := by
    simp_rw [sub_eq_add_neg]
    exact (Equiv.sum_comp (Equiv.addRight (-a)) χ).trans (quadraticChar_sum_zero ho)
  have hdiag (a : ZMod p) : ∑ x : ZMod p, χ (x-a)*χ (x-a) = (p : ℤ)-1 := by
    have hd (x : ZMod p) : χ (x-a)*χ (x-a) = if x = a then 0 else 1 := by
      split_ifs with h
      · simp [h, χ]
      · exact (pow_two _).symm.trans (quadraticChar_sq_one (sub_ne_zero.mpr h))
    simp [hd, sum_ite, Finset.filter_ne', Finset.card_erase_of_mem, ZMod.card, Nat.cast_sub hp.one_le]
  have gram (i j : Option (ZMod p)) :
      ∑ x, entry i x * entry j x = if i=j then (p : ℤ) else 0 := by
    cases i with
    | none =>
      cases j with
      | none => simp [Fintype.sum_option, entry, ZMod.card]
      | some b => simpa [Fintype.sum_option, entry, χ] using hsum b
    | some a =>
      cases j with
      | none => simpa [Fintype.sum_option, entry, χ] using hsum a
      | some b =>
        by_cases h : a=b
        · subst b
          simpa [Fintype.sum_option, entry, χ] using (show 1 + (∑ x, χ (x-a)*χ (x-a)) = (p : ℤ) by rw [hdiag]; omega)
        · have hc := correlation ho a b h
          simpa [Fintype.sum_option, entry, h] using (show 1 + (∑ x, quadraticChar _ (x-a)*quadraticChar _ (x-b)) = 0 by omega)
  let e : Fin (p+1) ≃ Option (ZMod p) := Fintype.equivOfCardEq (by simp [ZMod.card])
  let A : Matrix (Fin (p+1)) (Fin (p+1)) ℤ := fun i j => entry (e i) (e j)
  refine ⟨A, ?_, ?_, ?_⟩
  · apply Matrix.IsSymm.ext
    intro i j
    change entry (e j) (e i) = entry (e i) (e j)
    cases e i <;> cases e j <;> simp [entry]
    rename_i a b
    change χ (a-b) = χ (b-a)
    rw [show a-b = (-1)*(b-a) by ring, map_mul, hneg, one_mul]
  · intro i j
    change entry (e i) (e j) = -1 ∨ entry (e i) (e j) = 0 ∨ entry (e i) (e j) = 1
    cases e i <;> cases e j <;> simp [entry]
    rename_i a b
    rcases quadraticChar_isQuadratic (ZMod p) (b-a) with h|h|h <;> tauto
  · ext i j
    rw [Matrix.mul_apply]
    change ∑ x, entry (e i) (e x)*entry (e j) (e x) = _
    rw [e.sum_comp (fun x => entry (e i) x * entry (e j) x)]
    by_cases hij : i=j <;> simp [gram, Matrix.smul_apply, hij]
