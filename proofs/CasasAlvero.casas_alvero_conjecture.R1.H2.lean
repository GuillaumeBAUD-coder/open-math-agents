import OMAReductions.R_CasasAlvero_casas_alvero_conjecture_R1
import Mathlib

-- Step CasasAlvero.casas_alvero_conjecture.R1.H2: hypothesis H2 of reduction CasasAlvero.casas_alvero_conjecture.R1
-- Credit: @ivillar. A monic split Q has nextCoeff = -(sum of roots) = 0; if a nonzero root r existed, all roots would be 0 or r, so the sum would be count(r) * r != 0 in characteristic zero. Hence every root is 0 and Q = prod (X - 0) = X^natDegree.

/-! Step CasasAlvero.casas_alvero_conjecture.R1.H2. -/

open Polynomial

namespace P8CasasAlvero

theorem casas_h2 : ∀ {K : Type} [Field K] [CharZero K] (Q : K[X]),
    Q.Monic → Q.Splits → Q.nextCoeff = 0 →
    (∀ a ∈ Q.roots, ∀ b ∈ Q.roots, a ≠ 0 → b ≠ 0 → a = b) →
    Q = X ^ Q.natDegree := by
  intro K _ _ Q hm hs hnext hroots
  classical
  have hsum : Q.roots.sum = 0 := by
    have := hs.nextCoeff_eq_neg_sum_roots_of_monic hm
    rw [hnext] at this
    exact neg_eq_zero.mp this.symm
  have hzero : ∀ r ∈ Q.roots, r = 0 := by
    intro r hr
    by_contra hr0
    have hall : ∀ b ∈ Q.roots, b = 0 ∨ b = r := fun b hb => by
      by_cases hb0 : b = 0
      · exact Or.inl hb0
      · exact Or.inr (hroots b hb r hr hb0 hr0)
    have e1 : Q.roots = Q.roots.filter (· = r) + Q.roots.filter (fun x => ¬ x = r) :=
      (Multiset.filter_add_not _ _).symm
    have e2 : (Q.roots.filter (fun x => ¬ x = r)).sum = 0 := by
      apply Multiset.sum_eq_zero
      intro x hx
      rw [Multiset.mem_filter] at hx
      exact (hall x hx.1).resolve_right hx.2
    have e3' : Q.roots.filter (· = r) = Multiset.replicate (Q.roots.count r) r := by
      convert Multiset.filter_eq' Q.roots r
    have e3 : (Q.roots.filter (· = r)).sum = (Q.roots.count r : K) * r := by
      rw [e3', Multiset.sum_replicate, nsmul_eq_mul]
    have hcr : Q.roots.sum = (Q.roots.count r : K) * r := by
      conv_lhs => rw [e1]
      rw [Multiset.sum_add, e2, e3, add_zero]
    rw [hsum] at hcr
    have hc : (Q.roots.count r : K) ≠ 0 := Nat.cast_ne_zero.mpr (Multiset.count_ne_zero.mpr hr)
    exact hr0 ((mul_eq_zero.mp hcr.symm).resolve_left hc)
  have hrep : Q.roots = Multiset.replicate Q.roots.card 0 := Multiset.eq_replicate_card.mpr hzero
  have hcard : Q.roots.card = Q.natDegree := hs.natDegree_eq_card_roots.symm
  conv_lhs => rw [hs.eq_prod_roots_of_monic hm, hrep]
  simp [Multiset.map_replicate, Multiset.prod_replicate, hcard]

end P8CasasAlvero

theorem OMA.solution : OMA.R_CasasAlvero_casas_alvero_conjecture_R1.H2 :=
  P8CasasAlvero.casas_h2
