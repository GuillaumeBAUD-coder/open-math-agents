import OMAStatements.S_mse_1696714
import Mathlib

-- Problem mse-1696714: the statement claims that for finite groups G1, G2 of the same order, if the derived
-- subgroup of G1 is strictly smaller than that of G2, then the center of G2 has at most as many elements as
-- the center of G1.
-- Upstream: statements/mse-1696714.lean (declaration OMA.S_mse_1696714.main)
-- Credit: @cclyles (the owner of the agent is credited as the solver)
--
-- Refutation: take G1 = A4 x C5 and G2 = D5 x C6, both of order 60 (D5 is the dihedral group of order 10).
-- The derived subgroup of G1 is the Klein four-group of A4 (order 4) and its center is 1 x C5 (order 5),
-- because A4 has trivial center. In G2 the commutator of (s, 1) and (r^2, 1) is (r, 1), of order 5, so the
-- derived subgroup has at least 5 elements, and (1, g) with g a generator of C6 is central of order 6, so the
-- center has at least 6 elements. So 4 < |G2'| but |Z(G2)| >= 6 > 5 = |Z(G1)|.

open scoped commutatorElement

theorem OMA.disproof : ¬ (type_of% @OMA.S_mse_1696714.main) := by
  intro h
  have h4 : Nat.card (Fin 4) = 4 := Nat.card_fin 4
  have hA : Nat.card (alternatingGroup (Fin 4)) = 12 := by
    rw [nat_card_alternatingGroup, h4]
    decide
  have hC5 : Nat.card (Multiplicative (ZMod 5)) = 5 := by
    rw [Nat.card_eq_fintype_card]
    decide
  have hC6 : Nat.card (Multiplicative (ZMod 6)) = 6 := by
    rw [Nat.card_eq_fintype_card]
    decide
  have hD : Nat.card (DihedralGroup 5) = 10 := by rw [DihedralGroup.nat_card]
  have hcard : Nat.card (alternatingGroup (Fin 4) × Multiplicative (ZMod 5)) =
      Nat.card (DihedralGroup 5 × Multiplicative (ZMod 6)) := by
    rw [Nat.card_prod, Nat.card_prod, hA, hC5, hD, hC6]
  -- the derived subgroup of G1 has 4 elements
  have hKA : Nat.card (commutator (alternatingGroup (Fin 4))) = 4 := by
    rw [← alternatingGroup.kleinFour_eq_commutator h4]
    exact alternatingGroup.kleinFour_card_of_card_eq_four h4
  have hKB : Nat.card (commutator (Multiplicative (ZMod 5))) = 1 := by
    rw [(commutator_eq_bot_iff (G := Multiplicative (ZMod 5))).mpr inferInstance, Subgroup.card_bot]
  have e1 : commutator (alternatingGroup (Fin 4) × Multiplicative (ZMod 5)) =
      (commutator (alternatingGroup (Fin 4))).prod (commutator (Multiplicative (ZMod 5))) := by
    show ⁅(⊤ : Subgroup (alternatingGroup (Fin 4) × Multiplicative (ZMod 5))),
        (⊤ : Subgroup (alternatingGroup (Fin 4) × Multiplicative (ZMod 5)))⁆ =
      Subgroup.prod ⁅(⊤ : Subgroup (alternatingGroup (Fin 4))), (⊤ : Subgroup (alternatingGroup (Fin 4)))⁆
        ⁅(⊤ : Subgroup (Multiplicative (ZMod 5))), (⊤ : Subgroup (Multiplicative (ZMod 5)))⁆
    rw [← Subgroup.commutator_prod_prod, Subgroup.top_prod_top]
  have hcomm1 : Nat.card (commutator (alternatingGroup (Fin 4) × Multiplicative (ZMod 5))) = 4 := by
    rw [e1, Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod, hKA, hKB]
  -- the center of G1 has 5 elements
  have hZA : Nat.card (Subgroup.center (alternatingGroup (Fin 4))) = 1 := by
    rw [alternatingGroup.center_eq_bot (le_of_eq h4.symm), Subgroup.card_bot]
  have hZB : Nat.card (Subgroup.center (Multiplicative (ZMod 5))) = 5 := by
    rw [Subgroup.center_eq_top, Subgroup.card_top, hC5]
  have hcen1 : Nat.card (Subgroup.center (alternatingGroup (Fin 4) × Multiplicative (ZMod 5))) = 5 := by
    rw [Subgroup.center_prod, Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod, hZA, hZB]
  -- the derived subgroup of G2 has at least 5 elements
  have hc : ⁅((DihedralGroup.sr 0, 1) : DihedralGroup 5 × Multiplicative (ZMod 6)),
      ((DihedralGroup.r 2, 1) : DihedralGroup 5 × Multiplicative (ZMod 6))⁆ =
        ((DihedralGroup.r 1, 1) : DihedralGroup 5 × Multiplicative (ZMod 6)) := by decide
  have hcmem : ((DihedralGroup.r 1, 1) : DihedralGroup 5 × Multiplicative (ZMod 6)) ∈
      commutator (DihedralGroup 5 × Multiplicative (ZMod 6)) := by
    rw [← hc]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have hc5 : ((DihedralGroup.r 1, 1) : DihedralGroup 5 × Multiplicative (ZMod 6)) ^ 5 = 1 := by decide
  have hc1 : ((DihedralGroup.r 1, 1) : DihedralGroup 5 × Multiplicative (ZMod 6)) ≠ 1 := by decide
  have hp5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hord : orderOf ((DihedralGroup.r 1, 1) : DihedralGroup 5 × Multiplicative (ZMod 6)) = 5 :=
    orderOf_eq_prime hc5 hc1
  have hcomm2 : 5 ≤ Nat.card (commutator (DihedralGroup 5 × Multiplicative (ZMod 6))) := by
    have h1 := Subgroup.card_le_of_le (Subgroup.zpowers_le.mpr hcmem)
    rwa [Nat.card_zpowers, hord] at h1
  -- the center of G2 has at least 6 elements
  have hz : ((1, Multiplicative.ofAdd (1 : ZMod 6)) : DihedralGroup 5 × Multiplicative (ZMod 6)) ∈
      Subgroup.center (DihedralGroup 5 × Multiplicative (ZMod 6)) := by
    rw [Subgroup.mem_center_iff]
    decide
  have hzord : orderOf ((1, Multiplicative.ofAdd (1 : ZMod 6)) :
      DihedralGroup 5 × Multiplicative (ZMod 6)) = 6 := by
    rw [orderOf_eq_iff (by norm_num)]
    constructor
    · decide
    · decide
  have hcen2 : 6 ≤ Nat.card (Subgroup.center (DihedralGroup 5 × Multiplicative (ZMod 6))) := by
    have h1 := Subgroup.card_le_of_le (Subgroup.zpowers_le.mpr hz)
    rwa [Nat.card_zpowers, hzord] at h1
  have key := h (alternatingGroup (Fin 4) × Multiplicative (ZMod 5))
    (DihedralGroup 5 × Multiplicative (ZMod 6)) hcard (by rw [hcomm1]; omega)
  rw [hcen1] at key
  omega
