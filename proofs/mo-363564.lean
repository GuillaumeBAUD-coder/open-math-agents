import OMAStatements.S_mo_363564
import Mathlib

-- Problem mo-363564: the statement claims that for increasing families U_i, V_i of sets indexed by a linear
-- order, |U_i| <= |V_i| for all i implies that the union of the U_i has at most the size of the union of the
-- V_i.
-- Upstream: statements/mo-363564.lean (declaration OMA.S_mo_363564.main)
-- Credit: @cclyles (the owner of the agent is credited as the solver)
--
-- Refutation: index by the first uncountable ordinal w1. Let U_i be the set of ordinals below i, which is
-- countable, and let V_i be the set of all natural numbers for every i. Both families are increasing and
-- |U_i| <= |V_i|. But the union of the U_i is all of w1 (it has no largest element), which is uncountable, while
-- the union of the V_i is countable.

open Cardinal

private abbrev W1 : Type := (aleph 1 : Cardinal.{0}).ord.ToType

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_363564.main) := by
  intro h
  have hnm : NoMaxOrder W1 := Cardinal.noMaxOrder (le_of_lt aleph0_lt_aleph_one)
  have hU : Monotone (fun i : W1 => Set.Iio i) := by
    intro a b hab x hx
    exact lt_of_lt_of_le hx hab
  have hV : Monotone (fun _ : W1 => (Set.univ : Set ℕ)) := fun _ _ _ => le_refl _
  have hcard : ∀ i : W1, Cardinal.mk (Set.Iio i) ≤ Cardinal.mk (Set.univ : Set ℕ) := by
    intro i
    have h1 : Cardinal.mk (Set.Iio i) < aleph 1 := Cardinal.mk_Iio_toType_ord_lt i
    rw [Cardinal.mk_univ, Cardinal.mk_nat]
    exact Cardinal.lt_aleph_one_iff.mp h1
  have key : Cardinal.mk (⋃ i : W1, Set.Iio i) ≤ Cardinal.mk (⋃ _ : W1, (Set.univ : Set ℕ)) :=
    h W1 W1 ℕ (fun i : W1 => Set.Iio i) (fun _ => (Set.univ : Set ℕ)) hU hV hcard
  have hunion : (⋃ i : W1, Set.Iio i) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨y, hy⟩ := exists_gt x
    exact Set.mem_iUnion.mpr ⟨y, hy⟩
  have h2 : Cardinal.mk (⋃ _ : W1, (Set.univ : Set ℕ)) ≤ aleph0 := by
    have h3 := Cardinal.mk_set_le (⋃ _ : W1, (Set.univ : Set ℕ))
    rwa [Cardinal.mk_nat] at h3
  rw [hunion, Cardinal.mk_univ, Cardinal.mk_ord_toType] at key
  exact absurd (le_trans key h2) (not_le.mpr aleph0_lt_aleph_one)
