import FormalConjectures.ErdosProblems.«792»

-- Problem: Erdős Problem 792 — alon kleitman
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/792.lean:123 (declaration Erdos792.erdos_792.variants.alon_kleitman)
-- Credit: @LordMike (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA

open Finset

lemma val_sumfree (p k : ℕ) (hp : p = 3 * k + 2) [NeZero p] (u v : ZMod p)
    (hu1 : k + 1 ≤ u.val) (hu2 : u.val ≤ 2 * k + 1) (hv1 : k + 1 ≤ v.val)
    (hv2 : v.val ≤ 2 * k + 1)
    (hw1 : k + 1 ≤ (u + v).val) (hw2 : (u + v).val ≤ 2 * k + 1) : False := by
  rw [ZMod.val_add] at hw1 hw2
  rcases Nat.lt_or_ge (u.val + v.val) p with h | h
  · rw [Nat.mod_eq_of_lt h] at hw1 hw2; omega
  · rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)] at hw1 hw2; omega

lemma card_S (p k : ℕ) (hp : p = 3 * k + 2) [NeZero p] :
    (univ.filter (fun y : ZMod p => y.val ∈ Icc (k + 1) (2 * k + 1))).card = k + 1 := by
  have hset : (univ.filter (fun y : ZMod p => y.val ∈ Icc (k + 1) (2 * k + 1))) =
      (Icc (k + 1) (2 * k + 1)).image (fun n : ℕ => (n : ZMod p)) := by
    ext y
    simp only [mem_filter, mem_univ, true_and, mem_image]
    constructor
    · intro h; exact ⟨y.val, h, ZMod.natCast_zmod_val y⟩
    · rintro ⟨n, hn, rfl⟩
      rw [ZMod.val_cast_of_lt (by simp only [mem_Icc] at hn; omega)]
      exact hn
  rw [hset, card_image_of_injOn]
  · simp only [Nat.card_Icc]; omega
  intro m hm n hn h
  simp only [coe_Icc, Set.mem_Icc] at hm hn
  have h2 := congrArg ZMod.val h
  simp only at h2
  rwa [ZMod.val_cast_of_lt (by omega), ZMod.val_cast_of_lt (by omega)] at h2

theorem solution_aux : type_of% @Erdos792.erdos_792.variants.alon_kleitman := by
  intro A hpos hcard
  obtain ⟨p, hpM, hp, hp3⟩ := Nat.forall_exists_prime_gt_and_eq_mod (q := 3) (a := 2)
    (IsUnit.of_mul_eq_one (a := (2 : ZMod 3)) 2 (by decide)) (A.sup (fun a => a.toNat))
  have hp3' : p % 3 = 2 := by
    have h := congrArg ZMod.val hp3
    rw [ZMod.val_natCast] at h
    exact h
  have := Fact.mk hp
  set k := p / 3 with hk
  have hpk : p = 3 * k + 2 := by omega
  set B : ZMod p → Finset ℤ := fun x =>
    A.filter (fun a => ((a : ZMod p) * x).val ∈ Icc (k + 1) (2 * k + 1)) with hB
  have hne : ∀ a ∈ A, (a : ZMod p) ≠ 0 := by
    intro a ha h
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
    have h1 := Int.le_of_dvd (hpos a ha) h
    have h2 : a.toNat ≤ A.sup (fun a => a.toNat) := Finset.le_sup (f := fun a => a.toNat) ha
    have h3 := hpos a ha
    omega
  have hsum : ∑ x : ZMod p, (B x).card = A.card * (k + 1) := by
    simp only [hB, card_filter]
    rw [Finset.sum_comm]
    rw [Finset.card_eq_sum_ones, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a ha
    rw [one_mul]
    have := Equiv.sum_comp (Equiv.mulLeft₀ (a : ZMod p) (hne a ha))
      (fun y => if y.val ∈ Icc (k + 1) (2 * k + 1) then 1 else 0)
    simp only [Equiv.mulLeft₀_apply] at this
    rw [this, ← card_filter, card_S p k hpk]
  have hex : ∃ x, A.card < 3 * (B x).card := by
    by_contra hcon
    push_neg at hcon
    have h1 : ∑ x : ZMod p, 3 * (B x).card ≤ ∑ _x : ZMod p, A.card :=
      Finset.sum_le_sum (fun x _ => hcon x)
    rw [← Finset.mul_sum, hsum, Finset.sum_const, Finset.card_univ, ZMod.card,
      smul_eq_mul, hpk] at h1
    nlinarith
  obtain ⟨x, hx⟩ := hex
  refine ⟨B x, Finset.filter_subset _ _, ?_, by omega⟩
  rw [isSumFree_iff]
  intro u hu v hv huv
  simp only [hB, coe_filter, Set.mem_setOf_eq, mem_Icc] at hu hv huv
  apply val_sumfree p k hpk ((u : ZMod p) * x) ((v : ZMod p) * x) hu.2.1 hu.2.2 hv.2.1 hv.2.2
  · have := huv.2.1; push_cast at this; rwa [add_mul] at this
  · have := huv.2.2; push_cast at this; rwa [add_mul] at this

end OMA

theorem OMA.solution : type_of% @Erdos792.erdos_792.variants.alon_kleitman :=
  OMA.solution_aux
