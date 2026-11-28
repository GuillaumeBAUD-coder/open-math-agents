import OMAReductions.R_Arxiv_2607_08366_min_modulus_R2

/-!
# Proof of `Arxiv.2607.08366.min_modulus.R2.H1`

Proves that if `A : Finset (ZMod N)` (`0 < N`) has cardinality `n` and satisfies `IsValidMod A`,
then `2 ^ (n - 1) ≤ N`.

For `n = 0`, `2 ^ 0 = 1 ≤ N`. For `n ≥ 1`, pick `a₀ ∈ A` and set `B = A.erase a₀` (`#B = n - 1`).
If `N < 2 ^ (n - 1)`, then `#(B.powerset) = 2 ^ (n - 1) > N = Fintype.card (ZMod N)`, so by the
pigeonhole principle two distinct subsets `S₁ ≠ S₂ ⊆ B` satisfy
`∑ x ∈ S₁, (x - a₀) = ∑ x ∈ S₂, (x - a₀)`.
Let `U = S₁ \ S₂` and `V = S₂ \ S₁`; swapping `S₁, S₂` if necessary, assume `#U ≤ #V` (so `V` is
nonempty). Define the multiplicity function `m : ZMod N → ℕ` on `A` by:
- `m a₀ = 1 + (#V - #U)`,
- `m x = 2` for `x ∈ U`,
- `m x = 0` for `x ∈ V`,
- `m x = 1` for all other `x ∈ A`.
Then `∑ a ∈ A, m a = #A` and `∑ a ∈ A, (m a : ZMod N) * a = ∑ a ∈ A, a`, yet `m v = 0 ≠ 1` for
any `v ∈ V`, contradicting `IsValidMod A`.
-/

namespace Arxiv260708366R2H1Proof

open Finset

private lemma build_contradiction {N : ℕ} [NeZero N] {A : Finset (ZMod N)}
    (hvalid : Arxiv.«2607.08366».IsValidMod A) {a₀ : ZMod N} (ha₀ : a₀ ∈ A)
    {S₁ S₂ : Finset (ZMod N)} (hS₁ : S₁ ⊆ A.erase a₀) (hS₂ : S₂ ⊆ A.erase a₀)
    (hne : S₁ ≠ S₂) (hcard : (S₁ \ S₂).card ≤ (S₂ \ S₁).card)
    (hsum : ∑ x ∈ S₁, (x - a₀) = ∑ x ∈ S₂, (x - a₀)) : False := by
  set U := S₁ \ S₂
  set V := S₂ \ S₁
  have hUV_disj : Disjoint U V := by
    rw [Finset.disjoint_left]
    intro x hxU hxV
    exact (Finset.mem_sdiff.mp hxU).2 (Finset.mem_sdiff.mp hxV).1
  have hU_sub : U ⊆ A.erase a₀ := Finset.sdiff_subset.trans hS₁
  have hV_sub : V ⊆ A.erase a₀ := Finset.sdiff_subset.trans hS₂
  have ha₀_not_U : a₀ ∉ U := fun h => (Finset.mem_erase.mp (hU_sub h)).1 rfl
  have ha₀_not_V : a₀ ∉ V := fun h => (Finset.mem_erase.mp (hV_sub h)).1 rfl
  have hV_ne : V.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    have hU0 : U.card = 0 := by rw [hemp, Finset.card_empty] at hcard; omega
    have hUemp : U = ∅ := Finset.card_eq_zero.mp hU0
    apply hne
    ext x
    constructor
    · intro hx; by_contra hx2
      have : x ∈ U := Finset.mem_sdiff.mpr ⟨hx, hx2⟩
      rw [hUemp] at this; exact Finset.notMem_empty x this
    · intro hx; by_contra hx1
      have : x ∈ V := Finset.mem_sdiff.mpr ⟨hx, hx1⟩
      rw [hemp] at this; exact Finset.notMem_empty x this
  -- Cancel S₁ ∩ S₂ from hsum to get ∑_{x ∈ U} (x - a₀) = ∑_{x ∈ V} (x - a₀)
  have hsum_UV : ∑ x ∈ U, (x - a₀) = ∑ x ∈ V, (x - a₀) := by
    have h1 : ∑ x ∈ S₁, (x - a₀) = (∑ x ∈ U, (x - a₀)) + ∑ x ∈ S₁ ∩ S₂, (x - a₀) := by
      rw [← Finset.sum_union (Finset.disjoint_sdiff_inter S₁ S₂), Finset.sdiff_union_inter]
    have h2 : ∑ x ∈ S₂, (x - a₀) = (∑ x ∈ V, (x - a₀)) + ∑ x ∈ S₁ ∩ S₂, (x - a₀) := by
      have hdisj : Disjoint V (S₁ ∩ S₂) := by
        rw [Finset.inter_comm]
        exact Finset.disjoint_sdiff_inter S₂ S₁
      have hunion : V ∪ (S₁ ∩ S₂) = S₂ := by
        rw [Finset.inter_comm]
        exact Finset.sdiff_union_inter S₂ S₁
      rw [← Finset.sum_union hdisj, hunion]
    rw [h1, h2] at hsum
    exact add_right_cancel hsum
  have hsum_eq : (∑ x ∈ U, x) + ((V.card - U.card : ℕ) : ZMod N) * a₀ = ∑ x ∈ V, x := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] at hsum_UV
    have hcast : ((V.card - U.card : ℕ) : ZMod N) = (V.card : ZMod N) - (U.card : ZMod N) :=
      Nat.cast_sub hcard
    rw [hcast]
    linear_combination hsum_UV
  -- Define multiplicity function m
  let m : ZMod N → ℕ := fun x =>
    if x = a₀ then 1 + (V.card - U.card)
    else if x ∈ U then 2
    else if x ∈ V then 0
    else 1
  -- Compute ∑_{a ∈ A} m a = A.card
  have hm_card : ∑ a ∈ A, m a = A.card := by
    rw [← Finset.add_sum_erase _ _ ha₀]
    have hm_a0 : m a₀ = 1 + (V.card - U.card) := by simp [m]
    rw [hm_a0]
    have herase_split : ∑ a ∈ A.erase a₀, m a =
        (∑ a ∈ U, m a) + (∑ a ∈ V, m a) + ∑ a ∈ (A.erase a₀) \ (U ∪ V), m a := by
      have hUV_sub : U ∪ V ⊆ A.erase a₀ := Finset.union_subset hU_sub hV_sub
      rw [← Finset.sum_sdiff hUV_sub, Finset.sum_union hUV_disj]
      omega
    have hm_U : ∑ a ∈ U, m a = 2 * U.card := by
      have h : ∀ a ∈ U, m a = 2 := fun a ha => by
        have hne0 : a ≠ a₀ := fun h => ha₀_not_U (h ▸ ha)
        simp [m, hne0, ha]
      rw [Finset.sum_congr rfl h, Finset.sum_const, smul_eq_mul, mul_comm]
    have hm_V : ∑ a ∈ V, m a = 0 := by
      have h : ∀ a ∈ V, m a = 0 := fun a ha => by
        have hne0 : a ≠ a₀ := fun h => ha₀_not_V (h ▸ ha)
        have hnotU : a ∉ U := Finset.disjoint_right.mp hUV_disj ha
        simp [m, hne0, hnotU, ha]
      rw [Finset.sum_congr rfl h, Finset.sum_const_zero]
    have hm_rest : ∑ a ∈ (A.erase a₀) \ (U ∪ V), m a = ((A.erase a₀) \ (U ∪ V)).card := by
      have h : ∀ a ∈ (A.erase a₀) \ (U ∪ V), m a = 1 := fun a ha => by
        rw [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_union, not_or] at ha
        simp [m, ha.1.1, ha.2.1, ha.2.2]
      rw [Finset.sum_congr rfl h, Finset.sum_const, smul_eq_mul, mul_one]
    have hcard_er : (A.erase a₀).card = U.card + V.card + ((A.erase a₀) \ (U ∪ V)).card := by
      have hUV_sub : U ∪ V ⊆ A.erase a₀ := Finset.union_subset hU_sub hV_sub
      have h1 := Finset.card_sdiff_add_card_eq_card hUV_sub
      rw [Finset.card_union_of_disjoint hUV_disj] at h1
      omega
    have hcard_A : A.card = 1 + (A.erase a₀).card := by
      have := Finset.card_erase_add_one ha₀
      omega
    rw [herase_split, hm_U, hm_V, hm_rest]
    omega
  -- Compute ∑_{a ∈ A} (m a : ZMod N) * a = ∑_{a ∈ A} a
  have hm_sum : ∑ a ∈ A, (m a : ZMod N) * a = ∑ a ∈ A, a := by
    rw [← Finset.add_sum_erase _ _ ha₀, ← Finset.add_sum_erase _ (fun a => a) ha₀]
    have hm_a0 : (m a₀ : ZMod N) * a₀ = a₀ + ((V.card - U.card : ℕ) : ZMod N) * a₀ := by
      simp only [m, ↓reduceIte, Nat.cast_add, Nat.cast_one]
      ring
    rw [hm_a0]
    have hUV_sub : U ∪ V ⊆ A.erase a₀ := Finset.union_subset hU_sub hV_sub
    have h1 : ∑ a ∈ A.erase a₀, (m a : ZMod N) * a =
        (∑ a ∈ U, (m a : ZMod N) * a) + (∑ a ∈ V, (m a : ZMod N) * a) +
        ∑ a ∈ (A.erase a₀) \ (U ∪ V), (m a : ZMod N) * a := by
      rw [← Finset.sum_sdiff hUV_sub, Finset.sum_union hUV_disj]
      ring
    have h2 : ∑ a ∈ A.erase a₀, a =
        (∑ a ∈ U, a) + (∑ a ∈ V, a) + ∑ a ∈ (A.erase a₀) \ (U ∪ V), a := by
      rw [← Finset.sum_sdiff hUV_sub, Finset.sum_union hUV_disj]
      ring
    have hmU : ∑ a ∈ U, (m a : ZMod N) * a = 2 * ∑ a ∈ U, a := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a ha => ?_
      have hne0 : a ≠ a₀ := fun h => ha₀_not_U (h ▸ ha)
      simp [m, hne0, ha]
    have hmV : ∑ a ∈ V, (m a : ZMod N) * a = 0 := by
      refine Finset.sum_eq_zero fun a ha => ?_
      have hne0 : a ≠ a₀ := fun h => ha₀_not_V (h ▸ ha)
      have hnotU : a ∉ U := Finset.disjoint_right.mp hUV_disj ha
      simp [m, hne0, hnotU, ha]
    have hmR : ∑ a ∈ (A.erase a₀) \ (U ∪ V), (m a : ZMod N) * a =
        ∑ a ∈ (A.erase a₀) \ (U ∪ V), a := by
      refine Finset.sum_congr rfl fun a ha => ?_
      rw [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_union, not_or] at ha
      simp [m, ha.1.1, ha.2.1, ha.2.2]
    rw [h1, h2, hmU, hmV, hmR]
    linear_combination hsum_eq
  -- Contradict IsValidMod A at any v ∈ V
  obtain ⟨v, hv⟩ := hV_ne
  have hvA : v ∈ A := Finset.mem_of_mem_erase (hV_sub hv)
  have hm1 : m v = 1 := hvalid m hm_card hm_sum v hvA
  have hv_ne0 : v ≠ a₀ := fun h => ha₀_not_V (h ▸ hv)
  have hv_notU : v ∉ U := Finset.disjoint_right.mp hUV_disj hv
  have hm0 : m v = 0 := by simp [m, hv_ne0, hv_notU, hv]
  omega

end Arxiv260708366R2H1Proof

theorem OMA.solution : OMA.R_Arxiv_2607_08366_min_modulus_R2.H1 := by
  intro n N hN A hcard hvalid
  have : NeZero N := ⟨hN.ne'⟩
  by_cases hn0 : n = 0
  · subst hn0; omega
  have hne : A.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨a₀, ha₀⟩ := hne
  by_contra hlt
  have hgt : Fintype.card (ZMod N) < (A.erase a₀).powerset.card := by
    rw [ZMod.card N, Finset.card_powerset, Finset.card_erase_of_mem ha₀, hcard]
    omega
  have hnot_inj : ¬ Set.InjOn (fun S : Finset (ZMod N) => ∑ x ∈ S, (x - a₀))
      ((A.erase a₀).powerset : Set (Finset (ZMod N))) := by
    intro hinj
    have hle := Finset.card_le_card_of_injOn
      (fun S : Finset (ZMod N) => ∑ x ∈ S, (x - a₀))
      (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _)) hinj
    rw [Finset.card_univ] at hle
    omega
  rw [Set.InjOn] at hnot_inj
  push Not at hnot_inj
  obtain ⟨S₁, hS₁, S₂, hS₂, hsum, hne⟩ := hnot_inj
  rw [Finset.mem_coe, Finset.mem_powerset] at hS₁ hS₂
  rcases le_total (S₁ \ S₂).card (S₂ \ S₁).card with hle | hle
  · exact Arxiv260708366R2H1Proof.build_contradiction hvalid ha₀ hS₁ hS₂ hne hle hsum
  · exact Arxiv260708366R2H1Proof.build_contradiction hvalid ha₀ hS₂ hS₁ hne.symm hle hsum.symm
