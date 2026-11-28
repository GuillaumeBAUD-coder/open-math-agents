import OMAStatements.S_mo_210872
import Mathlib

namespace OMA.P_mo_210872
open Finset Polynomial OMA.S_mo_210872

theorem coeff_prod_sum {G ι α : Type*} [AddCommMonoid G] [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α] [DecidableEq G] (g : ι → α → G) (c : G) :
    (∏ i, ∑ a, (AddMonoidAlgebra.single (g i a) 1 : AddMonoidAlgebra ℕ G)).coeff c =
      #{x : ι → α | ∑ i, g i (x i) = c} := by
  rw [Finset.prod_univ_sum]
  simp only [AddMonoidAlgebra.prod_single, AddMonoidAlgebra.coeff_sum,
    AddMonoidAlgebra.coeff_single, Finset.prod_const_one, Finsupp.finsetSum_apply,
    Finsupp.single_apply, Fintype.piFinset_univ]
  rw [Finset.card_filter]

theorem joint_eq {n L : ℕ} (T : Finset (Mask n)) :
    joint L T = #{x : Box n L | ∀ s ∈ T, summ x s = 0} := by
  classical
  unfold joint
  rw [coeff_prod_sum]
  congr 1
  apply Finset.filter_congr
  intro x _
  rw [funext_iff]
  apply forall_congr'
  intro s
  simp only [Finset.sum_apply, col, Pi.zero_apply, summ]
  by_cases hs : s ∈ T
  · simp [hs, Finset.sum_ite_mem]
  · simp [hs]

theorem hits_sub {n L : ℕ} (x : Box n L) : hits x ⊆ labels n := Finset.filter_subset _ _

theorem law_eq (n L : ℕ) : law n L = ∑ x : Box n L, (X : ℤ[X]) ^ (hits x).card := by
  classical
  have h1 : ∀ T ∈ (labels n).powerset, (C (joint L T : ℤ) * (X-1)^T.card : ℤ[X]) =
      ∑ x : Box n L, if T ⊆ hits x then (X-1 : ℤ[X])^T.card else 0 := by
    intro T hT
    rw [Finset.mem_powerset] at hT
    rw [joint_eq, Finset.card_filter, Nat.cast_sum, map_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x _
    have : (∀ s ∈ T, summ x s = 0) ↔ T ⊆ hits x := by
      constructor
      · intro h s hs
        exact Finset.mem_filter.mpr ⟨hT hs, h s hs⟩
      · intro h s hs
        exact (Finset.mem_filter.mp (h hs)).2
    by_cases hx : T ⊆ hits x
    · rw [if_pos (this.mpr hx), if_pos hx]
      simp
    · have h2 : ¬ (∀ s ∈ T, summ x s = 0) := fun h => hx (this.mp h)
      rw [if_neg h2, if_neg hx]
      simp
  unfold law
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [← Finset.sum_filter]
  have hf : (labels n).powerset.filter (fun T => T ⊆ hits x) = (hits x).powerset := by
    ext T
    simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨fun h => h.2, fun h => ⟨h.trans (hits_sub x), h⟩⟩
  rw [hf]
  have := Finset.sum_pow_mul_eq_add_pow (X - 1 : ℤ[X]) 1 (hits x)
  simp only [one_pow, mul_one, sub_add_cancel] at this
  exact this

theorem part1 (n L : ℕ) : ∀ m, (mass n L m : ℤ) = (law n L).coeff m := by
  classical
  intro m
  rw [law_eq, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_X_pow]
  unfold mass
  rw [Finset.card_filter, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : (hits x).card = m
  · simp [h]
  · simp [h, Ne.symm h]

theorem count_one {n L : ℕ} (s : Mask n) :
    #{x : Box n L | summ x s = 0} = ((step L)^s.card).coeff 0 * (2*L+1)^(n-s.card) := by
  classical
  let g : Fin n → Fin (2*L+1) → ℤ := fun i a => if i ∈ s then val a else 0
  have h1 := coeff_prod_sum g 0
  have h2 : ∀ x : Box n L, (∑ i, g i (x i) = 0) ↔ summ x s = 0 := by
    intro x
    simp only [g, summ, Finset.sum_ite_mem, Finset.univ_inter]
  have h3 : (∏ i, ∑ a, (AddMonoidAlgebra.single (g i a) 1 : AddMonoidAlgebra ℕ ℤ)) =
      ∏ i, (if i ∈ s then step L else AddMonoidAlgebra.single 0 (2*L+1)) := by
    apply Finset.prod_congr rfl
    intro i _
    by_cases hi : i ∈ s
    · simp [g, hi, step]
    · simp [g, hi, Finset.sum_const]
  rw [h3, Finset.prod_ite, Finset.prod_const, Finset.prod_const,
    AddMonoidAlgebra.single_pow, smul_zero, AddMonoidAlgebra.coeff_mul_single_zero] at h1
  have h4 : #({i | i ∈ s} : Finset (Fin n)) = s.card := by
    rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
  have h5 : #({i | i ∉ s} : Finset (Fin n)) = n - s.card := by
    rw [Finset.filter_not, Finset.filter_mem_eq_inter, Finset.univ_inter,
      Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
  rw [h4, h5] at h1
  rw [h1]
  congr 1
  exact Finset.filter_congr (fun x _ => (h2 x).symm)

theorem part2 (n L : ℕ) : (∑ x : Box n L, (hits x).card) = meanCount n L := by
  classical
  unfold meanCount
  simp only [← count_one]
  unfold hits
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]

theorem val_inj {L : ℕ} {a b : Fin (2*L+1)} (h : S_mo_210872.val a = S_mo_210872.val b) : a = b := by
  unfold S_mo_210872.val at h
  exact Fin.ext (by omega)

theorem det_one {n L : ℕ} {x y : Box n L} {u : Mask n} {i : Fin n} (hi : i ∈ u)
    (hag : ∀ k ∈ u, k ≠ i → x k = y k) (h : summ x u = summ y u) : x i = y i := by
  unfold summ at h
  rw [← Finset.add_sum_erase _ _ hi, ← Finset.add_sum_erase _ _ hi] at h
  have : ∑ k ∈ u.erase i, S_mo_210872.val (x k) = ∑ k ∈ u.erase i, S_mo_210872.val (y k) :=
    Finset.sum_congr rfl (fun k hk => by
      rw [hag k (Finset.mem_of_mem_erase hk) (Finset.ne_of_mem_erase hk)])
  exact val_inj (by linarith)

theorem pair_bound {n L : ℕ} {u v : Mask n} {i j : Fin n} (hij : i ≠ j) (hi : i ∈ u)
    (hju : j ∉ u) (hjv : j ∈ v) :
    #{x : Box n L | summ x u = 0 ∧ summ x v = 0} ≤ (2*L+1)^(n-2) := by
  classical
  let S : Finset (Fin n) := ({i, j} : Finset (Fin n))ᶜ
  let f : Box n L → (S → Fin (2*L+1)) := fun x k => x k.1
  have hc : (Finset.univ : Finset (S → Fin (2*L+1))).card = (2*L+1)^(n-2) := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_coe, Fintype.card_fin,
      Finset.card_compl, Finset.card_pair hij, Fintype.card_fin]
  rw [← hc]
  apply Finset.card_le_card_of_injOn f (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _))
  intro x hx y hy hxy
  simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_univ, true_and] at hx hy
  have hag : ∀ k, k ≠ i → k ≠ j → x k = y k := by
    intro k hki hkj
    have hk : k ∈ S := by simp [S, hki, hkj]
    exact congrFun hxy ⟨k, hk⟩
  have hxi : x i = y i := det_one hi (fun k hk hki => hag k hki (fun e => hju (e ▸ hk)))
    (by rw [hx.1, hy.1])
  have hxj : x j = y j := det_one hjv (fun k _ hkj => by
      by_cases hki : k = i
      · rw [hki]; exact hxi
      · exact hag k hki hkj)
    (by rw [hx.2, hy.2])
  funext k
  by_cases hki : k = i
  · rw [hki]; exact hxi
  · by_cases hkj : k = j
    · rw [hkj]; exact hxj
    · exact hag k hki hkj

theorem pair_bound' {n L : ℕ} {s t : Mask n} (hs : s ∈ labels n) (ht : t ∈ labels n)
    (hst : s ≠ t) :
    #{x : Box n L | summ x s = 0 ∧ summ x t = 0} ≤ (2*L+1)^(n-2) := by
  classical
  have hs' : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hs).1
  have ht' : t.Nonempty := Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp ht).1
  by_cases hts : t ⊆ s
  · have hst' : ¬ s ⊆ t := fun h => hst (Finset.Subset.antisymm h hts)
    obtain ⟨j, hjs, hjt⟩ := Finset.not_subset.mp hst'
    obtain ⟨i, hi⟩ := ht'
    have hij : i ≠ j := fun e => hjt (e ▸ hi)
    have := pair_bound (L := L) hij hi hjt hjs
    calc #{x : Box n L | summ x s = 0 ∧ summ x t = 0}
        = #{x : Box n L | summ x t = 0 ∧ summ x s = 0} := by
          congr 1
          exact Finset.filter_congr (fun x _ => and_comm)
      _ ≤ _ := this
  · obtain ⟨j, hjt, hjs⟩ := Finset.not_subset.mp hts
    obtain ⟨i, hi⟩ := hs'
    have hij : i ≠ j := fun e => hjs (e ▸ hi)
    exact pair_bound hij hi hjs hjt

theorem hits_offDiag {n L : ℕ} (x : Box n L) :
    ((hits x).offDiag).card = ∑ p ∈ (labels n).offDiag,
      if summ x p.1 = 0 ∧ summ x p.2 = 0 then 1 else 0 := by
  classical
  rw [← Finset.card_filter]
  congr 1
  ext p
  simp only [hits, Finset.mem_offDiag, Finset.mem_filter]
  tauto

theorem offDiag_bound (n L : ℕ) :
    ∑ x : Box n L, ((hits x).offDiag).card ≤
      (labels n).card*((labels n).card-1)*(2*L+1)^(n-2) := by
  classical
  simp only [hits_offDiag]
  rw [Finset.sum_comm]
  have h : ∀ p ∈ (labels n).offDiag, (∑ x : Box n L,
      if summ x p.1 = 0 ∧ summ x p.2 = 0 then 1 else 0) ≤ (2*L+1)^(n-2) := by
    intro p hp
    rw [← Finset.card_filter]
    obtain ⟨h1, h2, h3⟩ := Finset.mem_offDiag.mp hp
    exact pair_bound' h1 h2 h3
  calc _ ≤ ∑ p ∈ (labels n).offDiag, (2*L+1)^(n-2) := Finset.sum_le_sum h
    _ = _ := by
      rw [Finset.sum_const, Finset.offDiag_card, smul_eq_mul, Nat.mul_sub_one]

theorem part3 (n L : ℕ) :
    2*tail n L ≤ (labels n).card*((labels n).card-1)*(2*L+1)^(n-2) := by
  classical
  refine le_trans ?_ (offDiag_bound n L)
  unfold tail
  rw [Finset.card_filter, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  rw [Finset.offDiag_card]
  generalize (hits x).card = k
  split_ifs with hk
  · have : 2*k ≤ k*k := Nat.mul_le_mul_right k hk
    generalize k*k = m at *
    omega
  · omega

theorem part4 (n L : ℕ) : mass n L 1 ≤ meanCount n L := by
  classical
  rw [← part2]
  unfold mass
  rw [Finset.card_filter]
  apply Finset.sum_le_sum
  intro x _
  split_ifs with hk <;> omega

theorem part5 (n L : ℕ) : meanCount n L ≤
    mass n L 1 + (labels n).card*((labels n).card-1)*(2*L+1)^(n-2) := by
  classical
  refine le_trans ?_ (Nat.add_le_add_left (offDiag_bound n L) _)
  rw [← part2]
  unfold mass
  rw [Finset.card_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x _
  rw [Finset.offDiag_card]
  generalize (hits x).card = k
  split_ifs with hk
  · omega
  · rcases Nat.lt_or_ge k 2 with h | h
    · have : k = 0 := by omega
      subst this
      simp
    · have : 2*k ≤ k*k := Nat.mul_le_mul_right k h
      generalize k*k = m at *
      omega

end OMA.P_mo_210872

theorem OMA.solution : type_of% @OMA.S_mo_210872.main := by
  intro n L
  exact ⟨OMA.P_mo_210872.part1 n L, OMA.P_mo_210872.part2 n L, OMA.P_mo_210872.part3 n L,
    OMA.P_mo_210872.part4 n L, OMA.P_mo_210872.part5 n L⟩
