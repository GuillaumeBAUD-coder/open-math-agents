import OMAStatements.S_mo_233932

open Equiv Finset
open scoped BigOperators

namespace OMA.Mo233932

private abbrev P (n : ℕ) := Perm (Fin n)

private theorem dist_eq_support {n : ℕ} (p c : P n) :
    hammingDist (fun i ↦ p i) (fun i ↦ c i) = (c⁻¹ * p).support.card := by
  unfold hammingDist
  congr 1
  ext i
  simp only [mem_filter, mem_univ, true_and, Perm.mem_support, Perm.mul_apply,
    Perm.coe_inv]
  exact not_congr ⟨fun h ↦ by rw [h, c.symm_apply_apply],
    fun h ↦ by simpa using congrArg c h⟩

private def ball {n : ℕ} (r : ℕ) (c : P n) : Finset (P n) :=
  univ.filter fun p ↦ hammingDist (fun i ↦ p i) (fun i ↦ c i) ≤ r

private theorem card_support_fiber {n : ℕ} (A : Finset (Fin n)) :
    (univ.filter fun p : P n ↦ p.support = A).card = numDerangements A.card := by
  classical
  let e : derangements A ≃ (univ.filter fun p : P n ↦ p.support = A) :=
    (derangements.subtypeEquiv (fun x ↦ x ∈ A)).trans
      (Equiv.subtypeEquivRight fun p ↦ by
        simp only [mem_filter, mem_univ, true_and, Finset.ext_iff, Perm.mem_support,
          Function.mem_fixedPoints, Function.IsFixedPt]
        exact forall_congr' fun x ↦ by tauto)
  rw [← Fintype.card_coe, ← Fintype.card_congr e, card_derangements_eq_numDerangements,
    Fintype.card_coe]

private theorem card_support_size (n k : ℕ) :
    (univ.filter fun p : P n ↦ p.support.card = k).card =
      n.choose k * numDerangements k := by
  classical
  let S := (univ : Finset (Fin n)).powersetCard k
  rw [card_eq_sum_card_fiberwise (f := fun p : P n ↦ p.support) (t := S) (by
    intro p hp
    exact mem_powersetCard.mpr ⟨subset_univ _, (mem_filter.mp hp).2⟩)]
  have hfiber (A : Finset (Fin n)) (hA : A ∈ S) :
      ((univ.filter fun p : P n ↦ p.support.card = k).filter
        fun p ↦ p.support = A).card = numDerangements k := by
    have hAk := (mem_powersetCard.mp hA).2
    rw [← hAk, ← card_support_fiber]
    congr 1
    ext p
    simp only [mem_filter, mem_univ, true_and]
    exact ⟨And.right, fun hp ↦ ⟨congrArg Finset.card hp, hp⟩⟩
  rw [sum_const_nat hfiber]
  simp [S, card_powersetCard]

private theorem card_ball {n : ℕ} (r : ℕ) (c : P n) :
    (ball r c).card = OMA.S_mo_233932.volume n r := by
  classical
  let e : ball r c ≃ univ.filter (fun p : P n ↦ p.support.card ≤ r) :=
    (Equiv.mulLeft c⁻¹).subtypeEquiv fun p ↦ by
      simp [ball, dist_eq_support, Equiv.mulLeft]
  rw [← Fintype.card_coe, Fintype.card_congr e, Fintype.card_coe,
    card_eq_sum_card_fiberwise (f := fun p : P n ↦ p.support.card) (t := range (r + 1)) (by
      intro p hp
      exact mem_range_succ_iff.mpr (mem_filter.mp hp).2)]
  unfold OMA.S_mo_233932.volume
  refine sum_congr rfl fun k hk ↦ ?_
  have hkr := mem_range_succ_iff.mp hk
  rw [← card_support_size]
  congr 1
  ext p
  simp only [mem_filter, mem_univ, true_and]
  exact ⟨And.right, fun hp ↦ ⟨hp ▸ hkr, hp⟩⟩

private theorem lower_bound {n r : ℕ} (C : Finset (P n))
    (hC : OMA.S_mo_233932.covers C r) :
    n.factorial ≤ C.card * OMA.S_mo_233932.volume n r := by
  classical
  have hcover : C.biUnion (ball r) = univ := by
    apply eq_univ_of_forall
    intro p
    obtain ⟨c, hc, hdist⟩ := hC p
    exact mem_biUnion.mpr ⟨c, hc, mem_filter.mpr ⟨mem_univ _, hdist⟩⟩
  have hcard := card_biUnion_le (s := C) (t := ball r)
  rw [hcover, card_univ, Fintype.card_perm, Fintype.card_fin,
    sum_const_nat (fun c _ ↦ card_ball r c)] at hcard
  exact hcard

private theorem prefix_cover (n r : ℕ) (hr : r ≤ n) :
    ∃ C : Finset (P n), C.card ≤ n.factorial / r.factorial ∧
      OMA.S_mo_233932.covers C r := by
  classical
  obtain ⟨A, _, hA⟩ := exists_subset_card_eq (s := (univ : Finset (Fin n))) (by simpa using hr)
  let H : Subgroup (P n) :=
    { carrier := {p | ∀ i ∉ A, p i = i}
      one_mem' := fun _ _ ↦ rfl
      mul_mem' := fun hp hq i hi ↦ by simp [Perm.mul_apply, hp i hi, hq i hi]
      inv_mem' := fun {p} hp i hi ↦ p.injective (by simpa using (hp i hi).symm) }
  let : Fintype (P n ⧸ H) := Fintype.ofFinite _
  let C : Finset (P n) := (univ : Finset (P n ⧸ H)).image Quotient.out
  have hH : Nat.card H = r.factorial := by
    let e : Perm A ≃ H := Perm.subtypeEquivSubtypePerm (fun i ↦ i ∈ A)
    rw [← Nat.card_congr e, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_coe, hA]
  have hindex : H.index = n.factorial / r.factorial := by
    have hcard := H.index_mul_card
    rw [hH, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin] at hcard
    rw [← hcard, Nat.mul_div_cancel _ (Nat.factorial_pos _)]
  refine ⟨C, ?_, ?_⟩
  · calc
      C.card ≤ Fintype.card (P n ⧸ H) := (card_image_le).trans_eq card_univ
      _ = n.factorial / r.factorial := by rw [← Nat.card_eq_fintype_card, ← H.index_eq_card, hindex]
  · intro p
    let q : P n ⧸ H := p
    have hfix : q.out⁻¹ * p ∈ H :=
      QuotientGroup.eq.mp (QuotientGroup.out_eq' q)
    refine ⟨q.out, mem_image.mpr ⟨q, mem_univ _, rfl⟩, ?_⟩
    rw [dist_eq_support, ← hA]
    exact card_le_card fun i hi ↦ by
      by_contra hmiss
      exact (Perm.mem_support.mp hi) (hfix i hmiss)

private theorem tuple_cover (n r K : ℕ)
    (hcount : n.factorial * (n.factorial - OMA.S_mo_233932.volume n r) ^ K <
      n.factorial ^ K) :
    ∃ C : Finset (P n), C.card ≤ K ∧ OMA.S_mo_233932.covers C r := by
  classical
  let bad (p : P n) : Finset (Fin K → P n) :=
    univ.filter fun f ↦ ∀ i, f i ∈ (univ \ ball r p : Finset (P n))
  have hbad (p : P n) :
      (bad p).card = (n.factorial - OMA.S_mo_233932.volume n r) ^ K := by
    let e : (Fin K → (univ \ ball r p : Finset (P n))) ≃ bad p :=
      { toFun := fun f ↦ ⟨fun i ↦ f i, mem_filter.mpr ⟨mem_univ _, fun i ↦ (f i).2⟩⟩
        invFun := fun f i ↦ ⟨f.val i, (mem_filter.mp f.2).2 i⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
    rw [← Fintype.card_coe, ← Fintype.card_congr e, Fintype.card_fun, Fintype.card_fin,
      Fintype.card_coe, card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_perm,
      Fintype.card_fin, card_ball]
  have hlt : ((univ : Finset (P n)).biUnion bad).card <
      (univ : Finset (Fin K → P n)).card := by
    refine card_biUnion_le.trans_lt ?_
    simpa [Fintype.card_fun, Fintype.card_perm, hbad] using hcount
  obtain ⟨f, _, hf⟩ := exists_mem_notMem_of_card_lt_card hlt
  refine ⟨univ.image f, card_image_le.trans_eq (by simp), ?_⟩
  intro p
  have hnot : f ∉ bad p := fun h ↦ hf (mem_biUnion.mpr ⟨p, mem_univ _, h⟩)
  have hex : ∃ i, f i ∈ ball r p := by
    by_contra! hn
    apply hnot
    exact mem_filter.mpr ⟨mem_univ _, fun i ↦ mem_sdiff.mpr ⟨mem_univ _, hn i⟩⟩
  obtain ⟨i, hi⟩ := hex
  have hd : hammingDist (fun j ↦ f i j) (fun j ↦ p j) ≤ r := (mem_filter.mp hi).2
  rw [hammingDist_comm] at hd
  exact ⟨f i, mem_image.mpr ⟨i, mem_univ _, rfl⟩, hd⟩

private theorem covering_result : type_of% @OMA.S_mo_233932.main := by
  classical
  intro n r hr
  refine ⟨lower_bound, ?_⟩
  intro K hK h
  obtain ⟨C, hcard, hcover⟩ : ∃ C : Finset (P n), C.card ≤ K ∧
      OMA.S_mo_233932.covers C r := by
    rcases h with hprefix | htuple
    · obtain ⟨C, hC, hcover⟩ := prefix_cover n r hr
      exact ⟨C, hC.trans hprefix, hcover⟩
    · exact tuple_cover n r K htuple
  obtain ⟨D, hCD, hD⟩ := C.exists_superset_card_eq hcard (by simpa [Fintype.card_perm] using hK)
  exact ⟨D, hD, fun p ↦ by
    obtain ⟨c, hc, hd⟩ := hcover p
    exact ⟨c, hCD hc, hd⟩⟩

end OMA.Mo233932

theorem OMA.solution : type_of% @OMA.S_mo_233932.main := OMA.Mo233932.covering_result
