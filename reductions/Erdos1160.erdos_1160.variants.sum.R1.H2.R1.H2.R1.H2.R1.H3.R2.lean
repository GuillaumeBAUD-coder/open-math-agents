import OMAReductions.R_Erdos1160_erdos_1160_variants_sum_R1_H2_R1_H2_R1_H2_R1
import Mathlib.GroupTheory.Rank
import Mathlib.GroupTheory.FreeGroup.Basic

/-!
# Counting finite 2-groups with few generators

For groups of order 2^m with at most d generators, we give a list of marked
presentations of size at most 2^((d+1)m(m+1)/2). At each central lift, one bit
per old relator records whether it maps to the nonidentity kernel element.
This proves the required estimate throughout the range 7d ≤ m. The two
remaining estimates concern higher generator ranks in class three and above.
-/

open Subgroup Filter CategoryTheory
open scoped commutatorElement

namespace OMA.R_Erdos1160_erdos_1160_variants_sum_R1_H2_R1_H2_R1_H2_R1_H3_R2

/-- The class-three part with more than m/7 generators. -/
def H1 : Prop := ∀ᶠ m : ℕ in atTop,
  (24 * (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
    {G : FiniteGrp.{0} | Nat.card G = 2^m ∧ ¬commutator G ≤ center G ∧
      2 < Nat.card ((⊤ : Subgroup G).lowerCentralSeries 2) ∧
      m / 7 < Group.rank G ∧ (⊤ : Subgroup G).lowerCentralSeries 2 ≤ center G}).ncard)^27 *
      2^(9*m^2) ≤ 2^(2*m^3)

/-- The higher-class part with more than m/7 generators. -/
def H2 : Prop := ∀ᶠ m : ℕ in atTop,
  (24 * (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
    {G : FiniteGrp.{0} | Nat.card G = 2^m ∧ ¬commutator G ≤ center G ∧
      2 < Nat.card ((⊤ : Subgroup G).lowerCentralSeries 2) ∧
      m / 7 < Group.rank G ∧ ¬(⊤ : Subgroup G).lowerCentralSeries 2 ≤ center G}).ncard)^27 *
      2^(9*m^2) ≤ 2^(2*m^3)

/-- Killing the corrected relations, one square and the generator commutators
recovers the kernel of a marked central extension of order two. -/
lemma lift_kernel {F G : Type} [Group F] [Group G] [DecidableEq F] (f : F →* G)
    (S R D : Finset F) (hS : closure (S : Set F) = ⊤)
    (t : F) (ht : f t ≠ 1) (htsq : (f t)^2 = 1) (htc : f t ∈ center G)
    (hR : f.ker ≤ normalClosure (R : Set F))
    (hb : ∀ r ∈ R, f r = if r ∈ D then f t else 1) :
    let L := (R.image fun r => if r ∈ D then r * t⁻¹ else r) ∪
      insert (t^2) (S.image fun s => ⁅s,t⁆)
    normalClosure (L : Set F) = f.ker := by
  classical
  intro L
  let K := normalClosure (L : Set F)
  let j := QuotientGroup.mk' K
  have hL : ∀ x ∈ L, f x = 1 := by
    intro x hx
    rcases Finset.mem_union.mp hx with hc | he
    · obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hc
      split <;> rename_i h
      · simp [hb r hr, h]
      · simpa [h] using hb r hr
    · rcases Finset.mem_insert.mp he with rfl | he
      · simpa using htsq
      · obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp he
        rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
        exact (Subgroup.mem_center_iff.mp htc _)
  have hK : K ≤ f.ker := normalClosure_le_normal hL
  have kill (x) (hx : x ∈ L) : j x = 1 :=
    (QuotientGroup.eq_one_iff x).mpr (subset_normalClosure hx)
  have hsquare : (j t)^2 = 1 := by
    rw [← map_pow]
    exact kill _ (Finset.mem_union_right _ (Finset.mem_insert_self ..))
  have commute_all (y : F) : j y * j t = j t * j y := by
    have hs : closure (S : Set F) ≤ (centralizer {j t}).comap j := by
      apply (closure_le _).mpr
      intro s hs
      apply mem_centralizer_singleton_iff.mpr
      rw [← commutatorElement_eq_one_iff_mul_comm, ← map_commutatorElement]
      exact kill _ (Finset.mem_union_right _ (Finset.mem_insert_of_mem
        (Finset.mem_image_of_mem _ hs)))
    exact mem_centralizer_singleton_iff.mp (hs (hS.symm ▸ mem_top y))
  have hs2 : j t * j t = 1 := by simpa [pow_two] using hsquare
  let T : Subgroup F :=
    { carrier := {x | j x = 1 ∨ j x = j t}
      one_mem' := Or.inl (map_one j)
      mul_mem' := by
        intro x y hx hy
        change j (x*y) = 1 ∨ j (x*y) = j t
        rcases hx with hx | hx <;> rcases hy with hy | hy <;> simp [map_mul, hx, hy, hs2]
      inv_mem' := by
        intro x hx
        change j x⁻¹ = 1 ∨ j x⁻¹ = j t
        rcases hx with hx | hx
        · simp [hx]
        · exact Or.inr (by rw [map_inv, hx]; exact inv_eq_of_mul_eq_one_right hs2) }
  have : T.Normal := ⟨by
    intro x hx g
    change j (g*x*g⁻¹) = 1 ∨ j (g*x*g⁻¹) = j t
    rcases hx with hx | hx
    · simp [hx]
    · right
      rw [map_mul, map_mul, map_inv, hx, commute_all g, mul_assoc, mul_inv_cancel, mul_one]⟩
  have hRT : normalClosure (R : Set F) ≤ T := by
    apply normalClosure_le_normal
    intro r hr
    have hw := kill _ (Finset.mem_union_left _ (Finset.mem_image_of_mem
      (fun r => if r ∈ D then r * t⁻¹ else r) hr))
    by_cases hd : r ∈ D
    · exact Or.inr (mul_inv_eq_one.mp (by simpa [hd] using hw))
    · exact Or.inl (by simpa [hd] using hw)
  refine le_antisymm hK ?_
  intro x hx
  rcases hRT (hR hx) with h | h
  · exact (QuotientGroup.eq_one_iff _).mp h
  · exact (ht ((congrArg (QuotientGroup.lift K f hK) h).symm.trans hx)).elim

/-- Every nontrivial finite 2-group contains a central subgroup of order two. -/
lemma central_pair {G : Type} [Group G] [Finite G] (m : ℕ)
    (hG : Nat.card G = 2^(m+1)) :
    ∃ Z : Subgroup G, Z.Normal ∧ Z ≤ center G ∧ Nat.card Z = 2 := by
  obtain ⟨k,hk,hZ⟩ := IsPGroup.card_center_eq_prime_pow hG (by omega)
  obtain ⟨P,hP⟩ := Sylow.exists_subgroup_card_pow_prime (G := center G) 2
    (n := 1) (by rw [hZ]; exact pow_dvd_pow _ hk)
  let Z := P.map (center G).subtype
  have hle : Z ≤ center G := by rintro _ ⟨a,_,rfl⟩; exact a.property
  refine ⟨Z, ⟨?_⟩, hle, ?_⟩
  · intro x hx y
    rwa [Subgroup.mem_center_iff.mp (hle hx) y, mul_assoc, mul_inv_cancel, mul_one]
  · exact (Nat.card_congr (P.equivMapOfInjective _ Subtype.val_injective).toEquiv).symm.trans
      (by simpa using hP)

/-- Enumerate kernels of marked quotients, keeping a bound on the length of every
relation list to control branching in the next central lift. -/
lemma presentations {F : Type} [Group F] (S : Finset F) (hS : closure (S : Set F) = ⊤)
    (m : ℕ) : ∃ A : Finset (Finset F),
    A.card ≤ 2^(∑ i ∈ Finset.range m, (S.card+1)*(i+1)) ∧
    (∀ R ∈ A, R.card ≤ (S.card+1)*(m+1)) ∧
    ∀ (G : Type) [Group G] [Finite G] (f : F →* G), Function.Surjective f →
      Nat.card G = 2^m → ∃ R ∈ A, normalClosure (R : Set F) = f.ker := by
  classical
  induction m with
  | zero =>
    refine ⟨{S}, by simp, by simp, ?_⟩
    intro G _ _ f hf hg
    have : Subsingleton G := Nat.card_eq_one_iff_unique.mp (by simpa using hg) |>.1
    refine ⟨S, by simp, top_unique ?_ |>.trans (top_unique (a := f.ker) ?_).symm⟩
    · rw [← hS]
      exact closure_le_normalClosure
    · intro x _
      exact Subsingleton.elim _ _
  | succ m ih =>
    obtain ⟨A,hA,hsize,hcover⟩ := ih
    let pivot (D : Finset F) := if h : D.Nonempty then h.choose else 1
    let extend (R D : Finset F) :=
      (R.image fun r => if r ∈ D then r * (pivot D)⁻¹ else r) ∪
        insert ((pivot D)^2) (S.image fun s => ⁅s,pivot D⁆)
    let children (R : Finset F) := R.powerset.image (extend R)
    refine ⟨A.biUnion children, ?_, ?_, ?_⟩
    · calc
        _ ≤ ∑ R ∈ A, (children R).card := Finset.card_biUnion_le
        _ ≤ ∑ _R ∈ A, 2^((S.card+1)*(m+1)) := by
          apply Finset.sum_le_sum
          intro R hr
          exact Finset.card_image_le.trans ((Finset.card_powerset R) ▸
            Nat.pow_le_pow_right (by decide : 0 < 2) (hsize R hr))
        _ ≤ _ := by
          simp only [Finset.sum_const, smul_eq_mul, Finset.sum_range_succ, pow_add]
          exact Nat.mul_le_mul_right _ hA
    · intro L hL
      obtain ⟨R,hr,hchild⟩ := Finset.mem_biUnion.mp hL
      obtain ⟨D,hd,rfl⟩ := Finset.mem_image.mp hchild
      have h := Finset.card_union_le (R.image fun r => if r ∈ D then r * (pivot D)⁻¹ else r)
        (insert ((pivot D)^2) (S.image fun s => ⁅s,pivot D⁆))
      have h₁ := Finset.card_image_le (s := R) (f := fun r => if r ∈ D then r * (pivot D)⁻¹ else r)
      have h₂ := Finset.card_insert_le ((pivot D)^2) (S.image fun s => ⁅s,pivot D⁆)
      have h₃ := Finset.card_image_le (s := S) (f := fun s => ⁅s,pivot D⁆)
      change (extend R D).card ≤ _
      dsimp only [extend]
      have hs := hsize R hr
      rw [Nat.mul_succ]
      omega
    · intro G _ _ f hf hg
      obtain ⟨Z,hN,hZ,hz⟩ := central_pair m hg
      let q := QuotientGroup.mk' Z
      have hg' : Nat.card (G ⧸ Z) = 2^m := by
        have h := Subgroup.card_eq_card_quotient_mul_card_subgroup Z
        rw [hz,hg,pow_succ] at h
        omega
      obtain ⟨R,hr,hR⟩ := hcover _ (q.comp f) ((QuotientGroup.mk'_surjective Z).comp hf) hg'
      let D := R.filter fun x => f x ≠ 1
      have hne : D.Nonempty := by
        by_contra h
        have hk : normalClosure (R : Set F) ≤ f.ker := by
          apply normalClosure_le_normal
          intro r hr
          by_contra hn
          exact h ⟨r, Finset.mem_filter.mpr ⟨hr, hn⟩⟩
        obtain ⟨z,hz',_⟩ := (Nat.card_eq_two_iff' (1 : Z)).mp hz
        obtain ⟨x,hx⟩ := hf (z : G)
        apply hz'
        apply Subtype.ext
        have hx' : x ∈ (q.comp f).ker := (QuotientGroup.eq_one_iff _).mpr (hx ▸ z.property)
        simpa [← hx] using hk (hR.symm ▸ hx')
      have ht := (Finset.mem_filter.mp (show pivot D ∈ D by simpa [pivot,hne] using hne.choose_spec))
      have memZ (r) (hr : r ∈ R) : f r ∈ Z := by
        apply (QuotientGroup.eq_one_iff _).mp
        change r ∈ (q.comp f).ker
        rw [← hR]
        exact subset_normalClosure hr
      let u : Z := ⟨f (pivot D), memZ _ ht.1⟩
      have hu : u ≠ 1 := fun e => ht.2 (congrArg Subtype.val e)
      have hsq : u^2 = 1 := by rw [← hz, pow_card_eq_one']
      refine ⟨extend R D, Finset.mem_biUnion.mpr ⟨R,hr,Finset.mem_image.mpr
        ⟨D,Finset.mem_powerset.mpr (Finset.filter_subset ..), rfl⟩⟩, ?_⟩
      apply lift_kernel f S R D hS (pivot D) ht.2 (congrArg Subtype.val hsq) (hZ u.property)
      · rw [hR]
        intro x hx
        change q (f x) = 1
        rw [show f x = 1 from hx, map_one]
      · intro r hrr
        by_cases he : f r = 1
        · simp [D,he]
        · have hv : (⟨f r,memZ r hrr⟩ : Z) ≠ 1 := fun e => he (congrArg Subtype.val e)
          have hsame := ((Nat.card_eq_two_iff' (1 : Z)).mp hz).unique hv hu
          simpa [D,hrr,he] using congrArg Subtype.val hsame

lemma free_surjection (G : Type) [Group G] [Finite G] (d : ℕ) (hd : Group.rank G ≤ d) :
    ∃ f : FreeGroup (Fin d) →* G, Function.Surjective f := by
  classical
  obtain ⟨T,hc,hgen⟩ := Group.rank_spec G
  let e := Fintype.equivFinOfCardEq (show Fintype.card T = Group.rank G by simpa using hc)
  let gens (i : Fin d) : G := if h : i.val < Group.rank G then (e.symm ⟨i.val,h⟩).val else 1
  refine ⟨FreeGroup.lift gens, FreeGroup.lift_surjective_iff_closure_range_eq_top.mpr ?_⟩
  apply top_unique
  rw [← hgen]
  apply Subgroup.closure_mono
  intro x hx
  let i := e ⟨x,hx⟩
  refine ⟨⟨i.val,i.isLt.trans_le hd⟩, ?_⟩
  simp [gens,i.isLt,i]

/-- Forgetting the marking only decreases the number of isomorphism classes. -/
lemma few_generators_count (m d : ℕ) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = 2^m ∧ Group.rank G ≤ d}).ncard ≤
      2^(∑ i ∈ Finset.range m, (d+1)*(i+1)) := by
  classical
  let F := FreeGroup (Fin d)
  let S : Finset F := Finset.univ.image FreeGroup.of
  have hs : (S : Set F) = Set.range FreeGroup.of := by simp [S]
  have hgen : closure (S : Set F) = ⊤ := hs ▸ FreeGroup.closure_range_of _
  obtain ⟨A,hA,_,hcover⟩ := presentations S hgen m
  let q := Quotient.mk (isIsomorphicSetoid FiniteGrp.{0})
  let model (R : Finset F) : Quotient (isIsomorphicSetoid FiniteGrp.{0}) :=
    let K := normalClosure (R : Set F)
    if h : Finite (F ⧸ K) then q (FiniteGrp.of (F ⧸ K)) else q (FiniteGrp.of PUnit)
  have sub : q '' {G : FiniteGrp.{0} | Nat.card G = 2^m ∧ Group.rank G ≤ d} ⊆ model '' (A : Set _) := by
    rintro _ ⟨G,⟨hG,hd⟩,rfl⟩
    obtain ⟨f,hf⟩ := free_surjection G d hd
    obtain ⟨R,hr,hR⟩ := hcover G f hf hG
    let e : (F ⧸ normalClosure (R : Set F)) ≃* G :=
      (QuotientGroup.quotientMulEquivOfEq hR).trans (QuotientGroup.quotientKerEquivOfSurjective f hf)
    have hfin : Finite (F ⧸ normalClosure (R : Set F)) := Finite.of_equiv G e.symm.toEquiv
    refine ⟨R,hr,?_⟩
    simp only [model, dif_pos hfin]
    exact Quotient.sound ⟨InducedCategory.isoMk (F := FiniteGrp.toGrp)
      (MulEquiv.toGrpIso (X := (FiniteGrp.of (F ⧸ normalClosure (R : Set F))).toGrp)
        (Y := G.toGrp) e)⟩
  have hs' : S.card ≤ d := Finset.card_image_le.trans_eq (by simp)
  calc
    _ ≤ _ := Set.ncard_le_ncard sub (A.finite_toSet.image _)
    _ ≤ A.card := (Set.ncard_image_le A.finite_toSet).trans_eq (Set.ncard_coe_finset _)
    _ ≤ _ := hA.trans (Nat.pow_le_pow_right (by decide) (Finset.sum_le_sum fun i _ =>
        Nat.mul_le_mul_right (i+1) (by omega)))

lemma twice_cost (m d : ℕ) :
    2*(∑ i ∈ Finset.range m, (d+1)*(i+1)) = (d+1)*m*(m+1) := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, mul_add, ih]; ring

lemma low_rank_bound (m : ℕ) (hm : 512 ≤ m) :
    (24 * (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = 2^m ∧ Group.rank G ≤ m/7}).ncard)^27 *
        2^(9*m^2) ≤ 2^(2*m^3) := by
  let b := ∑ i ∈ Finset.range m, (m/7+1)*(i+1)
  have cost : 2*b = (m/7+1)*m*(m+1) := twice_cost m (m/7)
  have hlin : 7*(m/7+1) ≤ m+7 := by omega
  have hmul := Nat.mul_le_mul_right (m*(m+1)) hlin
  have hpoly : 27*(m+7)*m*(m+1) + 126*m^2 + 1890 ≤ 28*m^3 := by
    obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hm
    nlinarith [Nat.zero_le (k^3), Nat.zero_le (k^2)]
  have powers : (5+b)*27+9*m^2 ≤ 2*m^3 := by nlinarith only [cost, hmul, hpoly]
  have hval := Nat.mul_le_mul (by decide : 24 ≤ 2^5) (few_generators_count m (m/7))
  change _ ≤ 2^5 * 2^b at hval
  rw [← pow_add] at hval
  calc
    _ ≤ (2^(5+b))^27 * 2^(9*m^2) :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hval _)
    _ = 2^((5+b)*27+9*m^2) := by rw [← pow_mul, ← pow_add]
    _ ≤ _ := Nat.pow_le_pow_right (by decide) powers

theorem main : H1 → H2 → OMA.R_Erdos1160_erdos_1160_variants_sum_R1_H2_R1_H2_R1_H2_R1.H3 := by
  intro h₁ h₂
  filter_upwards [h₁,h₂,eventually_ge_atTop 512] with m h₁ h₂ hm
  let q := Quotient.mk (isIsomorphicSetoid FiniteGrp.{0})
  let D (G : FiniteGrp.{0}) := Nat.card G = 2^m
  let C (G : FiniteGrp.{0}) := (⊤ : Subgroup G).lowerCentralSeries 2 ≤ center G
  let X := q '' {G : FiniteGrp.{0} | D G ∧ ¬commutator G ≤ center G ∧
    2 < Nat.card ((⊤ : Subgroup G).lowerCentralSeries 2)}
  let A := q '' {G : FiniteGrp.{0} | D G ∧ Group.rank G ≤ m/7}
  let B := q '' {G : FiniteGrp.{0} | D G ∧ ¬commutator G ≤ center G ∧
    2 < Nat.card ((⊤ : Subgroup G).lowerCentralSeries 2) ∧ m/7 < Group.rank G ∧ C G}
  let E := q '' {G : FiniteGrp.{0} | D G ∧ ¬commutator G ≤ center G ∧
    2 < Nat.card ((⊤ : Subgroup G).lowerCentralSeries 2) ∧ m/7 < Group.rank G ∧ ¬C G}
  have sub : X ⊆ (A ∪ B) ∪ E := by
    rintro _ ⟨G,⟨hg,hn,hk⟩,rfl⟩
    rcases le_or_gt (Group.rank G) (m/7) with hr | hr
    · exact Or.inl (Or.inl ⟨G,⟨hg,hr⟩,rfl⟩)
    · by_cases hc : C G
      · exact Or.inl (Or.inr ⟨G,⟨hg,hn,hk,hr,hc⟩,rfl⟩)
      · exact Or.inr ⟨G,⟨hg,hn,hk,hr,hc⟩,rfl⟩
  have hf : ((A ∪ B) ∪ E).Finite := by
    apply (OMA.R_Erdos1160_erdos_1160_variants_sum_R1_H2_R1_H2_R1_H2_R1.finite_order_classes (2^m)).subset
    rintro _ ((⟨G,h,rfl⟩ | ⟨G,h,rfl⟩) | ⟨G,h,rfl⟩) <;> exact ⟨G,h.1,rfl⟩
  have hn := (Set.ncard_le_ncard sub hf).trans (Set.ncard_union_le (A ∪ B) E)
  have hab := Set.ncard_union_le A B
  have hmax : 8*X.ncard ≤ 24*max A.ncard (max B.ncard E.ncard) := by omega
  change (8*X.ncard)^27 * 2^(9*m^2) ≤ _
  apply (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hmax 27)).trans
  rcases max_cases A.ncard (max B.ncard E.ncard) with ha | hbe
  · rw [ha.1]
    exact low_rank_bound m hm
  · rw [hbe.1]
    rcases max_cases B.ncard E.ncard with hb | he
    · rw [hb.1]; exact h₁
    · rw [he.1]; exact h₂

end OMA.R_Erdos1160_erdos_1160_variants_sum_R1_H2_R1_H2_R1_H2_R1_H3_R2
