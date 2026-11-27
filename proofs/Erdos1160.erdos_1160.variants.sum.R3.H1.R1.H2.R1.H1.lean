import OMAReductions.R_Erdos1160_erdos_1160_variants_sum_R3_H1_R1_H2_R1
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Category.Grp.FiniteGrp
import Mathlib.CategoryTheory.IsomorphismClasses
import Mathlib.Data.Set.Card

/-!
# Contagem de grupos de ordem potência de primo por extensões centrais

Ao retirar um subgrupo central de ordem p, cada relação da apresentação do
quociente recebe uma correção em Fin p. O novo gerador central acrescenta
uma relação de potência e uma relação de comutação por gerador anterior.
-/


open CategoryTheory

abbrev Erdos1160.FixedCofactor.OrderClasses (n : ℕ) := ↥(Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
  {G : FiniteGrp.{0} | Nat.card G = n})

namespace Erdos1160.FixedCofactor
noncomputable def orderRepresentative {n : ℕ} (i : OrderClasses n) : FiniteGrp.{0} := i.property.choose

theorem orderRepresentative_spec {n : ℕ} (i : OrderClasses n) :
    Nat.card (orderRepresentative i) = n ∧
      Quotient.mk (CategoryTheory.isIsomorphicSetoid FiniteGrp.{0}) (orderRepresentative i) = i.val :=
  i.property.choose_spec

end Erdos1160.FixedCofactor

namespace Erdos1160.PrimePower

private abbrev letter {X : Type} (x : X) := FreeGroup.of x

private def nextWord {X R : Type} (p : ℕ) (r : R → FreeGroup X) (v : R → Fin p) :
    Unit ⊕ (X ⊕ R) → FreeGroup (Option X)
  | .inl _ => letter none ^ p
  | .inr (.inl x) => (letter none * letter (some x)) * (letter (some x) * letter none)⁻¹
  | .inr (.inr i) => FreeGroup.map some (r i) * (letter none ^ (v i).val)⁻¹

private abbrev Model {X R : Type} (r : R → FreeGroup X) := PresentedGroup (Set.range r)

private def newLetter {X R : Type} {p : ℕ} (r : R → FreeGroup X) (v : R → Fin p) :
    Model (nextWord p r v) := PresentedGroup.of none

private theorem new_properties {X R : Type} {p : ℕ} (r : R → FreeGroup X) (v : R → Fin p) :
    newLetter r v ^ p = 1 ∧ newLetter r v ∈ Subgroup.center (Model (nextWord p r v)) ∧
    ∀ i, PresentedGroup.mk (Set.range (nextWord p r v)) (FreeGroup.map some (r i)) =
      newLetter r v ^ (v i).val := by
  let w := nextWord p r v
  let z := newLetter r v
  have hz : z^p = 1 := by
    have h := PresentedGroup.one_of_mem (Set.mem_range_self (Sum.inl ()) :
      w (Sum.inl ()) ∈ Set.range w)
    simpa only [w, nextWord, map_pow, z, newLetter, PresentedGroup.of, letter] using h
  have comm (x : X) : z * PresentedGroup.of (some x) = PresentedGroup.of (some x) * z := by
    have h := PresentedGroup.mk_eq_mk_of_mul_inv_mem (Set.mem_range_self (Sum.inr (Sum.inl x)) :
      w (Sum.inr (Sum.inl x)) ∈ Set.range w)
    simpa only [map_mul, z, newLetter, PresentedGroup.of, letter, w] using h
  have cen : z ∈ Subgroup.center (Model w) := by
    apply Subgroup.mem_center_iff.mpr
    intro y
    have h := PresentedGroup.generated_by (Set.range w) (Subgroup.centralizer {z}) (fun j => by
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      cases j with
      | none => rfl
      | some x => exact (comm x).symm) y
    exact Subgroup.mem_centralizer_singleton_iff.mp h
  refine ⟨hz,cen,fun i => ?_⟩
  have h := PresentedGroup.mk_eq_mk_of_mul_inv_mem (Set.mem_range_self (Sum.inr (Sum.inr i)) :
    w (Sum.inr (Sum.inr i)) ∈ Set.range w)
  simpa only [map_pow, w, newLetter, PresentedGroup.of, letter] using h

private theorem lift_old {X G : Type} [Group G] (f : Option X → G) :
    (FreeGroup.lift f).comp (FreeGroup.map some) = FreeGroup.lift (fun x => f (some x)) :=
  FreeGroup.ext_hom _ _ fun x => by simp

private theorem centralNormal {G : Type*} [Group G] {K : Subgroup G} (h : K ≤ Subgroup.center G) :
    K.Normal where
  conj_mem x hx g := by
    rw [Subgroup.mem_center_iff.mp (h hx) g, mul_assoc, mul_inv_cancel, mul_one]
    exact hx

private theorem next_card {X R : Type} {p : ℕ} (hp : 0 < p) (r : R → FreeGroup X)
    (v : R → Fin p) [Finite (Model r)] :
    Finite (Model (nextWord p r v)) ∧ Nat.card (Model (nextWord p r v)) ≤ p * Nat.card (Model r) := by
  let w := nextWord p r v
  let E := Model w
  let z := newLetter r v
  obtain ⟨hz,hcen,hword⟩ := new_properties r v
  let K := Subgroup.zpowers z
  have hKC : K ≤ Subgroup.center E := (Subgroup.zpowers_le).mpr hcen
  let : K.Normal := centralNormal hKC
  let π := QuotientGroup.mk' K
  have hzq : π z = 1 := (QuotientGroup.eq_one_iff z).mpr (Subgroup.mem_zpowers z)
  let f (x : X) := π (PresentedGroup.of (some x))
  have comp : ((π.comp (PresentedGroup.mk (Set.range w))).comp (FreeGroup.map some)) =
      FreeGroup.lift f := FreeGroup.ext_hom _ _ fun x => by rfl
  have rel (u : FreeGroup X) (hu : u ∈ Set.range r) : FreeGroup.lift f u = 1 := by
    obtain ⟨i,rfl⟩ := hu
    rw [← comp]
    change π (PresentedGroup.mk _ (FreeGroup.map some (r i))) = 1
    rw [hword i, map_pow, hzq, one_pow]
  let old := PresentedGroup.toGroup rel
  have onto : Function.Surjective old := by
    intro y
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective K y
    have h := PresentedGroup.generated_by (Set.range w) (old.range.comap π) (fun j => by
      cases j with
      | none => change π z ∈ old.range; rw [hzq]; exact old.range.one_mem
      | some j => exact ⟨PresentedGroup.of j, PresentedGroup.toGroup.of rel⟩) x
    exact h
  let : Finite (E ⧸ K) := Finite.of_surjective old onto
  have hk : Nat.card K = orderOf z := Nat.card_zpowers z
  have hdiv := orderOf_dvd_of_pow_eq_one hz
  have hcard : Nat.card E = Nat.card K * Nat.card (E ⧸ K) := by
    rw [← K.index_eq_card, K.card_mul_index]
  have hnonzero : orderOf z ≠ 0 := fun h => by rw [h, zero_dvd_iff] at hdiv; omega
  refine ⟨Nat.finite_of_card_ne_zero (by rw [hcard,hk]; exact Nat.mul_ne_zero hnonzero Nat.card_pos.ne'), ?_⟩
  rw [hcard,hk]
  exact Nat.mul_le_mul (Nat.le_of_dvd hp hdiv) (Nat.card_le_card_of_surjective old onto)

private theorem lift_code {X R G : Type} [Group G] [Finite G] {p : ℕ}
    (r : R → FreeGroup X) (z : G) (hz : orderOf z = p) (hc : z ∈ Subgroup.center G)
    [(Subgroup.zpowers z).Normal] (e : Model r ≃* (G ⧸ Subgroup.zpowers z)) :
    ∃ v : R → Fin p, ∃ F : Model (nextWord p r v) →* G, Function.Surjective F := by
  classical
  let K := Subgroup.zpowers z
  let π := QuotientGroup.mk' K
  have lifts (x : X) := QuotientGroup.mk'_surjective K (e (PresentedGroup.of x))
  choose l hl using lifts
  let old := FreeGroup.lift l
  have proj : π.comp old = e.toMonoidHom.comp (PresentedGroup.mk (Set.range r)) := by
    apply FreeGroup.ext_hom
    intro x
    simpa only [MonoidHom.comp_apply, old, FreeGroup.lift_apply_of, MulEquiv.coe_toMonoidHom, π, PresentedGroup.of] using hl x
  have exp (i : R) : ∃ v : Fin p, old (r i) = z^v.val := by
    have hzero : π (old (r i)) = 1 := by
      change π.comp old (r i) = 1
      rw [proj,MonoidHom.comp_apply,PresentedGroup.one_of_mem (Set.mem_range_self i),map_one]
    have hmem := (QuotientGroup.eq_one_iff _).mp hzero
    obtain ⟨j,hj,he⟩ := Finset.mem_image.mp (mem_zpowers_iff_mem_range_orderOf.mp hmem)
    exact ⟨⟨j, hz ▸ Finset.mem_range.mp hj⟩, he.symm⟩
  choose v hv using exp
  let f : Option X → G := fun o => o.elim z l
  have hold : (FreeGroup.lift f).comp (FreeGroup.map some) = old := lift_old f
  let w := nextWord p r v
  have rel (u) (hu : u ∈ Set.range w) : FreeGroup.lift f u = 1 := by
    obtain ⟨j,rfl⟩ := hu
    rcases j with j | (x | i)
    · change FreeGroup.lift f (FreeGroup.of none ^ p) = 1
      rw [map_pow, FreeGroup.lift_apply_of]
      exact hz ▸ pow_orderOf_eq_one z
    · change FreeGroup.lift f ((letter none * letter (some x)) * (letter (some x) * letter none)⁻¹) = 1
      simp only [map_mul,map_inv,letter,FreeGroup.lift_apply_of,mul_inv_eq_one]
      exact (Subgroup.mem_center_iff.mp hc (l x)).symm
    · change FreeGroup.lift f (FreeGroup.map some (r i) * (letter none ^ (v i).val)⁻¹) = 1
      rw [map_mul, map_inv, map_pow, mul_inv_eq_one, letter, FreeGroup.lift_apply_of]
      change (FreeGroup.lift f).comp (FreeGroup.map some) (r i) = z^(v i).val
      rw [hold, hv]
  let F := PresentedGroup.toGroup rel
  have fgen (j : Option X) : F (PresentedGroup.of j) = f j := PresentedGroup.toGroup.of rel
  have hzF : z ∈ F.range := ⟨PresentedGroup.of none, fgen none⟩
  have hKF : K ≤ F.range := Subgroup.zpowers_le.mpr hzF
  have allOld (b : Model r) : e b ∈ (π.comp F).range := by
    apply PresentedGroup.generated_by (Set.range r) ((π.comp F).range.comap e.toMonoidHom) _ b
    intro x
    refine ⟨PresentedGroup.of (some x), ?_⟩
    rw [MonoidHom.comp_apply, fgen]
    exact hl x
  refine ⟨v,F,fun g => ?_⟩
  have h := allOld (e.symm (π g))
  rw [e.apply_symm_apply] at h
  obtain ⟨w,hw⟩ := h
  have hv : g*(F w)⁻¹ ∈ K := (QuotientGroup.eq_one_iff _).mp (by
    change π (g*(F w)⁻¹) = 1
    rw [map_mul,map_inv,← MonoidHom.comp_apply, hw, mul_inv_cancel])
  have hm := F.range.mul_mem (hKF hv) (show F w ∈ F.range from ⟨w,rfl⟩)
  change g ∈ F.range
  simpa using hm

private def Letters : ℕ → Type
  | 0 => Empty
  | a+1 => Option (Letters a)

private def Relations : ℕ → Type
  | 0 => Empty
  | a+1 => Unit ⊕ (Letters a ⊕ Relations a)

private def Code (p : ℕ) : ℕ → Type
  | 0 => Unit
  | a+1 => Code p a × (Relations a → Fin p)

private def words (p : ℕ) : (a : ℕ) → Code p a → Relations a → FreeGroup (Letters a)
  | 0, _, x => Empty.elim x
  | a+1, w, i => nextWord p (words p a w.1) w.2 i

private abbrev family {p a : ℕ} (c : Code p a) := Model (words p a c)

private theorem baseSubsingleton (p : ℕ) : Subsingleton (family (p := p) (a := 0) ()) := by
  let one (x : family (p := p) (a := 0) ()) : x = 1 :=
    PresentedGroup.generated_by _ ⊥ (fun i => Empty.elim i) x
  exact ⟨fun x y => (one x).trans (one y).symm⟩

private theorem modelBound (p : ℕ) (hp : 0 < p) (a : ℕ) (w : Code p a) :
    Finite (family w) ∧ Nat.card (family w) ≤ p^a := by
  induction a with
  | zero =>
    cases w
    let : Subsingleton (family (p := p) (a := 0) ()) := baseSubsingleton p
    exact ⟨inferInstance,by simp⟩
  | succ a ih =>
    obtain ⟨hfin,hcard⟩ := ih w.1
    let : Finite (family w.1) := hfin
    obtain ⟨hfinite,hb⟩ := next_card hp (words p a w.1) w.2
    exact ⟨hfinite,hb.trans (by rw [pow_succ, Nat.mul_comm (p^a)]; exact Nat.mul_le_mul_left p hcard)⟩

private theorem cover (p : ℕ) [hp : Fact p.Prime] (a : ℕ) (G : Type) [Group G] [Finite G]
    (hG : Nat.card G = p^a) : ∃ c : Code p a, Nonempty (family c ≃* G) := by
  classical
  induction a generalizing G with
  | zero =>
    let : Subsingleton G := (Nat.card_eq_one_iff_unique.mp (by simpa using hG)).1
    let : Subsingleton (family (p := p) (a := 0) ()) := baseSubsingleton p
    let f : family (p := p) (a := 0) () →* G := 1
    exact ⟨(),⟨MulEquiv.ofBijective f ⟨fun _ _ _ => Subsingleton.elim ..,
      fun y => ⟨1,Subsingleton.elim ..⟩⟩⟩⟩
  | succ a ih =>
    obtain ⟨b,hb,hbcard⟩ := IsPGroup.card_center_eq_prime_pow hG (Nat.succ_pos _)
    have hdiv : p ∣ Nat.card (Subgroup.center G) := by rw [hbcard]; exact dvd_pow_self p hb.ne'
    obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' p hdiv
    have ho : orderOf (z : G) = p :=
      (orderOf_injective (Subgroup.center G).subtype Subtype.val_injective z).trans hz
    let K := Subgroup.zpowers (z : G)
    let : K.Normal := centralNormal ((Subgroup.zpowers_le).mpr z.property)
    have hK : Nat.card K = p := (Nat.card_zpowers _).trans ho
    have hQ : Nat.card (G ⧸ K) = p^a := by
      apply Nat.eq_of_mul_eq_mul_right hp.out.pos
      rw [← K.index_eq_card, ← hK, K.index_mul_card, hG, hK,pow_succ]
    obtain ⟨c,⟨e⟩⟩ := ih (G ⧸ K) hQ
    obtain ⟨v,F,hF⟩ := lift_code (words p a c) (z : G) ho z.property e
    let c' : Code p (a+1) := (c,v)
    obtain ⟨hf,hc⟩ := modelBound p hp.out.pos (a+1) c'
    let : Finite (family c') := hf
    have hbnd : Nat.card (family c') ≤ Nat.card G := hG ▸ hc
    let : Finite (Model (nextWord p (words p a c) v)) := hf
    exact ⟨c',⟨MulEquiv.ofBijective F (hF.bijective_of_nat_card_le hbnd)⟩⟩

private instance lettersFintype : (a : ℕ) → Fintype (Letters a)
  | 0 => inferInstanceAs (Fintype Empty)
  | a+1 => letI := lettersFintype a; inferInstanceAs (Fintype (Option (Letters a)))

private instance relationsFintype : (a : ℕ) → Fintype (Relations a)
  | 0 => inferInstanceAs (Fintype Empty)
  | a+1 => letI := relationsFintype a; inferInstanceAs (Fintype (Unit ⊕ (Letters a ⊕ Relations a)))

private noncomputable instance codesFintype (p : ℕ) : (a : ℕ) → Fintype (Code p a)
  | 0 => inferInstanceAs (Fintype Unit)
  | a+1 => by
    classical
    letI := codesFintype p a
    exact inferInstanceAs (Fintype (Code p a × (Relations a → Fin p)))

private theorem letterCount (a : ℕ) : Fintype.card (Letters a) = a := by
  induction a with
  | zero => rfl
  | succ a ih =>
    change Fintype.card (Option (Letters a)) = _
    rw [Fintype.card_option, ih]

private theorem relCount (a : ℕ) : 2 * Fintype.card (Relations a) = a*(a+1) := by
  induction a with
  | zero => rfl
  | succ a ih =>
    change 2 * Fintype.card (Unit ⊕ (Letters a ⊕ Relations a)) = _
    rw [Fintype.card_sum,Fintype.card_sum,letterCount,Fintype.card_unit]
    nlinarith only [ih]

private def exponent : ℕ → ℕ
  | 0 => 0
  | a+1 => exponent a + Fintype.card (Relations a)

private theorem exponent_identity (a : ℕ) : 6*exponent a+a = a^3 := by
  induction a with
  | zero => rfl
  | succ a ih => dsimp only [exponent]; nlinarith only [ih,relCount a]

private theorem codeCount (p a : ℕ) : Fintype.card (Code p a) = p^exponent a := by
  classical
  induction a with
  | zero => rfl
  | succ a ih =>
    change Fintype.card (Code p a × (Relations a → Fin p)) = _
    rw [Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,ih,exponent,pow_add]

/-- Cota uniforme para o número de grupos de ordem p^a, válida também para a = 0. -/
theorem group_count_prime_power (p a : ℕ) (hp : p.Prime) :
    (Nat.card (FixedCofactor.OrderClasses (p^a)))^6 * p^a ≤ p^(a^3) := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let I := FixedCofactor.OrderClasses (p^a)
  have h (i : I) := cover p a (FixedCofactor.orderRepresentative i) (FixedCofactor.orderRepresentative_spec i).1
  choose code iso using h
  have hinj : Function.Injective code := by
    intro i j hij
    obtain ⟨e⟩ := iso i
    obtain ⟨f⟩ := iso j
    let t : family (code i) ≃* family (code j) := hij ▸ MulEquiv.refl _
    let eqv := (e.symm.trans t).trans f
    apply Subtype.ext
    rw [← (FixedCofactor.orderRepresentative_spec i).2, ← (FixedCofactor.orderRepresentative_spec j).2]
    exact Quotient.sound ⟨CategoryTheory.InducedCategory.isoMk (F := FiniteGrp.toGrp)
      (MulEquiv.toGrpIso (X := (FixedCofactor.orderRepresentative i).toGrp)
        (Y := (FixedCofactor.orderRepresentative j).toGrp) eqv)⟩
  have hc := Nat.card_le_card_of_injective code hinj
  rw [Nat.card_eq_fintype_card (α := Code p a),codeCount] at hc
  calc
    _ ≤ (p^exponent a)^6*p^a := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hc _)
    _ = _ := by rw [← pow_mul, ← pow_add, Nat.mul_comm (exponent a), exponent_identity]


end Erdos1160.PrimePower

theorem OMA.solution : OMA.R_Erdos1160_erdos_1160_variants_sum_R3_H1_R1_H2_R1.H1 := by
  intro p a hp
  exact Erdos1160.PrimePower.group_count_prime_power p a hp