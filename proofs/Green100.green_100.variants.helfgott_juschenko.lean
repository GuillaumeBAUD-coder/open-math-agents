import FormalConjectures.GreensOpenProblems.«100»
import Mathlib.GroupTheory.HNNExtension
import Mathlib.GroupTheory.PushoutI

/-!
# Helfgott–Juschenko's consequence of Higman soficity

The proof uses the finite conjugacy argument in Theorem 2 of
Helfgott and Juschenko, [Soficity, short cycles and the Higman group](https://arxiv.org/abs/1512.02135).

A chain of two Baumslag–Solitar groups is an amalgam over its middle cyclic
subgroup. Its outer cyclic subgroups freely generate their free product,
which can then be amalgamated with a second copy of the chain.
-/

open Monoid

namespace HigmanAdjacent

section WordMap

variable {ι H : Type*} [Group H]
variable {A B : ι → Type*} [∀ i, Group (A i)] [∀ i, Group (B i)]
variable (φ : ∀ i, H →* B i) (f : ∀ i, A i →* B i)

private def letter (l : Σ i, A i) : Σ i, B i :=
  ⟨l.1, f l.1 l.2⟩

private def wordMap (hf : ∀ i, Function.Injective (f i)) (w : CoprodI.Word A) :
    CoprodI.Word B where
  toList := w.toList.map (letter f)
  ne_one := by
    intro l hl
    obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hl
    have hn : m.2 ≠ 1 := w.ne_one m hm
    change f m.1 m.2 ≠ 1
    intro he
    apply hn
    apply hf m.1
    rw [he, map_one]
  chain_ne := by
    rw [List.isChain_map]
    exact w.chain_ne

/-- When each nonidentity letter avoids the amalgamating subgroup, the lifted
map of the free product into the amalgam is injective. -/
theorem lift_avoiding_injective (hφ : ∀ i, Function.Injective (φ i))
    (havoid : ∀ i (x : A i), x ≠ 1 → f i x ∉ (φ i).range) :
    Function.Injective (CoprodI.lift fun i => (PushoutI.of (φ := φ) i).comp (f i)) := by
  classical
  let ψ : CoprodI A →* PushoutI φ := CoprodI.lift fun i => (PushoutI.of i).comp (f i)
  have hf (i : ι) : Function.Injective (f i) := by
    apply (injective_iff_map_eq_one _).mpr
    intro x hx
    by_contra hn
    exact havoid i x hn (hx ▸ (φ i).range.one_mem)
  apply (injective_iff_map_eq_one ψ).mpr
  intro x hx
  let w : CoprodI.Word A := CoprodI.Word.equiv x
  have hw : w.prod = x := CoprodI.Word.equiv.symm_apply_apply x
  let v := wordMap f hf w
  have hv : PushoutI.ofCoprodI v.prod = ψ w.prod := by
    simp [v, wordMap, CoprodI.Word.prod, List.map_map, letter, ψ, Function.comp_def,
      map_list_prod]
    apply congrArg List.prod
    apply List.map_congr_left
    intro l _
    exact PushoutI.ofCoprodI_of l.1 (f l.1 l.2)
  have hred : PushoutI.Reduced φ v := by
    intro l hl
    obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hl
    exact havoid m.1 m.2 (w.ne_one m hm)
  have hbase : PushoutI.ofCoprodI v.prod ∈ (PushoutI.base φ).range := by
    rw [hv, hw, hx]
    exact (PushoutI.base φ).range.one_mem
  have hv0 := hred.eq_empty_of_mem_range hφ hbase
  have hnil := congrArg CoprodI.Word.toList hv0
  have hw0 : w = CoprodI.Word.empty := by
    apply CoprodI.Word.ext
    exact List.map_eq_nil_iff.mp hnil
  rw [← hw, hw0, CoprodI.Word.prod_empty]

end WordMap

open Multiplicative

abbrev InfiniteCyclic := Multiplicative ℤ

def twice : InfiniteCyclic →* InfiniteCyclic := zpowersHom _ (ofAdd (2 : ℤ))

private theorem twice_injective : Function.Injective twice := by
  intro x y h
  have h' : (2 : ℤ) * x.toAdd = 2 * y.toAdd := by
    simpa [twice, Int.toAdd_zpow] using congrArg Multiplicative.toAdd h
  exact congrArg Multiplicative.ofAdd (show x.toAdd = y.toAdd by omega)

noncomputable def twiceEquiv : (⊤ : Subgroup InfiniteCyclic) ≃* twice.range :=
  Subgroup.topEquiv.trans (MonoidHom.ofInjective twice_injective)

abbrev BS := HNNExtension InfiniteCyclic (⊤ : Subgroup InfiniteCyclic) twice.range twiceEquiv

noncomputable def trans : BS := HNNExtension.of (ofAdd (1 : ℤ))

noncomputable def scale : BS := (HNNExtension.t : BS)⁻¹

private theorem twice_ofAdd (i : ℤ) : twice (ofAdd i) = ofAdd (2 * i) := by
  simp [twice]

theorem bs_relation : scale⁻¹ * trans * scale = trans ^ 2 := by
  let z : (⊤ : Subgroup InfiniteCyclic) := ⟨ofAdd (1 : ℤ), Subgroup.mem_top _⟩
  have h := (HNNExtension.equiv_eq_conj (φ := twiceEquiv) z).symm
  change (HNNExtension.t : BS) * trans * (HNNExtension.t : BS)⁻¹ =
    HNNExtension.of (twice (ofAdd (1 : ℤ))) at h
  unfold scale
  rw [inv_inv, h, twice_ofAdd, mul_one]
  change HNNExtension.of ((ofAdd (1 : ℤ) : InfiniteCyclic) ^ 2) = trans ^ 2
  exact map_pow _ _ _

/-- The two generators of the adjacent Baumslag–Solitar group determine a homomorphism
whenever their images satisfy the Baumslag–Solitar relation. -/
noncomputable def bsLift {G : Type*} [Group G] (a b : G)
    (h : b⁻¹ * a * b = a ^ 2) : BS →* G :=
  HNNExtension.lift (zpowersHom G a) b⁻¹ (by
    intro z
    have he : (MulAut.conj b⁻¹).toMonoidHom.comp (zpowersHom G a) =
        (zpowersHom G a).comp twice := by
      apply MonoidHom.ext_mint
      simpa [twice_ofAdd, MulAut.conj_apply] using h
    have hz := DFunLike.congr_fun he z.val
    change b⁻¹ * (zpowersHom G a) z.val * (b⁻¹)⁻¹ =
      (zpowersHom G a) (twice z.val) at hz
    change b⁻¹ * (zpowersHom G a) z.val = (zpowersHom G a) (twice z.val) * b⁻¹
    simpa [mul_assoc] using congrArg (fun x => x * b⁻¹) hz)

@[simp] theorem bsLift_trans {G : Type*} [Group G] (a b : G)
    (h : b⁻¹ * a * b = a ^ 2) : bsLift a b h trans = a := by
  simp [bsLift, trans]

@[simp] theorem bsLift_scale {G : Type*} [Group G] (a b : G)
    (h : b⁻¹ * a * b = a ^ 2) : bsLift a b h scale = b := by
  simp [bsLift, scale]

theorem bs_ext {G : Type*} [Group G] {f g : BS →* G}
    (ha : f trans = g trans) (hb : f scale = g scale) : f = g := by
  apply HNNExtension.hom_ext
  · apply MonoidHom.ext_mint
    exact ha
  · exact inv_injective (by simpa [scale] using hb)

private noncomputable def height : BS →* InfiniteCyclic :=
  HNNExtension.lift (1 : InfiniteCyclic →* InfiniteCyclic) (ofAdd (1 : ℤ)) (by simp)

@[simp] private theorem height_trans : height trans = 1 := by
  simp [height, trans]

@[simp] private theorem height_scale : height scale = ofAdd (-1 : ℤ) := by
  simp [height, scale]

private theorem transHom_injective : Function.Injective (zpowersHom BS trans) := by
  have he : zpowersHom BS trans = HNNExtension.of := by
    apply MonoidHom.ext_mint
    simp [trans]
  rw [he]
  exact HNNExtension.of_injective twiceEquiv

private theorem scaleHom_injective : Function.Injective (zpowersHom BS scale) := by
  intro x y h
  have hx := congrArg height h
  have hz : -x.toAdd = -y.toAdd := by
    simpa [zpowersHom_apply] using congrArg Multiplicative.toAdd hx
  exact congrArg (fun z : ℤ => Multiplicative.ofAdd z) (neg_injective hz)

private theorem pow_eq_one_of_trans_eq_scale {x y : InfiniteCyclic}
    (h : zpowersHom BS trans x = zpowersHom BS scale y) : x = 1 ∧ y = 1 := by
  have hh := congrArg height h
  have hy : y = 1 := by
    have hz : -y.toAdd = 0 := by
      simpa [zpowersHom_apply] using (congrArg Multiplicative.toAdd hh).symm
    exact congrArg Multiplicative.ofAdd (neg_eq_zero.mp hz)
  subst y
  exact ⟨transHom_injective (by simpa using h), rfl⟩

private noncomputable def middle : Bool → InfiniteCyclic →* BS
  | false => zpowersHom BS scale
  | true => zpowersHom BS trans

private theorem middle_injective (j : Bool) : Function.Injective (middle j) := by
  cases j
  · exact scaleHom_injective
  · exact transHom_injective

private noncomputable def outer : Bool → InfiniteCyclic →* BS
  | false => zpowersHom BS trans
  | true => zpowersHom BS scale

private theorem outer_avoids_middle (j : Bool) (x : InfiniteCyclic) (hx : x ≠ 1) :
    outer j x ∉ (middle j).range := by
  rintro ⟨y, hy⟩
  cases j
  · exact hx (pow_eq_one_of_trans_eq_scale hy.symm).1
  · exact hx (pow_eq_one_of_trans_eq_scale hy).2

private abbrev Chain := PushoutI middle

private noncomputable def chainLeft : BS →* Chain := PushoutI.of (φ := middle) false

private noncomputable def chainRight : BS →* Chain := PushoutI.of (φ := middle) true

private theorem chainLeft_injective : Function.Injective chainLeft :=
  PushoutI.of_injective middle_injective false

private noncomputable def leftEnd : Chain := chainLeft trans

private noncomputable def midpoint : Chain := chainLeft scale

private noncomputable def rightEnd : Chain := chainRight scale

private theorem midpoint_eq : midpoint = chainRight trans := by
  let z : InfiniteCyclic := ofAdd (1 : ℤ)
  simpa [midpoint, chainLeft, chainRight, middle, z] using
    (PushoutI.of_apply_eq_base middle false z).trans
      (PushoutI.of_apply_eq_base middle true z).symm

private theorem chain_first : midpoint⁻¹ * leftEnd * midpoint = leftEnd ^ 2 := by
  simpa [midpoint, leftEnd] using congrArg chainLeft bs_relation

private theorem chain_second : rightEnd⁻¹ * midpoint * rightEnd = midpoint ^ 2 := by
  simpa [midpoint_eq, rightEnd] using congrArg chainRight bs_relation

private abbrev TwoEnds := CoprodI (fun _ : Bool => InfiniteCyclic)

private noncomputable def endHom (j : Bool) : InfiniteCyclic →* Chain :=
  (PushoutI.of (φ := middle) j).comp (outer j)

private noncomputable def forward : TwoEnds →* Chain := CoprodI.lift endHom

private theorem forward_injective : Function.Injective forward :=
  lift_avoiding_injective middle outer middle_injective outer_avoids_middle

private noncomputable def turn : TwoEnds →* TwoEnds :=
  CoprodI.lift fun j => CoprodI.of (M := fun _ : Bool => InfiniteCyclic) (i := !j)

private theorem turn_twice (x : TwoEnds) : turn (turn x) = x := by
  have h : turn.comp turn = MonoidHom.id TwoEnds := by
    apply CoprodI.ext_hom
    intro j
    apply MonoidHom.ext
    intro z
    simp [turn]
  exact DFunLike.congr_fun h x

private noncomputable def glue : Bool → TwoEnds →* Chain
  | false => forward
  | true => forward.comp turn

private theorem glue_injective (j : Bool) : Function.Injective (glue j) := by
  cases j
  · exact forward_injective
  · exact forward_injective.comp (Function.LeftInverse.injective turn_twice)

private abbrev Model := PushoutI glue

private noncomputable def copy (j : Bool) : Chain →* Model := PushoutI.of (φ := glue) j

private theorem copy_injective (j : Bool) : Function.Injective (copy j) :=
  PushoutI.of_injective glue_injective j

private theorem glue_left_end : copy false leftEnd = copy true rightEnd := by
  let z : TwoEnds := CoprodI.of (i := false) (ofAdd (1 : ℤ))
  have h := (PushoutI.of_apply_eq_base glue false z).trans
    (PushoutI.of_apply_eq_base glue true z).symm
  simpa [z, glue, forward, turn, endHom, outer, leftEnd, rightEnd,
    chainLeft, chainRight, copy] using h

private theorem glue_right_end : copy false rightEnd = copy true leftEnd := by
  let z : TwoEnds := CoprodI.of (i := true) (ofAdd (1 : ℤ))
  have h := (PushoutI.of_apply_eq_base glue false z).trans
    (PushoutI.of_apply_eq_base glue true z).symm
  simpa [z, glue, forward, turn, endHom, outer, leftEnd, rightEnd,
    chainLeft, chainRight, copy] using h

private noncomputable def modelGen (i : ZMod 4) : Model :=
  if i = 0 then copy false leftEnd else
  if i = 1 then copy false midpoint else
  if i = 2 then copy false rightEnd else
  copy true midpoint

@[simp] private theorem modelGen_zero : modelGen 0 = copy false leftEnd := by
  simp [modelGen]

@[simp] private theorem modelGen_one : modelGen 1 = copy false midpoint := by
  simp [modelGen, show (1 : ZMod 4) ≠ 0 by decide]

@[simp] private theorem modelGen_two : modelGen 2 = copy false rightEnd := by
  simp [modelGen, show (2 : ZMod 4) ≠ 0 by decide, show (2 : ZMod 4) ≠ 1 by decide]

@[simp] private theorem modelGen_three : modelGen 3 = copy true midpoint := by
  simp [modelGen, show (3 : ZMod 4) ≠ 0 by decide, show (3 : ZMod 4) ≠ 1 by decide,
    show (3 : ZMod 4) ≠ 2 by decide]

private theorem model_relation (i : ZMod 4) :
    (modelGen (i + 1))⁻¹ * modelGen i * modelGen (i + 1) = modelGen i ^ 2 := by
  fin_cases i
  · change (modelGen 1)⁻¹ * modelGen 0 * modelGen 1 = modelGen 0 ^ 2
    simpa using congrArg (copy false) chain_first
  · change (modelGen 2)⁻¹ * modelGen 1 * modelGen 2 = modelGen 1 ^ 2
    simpa using congrArg (copy false) chain_second
  · change (modelGen 3)⁻¹ * modelGen 2 * modelGen 3 = modelGen 2 ^ 2
    simp only [modelGen_two, modelGen_three, glue_right_end]
    simpa using congrArg (copy true) chain_first
  · change (modelGen 0)⁻¹ * modelGen 3 * modelGen 0 = modelGen 3 ^ 2
    simp only [modelGen_zero, modelGen_three, glue_left_end]
    simpa using congrArg (copy true) chain_second

private noncomputable def toModel : Green100.HigmanGroup →* Model :=
  PresentedGroup.toGroup (f := modelGen) (by
    rintro _ ⟨i, rfl⟩
    simp only [map_mul, map_inv, map_pow, FreeGroup.lift_apply_of, model_relation,
      mul_inv_cancel])

private theorem higman_relation :
    (PresentedGroup.of (1 : ZMod 4) : Green100.HigmanGroup)⁻¹ *
      PresentedGroup.of (0 : ZMod 4) * PresentedGroup.of (1 : ZMod 4) =
      (PresentedGroup.of (0 : ZMod 4) : Green100.HigmanGroup) ^ 2 := by
  have h : (FreeGroup.of (1 : ZMod 4))⁻¹ * FreeGroup.of 0 * FreeGroup.of 1 *
      (FreeGroup.of 0 ^ 2)⁻¹ ∈
      Set.range (fun i : ZMod 4 => (FreeGroup.of (i + 1))⁻¹ * FreeGroup.of i *
        FreeGroup.of (i + 1) * (FreeGroup.of i ^ 2)⁻¹) :=
    Set.mem_range_self (0 : ZMod 4)
  simpa only [PresentedGroup.of, map_mul, map_inv, map_pow] using
    PresentedGroup.mk_eq_mk_of_mul_inv_mem h

/-- The adjacent Baumslag–Solitar group maps the translation and the stable
letter to the first two generators of the pinned Higman group. -/
noncomputable def adjacent : BS →* Green100.HigmanGroup :=
  bsLift (PresentedGroup.of (0 : ZMod 4)) (PresentedGroup.of (1 : ZMod 4)) higman_relation

@[simp] theorem adjacent_trans :
    adjacent trans = PresentedGroup.of (0 : ZMod 4) := by simp [adjacent]

@[simp] theorem adjacent_scale :
    adjacent scale = PresentedGroup.of (1 : ZMod 4) := by simp [adjacent]

/-- The adjacent Baumslag–Solitar group embeds in Higman's group. -/
theorem adjacent_injective : Function.Injective adjacent := by
  have he : toModel.comp adjacent = (copy false).comp chainLeft := by
    with_unfolding_all
      refine @bs_ext Model _ (toModel.comp adjacent) ((copy false).comp chainLeft) ?_ ?_
    · simp [toModel, leftEnd]
    · simp [toModel, midpoint]
  apply Function.Injective.of_comp (f := toModel)
  change Function.Injective (toModel.comp adjacent)
  rw [he]
  exact (copy_injective false).comp chainLeft_injective

theorem higman_nontrivial : Nontrivial Green100.HigmanGroup := by
  have h : trans ≠ 1 := by
    intro he
    have he' : (zpowersHom BS trans) (ofAdd (1 : ℤ)) = (zpowersHom BS trans) 1 := by
      simp [he]
    have hz := congrArg Multiplicative.toAdd (transHom_injective he')
    norm_num at hz
  exact ⟨⟨adjacent trans, adjacent 1, adjacent_injective.ne h⟩⟩

end HigmanAdjacent

namespace HigmanAffine

open HigmanAdjacent Multiplicative

/-- A dyadic translation, written using a common denominator (2^k). -/
noncomputable def dyadic (k z : ℤ) : BS :=
  scale ^ k * trans ^ z * scale ^ (-k)

private theorem trans_pow_conj (z : ℤ) :
    scale⁻¹ * trans ^ z * scale = trans ^ (2 * z) := by
  let f := MulAut.conj scale⁻¹
  have h := map_zpow f trans z
  change scale⁻¹ * trans ^ z * scale⁻¹⁻¹ = (scale⁻¹ * trans * scale⁻¹⁻¹) ^ z at h
  rw [inv_inv, bs_relation] at h
  rw [h, ← zpow_natCast, ← zpow_mul]
  norm_num

private theorem dyadic_succ (k z : ℤ) : dyadic (k + 1) (2 * z) = dyadic k z := by
  rw [dyadic, dyadic, ← trans_pow_conj, zpow_add, neg_add, zpow_add]
  simp only [zpow_one, zpow_neg]
  group

private theorem dyadic_widen {k l : ℤ} (h : k ≤ l) (z : ℤ) :
    ∃ w : ℤ, dyadic k z = dyadic l w := by
  obtain ⟨d, rfl⟩ := Int.le.dest h
  clear h
  induction d with
  | zero => exact ⟨z, by simp⟩
  | succ d ih =>
    obtain ⟨w, hw⟩ := ih
    refine ⟨2 * w, ?_⟩
    have he := hw.trans (dyadic_succ (k + (d : ℤ)) w).symm
    simpa [Nat.cast_succ, add_assoc] using he

private theorem dyadic_same (k x y : ℤ) :
    dyadic k x * dyadic k y = dyadic k (x + y) := by
  simp only [dyadic, zpow_add]
  group

private theorem normal_mul (k z l k' z' l' : ℤ) :
    (dyadic k z * scale ^ l) * (dyadic k' z' * scale ^ l') =
      (dyadic k z * dyadic (l + k') z') * scale ^ (l + l') := by
  simp only [dyadic, neg_add, zpow_add, zpow_neg]
  group

private theorem normal_inv (k z l : ℤ) :
    (dyadic k z * scale ^ l)⁻¹ =
      dyadic (k - l) (-z) * scale ^ (-l) := by
  simp only [dyadic, sub_eq_add_neg, neg_add, zpow_add, zpow_neg, inv_inv]
  group

/-- Each element of the adjacent Baumslag–Solitar group is a dyadic translation
followed by an integral power of the dilating generator. -/
theorem normal_form (g : BS) : ∃ k z l : ℤ, g = dyadic k z * scale ^ l := by
  induction g using HNNExtension.induction_on with
  | of c =>
    have hc : HNNExtension.of c = trans ^ c.toAdd := by
      change HNNExtension.of c = (HNNExtension.of (ofAdd (1 : ℤ)) : BS) ^ c.toAdd
      rw [← map_zpow, ← Int.ofAdd_mul, one_mul]
      rfl
    exact ⟨0, c.toAdd, 0, by simpa [dyadic] using hc⟩
  | t => exact ⟨0, 0, -1, by simp [dyadic, scale]⟩
  | mul x y hx hy =>
    obtain ⟨k, z, l, rfl⟩ := hx
    obtain ⟨k', z', l', rfl⟩ := hy
    let K := max k (l + k')
    obtain ⟨w, hw⟩ := dyadic_widen (le_max_left k (l + k')) z
    obtain ⟨w', hw'⟩ := dyadic_widen (le_max_right k (l + k')) z'
    exact ⟨K, w + w', l + l', by rw [normal_mul, hw, hw', dyadic_same]⟩
  | inv x hx =>
    obtain ⟨k, z, l, rfl⟩ := hx
    exact ⟨k - l, -z, -l, normal_inv _ _ _⟩

variable {R : Type*} [CommRing R]

/-- Multiplication by a unit as a permutation of the residue ring. -/
def dilation : Rˣ →* Equiv.Perm R where
  toFun u :=
    { toFun := fun x => (u : R) * x
      invFun := fun x => (↑u⁻¹ : R) * x
      left_inv := fun x => by
        change (↑u⁻¹ : R) * ((u : R) * x) = x
        rw [← mul_assoc, u.inv_mul, one_mul]
      right_inv := fun x => by
        change (u : R) * ((↑u⁻¹ : R) * x) = x
        rw [← mul_assoc, u.mul_inv, one_mul] }
  map_one' := by
    apply Equiv.ext
    intro x
    change (1 : R) * x = x
    exact one_mul _
  map_mul' u v := by
    apply Equiv.ext
    intro x
    change ((u * v : Rˣ) : R) * x = (u : R) * ((v : R) * x)
    exact mul_assoc _ _ _

/-- Additive translations as permutations. -/
def translation : Multiplicative R →* Equiv.Perm R where
  toFun c := Equiv.addRight c.toAdd
  map_one' := by
    apply Equiv.ext
    intro x
    exact add_zero _
  map_mul' c d := by
    apply Equiv.ext
    intro x
    change x + (c.toAdd + d.toAdd) = (x + d.toAdd) + c.toAdd
    abel

@[simp] theorem dilation_apply (u : Rˣ) (x : R) : dilation u x = (u : R) * x := rfl

@[simp] theorem translation_apply (c : Multiplicative R) (x : R) :
    translation c x = x + c.toAdd := rfl

private theorem model_rel (u : Rˣ) (hu : (u : R) = 2) :
    (dilation u⁻¹)⁻¹ * translation (ofAdd (-1 : R)) * dilation u⁻¹ =
      translation (ofAdd (-1 : R)) ^ 2 := by
  rw [← map_inv, inv_inv, ← map_pow]
  apply Equiv.ext
  intro x
  simp only [Equiv.Perm.mul_apply, dilation_apply, translation_apply, toAdd_pow,
    toAdd_ofAdd, two_nsmul]
  rw [mul_add, ← mul_assoc, u.mul_inv, one_mul, hu]
  ring

/-- The exact affine realization, translating by (-1) and scaling by (1/2). -/
noncomputable def model (u : Rˣ) (hu : (u : R) = 2) : BS →* Equiv.Perm R :=
  bsLift (translation (ofAdd (-1 : R))) (dilation u⁻¹) (model_rel u hu)

@[simp] theorem model_trans (u : Rˣ) (hu : (u : R) = 2) :
    model u hu trans = translation (ofAdd (-1 : R)) := by simp [model]

@[simp] theorem model_scale (u : Rˣ) (hu : (u : R) = 2) :
    model u hu scale = dilation u⁻¹ := by simp [model]

private theorem model_scale_zpow (u : Rˣ) (hu : (u : R) = 2) (l : ℤ) (x : R) :
    model u hu (scale ^ l) x = (↑(u ^ (-l)) : R) * x := by
  rw [map_zpow, model_scale, ← map_zpow, inv_zpow, ← zpow_neg, dilation_apply]

private theorem model_trans_zpow (u : Rˣ) (hu : (u : R) = 2) (z : ℤ) (x : R) :
    model u hu (trans ^ z) x = x - (z : R) := by
  rw [map_zpow, model_trans, ← map_zpow, translation_apply]
  simp [zsmul_eq_mul, sub_eq_add_neg]

/-- Evaluate the normal form in an arbitrary ring in which two is invertible. -/
theorem model_normal (u : Rˣ) (hu : (u : R) = 2) (k z l : ℤ) (x : R) :
    model u hu (dyadic k z * scale ^ l) x =
      (↑(u ^ (-l)) : R) * x - (↑(u ^ (-k)) : R) * (z : R) := by
  simp only [dyadic, map_mul, Equiv.Perm.mul_apply, model_scale_zpow, model_trans_zpow,
    neg_neg, mul_sub]
  have h : (↑(u ^ (-k)) : R) * (↑(u ^ k) : R) = 1 := by
    rw [← Units.val_mul, ← zpow_add, neg_add_cancel, zpow_zero]
    rfl
  rw [← mul_assoc, h, one_mul]

/-- A nonzero integer coefficient bounds the size of each fibre of multiplication
in a finite residue ring. -/
theorem mul_fibre_le {n c : ℕ} [NeZero n] (hc : 0 < c) (b : ZMod n) :
    (Finset.univ.filter fun x : ZMod n => (c : ZMod n) * x = b).card ≤ c := by
  let S := Finset.univ.filter fun x : ZMod n => (c : ZMod n) * x = b
  let e (x : S) : Fin c := ⟨(c * x.val.val) / n,
    (Nat.div_lt_iff_lt_mul (Nat.pos_of_ne_zero (NeZero.ne n))).2
      (Nat.mul_lt_mul_of_pos_left (ZMod.val_lt x.val) hc)⟩
  have hrem (x : S) : (c * x.val.val) % n = b.val := by
    have hx := (Finset.mem_filter.mp x.property).2
    rw [← ZMod.val_natCast, Nat.cast_mul, ZMod.natCast_zmod_val, hx]
  have hI : Function.Injective e := by
    intro x y he
    apply Subtype.ext
    apply ZMod.val_injective n
    have hq : (c * x.val.val) / n = (c * y.val.val) / n := congrArg Fin.val he
    apply Nat.eq_of_mul_eq_mul_left hc
    calc
      c * x.val.val = (c * x.val.val) % n + n * ((c * x.val.val) / n) :=
        (Nat.mod_add_div _ _).symm
      _ = (c * y.val.val) % n + n * ((c * y.val.val) / n) := by
        rw [hrem x, hrem y, hq]
      _ = c * y.val.val := Nat.mod_add_div _ _
  calc
    S.card = Fintype.card S := (Fintype.card_coe S).symm
    _ ≤ Fintype.card (Fin c) := Fintype.card_le_of_injective e hI
    _ = c := Fintype.card_fin c

/-- A nonidentity word has only boundedly many fixed points in the canonical
affine permutations modulo sufficiently large odd integers. -/
theorem eventually_few_fixed (g : BS) (hg : g ≠ 1) :
    ∃ K N : ℕ, ∀ (n : ℕ) [NeZero n], N ≤ n →
      ∀ (u : (ZMod n)ˣ) (hu : (u : ZMod n) = 2),
      (Finset.univ.filter fun x : ZMod n => model u hu g x = x).card ≤ K := by
  obtain ⟨k, z, l, rfl⟩ := normal_form g
  by_cases hl : l = 0
  · subst l
    have hz : z ≠ 0 := by
      intro hz
      subst z
      apply hg
      simp [dyadic, zpow_neg]
    refine ⟨0, z.natAbs + 1, ?_⟩
    intro n _ hn u hu
    rw [Nat.le_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro x _ hx
    rw [model_normal] at hx
    simp only [neg_zero, zpow_zero, Units.val_one, one_mul] at hx
    have he : (↑(u ^ (-k)) : ZMod n) * (z : ZMod n) = 0 := sub_eq_self.mp hx
    have hz0 : (z : ZMod n) = 0 := by
      have h := congrArg (fun x : ZMod n => (↑(u ^ k) : ZMod n) * x) he
      rw [← mul_assoc, ← Units.val_mul, ← zpow_add, add_neg_cancel, zpow_zero,
        Units.val_one, one_mul, mul_zero] at h
      exact h
    have hdiv := (ZMod.intCast_zmod_eq_zero_iff_dvd z n).mp hz0
    have hle : n ≤ z.natAbs := by simpa using Int.natAbs_le_of_dvd_ne_zero hdiv hz
    omega
  · let m := l.natAbs
    let c := 2 ^ m - 1
    have hm : 0 < m := Int.natAbs_pos.mpr hl
    have hc : 0 < c := by
      have hlt : 1 < (2 : ℕ) ^ m := one_lt_pow₀ (by decide) (by omega)
      omega
    refine ⟨c, 1, ?_⟩
    intro n _ _ u hu
    have hcast : (c : ZMod n) = (↑(u ^ (m : ℤ)) : ZMod n) - 1 := by
      dsimp [c]
      rw [Nat.cast_sub (Nat.succ_le_of_lt (by positivity : 0 < (2 : ℕ) ^ m)), Nat.cast_pow,
        Nat.cast_one, zpow_natCast, Units.val_pow_eq_pow_val, hu]
      norm_num
    let B := (↑(u ^ (-k)) : ZMod n) * (z : ZMod n)
    by_cases hp : 0 ≤ l
    · have hlm : l = (m : ℤ) := (Int.natAbs_of_nonneg hp).symm
      apply le_trans (Finset.card_le_card (t := Finset.univ.filter fun x : ZMod n =>
        (c : ZMod n) * x = -((↑(u ^ l) : ZMod n) * B)) ?_) (mul_fibre_le hc _)
      intro x hx
      have he := (Finset.mem_filter.mp hx).2
      rw [model_normal] at he
      change (↑(u ^ (-l)) : ZMod n) * x - B = x at he
      have h := congrArg (fun x : ZMod n => (↑(u ^ l) : ZMod n) * x) he
      change (↑(u ^ l) : ZMod n) * ((↑(u ^ (-l)) : ZMod n) * x - B) =
        (↑(u ^ l) : ZMod n) * x at h
      rw [mul_sub, ← mul_assoc, ← Units.val_mul, ← zpow_add, add_neg_cancel,
        zpow_zero, Units.val_one, one_mul] at h
      apply Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rw [hcast, ← hlm]
      linear_combination -h
    · have hlm : -l = (m : ℤ) := by
        have hnon : 0 ≤ -l := by omega
        simpa only [m, Int.natAbs_neg] using (Int.natAbs_of_nonneg hnon).symm
      apply le_trans (Finset.card_le_card (t := Finset.univ.filter fun x : ZMod n =>
        (c : ZMod n) * x = B) ?_) (mul_fibre_le hc _)
      intro x hx
      have he := (Finset.mem_filter.mp hx).2
      rw [model_normal] at he
      change (↑(u ^ (-l)) : ZMod n) * x - B = x at he
      apply Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rw [hcast, ← hlm]
      linear_combination he

end HigmanAffine

namespace HigmanFolner

open HigmanAdjacent HigmanAffine Multiplicative
open scoped BigOperators

section Boundary

variable {G : Type*} [Group G] [DecidableEq G]

/-- The number of elements whose left translate leaves the finite set. -/
def boundary (g : G) (S : Finset G) : ℕ := (S.filter fun s => g * s ∉ S).card

@[simp] theorem boundary_one (S : Finset G) : boundary 1 S = 0 := by
  simp [boundary]

theorem boundary_mul (g h : G) (S : Finset G) :
    boundary (g * h) S ≤ boundary g S + boundary h S := by
  let A := S.filter fun x => (g * h) * x ∉ S
  let B := S.filter fun x => h * x ∉ S
  let C := (S.filter fun x => h * x ∈ S).filter fun x => g * (h * x) ∉ S
  have hsub : A ⊆ B ∪ C := by
    intro x hx
    simp only [A, Finset.mem_filter, mul_assoc] at hx
    by_cases hh : h * x ∈ S
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨hx.1, hh⟩, hx.2⟩)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hx.1, hh⟩)
  have hC : C.card ≤ boundary g S := by
    rw [← Finset.card_image_of_injective C (mul_right_injective h)]
    apply Finset.card_le_card
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hy).1).2,
      (Finset.mem_filter.mp hy).2⟩
  exact ((Finset.card_le_card hsub).trans (Finset.card_union_le _ _)).trans
    (by simpa [B, boundary, add_comm] using Nat.add_le_add_left hC B.card)

theorem boundary_inv (g : G) (S : Finset G) : boundary g⁻¹ S = boundary g S := by
  let A := S.filter fun x => g * x ∈ S
  let B := S.filter fun x => g⁻¹ * x ∈ S
  have hImage : A.image (fun x => g * x) = B := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      have h := Finset.mem_filter.mp hy
      exact Finset.mem_filter.mpr ⟨h.2, by simpa using h.1⟩
    · intro hx
      have h := Finset.mem_filter.mp hx
      exact Finset.mem_image.mpr ⟨g⁻¹ * x, Finset.mem_filter.mpr
        ⟨h.2, by simpa using h.1⟩, by simp⟩
  have hCard : A.card = B.card := by
    rw [← hImage, Finset.card_image_of_injective _ (mul_right_injective g)]
  have hA : A.card + boundary g S = S.card :=
    S.card_filter_add_card_filter_not (fun x => g * x ∈ S)
  have hB : B.card + boundary g⁻¹ S = S.card :=
    S.card_filter_add_card_filter_not (fun x => g⁻¹ * x ∈ S)
  omega

end Boundary

noncomputable section

local instance : DecidableEq BS := Classical.decEq _

private def width (L : ℕ) : ℕ := L * 2 ^ L

private def coordinate (ij : ℕ × ℕ) : BS := scale ^ ij.1 * trans ^ ij.2

private theorem coordinate_injective : Function.Injective coordinate := by
  intro x y h
  have hheight := congrArg height h
  have hfirst : x.1 = y.1 := by
    have he := congrArg Multiplicative.toAdd hheight
    simp [coordinate] at he
    omega
  have hpow : trans ^ x.2 = trans ^ y.2 := by
    unfold coordinate at h
    rw [hfirst] at h
    exact mul_left_cancel h
  have hsecond : x.2 = y.2 := by
    have he : zpowersHom BS trans (ofAdd (x.2 : ℤ)) =
        zpowersHom BS trans (ofAdd (y.2 : ℤ)) := by
      simpa using hpow
    have hcast : (x.2 : ℤ) = (y.2 : ℤ) :=
      congrArg Multiplicative.toAdd (transHom_injective he)
    exact_mod_cast hcast
  exact Prod.ext hfirst hsecond

private def box (L : ℕ) : Finset BS :=
  ((Finset.range L) ×ˢ Finset.range (width L)).image coordinate

private theorem box_card (L : ℕ) : (box L).card = L * width L := by
  rw [box, Finset.card_image_of_injective _ coordinate_injective, Finset.card_product,
    Finset.card_range, Finset.card_range]

private theorem trans_mul_scale_pow (i : ℕ) :
    trans * scale ^ i = scale ^ i * trans ^ ((2 : ℕ) ^ i) := by
  induction i with
  | zero => simp
  | succ i ih =>
    have hrel : trans ^ ((2 : ℕ) ^ i) * scale =
        scale * trans ^ (2 * ((2 : ℕ) ^ i)) := by
      have he := congrArg (fun x : BS => scale * x)
        (trans_pow_conj ((((2 : ℕ) ^ i) : ℕ) : ℤ))
      simp only [← mul_assoc, mul_inv_cancel, one_mul] at he
      exact_mod_cast he
    calc
      _ = (trans * scale ^ i) * scale := by rw [pow_succ, mul_assoc]
      _ = scale ^ i * (trans ^ ((2 : ℕ) ^ i) * scale) := by rw [ih, mul_assoc]
      _ = scale ^ (i + 1) * trans ^ ((2 : ℕ) ^ (i + 1)) := by
        rw [hrel, ← mul_assoc, ← pow_succ,
          show (2 : ℕ) ^ (i + 1) = 2 * (2 : ℕ) ^ i by rw [pow_succ, Nat.mul_comm]]

private theorem boundary_trans (L : ℕ) : boundary trans (box L) ≤ width L := by
  let cap := 2 ^ L
  let Bad := (Finset.range L) ×ˢ Finset.Ico (width L - cap) (width L)
  have hsub : (box L).filter (fun s => trans * s ∉ box L) ⊆ Bad.image coordinate := by
    intro s hs
    obtain ⟨hbox, hout⟩ := Finset.mem_filter.mp hs
    obtain ⟨⟨i,j⟩, hij, rfl⟩ := Finset.mem_image.mp hbox
    have hi := Finset.mem_range.mp (Finset.mem_product.mp hij).1
    have hj := Finset.mem_range.mp (Finset.mem_product.mp hij).2
    have hlarge : width L - cap ≤ j := by
      by_contra! hlt
      have hpow : 2 ^ i ≤ cap := Nat.pow_le_pow_right (by decide) hi.le
      have hj' : j + 2 ^ i < width L := by omega
      apply hout
      have he : trans * coordinate (i,j) = coordinate (i,j + 2 ^ i) := by
        change trans * (scale ^ i * trans ^ j) = scale ^ i * trans ^ (j + 2 ^ i)
        rw [← mul_assoc, trans_mul_scale_pow, mul_assoc, ← pow_add, add_comm]
      rw [he]
      exact Finset.mem_image.mpr ⟨(i,j + 2 ^ i), Finset.mem_product.mpr
        ⟨Finset.mem_range.mpr hi, Finset.mem_range.mpr hj'⟩, rfl⟩
    exact Finset.mem_image.mpr ⟨(i,j), Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr hi, Finset.mem_Ico.mpr ⟨hlarge, hj⟩⟩, rfl⟩
  have hcard := Finset.card_le_card hsub
  have hb : Bad.card ≤ width L := by
    change ((Finset.range L) ×ˢ Finset.Ico (width L - cap) (width L)).card ≤ _
    rw [Finset.card_product, Finset.card_range, Nat.card_Ico]
    change L * (width L - (width L - cap)) ≤ L * cap
    apply Nat.mul_le_mul_left
    by_cases h : cap ≤ width L
    · rw [Nat.sub_sub_self h]
    · have h' : width L ≤ cap := le_of_not_ge h
      rwa [Nat.sub_eq_zero_of_le h', Nat.sub_zero]
  exact hcard.trans (Finset.card_image_le.trans hb)

private theorem boundary_scale (L : ℕ) : boundary scale (box L) ≤ width L := by
  let Bad := ({L - 1} : Finset ℕ) ×ˢ Finset.range (width L)
  have hsub : (box L).filter (fun s => scale * s ∉ box L) ⊆ Bad.image coordinate := by
    intro s hs
    obtain ⟨hbox, hout⟩ := Finset.mem_filter.mp hs
    obtain ⟨⟨i,j⟩, hij, rfl⟩ := Finset.mem_image.mp hbox
    have hi := Finset.mem_range.mp (Finset.mem_product.mp hij).1
    have hj := (Finset.mem_product.mp hij).2
    have hlast : i = L - 1 := by
      by_contra hn
      have hi' : i + 1 < L := by omega
      apply hout
      have he : scale * coordinate (i,j) = coordinate (i+1,j) := by
        change scale * (scale ^ i * trans ^ j) = scale ^ (i + 1) * trans ^ j
        rw [← mul_assoc, pow_succ']
      rw [he]
      exact Finset.mem_image.mpr ⟨(i+1,j), Finset.mem_product.mpr
        ⟨Finset.mem_range.mpr hi', hj⟩, rfl⟩
    exact Finset.mem_image.mpr ⟨(i,j), Finset.mem_product.mpr
      ⟨Finset.mem_singleton.mpr hlast, hj⟩, rfl⟩
  have hcard := Finset.card_le_card hsub
  exact hcard.trans (Finset.card_image_le.trans (by simp [Bad]))

private theorem boundary_bound (g : BS) :
    ∃ C : ℕ, ∀ L : ℕ, boundary g (box L) ≤ C * width L := by
  induction g using HNNExtension.induction_on with
  | of z =>
    have hgen (n : ℕ) : ∀ L, boundary (trans ^ n) (box L) ≤ n * width L := by
      intro L
      induction n with
      | zero => simp
      | succ n ih =>
        rw [pow_succ, Nat.succ_mul]
        exact (boundary_mul _ _ _).trans (Nat.add_le_add ih (boundary_trans L))
    have hz : HNNExtension.of z = trans ^ z.toAdd := by
      change HNNExtension.of z = (HNNExtension.of (ofAdd (1 : ℤ)) : BS) ^ z.toAdd
      rw [← map_zpow, ← Int.ofAdd_mul, one_mul]
      rfl
    refine ⟨z.toAdd.natAbs, fun L => ?_⟩
    rw [hz]
    cases hz : z.toAdd with
    | ofNat n => simpa using hgen n L
    | negSucc n =>
      have he : Int.negSucc n = -((n + 1 : ℕ) : ℤ) := by rw [Int.negSucc_eq]; omega
      rw [he, zpow_neg, zpow_natCast, boundary_inv, Int.natAbs_neg]
      exact hgen (n + 1) L
  | t =>
    refine ⟨1, fun L => ?_⟩
    have ht : (HNNExtension.t : BS) = scale⁻¹ := by simp [HigmanAdjacent.scale]
    rw [ht, boundary_inv, one_mul]
    exact boundary_scale L
  | mul g h hg hh =>
    obtain ⟨C, hC⟩ := hg
    obtain ⟨D, hD⟩ := hh
    refine ⟨C + D, fun L => ?_⟩
    rw [Nat.add_mul]
    exact (boundary_mul _ _ _).trans (Nat.add_le_add (hC L) (hD L))
  | inv g hg =>
    obtain ⟨C, hC⟩ := hg
    exact ⟨C, fun L => by rw [boundary_inv]; exact hC L⟩

/-- The dyadic affine group has finite sets with arbitrarily small total
left-translation boundary for any specified finite set of group elements. -/
theorem folner (K : Finset BS) (ε : ℝ) (hε : 0 < ε) :
    ∃ F : Finset BS, F.Nonempty ∧
      (∑ g ∈ K, (boundary g F : ℝ)) ≤ ε * F.card := by
  choose C hC using boundary_bound
  let M := ∑ g ∈ K, (C g : ℝ)
  obtain ⟨L, hL⟩ := exists_nat_gt (max 1 (M / ε))
  have hLpos : 0 < L := by
    have ht := (le_max_left (1 : ℝ) (M / ε)).trans_lt hL
    exact_mod_cast (show (0 : ℝ) < L by linarith)
  have hM : M ≤ ε * L := by
    have he := (le_max_right (1 : ℝ) (M / ε)).trans_lt hL
    simpa [mul_comm] using ((div_lt_iff₀ hε).mp he).le
  refine ⟨box L, Finset.card_pos.mp ?_, ?_⟩
  · rw [box_card]
    unfold width
    positivity
  · calc
      _ ≤ ∑ g ∈ K, (C g : ℝ) * width L := by
        exact Finset.sum_le_sum fun g _ => by exact_mod_cast hC g L
      _ = M * width L := by rw [Finset.sum_mul]
      _ ≤ (ε * L) * width L := mul_le_mul_of_nonneg_right hM (by positivity)
      _ = _ := by rw [box_card, Nat.cast_mul, mul_assoc]

end

end HigmanFolner

/-
# A coupled packing step for finite action models

Pairing new centres and keeping the same labels in both tiles avoids adjusting
the two resulting families to have equal tile counts after packing.
-/

open scoped BigOperators

namespace SoficCoupledPacking

variable {L X Y : Type*} [DecidableEq L] [DecidableEq X] [DecidableEq Y]

/-- A pair of centre points together with the labels retained in both copies. -/
structure Tile (L X Y : Type*) where
  leftCenter : X
  rightCenter : Y
  core : Finset L
deriving DecidableEq

def Tile.left (p : L → Equiv.Perm X) (t : Tile L X Y) : Finset X :=
  t.core.image fun l => p l t.leftCenter

def Tile.right (q : L → Equiv.Perm Y) (t : Tile L X Y) : Finset Y :=
  t.core.image fun l => q l t.rightCenter

def leftCovered (p : L → Equiv.Perm X) (P : Finset (Tile L X Y)) : Finset X :=
  P.biUnion (Tile.left p)

def rightCovered (q : L → Equiv.Perm Y) (P : Finset (Tile L X Y)) : Finset Y :=
  P.biUnion (Tile.right q)

omit [DecidableEq L] [DecidableEq Y] in
private theorem overlap_count (p : L → Equiv.Perm X)
    (F : Finset L) (A O : Finset X) :
    (∑ c ∈ A, (F.filter fun l => p l c ∈ O).card) ≤ F.card * O.card := by
  calc
    _ = ∑ c ∈ A, ∑ l ∈ F, if p l c ∈ O then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro c _
      simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = ∑ l ∈ F, ∑ c ∈ A, if p l c ∈ O then 1 else 0 := Finset.sum_comm
    _ ≤ ∑ _l ∈ F, O.card := by
      apply Finset.sum_le_sum
      intro l _
      rw [← Finset.sum_filter, ← Finset.card_eq_sum_ones]
      let T := A.filter fun c => p l c ∈ O
      have h := Finset.card_image_of_injective T (p l).injective
      rw [← h]
      apply Finset.card_le_card
      intro x hx
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hx
      exact (Finset.mem_filter.mp hc).2
    _ = _ := by simp

omit [DecidableEq L] [DecidableEq Y] in
private theorem exists_small_overlap (p : L → Equiv.Perm X)
    {F : Finset L} (hF : F.Nonempty) (A O : Finset X) {η : ℝ}
    (hO : (O.card : ℝ) < η * A.card) :
    ∃ c ∈ A, ((F.filter fun l => p l c ∈ O).card : ℝ) ≤ η * F.card := by
  by_contra! h
  have hlarge : (A.card : ℝ) * (η * F.card) ≤
      ∑ c ∈ A, ((F.filter fun l => p l c ∈ O).card : ℝ) := by
    simpa using (Finset.sum_le_sum fun c hc => (h c hc).le :
      (∑ _c ∈ A, η * (F.card : ℝ)) ≤ ∑ c ∈ A, ((F.filter fun l => p l c ∈ O).card : ℝ))
  have hcount := overlap_count p F A O
  have hupper : (∑ c ∈ A, ((F.filter fun l => p l c ∈ O).card : ℝ)) ≤
      (F.card : ℝ) * O.card := by exact_mod_cast hcount
  have hp : (0 : ℝ) < (F.card : ℝ) := by exact_mod_cast hF.card_pos
  have hstrict := mul_lt_mul_of_pos_left hO hp
  linarith [show (A.card : ℝ) * (η * F.card) = F.card * (η * A.card) by ring]

omit [DecidableEq L] in
private theorem same_size (p : L → Equiv.Perm X) (q : L → Equiv.Perm Y)
    {F : Finset L} {A : Finset X} {B : Finset Y} {P : Finset (Tile L X Y)}
    (hinjL : ∀ c ∈ A, Set.InjOn (fun l => p l c) F)
    (hinjR : ∀ c ∈ B, Set.InjOn (fun l => q l c) F)
    (hparams : ∀ t ∈ P, t.leftCenter ∈ A ∧ t.rightCenter ∈ B ∧ t.core ⊆ F)
    (hdL : (P : Set (Tile L X Y)).PairwiseDisjoint (Tile.left p))
    (hdR : (P : Set (Tile L X Y)).PairwiseDisjoint (Tile.right q)) :
    (leftCovered p P).card = (rightCovered q P).card := by
  rw [leftCovered, rightCovered, Finset.card_biUnion hdL, Finset.card_biUnion hdR]
  apply Finset.sum_congr rfl
  intro t ht
  obtain ⟨hL, hR, hF⟩ := hparams t ht
  rw [Tile.left, Tile.right,
    Finset.card_image_of_injOn ((hinjL _ hL).mono hF),
    Finset.card_image_of_injOn ((hinjR _ hR).mono hF)]

/-- A matched layer of partial tiles covers at least an η-fraction of the
smaller supply of available centres. Every tile retains at least
(1-2η) of the labels in both models. -/
theorem pack_layer
    (p : L → Equiv.Perm X) (q : L → Equiv.Perm Y)
    {F : Finset L} (hF : F.Nonempty) (A : Finset X) (B : Finset Y)
    (hinjL : ∀ c ∈ A, Set.InjOn (fun l => p l c) F)
    (hinjR : ∀ c ∈ B, Set.InjOn (fun l => q l c) F)
    {η : ℝ} (hη : η < 1 / 2) :
    ∃ P : Finset (Tile L X Y),
      (∀ t ∈ P, t.leftCenter ∈ A ∧ t.rightCenter ∈ B ∧ t.core ⊆ F ∧
        (1 - 2 * η) * F.card ≤ t.core.card) ∧
      (P : Set (Tile L X Y)).PairwiseDisjoint (Tile.left p) ∧
      (P : Set (Tile L X Y)).PairwiseDisjoint (Tile.right q) ∧
      η * (min A.card B.card : ℕ) ≤ (leftCovered p P).card ∧
      (leftCovered p P).card = (rightCovered q P).card := by
  classical
  let Valid (P : Finset (Tile L X Y)) : Prop :=
    (∀ t ∈ P, t.leftCenter ∈ A ∧ t.rightCenter ∈ B ∧ t.core ⊆ F ∧
      (1 - 2 * η) * F.card ≤ t.core.card) ∧
    (P : Set (Tile L X Y)).PairwiseDisjoint (Tile.left p) ∧
    (P : Set (Tile L X Y)).PairwiseDisjoint (Tile.right q)
  let M : Finset (Tile L X Y) := ((A ×ˢ B) ×ˢ F.powerset).image fun x =>
    ⟨x.1.1, x.1.2, x.2⟩
  let C := M.powerset.filter Valid
  have hc (P : Finset (Tile L X Y)) : P ∈ C ↔ Valid P := by
    rw [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨And.right, fun hv => ⟨?_, hv⟩⟩
    intro t ht
    obtain ⟨htA, htB, htF, _⟩ := hv.1 t ht
    exact Finset.mem_image.mpr ⟨((t.leftCenter, t.rightCenter), t.core),
      Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨htA, htB⟩,
        Finset.mem_powerset.mpr htF⟩, rfl⟩
  have hempty : Valid ∅ := by simp [Valid, Set.PairwiseDisjoint, Set.Pairwise]
  obtain ⟨P, hP, hmax⟩ := C.exists_max_image (fun P => (leftCovered p P).card)
    ⟨∅, (hc _).mpr hempty⟩
  obtain ⟨hval, hdl, hdr⟩ := (hc P).mp hP
  have heq := same_size p q hinjL hinjR
    (fun t ht => ⟨(hval t ht).1, (hval t ht).2.1, (hval t ht).2.2.1⟩) hdl hdr
  refine ⟨P, hval, hdl, hdr, ?_, heq⟩
  by_contra! hlt
  have hηp : 0 < η := by
    by_contra! he
    have hn : η * (min A.card B.card : ℕ) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg he (by positivity)
    have hnonneg : (0 : ℝ) ≤ (leftCovered p P).card := by positivity
    linarith
  have hLt : (leftCovered p P).card < η * A.card := hlt.trans_le
    (mul_le_mul_of_nonneg_left (by exact_mod_cast min_le_left A.card B.card) hηp.le)
  have hRt : (rightCovered q P).card < η * B.card := by
    rw [← heq]
    exact hlt.trans_le
      (mul_le_mul_of_nonneg_left (by exact_mod_cast min_le_right A.card B.card) hηp.le)
  obtain ⟨x, hx, hxO⟩ := exists_small_overlap p hF A (leftCovered p P) hLt
  obtain ⟨y, hy, hyO⟩ := exists_small_overlap q hF B (rightCovered q P) hRt
  let W := F.filter fun l => p l x ∉ leftCovered p P ∧ q l y ∉ rightCovered q P
  have hw : (1 - 2 * η) * F.card ≤ W.card := by
    let V := F.filter fun l => p l x ∈ leftCovered p P ∨ q l y ∈ rightCovered q P
    have hV : V.card ≤ (F.filter fun l => p l x ∈ leftCovered p P).card +
        (F.filter fun l => q l y ∈ rightCovered q P).card := by
      change (F.filter fun l => p l x ∈ leftCovered p P ∨ q l y ∈ rightCovered q P).card ≤ _
      rw [Finset.filter_or]
      exact Finset.card_union_le _ _
    have hsum : V.card + W.card = F.card := by
      simpa [V, W, not_or] using F.card_filter_add_card_filter_not
        (fun l => p l x ∈ leftCovered p P ∨ q l y ∈ rightCovered q P)
    have hV' := (show (V.card : ℝ) ≤
      ((F.filter fun l => p l x ∈ leftCovered p P).card : ℝ) +
      ((F.filter fun l => q l y ∈ rightCovered q P).card : ℝ) by exact_mod_cast hV)
    have hsum' : (V.card : ℝ) + (W.card : ℝ) = F.card := by exact_mod_cast hsum
    linarith
  let t : Tile L X Y := ⟨x, y, W⟩
  have hne : t.core.Nonempty := by
    have hpos : (0 : ℝ) < (1 - 2 * η) * F.card := by
      apply mul_pos (by linarith)
      exact_mod_cast hF.card_pos
    exact Finset.card_pos.mp (by exact_mod_cast (hpos.trans_le hw))
  have hnL : Disjoint (t.left p) (leftCovered p P) := by
    apply Finset.disjoint_left.mpr
    intro z hz
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hz
    exact (Finset.mem_filter.mp hl).2.1
  have hnR : Disjoint (t.right q) (rightCovered q P) := by
    apply Finset.disjoint_left.mpr
    intro z hz
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hz
    exact (Finset.mem_filter.mp hl).2.2
  have hv' : Valid (insert t P) := by
    refine ⟨?_, ?_, ?_⟩
    · intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact ⟨hx, hy, Finset.filter_subset _ _, hw⟩
      · exact hval _ hz
    · intro z hz w hwz hzw
      change z ∈ insert t P at hz
      change w ∈ insert t P at hwz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact hnL.mono_right (Finset.subset_biUnion_of_mem (Tile.left p) (Finset.mem_insert.mp hwz
          |>.resolve_left hzw.symm))
      · rcases Finset.mem_insert.mp hwz with rfl | hwz
        · exact (hnL.mono_right (Finset.subset_biUnion_of_mem (Tile.left p) hz)).symm
        · exact hdl hz hwz hzw
    · intro z hz w hwz hzw
      change z ∈ insert t P at hz
      change w ∈ insert t P at hwz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact hnR.mono_right (Finset.subset_biUnion_of_mem (Tile.right q) (Finset.mem_insert.mp hwz
          |>.resolve_left hzw.symm))
      · rcases Finset.mem_insert.mp hwz with rfl | hwz
        · exact (hnR.mono_right (Finset.subset_biUnion_of_mem (Tile.right q) hz)).symm
        · exact hdr hz hwz hzw
  have hm := hmax _ ((hc _).mpr hv')
  change ((insert t P).biUnion (Tile.left p)).card ≤ (leftCovered p P).card at hm
  rw [Finset.biUnion_insert] at hm
  change (t.left p ∪ leftCovered p P).card ≤ (leftCovered p P).card at hm
  rw [Finset.card_union_of_disjoint hnL] at hm
  have hpc : 0 < (t.left p).card := (hne.image _).card_pos
  omega

end SoficCoupledPacking

namespace SoficCoupledPacking

open scoped BigOperators

section Contact

variable {G X I : Type*} [Group G] [DecidableEq G] [DecidableEq X]

/-- All relative labels from the first shape to the second. -/
def relativeLabels (F H : Finset G) : Finset G :=
  (F ×ˢ H).image fun g => g.1⁻¹ * g.2

/-- Count the available centres after forbidding contact with a family of
older, disjoint cores. -/
theorem available_centres (p : G → Equiv.Perm X) (F : Finset G) (good : Finset X)
    (T : Finset I) (centre : I → X) (core shape : I → Finset G)
    (hcore : ∀ i ∈ T, core i ⊆ shape i)
    (hinj : ∀ i ∈ T, Set.InjOn (fun g => p g (centre i)) (core i))
    (hdisj : (T : Set I).PairwiseDisjoint (fun i => (core i).image fun g => p g (centre i)))
    (hact : ∀ i ∈ T, ∀ f ∈ F, ∀ g ∈ core i,
      (p f).symm (p g (centre i)) = p (f⁻¹ * g) (centre i))
    {β ρ : ℝ} (hβ : 0 < β) (hρ : 0 ≤ ρ)
    (hmass : ∀ i ∈ T, β * (shape i).card ≤ (core i).card)
    (hrel : ∀ i ∈ T, ((relativeLabels F (shape i)).card : ℝ) ≤ (1 + ρ) * (shape i).card) :
    let O := T.biUnion fun i => (core i).image fun g => p g (centre i)
    let A := good.filter fun x => Disjoint (F.image fun g => p g x) O
    β * good.card - (1 + ρ) * O.card ≤ β * A.card := by
  classical
  dsimp only
  let C (i : I) := (core i).image fun g => p g (centre i)
  let O := T.biUnion C
  let A := good.filter fun x => Disjoint (F.image fun g => p g x) O
  let B := good.filter fun x => ¬ Disjoint (F.image fun g => p g x) O
  let E (i : I) := (relativeLabels F (shape i)).image fun g => p g (centre i)
  have hB : B ⊆ T.biUnion E := by
    intro x hx
    obtain ⟨_, hbad⟩ := Finset.mem_filter.mp hx
    obtain ⟨y, hyF, hyO⟩ := Finset.not_disjoint_iff.mp hbad
    obtain ⟨f, hf, hfy⟩ := Finset.mem_image.mp hyF
    obtain ⟨i, hi, hyC⟩ := Finset.mem_biUnion.mp hyO
    obtain ⟨g, hg, hgy⟩ := Finset.mem_image.mp hyC
    have he : x = p (f⁻¹ * g) (centre i) := by
      have hh := hact i hi f hf g hg
      simpa only [hgy, ← hfy, Equiv.symm_apply_apply] using hh
    apply Finset.mem_biUnion.mpr
    refine ⟨i, hi, Finset.mem_image.mpr ⟨f⁻¹ * g, ?_, he.symm⟩⟩
    exact Finset.mem_image.mpr ⟨(f, g), Finset.mem_product.mpr ⟨hf, hcore i hi hg⟩, rfl⟩
  have hbound : (B.card : ℝ) ≤ ∑ i ∈ T, ((relativeLabels F (shape i)).card : ℝ) := by
    exact_mod_cast (calc
      B.card ≤ (T.biUnion E).card := Finset.card_le_card hB
      _ ≤ ∑ i ∈ T, (E i).card := Finset.card_biUnion_le
      _ ≤ ∑ i ∈ T, (relativeLabels F (shape i)).card :=
        Finset.sum_le_sum fun _ _ => Finset.card_image_le)
  have ho : (O.card : ℝ) = ∑ i ∈ T, ((core i).card : ℝ) := by
    have hh : O.card = ∑ i ∈ T, (core i).card := by
      change (T.biUnion C).card = _
      rw [Finset.card_biUnion hdisj]
      exact Finset.sum_congr rfl fun i hi => Finset.card_image_of_injOn (hinj i hi)
    exact_mod_cast hh
  have hsh : β * (∑ i ∈ T, ((shape i).card : ℝ)) ≤ O.card := by
    rw [Finset.mul_sum, ho]
    exact Finset.sum_le_sum hmass
  have hge : (B.card : ℝ) ≤ (1 + ρ) * ∑ i ∈ T, ((shape i).card : ℝ) := by
    rw [Finset.mul_sum]
    exact hbound.trans (Finset.sum_le_sum hrel)
  have hbc := calc
    β * (B.card : ℝ) ≤ β * ((1 + ρ) * ∑ i ∈ T, ((shape i).card : ℝ)) :=
      mul_le_mul_of_nonneg_left hge hβ.le
    _ = (1 + ρ) * (β * ∑ i ∈ T, ((shape i).card : ℝ)) := mul_left_comm _ _ _
    _ ≤ (1 + ρ) * O.card := mul_le_mul_of_nonneg_left hsh (by positivity)
  have hab : (A.card : ℝ) + B.card = good.card := by
    have hh : A.card + B.card = good.card :=
      good.card_filter_add_card_filter_not (fun x => Disjoint (F.image fun g => p g x) O)
    exact_mod_cast hh
  change β * (good.card : ℝ) - (1 + ρ) * O.card ≤ β * A.card
  rw [← hab, mul_add]
  linarith

end Contact

end SoficCoupledPacking

namespace SoficCoupledPacking

open scoped BigOperators

noncomputable section

variable {G X Y : Type*} [Group G] [DecidableEq G] [DecidableEq X] [DecidableEq Y]

/-- A family of coupled tiles, recording which scale supplied each tile. -/
structure Layered (k : ℕ) (p : G → Equiv.Perm X) (q : G → Equiv.Perm Y)
    (F : Fin k → Finset G) (P : Finset X) (Q : Finset Y) (β : ℝ) where
  tiles : Finset (Tile G X Y)
  level : Tile G X Y → Fin k
  valid : ∀ t ∈ tiles, t.leftCenter ∈ P ∧ t.rightCenter ∈ Q ∧
    t.core ⊆ F (level t) ∧ β * (F (level t)).card ≤ t.core.card
  leftDisjoint : (tiles : Set (Tile G X Y)).PairwiseDisjoint (Tile.left p)
  rightDisjoint : (tiles : Set (Tile G X Y)).PairwiseDisjoint (Tile.right q)

omit [Group G] [DecidableEq G] in
private theorem card_covered_left {k : ℕ} {p : G → Equiv.Perm X} {q : G → Equiv.Perm Y}
    {F : Fin k → Finset G} {P : Finset X} {Q : Finset Y} {β : ℝ}
    (B : Layered k p q F P Q β)
    (hp : ∀ j (x : X), x ∈ P → Set.InjOn (fun g => p g x) (F j)) :
    (leftCovered p B.tiles).card = ∑ t ∈ B.tiles, t.core.card := by
  rw [leftCovered, Finset.card_biUnion B.leftDisjoint]
  apply Finset.sum_congr rfl
  intro t ht
  exact Finset.card_image_of_injOn
    ((hp _ _ (B.valid t ht).1).mono (B.valid t ht).2.2.1)

omit [Group G] [DecidableEq G] in
private theorem card_covered_right {k : ℕ} {p : G → Equiv.Perm X} {q : G → Equiv.Perm Y}
    {F : Fin k → Finset G} {P : Finset X} {Q : Finset Y} {β : ℝ}
    (B : Layered k p q F P Q β)
    (hq : ∀ j (x : Y), x ∈ Q → Set.InjOn (fun g => q g x) (F j)) :
    (rightCovered q B.tiles).card = ∑ t ∈ B.tiles, t.core.card := by
  rw [rightCovered, Finset.card_biUnion B.rightDisjoint]
  apply Finset.sum_congr rfl
  intro t ht
  exact Finset.card_image_of_injOn
    ((hq _ _ (B.valid t ht).2.1).mono (B.valid t ht).2.2.1)

private theorem disjoint_biUnion_of_contact {ι Z : Type*} [DecidableEq Z]
    (D E : Finset ι) (c : ι → Finset Z)
    (h : ∀ i ∈ D, Disjoint (c i) (E.biUnion c)) :
    Disjoint (D.biUnion c) (E.biUnion c) := by
  apply Finset.disjoint_left.mpr
  intro z hz hE
  obtain ⟨i, hi, hz'⟩ := Finset.mem_biUnion.mp hz
  exact Finset.disjoint_left.mp (h i hi) hz' hE

private theorem pairwise_union {ι Z : Type*} [DecidableEq ι] [DecidableEq Z]
    {D E : Finset ι} {c : ι → Finset Z}
    (hD : (D : Set ι).PairwiseDisjoint c) (hE : (E : Set ι).PairwiseDisjoint c)
    (h : Disjoint (D.biUnion c) (E.biUnion c)) :
    ((D ∪ E : Finset ι) : Set ι).PairwiseDisjoint c := by
  intro a ha b hb hab
  rcases Finset.mem_union.mp ha with ha | ha <;>
    rcases Finset.mem_union.mp hb with hb | hb
  · exact hD ha hb hab
  · exact (h.mono_left (Finset.subset_biUnion_of_mem c ha)).mono_right
      (Finset.subset_biUnion_of_mem c hb)
  · exact (h.symm.mono_left (Finset.subset_biUnion_of_mem c ha)).mono_right
      (Finset.subset_biUnion_of_mem c hb)
  · exact hE ha hb hab

/-- Descending through the Følner scales gives a coupled packing covering
at least the chosen proportion of both finite models. -/
theorem pack_scales {k : ℕ} (hk : 0 < k) (p : G → Equiv.Perm X) (q : G → Equiv.Perm Y)
    (F : Fin k → Finset G) (hF : ∀ j, (F j).Nonempty) (P : Finset X) (Q : Finset Y)
    {n : ℕ} {δ η : ℝ} (hδ : 0 < δ) (hδ₁ : δ < 1) (hη : η = δ / 16)
    (hkbig : 1 - δ ≤ k * (η * (δ / 2)))
    (hpGood : (1 - η) * n ≤ P.card) (hqGood : (1 - η) * n ≤ Q.card)
    (hrel : ∀ i j, i < j →
      ((relativeLabels (F i) (F j)).card : ℝ) ≤ (1 + η) * (F j).card)
    (hpInj : ∀ j (x : X), x ∈ P → Set.InjOn (fun g => p g x) (F j))
    (hqInj : ∀ j (y : Y), y ∈ Q → Set.InjOn (fun g => q g y) (F j))
    (hpAct : ∀ i j (x : X), x ∈ P → ∀ f ∈ F i, ∀ g ∈ F j,
      (p f).symm (p g x) = p (f⁻¹ * g) x)
    (hqAct : ∀ i j (y : Y), y ∈ Q → ∀ f ∈ F i, ∀ g ∈ F j,
      (q f).symm (q g y) = q (f⁻¹ * g) y) :
    ∃ B : Layered k p q F P Q (1 - 2 * η),
      (1 - δ) * n ≤ (leftCovered p B.tiles).card ∧
      (leftCovered p B.tiles).card = (rightCovered q B.tiles).card := by
  classical
  let β := 1 - 2 * η
  let rate := η * (δ / 2)
  have hηp : 0 < η := by linarith
  have hηlt : η < 1 / 2 := by linarith
  have hβp : 0 < β := by dsimp [β]; linarith
  have hβle : β ≤ 1 := by dsimp [β]; linarith
  have hn : (0 : ℝ) ≤ n := by positivity
  have hmargin : δ / 2 ≤ β * (1 - η) - (1 + η) * (1 - δ) := by
    dsimp [β]
    nlinarith [mul_nonneg hηp.le hδ.le, sq_nonneg η]
  have loop (r : ℕ) (hr : r ≤ k) :
      ∃ B : Layered k p q F P Q β, (∀ t ∈ B.tiles, k - r ≤ (B.level t).val) ∧
        min ((1 - δ) * n) (r * rate * n) ≤ (leftCovered p B.tiles).card := by
    induction r with
    | zero =>
      let B : Layered k p q F P Q β :=
        ⟨∅, fun _ => ⟨0, hk⟩, by simp, by simp [Set.PairwiseDisjoint, Set.Pairwise],
          by simp [Set.PairwiseDisjoint, Set.Pairwise]⟩
      exact ⟨B, by simp [B], by simp [B, leftCovered]⟩
    | succ r ih =>
      obtain ⟨B, hlevels, hsize⟩ := ih (by omega)
      by_cases hfinished : (1 - δ) * n ≤ (leftCovered p B.tiles).card
      · exact ⟨B, fun t ht => (by omega : k - (r + 1) ≤ k - r).trans (hlevels t ht),
          (min_le_left _ _).trans hfinished⟩
      let j : Fin k := ⟨k - (r + 1), by omega⟩
      have hj (t : Tile G X Y) (ht : t ∈ B.tiles) : j < B.level t := by
        have := hlevels t ht
        change k - (r + 1) < (B.level t).val
        omega
      let L := leftCovered p B.tiles
      let R := rightCovered q B.tiles
      let A := P.filter fun x => Disjoint ((F j).image fun g => p g x) L
      let C := Q.filter fun y => Disjoint ((F j).image fun g => q g y) R
      have hLR : L.card = R.card :=
        (card_covered_left B hpInj).trans (card_covered_right B hqInj).symm
      have hAc : β * (P.card : ℝ) - (1 + η) * L.card ≤ β * A.card := by
        exact available_centres p (F j) P B.tiles Tile.leftCenter Tile.core
          (fun t => F (B.level t))
          (fun t ht => (B.valid t ht).2.2.1)
          (fun t ht => (hpInj _ _ (B.valid t ht).1).mono (B.valid t ht).2.2.1)
          B.leftDisjoint
          (fun t ht f hf g hg => hpAct j (B.level t) _ (B.valid t ht).1
            f hf g ((B.valid t ht).2.2.1 hg))
          hβp hηp.le (fun t ht => (B.valid t ht).2.2.2) (fun t ht => hrel _ _ (hj t ht))
      have hCc : β * (Q.card : ℝ) - (1 + η) * R.card ≤ β * C.card := by
        exact available_centres q (F j) Q B.tiles Tile.rightCenter Tile.core
          (fun t => F (B.level t))
          (fun t ht => (B.valid t ht).2.2.1)
          (fun t ht => (hqInj _ _ (B.valid t ht).2.1).mono (B.valid t ht).2.2.1)
          B.rightDisjoint
          (fun t ht f hf g hg => hqAct j (B.level t) _ (B.valid t ht).2.1
            f hf g ((B.valid t ht).2.2.1 hg))
          hβp hηp.le (fun t ht => (B.valid t ht).2.2.2) (fun t ht => hrel _ _ (hj t ht))
      have hnot : (L.card : ℝ) ≤ (1 - δ) * n := le_of_lt (lt_of_not_ge hfinished)
      have havail (M D : ℕ) (hM : (1 - η) * n ≤ M)
          (hD : β * (M : ℝ) - (1 + η) * L.card ≤ β * D) :
          (δ / 2) * n ≤ D := calc
        _ ≤ (β * (1 - η) - (1 + η) * (1 - δ)) * n :=
          mul_le_mul_of_nonneg_right hmargin hn
        _ ≤ β * (M : ℝ) - (1 + η) * L.card := by
          have ha := mul_le_mul_of_nonneg_left hM hβp.le
          have hb := mul_le_mul_of_nonneg_left hnot (by positivity : 0 ≤ (1 + η))
          nlinarith
        _ ≤ β * D := hD
        _ ≤ D := by simpa using mul_le_mul_of_nonneg_right hβle (show (0 : ℝ) ≤ D by positivity)
      have havA := havail P.card A.card hpGood hAc
      have havC := havail Q.card C.card hqGood (by simpa only [hLR] using hCc)
      obtain ⟨T, hT, hTL, hTR, hweight, _⟩ := pack_layer p q (hF j) A C
        (fun x hx => hpInj _ _ (Finset.mem_filter.mp hx).1)
        (fun y hy => hqInj _ _ (Finset.mem_filter.mp hy).1) hηlt
      have hweight' : rate * n ≤ (leftCovered p T).card := by
        apply le_trans ?_ hweight
        rw [Nat.cast_min]
        calc
          _ = η * ((δ / 2) * n) := mul_assoc _ _ _
          _ ≤ _ := mul_le_mul_of_nonneg_left (le_min havA havC) hηp.le
      have hDL : Disjoint (leftCovered p T) L := by
        apply disjoint_biUnion_of_contact
        intro t ht
        exact ((Finset.mem_filter.mp (hT t ht).1).2).mono_left
          (Finset.image_subset_image (hT t ht).2.2.1)
      have hDR : Disjoint (rightCovered q T) R := by
        apply disjoint_biUnion_of_contact
        intro t ht
        exact ((Finset.mem_filter.mp (hT t ht).2.1).2).mono_left
          (Finset.image_subset_image (hT t ht).2.2.1)
      let f t := if t ∈ T then j else B.level t
      let B' : Layered k p q F P Q β :=
        ⟨T ∪ B.tiles, f, by
          intro t ht
          by_cases htT : t ∈ T
          · obtain ⟨hA, hC, hsub, hc⟩ := hT t htT
            simpa only [f, if_pos htT] using And.intro (Finset.mem_filter.mp hA).1
              (And.intro (Finset.mem_filter.mp hC).1 (And.intro hsub hc))
          · have htB := (Finset.mem_union.mp ht).resolve_left htT
            simpa only [f, if_neg htT] using B.valid t htB,
          pairwise_union hTL B.leftDisjoint hDL, pairwise_union hTR B.rightDisjoint hDR⟩
      have hs : (r : ℝ) * rate * n ≤ (L.card : ℝ) := by
        rcases min_choice ((1 - δ) * n) ((r : ℝ) * rate * n) with h | h
        · exact (hfinished (by simpa only [h] using hsize)).elim
        · simpa only [h] using hsize
      refine ⟨B', ?_, ?_⟩
      · intro t ht
        by_cases htT : t ∈ T
        · simp [B', f, htT, j]
        · have htB : t ∈ B.tiles := (Finset.mem_union.mp ht).resolve_left htT
          exact (by omega : k - (r + 1) ≤ k - r).trans (by simpa [B', f, htT] using hlevels t htB)
      · apply (min_le_right _ _).trans
        have he : (leftCovered p B'.tiles).card = (leftCovered p T).card + L.card := by
          change ((T ∪ B.tiles).biUnion (Tile.left p)).card = _
          rw [Finset.union_biUnion]
          exact Finset.card_union_of_disjoint hDL
        rw [he]
        push_cast
        calc
          _ = rate * n + (r : ℝ) * rate * n := by ring
          _ ≤ _ := add_le_add hweight' hs
  obtain ⟨B, _, hsize⟩ := loop k le_rfl
  refine ⟨B, ?_, (card_covered_left B hpInj).trans (card_covered_right B hqInj).symm⟩
  have hfull := mul_le_mul_of_nonneg_right hkbig hn
  exact (le_min le_rfl hfull).trans hsize

end

end SoficCoupledPacking

namespace SoficCoupledPacking

open scoped BigOperators

/-- Equal-sized finite sets admit a bijection extending a pairing of two
injective images of the same finite label set. -/
theorem extend_injections {D X Y : Type*} [Fintype D] [Fintype X] [Fintype Y]
    (hcard : Fintype.card X = Fintype.card Y) (f : D → X) (g : D → Y)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    ∃ e : X ≃ Y, ∀ d, e (f d) = g d := by
  classical
  let l := Equiv.ofInjective f hf
  let r := Equiv.ofInjective g hg
  let v : (Set.range f : Set X) ≃ (Set.range g : Set Y) := l.symm.trans r
  have hc : Fintype.card ↥((Set.range f)ᶜ : Set X) =
      Fintype.card ↥((Set.range g)ᶜ : Set Y) := by
    change Fintype.card {x : X // ¬ x ∈ Set.range f} =
      Fintype.card {y : Y // ¬ y ∈ Set.range g}
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, hcard,
      Fintype.card_congr v]
  let w := Fintype.equivOfCardEq hc
  let e := (Equiv.Set.sumCompl (Set.range f)).symm.trans
    ((v.sumCongr w).trans (Equiv.Set.sumCompl (Set.range g)))
  refine ⟨e, fun d => ?_⟩
  have hmem : f d ∈ Set.range f := ⟨d, rfl⟩
  simp only [e, Equiv.trans_apply]
  rw [Equiv.Set.sumCompl_symm_apply_of_mem hmem]
  simp [v, l, r]

section Boundary

variable {G : Type*} [Group G] [DecidableEq G]

/-- The overlap count for a subshape loses only the original boundary and
one additional label for each discarded point of the original shape. -/
theorem boundary_core_le (s : G) {C F : Finset G} (hCF : C ⊆ F) :
    HigmanFolner.boundary s C ≤ HigmanFolner.boundary s F + (F.card - C.card) := by
  let A := C.filter fun g => s * g ∉ C
  let B := F.filter fun g => s * g ∉ F
  let D := C.filter fun g => s * g ∈ F ∧ s * g ∉ C
  have hAB : A ⊆ B ∪ D := by
    intro g hg
    obtain ⟨hgC, hout⟩ := Finset.mem_filter.mp hg
    by_cases he : s * g ∈ F
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hgC, he, hout⟩)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hCF hgC, he⟩)
  have hd : D.card ≤ (F \ C).card := by
    rw [← Finset.card_image_of_injective D (mul_right_injective s)]
    apply Finset.card_le_card
    intro x hx
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_sdiff.mpr (Finset.mem_filter.mp hg).2
  rw [Finset.card_sdiff_of_subset hCF] at hd
  exact ((Finset.card_le_card hAB).trans (Finset.card_union_le _ _)).trans
    (Nat.add_le_add_left hd B.card)

end Boundary

private theorem label_map_injective {G I Z : Type*} [DecidableEq Z]
    (T : Finset I) (C : I → Finset G) (f : I → G → Z)
    (hinj : ∀ t ∈ T, Set.InjOn (f t) (C t))
    (hdisj : (T : Set I).PairwiseDisjoint (fun t => (C t).image (f t))) :
    Function.Injective (fun d : Σ t : T, ↥(C t.val) => f d.1.val d.2.val) := by
  rintro ⟨t, g⟩ ⟨u, h⟩ he
  change f t.val g.val = f u.val h.val at he
  have htu : t = u := by
    apply Subtype.ext
    by_contra hne
    exact Finset.disjoint_left.mp (hdisj t.property u.property hne)
      (Finset.mem_image_of_mem _ g.property)
      (by rw [he]; exact Finset.mem_image_of_mem _ h.property)
  subst u
  have hgh : g = h := by
    apply Subtype.ext
    exact hinj t.val t.property g.property h.property he
  exact congrArg (Sigma.mk t) hgh

section Match

variable {G X Y : Type*} [Group G] [DecidableEq G] [DecidableEq X] [DecidableEq Y]
  [Fintype X] [Fintype Y]

/-- Matching the retained labels of a sufficiently large coupled packing
gives a bijection intertwining the specified permutations at most points. -/
theorem matching_of_packing {k n : ℕ} {p : G → Equiv.Perm X} {q : G → Equiv.Perm Y}
    {F : Fin k → Finset G} {P : Finset X} {Q : Finset Y} {δ η : ℝ}
    (hδ : 0 < δ) (hδ₁ : δ < 1) (hη : η = δ / 16)
    (B : Layered k p q F P Q (1 - 2 * η))
    (hX : Fintype.card X = n) (hY : Fintype.card Y = n)
    (hlarge : (1 - δ) * n ≤ (leftCovered p B.tiles).card)
    (hpInj : ∀ j (x : X), x ∈ P → Set.InjOn (fun g => p g x) (F j))
    (hqInj : ∀ j (y : Y), y ∈ Q → Set.InjOn (fun g => q g y) (F j))
    (S : Finset G)
    (hF : ∀ s ∈ S, ∀ j, (HigmanFolner.boundary s (F j) : ℝ) ≤ η * (F j).card)
    (hpAct : ∀ s ∈ S, ∀ j (x : X), x ∈ P → ∀ g ∈ F j, p s (p g x) = p (s * g) x)
    (hqAct : ∀ s ∈ S, ∀ j (y : Y), y ∈ Q → ∀ g ∈ F j, q s (q g y) = q (s * g) y) :
    ∃ e : X ≃ Y, ∀ s ∈ S,
      (hammingDist (fun x : X => e (p s x)) (fun x => q s (e x)) : ℝ) ≤ 2 * δ * n := by
  classical
  let D := Σ t : B.tiles, ↥(t.val.core)
  let a (d : D) := p d.2.val d.1.val.leftCenter
  let b (d : D) := q d.2.val d.1.val.rightCenter
  have hai (t : Tile G X Y) (ht : t ∈ B.tiles) :
      Set.InjOn (fun g => p g t.leftCenter) t.core :=
    (hpInj _ _ (B.valid t ht).1).mono (B.valid t ht).2.2.1
  have hbi (t : Tile G X Y) (ht : t ∈ B.tiles) :
      Set.InjOn (fun g => q g t.rightCenter) t.core :=
    (hqInj _ _ (B.valid t ht).2.1).mono (B.valid t ht).2.2.1
  have ha : Function.Injective a := label_map_injective B.tiles Tile.core _ hai B.leftDisjoint
  have hb : Function.Injective b := label_map_injective B.tiles Tile.core _ hbi B.rightDisjoint
  obtain ⟨e, he⟩ := extend_injections (hX.trans hY.symm) a b ha hb
  have hmatch (t : Tile G X Y) (ht : t ∈ B.tiles) (g : G) (hg : g ∈ t.core) :
      e (p g t.leftCenter) = q g t.rightCenter := he ⟨⟨t, ht⟩, ⟨g, hg⟩⟩
  refine ⟨e, ?_⟩
  intro s hs
  let Fgood (t : Tile G X Y) := t.core.filter fun g => s * g ∈ t.core
  let Cgood (t : Tile G X Y) := (Fgood t).image fun g => p g t.leftCenter
  let U := B.tiles.biUnion Cgood
  have hgood (x : X) (hx : x ∈ U) : e (p s x) = q s (e x) := by
    obtain ⟨t, ht, hxt⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hxt
    obtain ⟨hg₁, hg₂⟩ := Finset.mem_filter.mp hg
    obtain ⟨htP, htQ, hc, _⟩ := B.valid t ht
    rw [hpAct s hs _ _ htP g (hc hg₁), hmatch t ht _ hg₂, hmatch t ht _ hg₁,
      hqAct s hs _ _ htQ g (hc hg₁)]
  have hsum : (U.card : ℝ) = ∑ t ∈ B.tiles, ((Fgood t).card : ℝ) := by
    have hd : (B.tiles : Set (Tile G X Y)).PairwiseDisjoint Cgood := by
      intro t ht u hu hne
      exact (B.leftDisjoint ht hu hne).mono
        (Finset.image_subset_image (Finset.filter_subset _ _))
        (Finset.image_subset_image (Finset.filter_subset _ _))
    have hcount : U.card = ∑ t ∈ B.tiles, (Fgood t).card := by
      change (B.tiles.biUnion Cgood).card = _
      rw [Finset.card_biUnion hd]
      exact Finset.sum_congr rfl fun t ht => Finset.card_image_of_injOn
        ((hai t ht).mono (Finset.filter_subset _ _))
    exact_mod_cast hcount
  have hbnd (t : Tile G X Y) (ht : t ∈ B.tiles) :
      (HigmanFolner.boundary s t.core : ℝ) ≤ 3 * η * (F (B.level t)).card := by
    obtain ⟨_, _, hc, hmass⟩ := B.valid t ht
    have hnat := boundary_core_le s hc
    have hh : (HigmanFolner.boundary s t.core : ℝ) ≤
        (HigmanFolner.boundary s (F (B.level t)) : ℝ) + (F (B.level t)).card - t.core.card := by
      have : (HigmanFolner.boundary s t.core : ℝ) ≤
          (HigmanFolner.boundary s (F (B.level t)) : ℝ) +
            ((F (B.level t)).card - t.core.card : ℕ) := by exact_mod_cast hnat
      rw [Nat.cast_sub (Finset.card_le_card hc)] at this
      linarith
    linarith [hF s hs (B.level t)]
  have hsumCore : ((leftCovered p B.tiles).card : ℝ) = ∑ t ∈ B.tiles, (t.core.card : ℝ) := by
    exact_mod_cast card_covered_left B hpInj
  have hupper : ((leftCovered p B.tiles).card : ℝ) ≤ n := by
    exact_mod_cast ((leftCovered p B.tiles).card_le_univ.trans_eq hX)
  have hsumMass : (1 - 2 * η) * ∑ t ∈ B.tiles, ((F (B.level t)).card : ℝ) ≤
      (leftCovered p B.tiles).card := by
    rw [Finset.mul_sum, hsumCore]
    exact Finset.sum_le_sum fun t ht => (B.valid t ht).2.2.2
  have hδβ : 3 * η ≤ δ * (1 - 2 * η) := by
    have hsquare : η * δ ≤ η := by
      have hηp : 0 ≤ η := by linarith
      simpa using mul_le_mul_of_nonneg_left hδ₁.le hηp
    nlinarith
  have hsumB : ∑ t ∈ B.tiles, (HigmanFolner.boundary s t.core : ℝ) ≤ δ * n := calc
    _ ≤ ∑ t ∈ B.tiles, 3 * η * ((F (B.level t)).card : ℝ) := Finset.sum_le_sum hbnd
    _ = (3 * η) * ∑ t ∈ B.tiles, ((F (B.level t)).card : ℝ) := (Finset.mul_sum ..).symm
    _ ≤ δ * (1 - 2 * η) * ∑ t ∈ B.tiles, ((F (B.level t)).card : ℝ) :=
      mul_le_mul_of_nonneg_right hδβ (by positivity)
    _ ≤ _ := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (hsumMass.trans hupper) hδ.le
  have hbalance : (U.card : ℝ) +
      (∑ t ∈ B.tiles, (HigmanFolner.boundary s t.core : ℝ)) =
        (leftCovered p B.tiles).card := by
    rw [hsum, ← Finset.sum_add_distrib, hsumCore]
    exact Finset.sum_congr rfl fun t _ => by
      exact_mod_cast t.core.card_filter_add_card_filter_not (fun g => s * g ∈ t.core)
  let E := Finset.univ.filter fun x : X => e (p s x) ≠ q s (e x)
  have hds : Disjoint E U := by
    apply Finset.disjoint_left.mpr
    intro x hx hu
    exact (Finset.mem_filter.mp hx).2 (hgood x hu)
  have htot : (E.card : ℝ) + U.card ≤ n := by
    have he := (E ∪ U).card_le_univ
    rw [Finset.card_union_of_disjoint hds, hX] at he
    exact_mod_cast he
  change (E.card : ℝ) ≤ 2 * δ * n
  linarith

end Match

end SoficCoupledPacking

namespace SoficCoupledPacking

open scoped BigOperators

section Models

variable {G X : Type*} [Group G] [DecidableEq G] [Fintype X] [DecidableEq X]

/-- Raw finite error bounds on the tested multiplication and separation pairs. -/
structure Approximates (p : G → Equiv.Perm X) (E : Finset G) (τ : ℝ) : Prop where
  multiply : ∀ g ∈ E, ∀ h ∈ E, g * h ∈ E →
    (hammingDist (⇑(p g * p h)) (⇑(p (g * h))) : ℝ) ≤ τ * Fintype.card X
  separate : ∀ g ∈ E, ∀ h ∈ E, g ≠ h →
    ((Finset.univ.filter fun x : X => p g x = p h x).card : ℝ) ≤ τ * Fintype.card X

/-- Outside a finite union of exceptional sets, all tested equations hold
pointwise and the tested group elements have distinct images. -/
theorem good_centres {p : G → Equiv.Perm X} {E : Finset G} {τ η : ℝ}
    (h : Approximates p E τ) (hτ : 0 ≤ τ) (hbudget : τ * (2 * (E.card : ℝ)^2) ≤ η) :
    ∃ P : Finset X, (1 - η) * Fintype.card X ≤ P.card ∧
      (∀ x ∈ P, Set.InjOn (fun g => p g x) E) ∧
      ∀ x ∈ P, ∀ g ∈ E, ∀ h ∈ E, g * h ∈ E → p g (p h x) = p (g * h) x := by
  classical
  let pairs := E ×ˢ E
  let M (v : G × G) : Finset X := if v.1 * v.2 ∈ E then
    Finset.univ.filter fun x => p v.1 (p v.2 x) ≠ p (v.1 * v.2) x else ∅
  let D (v : G × G) : Finset X := if v.1 ≠ v.2 then
    Finset.univ.filter fun x => p v.1 x = p v.2 x else ∅
  let Lost := pairs.biUnion M ∪ pairs.biUnion D
  let P := (Finset.univ : Finset X) \ Lost
  have hM (v : G × G) (hv : v ∈ pairs) : ((M v).card : ℝ) ≤ τ * Fintype.card X := by
    obtain ⟨h₁,h₂⟩ := Finset.mem_product.mp hv
    by_cases he : v.1 * v.2 ∈ E
    · have hEq : (M v).card = hammingDist (⇑(p v.1 * p v.2)) (⇑(p (v.1 * v.2))) := by
        unfold hammingDist
        apply congrArg Finset.card
        have hM : M v = Finset.univ.filter
            (fun x => p v.1 (p v.2 x) ≠ p (v.1 * v.2) x) := if_pos he
        rw [hM]
        apply Finset.filter_congr
        intro x _
        rfl
      rw [hEq]
      exact h.multiply v.1 h₁ v.2 h₂ he
    · simpa [M, he] using (mul_nonneg hτ (by positivity : (0 : ℝ) ≤ Fintype.card X))
  have hD (v : G × G) (hv : v ∈ pairs) : ((D v).card : ℝ) ≤ τ * Fintype.card X := by
    obtain ⟨h₁,h₂⟩ := Finset.mem_product.mp hv
    by_cases he : v.1 ≠ v.2
    · simpa only [D, if_pos he] using h.separate v.1 h₁ v.2 h₂ he
    · have hzero : D v = ∅ := if_neg he
      rw [hzero, Finset.card_empty, Nat.cast_zero]
      positivity
  have hcount (A : G × G → Finset X)
      (ha : ∀ v ∈ pairs, ((A v).card : ℝ) ≤ τ * Fintype.card X) :
      ((pairs.biUnion A).card : ℝ) ≤ (E.card : ℝ)^2 * (τ * Fintype.card X) := calc
    _ ≤ ∑ v ∈ pairs, ((A v).card : ℝ) := by exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _v ∈ pairs, τ * (Fintype.card X : ℝ) := Finset.sum_le_sum ha
    _ = _ := by simp [pairs, Finset.card_product, pow_two]
  have hLost : (Lost.card : ℝ) ≤ η * Fintype.card X := by
    have hx : (Lost.card : ℝ) ≤ ((pairs.biUnion M).card : ℝ) + (pairs.biUnion D).card := by
      exact_mod_cast Finset.card_union_le (pairs.biUnion M) (pairs.biUnion D)
    have hb := mul_le_mul_of_nonneg_right hbudget (by positivity : (0 : ℝ) ≤ Fintype.card X)
    nlinarith [hcount M hM, hcount D hD]
  have hP : P.card + Lost.card = Fintype.card X := by
    rw [← Finset.card_univ]
    exact Finset.card_sdiff_add_card_eq_card (Finset.subset_univ Lost)
  refine ⟨P, ?_, ?_, ?_⟩
  · have hp : (P.card : ℝ) + Lost.card = Fintype.card X := by exact_mod_cast hP
    linarith
  · intro x hx g hg k hk eqVal
    by_contra hne
    apply (Finset.mem_sdiff.mp hx).2
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨(g,k), Finset.mem_product.mpr ⟨hg,hk⟩, by simp [D, hne, eqVal]⟩)
  · intro x hx g hg k hk hmul
    by_contra he
    apply (Finset.mem_sdiff.mp hx).2
    exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr
      ⟨(g,k), Finset.mem_product.mpr ⟨hg,hk⟩, by simp [M, hmul, he]⟩)

end Models

section FolnerShapes

variable {G : Type*} [Group G] [DecidableEq G]

private theorem relativeLabels_le (F H : Finset G) :
    (relativeLabels F H).card ≤ H.card + ∑ f ∈ F, HigmanFolner.boundary f H := by
  let B (f : G) := (H.filter fun h => f⁻¹ * h ∉ H).image fun h => f⁻¹ * h
  have hsub : relativeLabels F H ⊆ H ∪ F.biUnion B := by
    intro x hx
    obtain ⟨⟨f,h⟩, hh, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hf, hh⟩ := Finset.mem_product.mp hh
    by_cases he : f⁻¹ * h ∈ H
    · exact Finset.mem_union_left _ he
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨f, hf, Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hh, he⟩)⟩)
  calc
    _ ≤ (H ∪ F.biUnion B).card := Finset.card_le_card hsub
    _ ≤ H.card + (F.biUnion B).card := Finset.card_union_le _ _
    _ ≤ H.card + ∑ f ∈ F, (B f).card := Nat.add_le_add_left Finset.card_biUnion_le _
    _ ≤ _ := by
      apply Nat.add_le_add_left
      apply Finset.sum_le_sum
      intro f _
      rw [← HigmanFolner.boundary_inv f]
      exact Finset.card_image_le

private theorem choose_shapes
    (hFolner : ∀ K : Finset G, ∀ η : ℝ, 0 < η → ∃ H : Finset G, H.Nonempty ∧
      (∑ g ∈ K, (HigmanFolner.boundary g H : ℝ)) ≤ η * H.card)
    (S : Finset G) (η : ℝ) (hη : 0 < η) (k : ℕ) :
    ∃ F : Fin k → Finset G, (∀ j, (F j).Nonempty) ∧
      (∀ s ∈ S, ∀ j, (HigmanFolner.boundary s (F j) : ℝ) ≤ η * (F j).card) ∧
      ∀ i j, i < j → ((relativeLabels (F i) (F j)).card : ℝ) ≤ (1 + η) * (F j).card := by
  induction k with
  | zero => exact ⟨Fin.elim0, fun i => Fin.elim0 i, fun _ _ i => Fin.elim0 i,
      fun i => Fin.elim0 i⟩
  | succ k ih =>
    obtain ⟨F, hF, hB, hrel⟩ := ih
    let A := S ∪ Finset.univ.biUnion F
    obtain ⟨H, hH, hsum⟩ := hFolner A η hη
    let FF : Fin (k + 1) → Finset G := Fin.lastCases H F
    have hHs (s : G) (hs : s ∈ S) : (HigmanFolner.boundary s H : ℝ) ≤ η * H.card :=
      (Finset.single_le_sum (fun _ _ => by positivity)
        (Finset.mem_union_left _ hs)).trans hsum
    have hHr (i : Fin k) : ((relativeLabels (F i) H).card : ℝ) ≤ (1 + η) * H.card := by
      have hsub : F i ⊆ A :=
        (Finset.subset_biUnion_of_mem F (Finset.mem_univ i)).trans Finset.subset_union_right
      have hh : (∑ f ∈ F i, (HigmanFolner.boundary f H : ℝ)) ≤ η * H.card :=
        (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)).trans hsum
      have hc : ((relativeLabels (F i) H).card : ℝ) ≤
          (H.card : ℝ) + ∑ f ∈ F i, (HigmanFolner.boundary f H : ℝ) := by
        exact_mod_cast relativeLabels_le (F i) H
      linarith
    refine ⟨FF, ?_, ?_, ?_⟩
    · intro j
      refine Fin.lastCases ?_ ?_ j
      · simpa [FF] using hH
      · intro j
        simpa [FF] using hF j
    · intro s hs j
      refine Fin.lastCases ?_ ?_ j
      · simpa [FF] using hHs s hs
      · intro j
        simpa [FF] using hB s hs j
    · intro i j
      refine Fin.lastCases ?_ ?_ i
      · intro hij
        exact (not_lt_of_ge (Fin.le_last j) hij).elim
      · intro i
        refine Fin.lastCases ?_ ?_ j
        · intro _
          simpa [FF] using hHr i
        · intro j h
          simpa [FF] using hrel i j (Fin.castSucc_lt_castSucc_iff.mp h)

end FolnerShapes

/-- The finitary conjugacy conclusion for two models of a group with finite
Følner sets. The model test set and error bound are independent of model size. -/
theorem rectify {G : Type*} [Group G] [DecidableEq G]
    (hFolner : ∀ K : Finset G, ∀ η : ℝ, 0 < η → ∃ H : Finset G, H.Nonempty ∧
      (∑ g ∈ K, (HigmanFolner.boundary g H : ℝ)) ≤ η * H.card)
    (S : Finset G) (δ : ℝ) (hδ : 0 < δ) (hδ₁ : δ < 1) :
    ∃ E : Finset G, ∃ τ > 0,
      ∀ {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
        (p : G → Equiv.Perm X) (q : G → Equiv.Perm Y),
        Fintype.card X = Fintype.card Y → Approximates p E τ → Approximates q E τ →
        ∃ e : X ≃ Y, ∀ s ∈ S,
          (hammingDist (fun x : X => e (p s x)) (fun x => q s (e x)) : ℝ) ≤
            2 * δ * Fintype.card X := by
  classical
  let η := δ / 16
  have hη : 0 < η := by positivity
  let rate := η * (δ / 2)
  have hrate : 0 < rate := by positivity
  obtain ⟨k, hkB⟩ := exists_nat_gt (max 1 ((1 - δ) / rate))
  have hk : 0 < k := by
    have he := (le_max_left (1 : ℝ) ((1 - δ) / rate)).trans_lt hkB
    exact_mod_cast (show (0 : ℝ) < k by linarith)
  have hbig : 1 - δ ≤ (k : ℝ) * rate :=
    ((div_lt_iff₀ hrate).mp ((le_max_right _ _).trans_lt hkB)).le
  obtain ⟨F, hF, hB, hrel⟩ := choose_shapes hFolner S η hη k
  let U := Finset.univ.biUnion F
  let V := (S ×ˢ U).image fun gh => gh.1 * gh.2
  let E := S ∪ U ∪ V ∪ relativeLabels U U
  let C := 2 * (E.card : ℝ)^2
  let τ := η / (C + 1)
  have hτ : 0 < τ := by positivity
  have hbudget : τ * C ≤ η := calc
    _ ≤ τ * (C + 1) := mul_le_mul_of_nonneg_left (by linarith) hτ.le
    _ = η := div_mul_cancel₀ η (by positivity)
  refine ⟨E, τ, hτ, ?_⟩
  intro X Y _ _ _ _ p q hcard hp hq
  obtain ⟨P, hP, hPI, hPM⟩ := good_centres hp hτ.le hbudget
  obtain ⟨Q, hQ, hQI, hQM⟩ := good_centres hq hτ.le hbudget
  have hU (j) : F j ⊆ U := Finset.subset_biUnion_of_mem F (Finset.mem_univ _)
  have hUE : U ⊆ E := by
    intro g hg
    simp [E, hg]
  have hSE : S ⊆ E := by
    intro g hg
    simp [E, hg]
  have hRelE : relativeLabels U U ⊆ E := Finset.subset_union_right
  have hVE : V ⊆ E := Finset.subset_union_right.trans Finset.subset_union_left
  have hInv {Z : Type} (m : G → Equiv.Perm Z) (x : Z)
      (hm : ∀ g ∈ E, ∀ h ∈ E, g * h ∈ E → m g (m h x) = m (g * h) x)
      (i j) (f : G) (hf : f ∈ F i) (g : G) (hg : g ∈ F j) :
      (m f).symm (m g x) = m (f⁻¹ * g) x := by
    have hr : f⁻¹ * g ∈ E :=
      hRelE (Finset.mem_image.mpr
        ⟨(f,g), Finset.mem_product.mpr ⟨hU i hf, hU j hg⟩, rfl⟩)
    have hx : f * (f⁻¹ * g) ∈ E := by simpa using hUE (hU j hg)
    have hm' := hm f (hUE (hU i hf)) (f⁻¹ * g) hr hx
    simp only [mul_inv_cancel_left] at hm'
    rw [← hm', Equiv.symm_apply_apply]
  have hProd {Z : Type} (m : G → Equiv.Perm Z) (x : Z)
      (hm : ∀ g ∈ E, ∀ h ∈ E, g * h ∈ E → m g (m h x) = m (g * h) x)
      (s : G) (hs : s ∈ S) (j) (g : G) (hg : g ∈ F j) :
      m s (m g x) = m (s * g) x :=
    hm s (hSE hs) g (hUE (hU j hg))
      (hVE (Finset.mem_image.mpr ⟨(s,g), Finset.mem_product.mpr ⟨hs, hU j hg⟩, rfl⟩))
  have hpI (j) (x : X) (hx : x ∈ P) : Set.InjOn (fun g => p g x) (F j) :=
    (hPI x hx).mono (hU j |>.trans hUE)
  have hqI (j) (x : Y) (hx : x ∈ Q) : Set.InjOn (fun g => q g x) (F j) :=
    (hQI x hx).mono (hU j |>.trans hUE)
  obtain ⟨B, hLarge, _⟩ := pack_scales hk p q F hF P Q hδ hδ₁ (rfl : η = δ / 16)
    hbig hP (by simpa only [hcard] using hQ) hrel hpI hqI
    (fun i j x hx => hInv p x (hPM x hx) i j) (fun i j x hx => hInv q x (hQM x hx) i j)
  exact matching_of_packing hδ hδ₁ rfl B rfl hcard.symm hLarge hpI hqI S hB
    (fun s hs j x hx => hProd p x (hPM x hx) s hs j)
    (fun s hs j x hx => hProd q x (hQM x hx) s hs j)

end SoficCoupledPacking

/-
# Amplifying the separation of a sofic approximation
-/

open Filter
open scoped BigOperators Topology

namespace SoficAmplification

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The fraction of input points where two permutations agree. -/
noncomputable def agreement (f g : Equiv.Perm X) : ℝ :=
  ((Finset.univ.filter fun x => f x = g x).card : ℝ) / Fintype.card X

/-- The fraction of input points where two permutations disagree. -/
noncomputable def distance (f g : Equiv.Perm X) : ℝ :=
  (hammingDist (⇑f) (⇑g) : ℝ) / Fintype.card X

theorem agreement_add_distance [Nonempty X] (f g : Equiv.Perm X) :
    agreement f g + distance f g = 1 := by
  have h := (Finset.univ : Finset X).card_filter_add_card_filter_not (fun x => f x = g x)
  have hp : (Fintype.card X : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  unfold agreement distance hammingDist
  rw [← add_div]
  have h' : ((Finset.univ.filter fun x => f x = g x).card : ℝ) +
      ((Finset.univ.filter fun x => f x ≠ g x).card : ℝ) = Fintype.card X := by
    exact_mod_cast (by simpa using h :
      (Finset.univ.filter fun x => f x = g x).card +
        (Finset.univ.filter fun x => f x ≠ g x).card = Fintype.card X)
  rw [h', div_self hp]

theorem agreement_nonneg (f g : Equiv.Perm X) : 0 ≤ agreement f g := by
  unfold agreement
  positivity

theorem distance_nonneg (f g : Equiv.Perm X) : 0 ≤ distance f g := by
  unfold distance
  positivity

theorem distance_le_one [Nonempty X] (f g : Equiv.Perm X) : distance f g ≤ 1 := by
  linarith [agreement_nonneg f g, agreement_add_distance f g]

/-- Act independently with the same permutation on every coordinate. -/
def tensor (m : ℕ) (f : Equiv.Perm X) : Equiv.Perm (Fin m → X) :=
  Equiv.piCongrRight fun _ => f

omit [Fintype X] [DecidableEq X] in
@[simp] theorem tensor_apply (m : ℕ) (f : Equiv.Perm X) (x : Fin m → X) (i : Fin m) :
    tensor m f x i = f (x i) := rfl

omit [Fintype X] [DecidableEq X] in
@[simp] theorem tensor_mul (m : ℕ) (f g : Equiv.Perm X) :
    tensor m (f * g) = tensor m f * tensor m g := by
  apply Equiv.ext
  intro x
  funext i
  rfl

omit [Fintype X] [DecidableEq X] in
@[simp] theorem tensor_one (m : ℕ) : tensor m (1 : Equiv.Perm X) = 1 := by
  apply Equiv.ext
  intro x
  funext i
  rfl

/-- Coordinatewise agreement multiplies under taking finite tensor powers. -/
theorem agreement_tensor (m : ℕ) (f g : Equiv.Perm X) :
    agreement (tensor m f) (tensor m g) = (agreement f g) ^ m := by
  let S := Finset.univ.filter fun x => f x = g x
  have hs : (Finset.univ.filter fun x => tensor m f x = tensor m g x) =
      Fintype.piFinset (fun _ : Fin m => S) := by
    ext x
    simp [S, funext_iff]
  unfold agreement
  rw [hs, Fintype.card_piFinset_const, Fintype.card_pi_const]
  push_cast
  rw [div_pow]

theorem distance_tensor_le [Nonempty X] (m : ℕ) (f g : Equiv.Perm X) :
    distance (tensor m f) (tensor m g) ≤ m * distance f g := by
  have ht := agreement_add_distance (tensor m f) (tensor m g)
  rw [agreement_tensor] at ht
  have hd : agreement f g = 1 + (-distance f g) := by
    linarith [agreement_add_distance f g]
  have hb := one_add_mul_le_pow (show -2 ≤ -distance f g by
    linarith [distance_le_one f g]) m
  rw [← hd] at hb
  linarith

/-- The pinned constant-separation definition gives finite approximations with
arbitrarily small agreement between the images of distinct elements. -/
theorem arbitrarily_separated {G : Type*} [Group G] [Nontrivial G]
    (hG : Green100.IsSofic G) (E : Finset G) (δ : ℝ) (hδ : 0 < δ) :
    ∃ (m n : ℕ), 0 < n ∧ ∃ θ : G → Equiv.Perm (Fin m → Fin n),
      (∀ g ∈ E, ∀ h ∈ E, g * h ∈ E → distance (θ g * θ h) (θ (g * h)) ≤ δ) ∧
      (1 ∈ E → distance (θ 1) 1 ≤ δ) ∧
      ∀ g ∈ E, ∀ h ∈ E, g ≠ h → agreement (θ g) (θ h) ≤ δ := by
  classical
  have hlim : Tendsto (fun m : ℕ => (3 / 4 : ℝ) ^ m) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  obtain ⟨m, hm⟩ := (hlim.eventually (gt_mem_nhds hδ)).exists
  let ε := δ / ((m : ℝ) + 1)
  have hε : 0 < ε := by positivity
  obtain ⟨x, y, hxy⟩ := exists_pair_ne G
  let F := insert x (insert y E)
  have hEF : E ⊆ F := fun g hg => Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hg)
  obtain ⟨n, θ, hmul, hone, hsep⟩ := hG F ε hε
  have hn : 0 < n := by
    by_contra! h
    have hzero : n = 0 := by omega
    subst n
    have hc := hsep x (Finset.mem_insert_self _ _) y
      (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)) hxy
    norm_num [Green100.hammingDistNorm] at hc
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hbound (v : ℝ) (hv : v ≤ ε) : (m : ℝ) * v ≤ δ := calc
    _ ≤ (m : ℝ) * ε := mul_le_mul_of_nonneg_left hv (by positivity)
    _ ≤ ((m : ℝ) + 1) * ε := mul_le_mul_of_nonneg_right (by linarith) hε.le
    _ = δ := by dsimp [ε]; field_simp
  have hdist (f g : Equiv.Perm (Fin n)) (hd : Green100.hammingDistNorm f g < ε) :
      distance (tensor m f) (tensor m g) ≤ δ := by
    have hv : distance f g ≤ ε := by
      simpa [distance, Green100.hammingDistNorm] using hd.le
    exact (distance_tensor_le m f g).trans (hbound _ hv)
  refine ⟨m, n, hn, fun g => tensor m (θ g), ?_, ?_, ?_⟩
  · intro g hg h hh hhg
    rw [← tensor_mul]
    exact hdist _ _ (hmul g (hEF hg) h (hEF hh) (hEF hhg))
  · intro he
    rw [← tensor_one m]
    exact hdist _ _ (hone (hEF he))
  · intro g hg h hh hne
    have hsep' : (1 / 4 : ℝ) ≤ distance (θ g) (θ h) := by
      simpa [distance, Green100.hammingDistNorm] using hsep g (hEF hg) h (hEF hh) hne
    have hag : agreement (θ g) (θ h) ≤ 3 / 4 := by
      linarith [agreement_add_distance (θ g) (θ h)]
    rw [agreement_tensor]
    exact (pow_le_pow_left₀ (agreement_nonneg _ _) hag _).trans hm.le

end SoficAmplification

/-
# Exact cyclic symmetry of finite Higman approximations

The generator rotation of the Higman presentation can be implemented exactly
by a cyclic permutation of four copies of a finite approximation.
-/

namespace HigmanRotation

/-- Generator of the pinned presentation. -/
def gen (i : ZMod 4) : Green100.HigmanGroup := PresentedGroup.of i

theorem defining_relation (i : ZMod 4) :
    (gen (i + 1))⁻¹ * gen i * gen (i + 1) = gen i ^ 2 := by
  have h : (FreeGroup.of (i + 1))⁻¹ * FreeGroup.of i * FreeGroup.of (i + 1) *
      (FreeGroup.of i ^ 2)⁻¹ ∈
      Set.range (fun j : ZMod 4 => (FreeGroup.of (j + 1))⁻¹ * FreeGroup.of j *
        FreeGroup.of (j + 1) * (FreeGroup.of j ^ 2)⁻¹) := Set.mem_range_self i
  simpa only [gen, PresentedGroup.of, map_mul, map_inv, map_pow] using
    PresentedGroup.mk_eq_mk_of_mul_inv_mem h

/-- Relabel all generators by a fixed cyclic shift. -/
def shift (j : ZMod 4) : Green100.HigmanGroup →* Green100.HigmanGroup :=
  PresentedGroup.toGroup (f := fun i => gen (i + j)) (by
    rintro _ ⟨i, rfl⟩
    simp only [map_mul, map_inv, FreeGroup.lift_apply_of, map_pow]
    rw [add_right_comm i 1 j, defining_relation, mul_inv_cancel])

@[simp] theorem shift_gen (i j : ZMod 4) : shift j (gen i) = gen (i + j) := rfl

@[simp] theorem shift_zero (g : Green100.HigmanGroup) : shift 0 g = g := by
  have he : shift 0 = MonoidHom.id Green100.HigmanGroup := by
    apply PresentedGroup.ext
    intro i
    change gen (i + 0) = gen i
    rw [add_zero]
  rw [he, MonoidHom.id_apply]

@[simp] theorem shift_shift (i j : ZMod 4) (g : Green100.HigmanGroup) :
    shift i (shift j g) = shift (j + i) g := by
  have he : (shift i).comp (shift j) = shift (j + i) := by
    apply PresentedGroup.ext
    intro k
    change gen (k + j + i) = gen (k + (j + i))
    rw [add_assoc]
  exact DFunLike.congr_fun he g

/-- Apply the given permutation independently on each cyclically indexed copy. -/
def onCopies {α : Type*} (φ : ZMod 4 → Equiv.Perm α) : Equiv.Perm (ZMod 4 × α) where
  toFun x := (x.1, φ x.1 x.2)
  invFun x := (x.1, (φ x.1).symm x.2)
  left_inv x := by simp
  right_inv x := by simp

/-- The exact order-four rotation of the copies. -/
def cycle (α : Type*) : Equiv.Perm (ZMod 4 × α) :=
  (Equiv.addRight (-1 : ZMod 4)).prodCongr (Equiv.refl α)

theorem cycle_four (α : Type*) : cycle α ^ 4 = 1 := by
  apply Equiv.ext
  intro x
  have h : (4 : ZMod 4) = 0 := by decide
  change (x.1 + -1 + -1 + -1 + -1, x.2) = (x.1, x.2)
  congr 1
  calc
    x.1 + -1 + -1 + -1 + -1 = x.1 - 4 := by ring
    _ = x.1 := by rw [h, sub_zero]

/-- A finite approximation twisted independently on the four copies. -/
def rotateApprox {α : Type*} (θ : Green100.HigmanGroup → Equiv.Perm α)
    (g : Green100.HigmanGroup) : Equiv.Perm (ZMod 4 × α) :=
  onCopies fun j => θ (shift j g)

theorem cycle_rotateApprox {α : Type*}
    (θ : Green100.HigmanGroup → Equiv.Perm α) (g : Green100.HigmanGroup) :
    cycle α * rotateApprox θ g = rotateApprox θ (shift 1 g) * cycle α := by
  apply Equiv.ext
  intro x
  change (x.1 + -1, θ (shift x.1 g) x.2) =
    (x.1 + -1, θ (shift (x.1 + -1) (shift 1 g)) x.2)
  rw [shift_shift, add_comm 1, neg_add_cancel_right]

end HigmanRotation

/-
# Extracting the order-four map from finite permutation data

The two approximate affine permutations and the exact conjugation relation
give the required recurrence by excluding their disagreement sets.
-/

namespace HigmanExtraction

/-- Precomposition by a bijection preserves the number of disagreements. -/
theorem hamming_reindex {α β γ : Type*} [Fintype α] [Fintype β] [DecidableEq γ]
    (e : α ≃ β) (f g : β → γ) :
    hammingDist (f ∘ e) (g ∘ e) = hammingDist f g := by
  unfold hammingDist
  refine Finset.card_bij (fun i _ => e i) ?_ ?_ ?_
  · intro i hi
    simpa [Function.comp_def] using hi
  · intro i _ j _ he
    exact e.injective he
  · intro j hj
    exact ⟨e.symm j, by simpa [Function.comp_def] using hj, e.apply_symm_apply j⟩

/-- The pinned conclusion follows from an exactly cyclic conjugation that
matches the two canonical affine permutations away from small exceptional sets. -/
theorem extract {n : ℕ} [NeZero n] (ε : ℝ) (u : (ZMod n)ˣ)
    (hu : (u : ZMod n) = 2) (s a b : Equiv.Perm (ZMod n))
    (hpow : s ^ 4 = 1) (hconj : s * a = b * s)
    (herr : (hammingDist (⇑a) (fun x => x - 1) : ℝ) +
      (hammingDist (⇑b) (fun x => (↑u⁻¹ : ZMod n) * x) : ℝ) ≤ ε * n) :
    ∃ f : ZMod n → ZMod n, (1 - ε) * n ≤ Set.ncard {x | f (x + 1) = 2 * f x} ∧
      ∀ x, f (f (f (f x))) = x := by
  classical
  let e := Equiv.addRight (1 : ZMod n)
  let T := Finset.univ.filter fun x : ZMod n => s (x + 1) ≠ 2 * s x
  let A := Finset.univ.filter fun x : ZMod n => a (x + 1) ≠ x
  let B := Finset.univ.filter fun x : ZMod n => b (s (x + 1)) ≠ (↑u⁻¹ : ZMod n) * s (x + 1)
  have hA : A.card = hammingDist (⇑a) (fun x => x - 1) := by
    rw [← hamming_reindex e]
    simp [A, e, hammingDist]
  have hB : B.card = hammingDist (⇑b) (fun x => (↑u⁻¹ : ZMod n) * x) := by
    exact hamming_reindex (e.trans s) (⇑b) (fun x => (↑u⁻¹ : ZMod n) * x)
  have hfail : T ⊆ A ∪ B := by
    intro x hx
    simp only [T, A, B, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    by_contra! h
    have he := congrArg (fun σ : Equiv.Perm (ZMod n) => σ (x + 1)) hconj
    change s (a (x + 1)) = b (s (x + 1)) at he
    rw [h.1, h.2] at he
    apply hx
    have he' := congrArg (fun z : ZMod n => (u : ZMod n) * z) he
    change (u : ZMod n) * s x = (u : ZMod n) * ((↑u⁻¹ : ZMod n) * s (x + 1)) at he'
    have huu : (u : ZMod n) * (↑u⁻¹ : ZMod n) = 1 := u.mul_inv
    rw [← mul_assoc, huu, one_mul, hu] at he'
    exact he'.symm
  have hcount : T.card ≤ A.card + B.card :=
    (Finset.card_le_card hfail).trans (Finset.card_union_le _ _)
  let U := Finset.univ.filter fun x : ZMod n => s (x + 1) = 2 * s x
  have hcard : U.card + T.card = n := by
    simpa only [U, T, Finset.card_univ, ZMod.card] using
      (Finset.univ : Finset (ZMod n)).card_filter_add_card_filter_not
        (fun x => s (x + 1) = 2 * s x)
  have hn : Set.ncard {x : ZMod n | s (x + 1) = 2 * s x} = U.card := by
    rw [← Set.ncard_coe_finset]
    congr
    ext x
    simp [U]
  have hcount' : (T.card : ℝ) ≤ (A.card : ℝ) + (B.card : ℝ) := by exact_mod_cast hcount
  rw [hA, hB] at hcount'
  have hcard' : (U.card : ℝ) + (T.card : ℝ) = n := by exact_mod_cast hcard
  refine ⟨s, ?_, ?_⟩
  · rw [hn]
    linarith
  · intro x
    have h := congrArg (fun σ : Equiv.Perm (ZMod n) => σ x) hpow
    exact h

end HigmanExtraction

namespace HigmanModels

open HigmanAdjacent HigmanRotation SoficAmplification SoficCoupledPacking
open scoped BigOperators

private theorem card_filter_product {I X : Type*} [Fintype I] [Fintype X]
    (p : I → X → Prop) [DecidablePred (fun z : I × X => p z.1 z.2)]
    [∀ i, DecidablePred (p i)] :
    (Finset.univ.filter fun z : I × X => p z.1 z.2).card =
      ∑ i, (Finset.univ.filter (p i)).card := by
  let e := Equiv.sigmaEquivProd I X
  have h : (Finset.univ.filter fun z : I × X => p z.1 z.2) =
      (Finset.univ.sigma (fun i => Finset.univ.filter (p i))).map e.toEmbedding := by
    ext z
    simp [Finset.mem_map_equiv, Finset.mem_sigma, e, Equiv.sigmaEquivProd]
  rw [h, Finset.card_map, Finset.card_sigma]

private theorem card_filter_sum {X Y : Type*} [Fintype X] [Fintype Y]
    (p : X → Prop) (q : Y → Prop) [DecidablePred p] [DecidablePred q]
    [DecidablePred (Sum.elim p q)] :
    (Finset.univ.filter (Sum.elim p q)).card =
      (Finset.univ.filter p).card + (Finset.univ.filter q).card := by
  have h : (Finset.univ.filter (Sum.elim p q)) =
      (Finset.univ.filter p).disjSum (Finset.univ.filter q) := by
    ext z
    cases z <;> simp
  rw [h, Finset.card_disjSum]

private theorem shift_injective (i : ZMod 4) : Function.Injective (shift i) := by
  apply Function.LeftInverse.injective (g := shift (-i))
  intro g
  simp

private theorem card_four {X : Type*} [Fintype X] :
    Fintype.card (ZMod 4 × X) = 4 * Fintype.card X := by simp

/-- Repeat the given action on equal-sized blocks and fix the remaining points. -/
def pad {X : Type*} (r d : ℕ) :
    Equiv.Perm X →* Equiv.Perm ((Fin r × X) ⊕ Fin d) where
  toFun p := ((Equiv.refl (Fin r)).prodCongr p).sumCongr (Equiv.refl (Fin d))
  map_one' := by
    apply Equiv.ext
    rintro (⟨i,x⟩ | j) <;> rfl
  map_mul' p q := by
    apply Equiv.ext
    rintro (⟨i,x⟩ | j) <;> rfl

private theorem pad_hamming {X : Type*} [Fintype X] [DecidableEq X]
    (r d : ℕ) (p q : Equiv.Perm X) :
    hammingDist (⇑(pad r d p)) (⇑(pad r d q)) = r * hammingDist (⇑p) (⇑q) := by
  classical
  unfold hammingDist
  change (Finset.univ.filter fun z : (Fin r × X) ⊕ Fin d =>
    pad r d p z ≠ pad r d q z).card = _
  have he : (Finset.univ.filter fun z : (Fin r × X) ⊕ Fin d => pad r d p z ≠ pad r d q z) =
      Finset.univ.filter
        (Sum.elim (fun z : Fin r × X => p z.2 ≠ q z.2) (fun _ : Fin d => False)) := by
    ext z
    rcases z with (⟨i,x⟩ | j) <;> simp [pad, Prod.map]
  rw [he, card_filter_sum, card_filter_product (fun (_ : Fin r) x => p x ≠ q x)]
  simp

private theorem pad_agree {X : Type*} [Fintype X] [DecidableEq X]
    (r d : ℕ) (p q : Equiv.Perm X) :
    (Finset.univ.filter fun x => pad r d p x = pad r d q x).card =
      r * (Finset.univ.filter fun x => p x = q x).card + d := by
  classical
  have he : (Finset.univ.filter fun z : (Fin r × X) ⊕ Fin d => pad r d p z = pad r d q z) =
      Finset.univ.filter
        (Sum.elim (fun z : Fin r × X => p z.2 = q z.2) (fun _ : Fin d => True)) := by
    ext z
    rcases z with (⟨i,x⟩ | j) <;> simp [pad, Prod.map]
  rw [he, card_filter_sum, card_filter_product (fun (_ : Fin r) x => p x = q x)]
  simp

noncomputable section

local instance : DecidableEq BS := Classical.decEq _

/-- An arbitrary-sized finite model with an exact fourth-order intertwiner for
the two adjacent Baumslag–Solitar generators. -/
structure FiniteCyclicModel (n : ℕ) (E : Finset BS) (τ : ℝ) where
  X : Type
  finite : Fintype X
  decEq : DecidableEq X
  card_eq : @Fintype.card X finite = n
  action : BS → Equiv.Perm X
  approx : @Approximates BS X _ finite decEq action E τ
  step : Equiv.Perm X
  fourth : step ^ 4 = 1
  intertwine : step * action trans = action scale * step

/-- Soficity supplies such a finite model at every sufficiently large size.
The rotation is exact because it acts by rotating fibers, including after padding. -/
theorem eventually_cyclic_models (hH : Green100.IsSofic Green100.HigmanGroup)
    (E : Finset BS) {τ : ℝ} (hτ : 0 < τ) :
    ∃ N : ℕ, ∀ n ≥ N, Nonempty (FiniteCyclicModel n E τ) := by
  classical
  have : Nontrivial Green100.HigmanGroup := higman_nontrivial
  let D : Finset Green100.HigmanGroup := (Finset.univ : Finset (ZMod 4)).biUnion
    fun i => E.image fun g => shift i (adjacent g)
  have hD (i : ZMod 4) (g : BS) (hg : g ∈ E) : shift i (adjacent g) ∈ D :=
    Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_image_of_mem _ hg⟩
  obtain ⟨m, n₀, hn₀, θ, hθM, _, hθD⟩ :=
    arbitrarily_separated hH D (τ / 2) (by positivity)
  let B := Fin m → Fin n₀
  let A := ZMod 4 × B
  let c := Fintype.card A
  have hB : 0 < Fintype.card B := by
    simp [B, pow_pos hn₀]
  have hB' : (0 : ℝ) < Fintype.card B := by exact_mod_cast hB
  have hcEq : c = 4 * Fintype.card B := card_four
  have hc : 0 < c := by rw [hcEq]; positivity
  let φ (g : BS) : Equiv.Perm A := rotateApprox θ (adjacent g)
  have hφM (g h : BS) (hg : g ∈ E) (hh : h ∈ E) (hgh : g * h ∈ E) :
      (hammingDist (⇑(φ g * φ h)) (⇑(φ (g * h))) : ℝ) ≤ (τ / 2) * c := by
    have ha (i : ZMod 4) : (hammingDist
        (⇑(θ (shift i (adjacent g)) * θ (shift i (adjacent h))))
        (⇑(θ (shift i (adjacent (g * h))))) : ℝ) ≤ τ / 2 * Fintype.card B := by
      have hm := hθM _ (hD i g hg) _ (hD i h hh) (by simpa using hD i (g * h) hgh)
      rw [distance] at hm
      simpa only [map_mul] using (div_le_iff₀ hB').mp hm
    have hE : (Finset.univ.filter fun x : A => (φ g * φ h) x ≠ φ (g * h) x) =
        Finset.univ.filter (fun z : ZMod 4 × B =>
          θ (shift z.1 (adjacent g)) (θ (shift z.1 (adjacent h)) z.2) ≠
          θ (shift z.1 (adjacent (g * h))) z.2) := by
      apply Finset.filter_congr
      rintro ⟨i,x⟩ _
      change (i, θ (shift i (adjacent g)) (θ (shift i (adjacent h)) x)) ≠
          (i, θ (shift i (adjacent (g * h))) x) ↔ _
      exact not_congr ⟨fun he => congrArg Prod.snd he, fun he => congrArg (Prod.mk i) he⟩
    unfold hammingDist
    rw [hE, card_filter_product (fun i x =>
      θ (shift i (adjacent g)) (θ (shift i (adjacent h)) x) ≠
        θ (shift i (adjacent (g * h))) x)]
    push_cast
    calc
      _ ≤ ∑ _i : ZMod 4, (τ / 2) * (Fintype.card B : ℝ) :=
        Finset.sum_le_sum fun i _ => ha i
      _ = _ := by rw [hcEq, Nat.cast_mul]; simp [ZMod.card]; ring
  have hφD (g h : BS) (hg : g ∈ E) (hh : h ∈ E) (hne : g ≠ h) :
      ((Finset.univ.filter fun x : A => φ g x = φ h x).card : ℝ) ≤ (τ / 2) * c := by
    have ha (i : ZMod 4) : ((Finset.univ.filter fun x : B =>
        θ (shift i (adjacent g)) x = θ (shift i (adjacent h)) x).card : ℝ) ≤
          τ / 2 * Fintype.card B :=
      (div_le_iff₀ hB').mp (hθD _ (hD i g hg) _ (hD i h hh)
        ((shift_injective i).ne (adjacent_injective.ne hne)))
    have hE : (Finset.univ.filter fun x : A => φ g x = φ h x) =
        Finset.univ.filter (fun x : ZMod 4 × B =>
          θ (shift x.1 (adjacent g)) x.2 = θ (shift x.1 (adjacent h)) x.2) := by
      apply Finset.filter_congr
      rintro ⟨i,x⟩ _
      change (i, θ (shift i (adjacent g)) x) = (i, θ (shift i (adjacent h)) x) ↔ _
      exact ⟨fun he => congrArg Prod.snd he, fun he => congrArg (Prod.mk i) he⟩
    rw [hE, card_filter_product (fun i x =>
      θ (shift i (adjacent g)) x = θ (shift i (adjacent h)) x)]
    push_cast
    calc
      _ ≤ ∑ _i : ZMod 4, (τ / 2) * (Fintype.card B : ℝ) :=
        Finset.sum_le_sum fun i _ => ha i
      _ = _ := by rw [hcEq, Nat.cast_mul]; simp [ZMod.card]; ring
  obtain ⟨N, hN⟩ := exists_nat_gt ((c : ℝ) / (τ / 2))
  refine ⟨N, fun n hn => ?_⟩
  let r := n / c
  let d := n % c
  let X := (Fin r × A) ⊕ Fin d
  let f := pad (X := A) r d
  let p (g : BS) := f (φ g)
  let s := f (cycle B)
  have hsz : r * c + d = n := by simpa [r, c, d, Nat.mul_comm, add_comm] using (Nat.mod_add_div n c)
  have hX : Fintype.card X = n := by simpa [X, c] using hsz
  have hd : (d : ℝ) ≤ τ / 2 * n := by
    have hlt := (div_lt_iff₀ (by positivity : 0 < τ / 2)).mp hN
    have hlt' : (d : ℝ) < c := by exact_mod_cast Nat.mod_lt n hc
    have hs' : (N : ℝ) ≤ n := by exact_mod_cast hn
    have hb := mul_le_mul_of_nonneg_right hs' (by positivity : 0 ≤ τ / 2)
    nlinarith
  have hactive : (r : ℝ) * c ≤ n := by exact_mod_cast (show r * c ≤ n by omega)
  refine ⟨⟨X, inferInstance, inferInstance, hX, p, ?_, s, ?_, ?_⟩⟩
  · refine Approximates.mk ?_ ?_
    · intro g hg h hh hgh
      change (hammingDist (⇑(f (φ g) * f (φ h))) (⇑(f (φ (g * h)))) : ℝ) ≤ _
      rw [← map_mul, pad_hamming, Nat.cast_mul, hX]
      calc
        _ ≤ (r : ℝ) * (τ / 2 * (c : ℝ)) :=
          mul_le_mul_of_nonneg_left (hφM g h hg hh hgh) (by positivity)
        _ ≤ τ * n := by
          have he := mul_le_mul_of_nonneg_left hactive (by positivity : 0 ≤ τ / 2)
          nlinarith [mul_nonneg hτ.le (show (0 : ℝ) ≤ n by positivity)]
    · intro g hg h hh hne
      change ((Finset.univ.filter fun x => f (φ g) x = f (φ h) x).card : ℝ) ≤ _
      rw [pad_agree, Nat.cast_add, Nat.cast_mul, hX]
      calc
        _ ≤ (r : ℝ) * (τ / 2 * (c : ℝ)) + d :=
          add_le_add (mul_le_mul_of_nonneg_left (hφD g h hg hh hne)
            (show (0 : ℝ) ≤ r by positivity)) le_rfl
        _ ≤ τ * n := by
          have he := mul_le_mul_of_nonneg_left hactive (by positivity : 0 ≤ τ / 2)
          nlinarith
  · change f (cycle B) ^ 4 = 1
    rw [← map_pow, cycle_four, map_one]
  · change f (cycle B) * f (φ trans) = f (φ scale) * f (cycle B)
    rw [← map_mul, ← map_mul]
    congr 1
    have he : shift 1 (adjacent trans) = adjacent scale := by
      rw [adjacent_trans, adjacent_scale]
      exact shift_gen 0 1
    simpa only [φ, he] using cycle_rotateApprox θ (adjacent trans)

end

end HigmanModels

namespace HigmanModels

open HigmanAdjacent SoficCoupledPacking
open scoped BigOperators

noncomputable section

local instance : DecidableEq BS := Classical.decEq _

private theorem model_comparison (v : BS × BS) :
    ∃ K N : ℕ, ∀ (n : ℕ) [NeZero n], N ≤ n →
      ∀ (u : (ZMod n)ˣ) (hu : (u : ZMod n) = 2), v.1 ≠ v.2 →
        (Finset.univ.filter fun x : ZMod n =>
          HigmanAffine.model u hu v.1 x = HigmanAffine.model u hu v.2 x).card ≤ K := by
  by_cases h : v.1 = v.2
  · exact ⟨0, 0, fun _ _ _ _ _ hn => (hn h).elim⟩
  have he : v.1⁻¹ * v.2 ≠ 1 := by
    intro he
    have h' : v.2 = v.1 := by
      simpa using congrArg (fun z : BS => v.1 * z) he
    exact h h'.symm
  obtain ⟨K, N, hKN⟩ := HigmanAffine.eventually_few_fixed (v.1⁻¹ * v.2) he
  refine ⟨K, N, fun n _ hn u hu _ => ?_⟩
  have hs : (Finset.univ.filter fun x : ZMod n =>
      HigmanAffine.model u hu v.1 x = HigmanAffine.model u hu v.2 x) =
      Finset.univ.filter fun x : ZMod n => HigmanAffine.model u hu (v.1⁻¹ * v.2) x = x := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, map_inv, map_mul,
      Equiv.Perm.mul_apply]
    change _ ↔ (HigmanAffine.model u hu v.1).symm (HigmanAffine.model u hu v.2 x) = x
    rw [Equiv.symm_apply_eq, eq_comm]
  rw [hs]
  exact hKN n hn u hu

/-- The canonical affine model has arbitrarily small separation error on a
specified finite test set, for all sufficiently large odd moduli. -/
theorem eventually_standard_models (E : Finset BS) {τ : ℝ} (hτ : 0 < τ) :
    ∃ N : ℕ, ∀ (n : ℕ) [NeZero n], N ≤ n →
      ∀ (u : (ZMod n)ˣ) (hu : (u : ZMod n) = 2),
        Approximates (HigmanAffine.model u hu) E τ := by
  classical
  choose K N hKN using model_comparison
  let A := E ×ˢ E
  let Kmax := ∑ z ∈ A, K z
  let Nmax := ∑ z ∈ A, N z
  obtain ⟨M, hM⟩ := exists_nat_gt ((Kmax : ℝ) / τ)
  refine ⟨max Nmax M, fun n _ hn u hu => ?_⟩
  constructor
  · intro a ha b hb hab
    rw [map_mul, hammingDist_self, Nat.cast_zero]
    positivity
  · intro g hg h hh hne
    let v := (g,h)
    have hv : v ∈ A := Finset.mem_product.mpr ⟨hg,hh⟩
    have hN : N v ≤ Nmax := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hv
    have hK : K v ≤ Kmax := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hv
    have hv' := (hKN v n (hN.trans ((le_max_left _ _).trans hn)) u hu hne).trans hK
    have hM' : (M : ℝ) ≤ n := by exact_mod_cast ((le_max_right Nmax M).trans hn)
    have hE : (Kmax : ℝ) ≤ τ * n := by
      have hlt := (div_lt_iff₀ hτ).mp hM
      have hle := mul_le_mul_of_nonneg_right hM' hτ.le
      linarith
    rw [ZMod.card]
    exact (by exact_mod_cast hv' : _ ≤ (Kmax : ℝ)).trans hE

/-- Transport a permutation along an equivalence of its point set. -/
def transport {X Y : Type*} (e : X ≃ Y) : Equiv.Perm X →* Equiv.Perm Y where
  toFun p := (e.symm.trans p).trans e
  map_one' := by
    apply Equiv.ext
    intro y
    exact e.apply_symm_apply y
  map_mul' f g := by
    apply Equiv.ext
    intro y
    change e (f (g (e.symm y))) = e (f (e.symm (e (g (e.symm y)))))
    rw [e.symm_apply_apply]

@[simp] theorem transport_apply {X Y : Type*} (e : X ≃ Y) (p : Equiv.Perm X) (x : X) :
    transport e p (e x) = e (p x) := by
  change e (p (e.symm (e x))) = e (p x)
  rw [e.symm_apply_apply]

end

end HigmanModels

theorem OMA.solution : type_of% @Green100.green_100.variants.helfgott_juschenko := by
  classical
  intro hH ε hε
  let S : Finset HigmanAdjacent.BS := {HigmanAdjacent.trans, HigmanAdjacent.scale}
  let δ := min (ε / 4) (1 / 2)
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδ₁ : δ < 1 := (min_le_right _ _).trans_lt (by norm_num)
  obtain ⟨E, τ, hτ, hRectify⟩ := SoficCoupledPacking.rectify HigmanFolner.folner S δ hδ hδ₁
  obtain ⟨N₁, hCyclic⟩ := HigmanModels.eventually_cyclic_models hH E hτ
  obtain ⟨N₂, hStandard⟩ := HigmanModels.eventually_standard_models E hτ
  refine ⟨max 1 (max N₁ N₂), fun n hn hcoprime => ?_⟩
  have hN₁ : N₁ ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hN₂ : N₂ ≤ n := (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  have : NeZero n := ⟨by have := (le_max_left 1 (max N₁ N₂)).trans hn; omega⟩
  let u : (ZMod n)ˣ := ZMod.unitOfCoprime 2 hcoprime.symm
  have hu : (u : ZMod n) = 2 := rfl
  let ψ := HigmanAffine.model u hu
  obtain ⟨M⟩ := hCyclic n hN₁
  let : Fintype M.X := M.finite
  let : DecidableEq M.X := M.decEq
  have hCard : Fintype.card M.X = Fintype.card (ZMod n) := by rw [M.card_eq, ZMod.card]
  obtain ⟨e, he⟩ := hRectify M.action ψ hCard M.approx (hStandard n hN₂ u hu)
  let f := HigmanModels.transport e
  let a := f (M.action HigmanAdjacent.trans)
  let b := f (M.action HigmanAdjacent.scale)
  let s := f M.step
  have hp : s ^ 4 = 1 := by rw [← map_pow, M.fourth, map_one]
  have hc : s * a = b * s :=
    (f.map_mul _ _).symm.trans ((congrArg f M.intertwine).trans (f.map_mul _ _))
  have htrans (g : HigmanAdjacent.BS) (hg : g ∈ S) :
      (hammingDist (⇑(f (M.action g))) (⇑(ψ g)) : ℝ) ≤ 2 * δ * n := by
    have hdist := HigmanExtraction.hamming_reindex e (⇑(f (M.action g))) (⇑(ψ g))
    rw [← hdist]
    simpa [f, Function.comp_def, M.card_eq] using he g hg
  have ha := htrans HigmanAdjacent.trans (by simp [S])
  have hb := htrans HigmanAdjacent.scale (by simp [S])
  have hA (x : ZMod n) : ψ HigmanAdjacent.trans x = x - 1 := by
    simp only [ψ, HigmanAffine.model_trans, HigmanAffine.translation_apply]
    exact (sub_eq_add_neg x 1).symm
  have hB (x : ZMod n) : ψ HigmanAdjacent.scale x = (↑u⁻¹ : ZMod n) * x := by
    simp only [ψ, HigmanAffine.model_scale, HigmanAffine.dilation_apply]
  simp only [funext hA, funext hB] at ha hb
  apply HigmanExtraction.extract ε u hu s a b hp hc
  change (hammingDist (⇑(f (M.action HigmanAdjacent.trans))) (fun x => x - 1) : ℝ) +
    (hammingDist (⇑(f (M.action HigmanAdjacent.scale))) (fun x => (↑u⁻¹ : ZMod n) * x) : ℝ) ≤ ε * n
  have hδ' : 4 * δ ≤ ε := by
    have h := min_le_left (ε / 4) (1 / 2)
    linarith
  have he' := mul_le_mul_of_nonneg_right hδ' (show (0 : ℝ) ≤ n by positivity)
  linarith