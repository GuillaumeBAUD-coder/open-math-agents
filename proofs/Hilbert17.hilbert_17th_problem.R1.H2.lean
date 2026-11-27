import OMAReductions.R_Hilbert17_hilbert_17th_problem_R1
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Order.Zorn
import Mathlib.Algebra.Polynomial.FieldDivision

open Polynomial

namespace Hilbert17H2

/-- An ordered subfield of `AlgebraicClosure K` extending the order on `K`. -/
structure OrderedSubfield (K : Type) [Field K] [LinearOrder K] [IsStrictOrderedRing K] where
  carrier : Subfield (AlgebraicClosure K)
  pos : Set (AlgebraicClosure K)
  pos_sub : pos ⊆ (carrier : Set (AlgebraicClosure K))
  base_pos : ∀ x : K, 0 ≤ x → algebraMap K (AlgebraicClosure K) x ∈ pos
  add_mem : ∀ {x y}, x ∈ pos → y ∈ pos → x + y ∈ pos
  mul_mem : ∀ {x y}, x ∈ pos → y ∈ pos → x * y ∈ pos
  total : ∀ x ∈ carrier, x ∈ pos ∨ -x ∈ pos
  antisymm : ∀ {x}, x ∈ pos → -x ∈ pos → x = 0

section OrderedSubfieldAPI

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

instance : PartialOrder (OrderedSubfield K) where
  le A B := A.carrier ≤ B.carrier ∧ A.pos ⊆ B.pos
  le_refl _ := ⟨le_rfl, Set.Subset.rfl⟩
  le_trans _ _ _ h1 h2 := ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩
  le_antisymm A B h1 h2 := by
    have hc : A.carrier = B.carrier := le_antisymm h1.1 h2.1
    have hp : A.pos = B.pos := Set.Subset.antisymm h1.2 h2.2
    cases A
    cases B
    simp only at hc hp
    subst hc
    subst hp
    rfl

noncomputable def baseOrderedSubfield (K : Type) [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    OrderedSubfield K where
  carrier := (algebraMap K (AlgebraicClosure K)).fieldRange
  pos := {y | ∃ x : K, 0 ≤ x ∧ algebraMap K (AlgebraicClosure K) x = y}
  pos_sub := by
    rintro y ⟨x, _, rfl⟩
    exact ⟨x, rfl⟩
  base_pos x hx := ⟨x, hx, rfl⟩
  add_mem := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x + y, add_nonneg hx hy, map_add _ _ _⟩
  mul_mem := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x * y, mul_nonneg hx hy, map_mul _ _ _⟩
  total := by
    rintro _ ⟨x, rfl⟩
    rcases le_total (0 : K) x with h | h
    · exact Or.inl ⟨x, h, rfl⟩
    · exact Or.inr ⟨-x, neg_nonneg.mpr h, map_neg _ _⟩
  antisymm := by
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
    have h1 : algebraMap K (AlgebraicClosure K) y = algebraMap K (AlgebraicClosure K) (-x) := by
      rw [map_neg, hxy]
    have h2 : y = -x := (algebraMap K (AlgebraicClosure K)).injective h1
    have h3 : x = 0 := le_antisymm (neg_nonneg.mp (h2 ▸ hy)) hx
    rw [h3, map_zero]

instance : Nonempty (OrderedSubfield K) := ⟨baseOrderedSubfield K⟩

lemma exists_maximal_orderedSubfield : ∃ M : OrderedSubfield K, IsMax M := by
  refine zorn_le_nonempty fun c hc hne => ?_
  obtain ⟨A₀, hA₀⟩ := hne
  let U : Subfield (AlgebraicClosure K) :=
    { carrier := ⋃ A ∈ c, (A.carrier : Set (AlgebraicClosure K))
      zero_mem' := Set.mem_biUnion hA₀ A₀.carrier.zero_mem
      one_mem' := Set.mem_biUnion hA₀ A₀.carrier.one_mem
      add_mem' := by
        rintro x y hx hy
        rcases Set.mem_iUnion₂.mp hx with ⟨A, hA, hxA⟩
        rcases Set.mem_iUnion₂.mp hy with ⟨B, hB, hyB⟩
        rcases hc.total hA hB with hAB | hBA
        · exact Set.mem_biUnion hB (B.carrier.add_mem (hAB.1 hxA) hyB)
        · exact Set.mem_biUnion hA (A.carrier.add_mem hxA (hBA.1 hyB))
      neg_mem' := by
        rintro x hx
        rcases Set.mem_iUnion₂.mp hx with ⟨A, hA, hxA⟩
        exact Set.mem_biUnion hA (A.carrier.neg_mem hxA)
      mul_mem' := by
        rintro x y hx hy
        rcases Set.mem_iUnion₂.mp hx with ⟨A, hA, hxA⟩
        rcases Set.mem_iUnion₂.mp hy with ⟨B, hB, hyB⟩
        rcases hc.total hA hB with hAB | hBA
        · exact Set.mem_biUnion hB (B.carrier.mul_mem (hAB.1 hxA) hyB)
        · exact Set.mem_biUnion hA (A.carrier.mul_mem hxA (hBA.1 hyB))
      inv_mem' := by
        rintro x hx
        rcases Set.mem_iUnion₂.mp hx with ⟨A, hA, hxA⟩
        exact Set.mem_biUnion hA (A.carrier.inv_mem hxA) }
  let ub : OrderedSubfield K :=
    { carrier := U
      pos := ⋃ A ∈ c, A.pos
      pos_sub := by
        rintro x hx
        rcases Set.mem_iUnion₂.mp hx with ⟨A, hA, hxA⟩
        exact Set.mem_biUnion hA (A.pos_sub hxA)
      base_pos := fun x hx => Set.mem_biUnion hA₀ (A₀.base_pos x hx)
      add_mem := by
        rintro x y hx hy
        rcases Set.mem_iUnion₂.mp hx with ⟨A, hA, hxA⟩
        rcases Set.mem_iUnion₂.mp hy with ⟨B, hB, hyB⟩
        rcases hc.total hA hB with hAB | hBA
        · exact Set.mem_biUnion hB (B.add_mem (hAB.2 hxA) hyB)
        · exact Set.mem_biUnion hA (A.add_mem hxA (hBA.2 hyB))
      mul_mem := by
        rintro x y hx hy
        rcases Set.mem_iUnion₂.mp hx with ⟨A, hA, hxA⟩
        rcases Set.mem_iUnion₂.mp hy with ⟨B, hB, hyB⟩
        rcases hc.total hA hB with hAB | hBA
        · exact Set.mem_biUnion hB (B.mul_mem (hAB.2 hxA) hyB)
        · exact Set.mem_biUnion hA (A.mul_mem hxA (hBA.2 hyB))
      total := by
        rintro x hx
        rcases Set.mem_iUnion₂.mp hx with ⟨A, hA, hxA⟩
        rcases A.total x hxA with h | h
        · exact Or.inl (Set.mem_biUnion hA h)
        · exact Or.inr (Set.mem_biUnion hA h)
      antisymm := by
        rintro x hx hnx
        rcases Set.mem_iUnion₂.mp hx with ⟨A, hA, hxA⟩
        rcases Set.mem_iUnion₂.mp hnx with ⟨B, hB, hnxB⟩
        rcases hc.total hA hB with hAB | hBA
        · exact B.antisymm (hAB.2 hxA) hnxB
        · exact A.antisymm hxA (hBA.2 hnxB) }
  refine ⟨ub, fun A hA => ⟨?_, ?_⟩⟩
  · intro x hx
    exact Set.mem_biUnion hA hx
  · intro x hx
    exact Set.mem_biUnion hA hx

lemma OrderedSubfield.zero_mem_pos (M : OrderedSubfield K) : (0 : AlgebraicClosure K) ∈ M.pos := by
  simpa using M.base_pos 0 le_rfl

lemma OrderedSubfield.one_mem_pos (M : OrderedSubfield K) : (1 : AlgebraicClosure K) ∈ M.pos := by
  simpa using M.base_pos 1 zero_le_one

lemma OrderedSubfield.sq_mem_pos (M : OrderedSubfield K) {x : AlgebraicClosure K}
    (hx : x ∈ M.carrier) : x * x ∈ M.pos := by
  rcases M.total x hx with h | h
  · exact M.mul_mem h h
  · simpa [neg_mul, mul_neg, neg_neg] using M.mul_mem h h

/-- Induce a `LinearOrder` on `M.carrier` from `M.pos`. -/
noncomputable def OrderedSubfield.toLinearOrder (M : OrderedSubfield K) :
    LinearOrder M.carrier := by
  classical
  refine
    { le := fun x y => (y : AlgebraicClosure K) - (x : AlgebraicClosure K) ∈ M.pos
      le_refl := fun x => by simpa using M.zero_mem_pos
      le_trans := fun x y z hxy hyz => by
        have h := M.add_mem hyz hxy
        have heq : ((z : AlgebraicClosure K) - y) + (y - x) = z - x := by ring
        rwa [heq] at h
      le_antisymm := fun x y hxy hyx => by
        have hneg : -((y : AlgebraicClosure K) - x) = x - y := by ring
        have h0 : (y : AlgebraicClosure K) - x = 0 := M.antisymm hxy (hneg ▸ hyx)
        exact Subtype.ext (sub_eq_zero.mp h0).symm
      le_total := fun x y => by
        rcases M.total ((y : AlgebraicClosure K) - x) (M.carrier.sub_mem y.2 x.2) with h | h
        · exact Or.inl h
        · right
          have hneg : -((y : AlgebraicClosure K) - x) = x - y := by ring
          rwa [hneg] at h
      toDecidableLE := Classical.decRel _ }

lemma OrderedSubfield.toIsStrictOrderedRing (M : OrderedSubfield K) :
    @IsStrictOrderedRing M.carrier _ M.toLinearOrder.toPartialOrder := by
  letI : LinearOrder M.carrier := M.toLinearOrder
  have hadd : IsOrderedAddMonoid M.carrier :=
    { add_le_add_left := fun a b hab c => by
        change ((b + c : M.carrier) : AlgebraicClosure K) - (a + c : M.carrier) ∈ M.pos
        have heq : ((b : AlgebraicClosure K) + c) - (a + c) = (b : AlgebraicClosure K) - a := by ring
        have hab' : (b : AlgebraicClosure K) - a ∈ M.pos := hab
        simpa [heq] using hab' }
  have h01 : ZeroLEOneClass M.carrier :=
    { zero_le_one := by
        change (1 : AlgebraicClosure K) - 0 ∈ M.pos
        simpa using M.one_mem_pos }
  refine IsStrictOrderedRing.of_mul_pos fun a b ha hb => ?_
  have ha0 : (a : AlgebraicClosure K) - 0 ∈ M.pos := ha.le
  have hb0 : (b : AlgebraicClosure K) - 0 ∈ M.pos := hb.le
  have ha' : (a : AlgebraicClosure K) ∈ M.pos := by simpa using ha0
  have hb' : (b : AlgebraicClosure K) ∈ M.pos := by simpa using hb0
  have hab_nonneg : (0 : M.carrier) ≤ a * b := by
    change ((a * b : M.carrier) : AlgebraicClosure K) - 0 ∈ M.pos
    simpa using M.mul_mem ha' hb'
  have hab_ne : (a * b : M.carrier) ≠ 0 := mul_ne_zero ha.ne' hb.ne'
  exact lt_of_le_of_ne hab_nonneg hab_ne.symm

end OrderedSubfieldAPI

section ArtinSchreierExtension

/-- Extend a preordering on a subfield `L` of `Ω` to a total positive cone on `L`. -/
lemma exists_total_cone_extending {Ω : Type*} [Field Ω] {L : Subfield Ω}
    {P : Set Ω} (hP_sub : P ⊆ (L : Set Ω)) (h0 : (0 : Ω) ∈ P) (h1 : (1 : Ω) ∈ P)
    (hadd : ∀ {x y}, x ∈ P → y ∈ P → x + y ∈ P)
    (hmul : ∀ {x y}, x ∈ P → y ∈ P → x * y ∈ P)
    (hsq : ∀ x ∈ L, x * x ∈ P)
    (hneg1 : (-1 : Ω) ∉ P) :
    ∃ Q : Set Ω, P ⊆ Q ∧ Q ⊆ (L : Set Ω) ∧
      (∀ {x y}, x ∈ Q → y ∈ Q → x + y ∈ Q) ∧
      (∀ {x y}, x ∈ Q → y ∈ Q → x * y ∈ Q) ∧
      (∀ x ∈ L, x ∈ Q ∨ -x ∈ Q) ∧
      (∀ {x}, x ∈ Q → -x ∈ Q → x = 0) := by
  let S : Set (Set Ω) :=
    {T | P ⊆ T ∧ T ⊆ (L : Set Ω) ∧
      (∀ {x y}, x ∈ T → y ∈ T → x + y ∈ T) ∧
      (∀ {x y}, x ∈ T → y ∈ T → x * y ∈ T) ∧
      (-1 : Ω) ∉ T}
  have hPS : P ∈ S := ⟨Set.Subset.rfl, hP_sub, hadd, hmul, hneg1⟩
  have hchain : ∀ c ⊆ S, IsChain (· ⊆ ·) c → ∀ y ∈ c, ∃ ub ∈ S, ∀ z ∈ c, z ⊆ ub := by
    intro c hc hch y hy
    refine ⟨⋃ T ∈ c, T, ⟨?_, ?_, ?_, ?_, ?_⟩, fun z hz => Set.subset_biUnion_of_mem (u := id) hz⟩
    · exact (hc hy).1.trans (Set.subset_biUnion_of_mem (u := id) hy)
    · intro x hx
      rcases Set.mem_iUnion₂.mp hx with ⟨T, hT, hxT⟩
      exact (hc hT).2.1 hxT
    · intro x y hx hy'
      rcases Set.mem_iUnion₂.mp hx with ⟨T₁, hT₁, hx₁⟩
      rcases Set.mem_iUnion₂.mp hy' with ⟨T₂, hT₂, hy₂⟩
      rcases hch.total hT₁ hT₂ with h12 | h21
      · exact Set.mem_biUnion hT₂ ((hc hT₂).2.2.1 (h12 hx₁) hy₂)
      · exact Set.mem_biUnion hT₁ ((hc hT₁).2.2.1 hx₁ (h21 hy₂))
    · intro x y hx hy'
      rcases Set.mem_iUnion₂.mp hx with ⟨T₁, hT₁, hx₁⟩
      rcases Set.mem_iUnion₂.mp hy' with ⟨T₂, hT₂, hy₂⟩
      rcases hch.total hT₁ hT₂ with h12 | h21
      · exact Set.mem_biUnion hT₂ ((hc hT₂).2.2.2.1 (h12 hx₁) hy₂)
      · exact Set.mem_biUnion hT₁ ((hc hT₁).2.2.2.1 hx₁ (h21 hy₂))
    · intro h
      rcases Set.mem_iUnion₂.mp h with ⟨T, hT, hneg⟩
      exact (hc hT).2.2.2.2 hneg
  obtain ⟨Q, hPQ, hQS, hQmax⟩ := zorn_le_nonempty₀ S hchain P hPS
  rcases hQS with ⟨_, hQL, hQadd, hQmul, hQneg1⟩
  have hQ0 : (0 : Ω) ∈ Q := hPQ h0
  have hQ1 : (1 : Ω) ∈ Q := hPQ h1
  have hQsq : ∀ x ∈ L, x * x ∈ Q := fun x hx => hPQ (hsq x hx)
  have hQanti : ∀ {x}, x ∈ Q → -x ∈ Q → x = 0 := by
    intro x hx hnx
    by_contra hx0
    have hxinv : x⁻¹ ∈ L := L.inv_mem (hQL hx)
    have hsqinv : x⁻¹ * x⁻¹ ∈ Q := hQsq x⁻¹ hxinv
    have hprod : (-x) * x * (x⁻¹ * x⁻¹) ∈ Q := hQmul (hQmul hnx hx) hsqinv
    have heq : (-x) * x * (x⁻¹ * x⁻¹) = (-1 : Ω) := by field_simp [hx0]
    exact hQneg1 (heq ▸ hprod)
  have hQtotal : ∀ x ∈ L, x ∈ Q ∨ -x ∈ Q := by
    intro x hxL
    by_contra hneither
    push_neg at hneither
    rcases hneither with ⟨hxQ, hnxQ⟩
    have hneg_mem : ∀ z ∈ L, z ∉ Q → ∃ a ∈ Q, ∃ b ∈ Q, a + z * b = -1 := by
      intro z hzL hzQ
      let Qz : Set Ω := {w | ∃ a ∈ Q, ∃ b ∈ Q, w = a + z * b}
      have hQsubQz : Q ⊆ Qz := fun a ha => ⟨a, ha, 0, hQ0, by ring⟩
      have hz_in_Qz : z ∈ Qz := ⟨0, hQ0, 1, hQ1, by ring⟩
      have hQz_sub_L : Qz ⊆ (L : Set Ω) := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        exact L.add_mem (hQL ha) (L.mul_mem hzL (hQL hb))
      have hQz_add : ∀ {u v}, u ∈ Qz → v ∈ Qz → u + v ∈ Qz := by
        rintro _ _ ⟨a₁, ha₁, b₁, hb₁, rfl⟩ ⟨a₂, ha₂, b₂, hb₂, rfl⟩
        exact ⟨a₁ + a₂, hQadd ha₁ ha₂, b₁ + b₂, hQadd hb₁ hb₂, by ring⟩
      have hQz_mul : ∀ {u v}, u ∈ Qz → v ∈ Qz → u * v ∈ Qz := by
        rintro _ _ ⟨a₁, ha₁, b₁, hb₁, rfl⟩ ⟨a₂, ha₂, b₂, hb₂, rfl⟩
        refine ⟨a₁ * a₂ + (z * z) * (b₁ * b₂),
          hQadd (hQmul ha₁ ha₂) (hQmul (hQsq z hzL) (hQmul hb₁ hb₂)),
          a₁ * b₂ + b₁ * a₂, hQadd (hQmul ha₁ hb₂) (hQmul hb₁ ha₂), by ring⟩
      by_contra hno
      have hneg1Qz : (-1 : Ω) ∉ Qz := by
        rintro ⟨a, ha, b, hb, heq⟩
        exact hno ⟨a, ha, b, hb, heq.symm⟩
      have hQzS : Qz ∈ S := ⟨hPQ.trans hQsubQz, hQz_sub_L, hQz_add, hQz_mul, hneg1Qz⟩
      have hQzleQ : Qz ⊆ Q := hQmax hQzS hQsubQz
      exact hzQ (hQzleQ hz_in_Qz)
    obtain ⟨a₁, ha₁, b₁, hb₁, heq₁⟩ := hneg_mem x hxL hxQ
    obtain ⟨a₂, ha₂, b₂, hb₂, heq₂⟩ := hneg_mem (-x) (L.neg_mem hxL) hnxQ
    have hb₁0 : b₁ ≠ 0 := by
      intro h0'
      rw [h0', mul_zero, add_zero] at heq₁
      exact hQneg1 (heq₁ ▸ ha₁)
    have hs0 : b₁ + b₂ ≠ 0 := by
      intro hsum
      have hnegb : -b₁ = b₂ := by linear_combination -hsum
      exact hb₁0 (hQanti hb₁ (hnegb ▸ hb₂))
    have hsQ : b₁ + b₂ ∈ Q := hQadd hb₁ hb₂
    have hsL : b₁ + b₂ ∈ L := hQL hsQ
    have hsinvQ : (b₁ + b₂)⁻¹ ∈ Q := by
      have h := hQmul hsQ (hQsq (b₁ + b₂)⁻¹ (L.inv_mem hsL))
      have heq : (b₁ + b₂) * ((b₁ + b₂)⁻¹ * (b₁ + b₂)⁻¹) = (b₁ + b₂)⁻¹ := by field_simp [hs0]
      rwa [heq] at h
    have hnumQ : a₁ * b₂ + a₂ * b₁ ∈ Q := hQadd (hQmul ha₁ hb₂) (hQmul ha₂ hb₁)
    have hcomb : (a₁ * b₂ + a₂ * b₁) * (b₁ + b₂)⁻¹ = (-1 : Ω) := by
      have hlin : a₁ * b₂ + a₂ * b₁ = -(b₁ + b₂) := by
        linear_combination b₂ * heq₁ + b₁ * heq₂
      rw [hlin]
      field_simp [hs0]
    exact hQneg1 (hcomb ▸ hQmul hnumQ hsinvQ)
  exact ⟨Q, hPQ, hQL, hQadd, hQmul, hQtotal, hQanti⟩

/-- Cone generated by `P` and squares of elements of `L`. -/
inductive ConeGen {Ω : Type*} [Field Ω] (P : Set Ω) (L : Subfield Ω) : Ω → Prop
  | zero : ConeGen P L 0
  | add_mul_sq {p x s : Ω} (hp : p ∈ P) (hx : x ∈ L) (hs : ConeGen P L s) :
      ConeGen P L (p * (x * x) + s)

lemma coneGen_sub {Ω : Type*} [Field Ω] {P : Set Ω} {L : Subfield Ω}
    (hPL : P ⊆ (L : Set Ω)) {s : Ω} (hs : ConeGen P L s) : s ∈ L := by
  induction hs with
  | zero => exact L.zero_mem
  | add_mul_sq hp hx _ ih => exact L.add_mem (L.mul_mem (hPL hp) (L.mul_mem hx hx)) ih

lemma coneGen_add {Ω : Type*} [Field Ω] {P : Set Ω} {L : Subfield Ω}
    {s t : Ω} (hs : ConeGen P L s) (ht : ConeGen P L t) : ConeGen P L (s + t) := by
  induction hs with
  | zero => simpa using ht
  | add_mul_sq hp hx _ ih =>
    rw [add_assoc]
    exact ConeGen.add_mul_sq hp hx ih

lemma coneGen_mul_single {Ω : Type*} [Field Ω] {P : Set Ω} {L : Subfield Ω}
    (hPmul : ∀ {a b}, a ∈ P → b ∈ P → a * b ∈ P)
    {p x s : Ω} (hp : p ∈ P) (hx : x ∈ L) (hs : ConeGen P L s) :
    ConeGen P L (p * (x * x) * s) := by
  induction hs with
  | zero =>
    rw [mul_zero]
    exact ConeGen.zero
  | @add_mul_sq q y t hq hy _ ih =>
    have heq : p * (x * x) * (q * (y * y) + t) =
        (p * q) * ((x * y) * (x * y)) + p * (x * x) * t := by ring
    rw [heq]
    exact ConeGen.add_mul_sq (hPmul hp hq) (L.mul_mem hx hy) ih

lemma coneGen_mul {Ω : Type*} [Field Ω] {P : Set Ω} {L : Subfield Ω}
    (hPmul : ∀ {a b}, a ∈ P → b ∈ P → a * b ∈ P)
    {s t : Ω} (hs : ConeGen P L s) (ht : ConeGen P L t) : ConeGen P L (s * t) := by
  induction hs with
  | zero =>
    rw [zero_mul]
    exact ConeGen.zero
  | add_mul_sq hp hx _ ih =>
    rw [add_mul]
    exact coneGen_add (coneGen_mul_single hPmul hp hx ht) ih

end ArtinSchreierExtension

section AdjoinRootSubfield

/-- Given a subfield `F` of `Ω` and an irreducible polynomial `f : F[X]` with a root `α : Ω`,
the image of `F[X]` under evaluation at `α` is a subfield of `Ω`. -/
def adjoinRootSubfield {Ω : Type*} [Field Ω] (F : Subfield Ω) (f : F[X])
    (hf : Irreducible f) (α : Ω) (hα : f.eval₂ F.subtype α = 0) : Subfield Ω where
  carrier := {y | ∃ p : F[X], p.eval₂ F.subtype α = y}
  zero_mem' := ⟨0, by simp⟩
  one_mem' := ⟨1, by simp⟩
  add_mem' := by
    rintro _ _ ⟨p, rfl⟩ ⟨q, rfl⟩
    exact ⟨p + q, by simp [eval₂_add]⟩
  neg_mem' := by
    rintro _ ⟨p, rfl⟩
    exact ⟨-p, by simp [eval₂_neg]⟩
  mul_mem' := by
    rintro _ _ ⟨p, rfl⟩ ⟨q, rfl⟩
    exact ⟨p * q, by simp [eval₂_mul]⟩
  inv_mem' := by
    rintro _ ⟨p, rfl⟩
    by_cases h0 : p.eval₂ F.subtype α = 0
    · rw [h0, inv_zero]
      exact ⟨0, by simp⟩
    · have hndiv : ¬ f ∣ p := by
        rintro ⟨q, rfl⟩
        apply h0
        rw [eval₂_mul, hα, zero_mul]
      have hcop : IsCoprime f p := hf.coprime_iff_not_dvd.mpr hndiv
      rcases hcop with ⟨u, v, huv⟩
      refine ⟨v, ?_⟩
      have hev := congrArg (Polynomial.eval₂ F.subtype α) huv
      simp only [eval₂_add, eval₂_mul, eval₂_one, hα, mul_zero, zero_add] at hev
      exact eq_inv_of_mul_eq_one_left hev

lemma le_adjoinRootSubfield {Ω : Type*} [Field Ω] (F : Subfield Ω) (f : F[X])
    (hf : Irreducible f) (α : Ω) (hα : f.eval₂ F.subtype α = 0) :
    F ≤ adjoinRootSubfield F f hf α hα := by
  intro x hx
  exact ⟨C ⟨x, hx⟩, by simp⟩

lemma root_mem_adjoinRootSubfield {Ω : Type*} [Field Ω] (F : Subfield Ω) (f : F[X])
    (hf : Irreducible f) (α : Ω) (hα : f.eval₂ F.subtype α = 0) :
    α ∈ adjoinRootSubfield F f hf α hα :=
  ⟨X, by simp⟩

lemma exists_poly_lt_natDegree {Ω : Type*} [Field Ω] (F : Subfield Ω) (f : F[X])
    (hf : Irreducible f) (hfpos : 0 < f.natDegree) (α : Ω) (hα : f.eval₂ F.subtype α = 0)
    {y : Ω} (hy : y ∈ adjoinRootSubfield F f hf α hα) :
    ∃ g : F[X], g.natDegree < f.natDegree ∧ g.eval₂ F.subtype α = y := by
  rcases hy with ⟨p, rfl⟩
  have hf0 : f ≠ 0 := hf.ne_zero
  refine ⟨p % f, ?_, ?_⟩
  · by_cases hr : p % f = 0
    · rw [hr, natDegree_zero]
      exact hfpos
    · exact Polynomial.natDegree_lt_natDegree hr (Polynomial.degree_mod_lt p hf0)
  · have hdiv := EuclideanDomain.div_add_mod p f
    have hev := congrArg (Polynomial.eval₂ F.subtype α) hdiv
    simp only [eval₂_add, eval₂_mul, hα, zero_mul, zero_add] at hev
    exact hev

end AdjoinRootSubfield

section RealClosedProof

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Invariant for polynomials representing elements of `ConeGen M.pos L`. -/
def EvenPosPoly {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (D : ℕ) (H : R[X]) : Prop :=
  (∀ r : R, 0 ≤ H.eval r) ∧
    (H = 0 ∨ (Even H.natDegree ∧ H.natDegree ≤ D ∧ 0 < H.leadingCoeff))

lemma evenPosPoly_zero {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] (D : ℕ) :
    EvenPosPoly D (0 : R[X]) :=
  ⟨fun _ => by simp, Or.inl rfl⟩

lemma evenPosPoly_one {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] (D : ℕ) :
    EvenPosPoly D (1 : R[X]) :=
  ⟨fun _ => by simp, Or.inr ⟨by simp, by simp, by simp⟩⟩

lemma evenPosPoly_add {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    {D : ℕ} {H₁ H₂ : R[X]} (h₁ : EvenPosPoly D H₁) (h₂ : EvenPosPoly D H₂) :
    EvenPosPoly D (H₁ + H₂) := by
  refine ⟨fun r => by simpa [eval_add] using add_nonneg (h₁.1 r) (h₂.1 r), ?_⟩
  rcases h₁.2 with rfl | ⟨he₁, hd₁, hlc₁⟩
  · simpa using h₂.2
  rcases h₂.2 with rfl | ⟨he₂, hd₂, hlc₂⟩
  · simpa using Or.inr ⟨he₁, hd₁, hlc₁⟩
  right
  rcases lt_trichotomy H₁.natDegree H₂.natDegree with hlt | heq | hgt
  · have hdeg : (H₁ + H₂).natDegree = H₂.natDegree := natDegree_add_eq_right_of_natDegree_lt hlt
    have hlc : (H₁ + H₂).leadingCoeff = H₂.leadingCoeff :=
      leadingCoeff_add_of_degree_lt (degree_lt_degree hlt)
    exact ⟨hdeg ▸ he₂, hdeg ▸ hd₂, hlc ▸ hlc₂⟩
  · have hcoeff : (H₁ + H₂).coeff H₁.natDegree = H₁.leadingCoeff + H₂.leadingCoeff := by
      rw [coeff_add, coeff_natDegree, heq, coeff_natDegree]
    have hpos : 0 < (H₁ + H₂).coeff H₁.natDegree := hcoeff ▸ add_pos hlc₁ hlc₂
    have hne : (H₁ + H₂).coeff H₁.natDegree ≠ 0 := hpos.ne'
    have hle : (H₁ + H₂).natDegree ≤ H₁.natDegree := by
      exact (natDegree_add_le H₁ H₂).trans (by rw [heq, max_self])
    have hge : H₁.natDegree ≤ (H₁ + H₂).natDegree := le_natDegree_of_ne_zero hne
    have hdeg : (H₁ + H₂).natDegree = H₁.natDegree := le_antisymm hle hge
    have hlc : (H₁ + H₂).leadingCoeff = (H₁ + H₂).coeff H₁.natDegree := by
      rw [leadingCoeff, hdeg]
    exact ⟨hdeg ▸ he₁, hdeg ▸ hd₁, hlc ▸ hpos⟩
  · have hdeg : (H₁ + H₂).natDegree = H₁.natDegree := natDegree_add_eq_left_of_natDegree_lt hgt
    have hlc : (H₁ + H₂).leadingCoeff = H₁.leadingCoeff := by
      rw [add_comm]
      exact leadingCoeff_add_of_degree_lt (degree_lt_degree hgt)
    exact ⟨hdeg ▸ he₁, hdeg ▸ hd₁, hlc ▸ hlc₁⟩

lemma evenPosPoly_C_mul_sq {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    {D : ℕ} {p : R} (hp : 0 ≤ p) {g : R[X]} (hg : 2 * g.natDegree ≤ D) :
    EvenPosPoly D (C p * (g * g)) := by
  refine ⟨fun r => by
    simp only [eval_mul, eval_C]
    exact mul_nonneg hp (mul_self_nonneg _), ?_⟩
  by_cases hp0 : p = 0
  · left
    simp [hp0]
  by_cases hg0 : g = 0
  · left
    simp [hg0]
  right
  have hp_pos : 0 < p := lt_of_le_of_ne hp (Ne.symm hp0)
  have hCp0 : C p ≠ 0 := C_ne_zero.mpr hp0
  have hgg0 : g * g ≠ 0 := mul_ne_zero hg0 hg0
  have hdeg : (C p * (g * g)).natDegree = 2 * g.natDegree := by
    rw [natDegree_mul hCp0 hgg0, natDegree_C, zero_add, natDegree_mul hg0 hg0, two_mul]
  have hlc : (C p * (g * g)).leadingCoeff = p * (g.leadingCoeff * g.leadingCoeff) := by
    rw [leadingCoeff_mul, leadingCoeff_C, leadingCoeff_mul]
  have hglc0 : g.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hg0
  refine ⟨hdeg ▸ ⟨g.natDegree, two_mul _⟩, hdeg ▸ hg, hlc ▸ mul_pos hp_pos (mul_self_pos.mpr hglc0)⟩

lemma coneGen_lift_evenPosPoly (M : OrderedSubfield K)
    (f : M.carrier[X]) (hf : Irreducible f) (hfpos : 0 < f.natDegree)
    (α : AlgebraicClosure K) (hα : f.eval₂ M.carrier.subtype α = 0)
    {s : AlgebraicClosure K}
    (hs : ConeGen M.pos (adjoinRootSubfield M.carrier f hf α hα) s) :
    letI : LinearOrder M.carrier := M.toLinearOrder
    letI : IsStrictOrderedRing M.carrier := M.toIsStrictOrderedRing
    ∃ H : M.carrier[X],
      H.eval₂ M.carrier.subtype α = s ∧ EvenPosPoly (2 * (f.natDegree - 1)) H := by
  letI : LinearOrder M.carrier := M.toLinearOrder
  letI : IsStrictOrderedRing M.carrier := M.toIsStrictOrderedRing
  induction hs with
  | zero => exact ⟨0, by simp, evenPosPoly_zero _⟩
  | @add_mul_sq p x t hp hx _ ih =>
    obtain ⟨H, hHev, hHinv⟩ := ih
    obtain ⟨g, hgdeg, hgev⟩ := exists_poly_lt_natDegree M.carrier f hf hfpos α hα hx
    let p' : M.carrier := ⟨p, M.pos_sub hp⟩
    have hp'_nonneg : (0 : M.carrier) ≤ p' := by
      change (p : AlgebraicClosure K) - 0 ∈ M.pos
      simpa using hp
    have h2g : 2 * g.natDegree ≤ 2 * (f.natDegree - 1) := by omega
    refine ⟨C p' * (g * g) + H, ?_, evenPosPoly_add (evenPosPoly_C_mul_sq hp'_nonneg h2g) hHinv⟩
    simp only [eval₂_add, eval₂_mul, eval₂_C, hgev, hHev]
    rfl

/-- If an irreducible polynomial `f` over a maximal ordered subfield `M` has a root `α` in the
algebraic closure and `adjoinRootSubfield` admits an ordering extending `M.pos`, then `α ∈ M`. -/
lemma root_mem_of_not_neg_one_mem_coneGen (M : OrderedSubfield K) (hM : IsMax M)
    (f : M.carrier[X]) (hf : Irreducible f)
    (α : AlgebraicClosure K) (hα : f.eval₂ M.carrier.subtype α = 0)
    (hneg1 : ¬ ConeGen M.pos (adjoinRootSubfield M.carrier f hf α hα) (-1 : AlgebraicClosure K)) :
    α ∈ M.carrier := by
  let L := adjoinRootSubfield M.carrier f hf α hα
  have hML : M.carrier ≤ L := le_adjoinRootSubfield M.carrier f hf α hα
  let P : Set (AlgebraicClosure K) := {s | ConeGen M.pos L s}
  have hPsub : P ⊆ (L : Set (AlgebraicClosure K)) := fun _ hs =>
    coneGen_sub (M.pos_sub.trans hML) hs
  have hP0 : (0 : AlgebraicClosure K) ∈ P := ConeGen.zero
  have hP1 : (1 : AlgebraicClosure K) ∈ P := by
    have h := ConeGen.add_mul_sq (P := M.pos) (L := L) M.one_mem_pos L.one_mem ConeGen.zero
    simpa [P] using h
  have hPadd : ∀ {x y}, x ∈ P → y ∈ P → x + y ∈ P := fun hx hy => coneGen_add hx hy
  have hPmul : ∀ {x y}, x ∈ P → y ∈ P → x * y ∈ P := fun hx hy => coneGen_mul M.mul_mem hx hy
  have hPsq : ∀ x ∈ L, x * x ∈ P := fun x hx => by
    have h := ConeGen.add_mul_sq (P := M.pos) (L := L) M.one_mem_pos hx ConeGen.zero
    simpa [P] using h
  obtain ⟨Q, hPQ, hQL, hQadd, hQmul, hQtotal, hQanti⟩ :=
    exists_total_cone_extending hPsub hP0 hP1 hPadd hPmul hPsq hneg1
  have hMposQ : M.pos ⊆ Q := by
    intro p hp
    apply hPQ
    have h := ConeGen.add_mul_sq (P := M.pos) (L := L) hp L.one_mem ConeGen.zero
    simpa [P] using h
  let M' : OrderedSubfield K :=
    { carrier := L
      pos := Q
      pos_sub := hQL
      base_pos := fun x hx => hMposQ (M.base_pos x hx)
      add_mem := hQadd
      mul_mem := hQmul
      total := hQtotal
      antisymm := hQanti }
  have hle : M ≤ M' := ⟨hML, hMposQ⟩
  have hge : M' ≤ M := hM hle
  exact hge.1 (root_mem_adjoinRootSubfield M.carrier f hf α hα)

lemma maximal_isSquare_of_nonneg (M : OrderedSubfield K) (hM : IsMax M) :
    letI : LinearOrder M.carrier := M.toLinearOrder
    letI : IsStrictOrderedRing M.carrier := M.toIsStrictOrderedRing
    ∀ {a : M.carrier}, 0 ≤ a → IsSquare a := by
  letI : LinearOrder M.carrier := M.toLinearOrder
  letI : IsStrictOrderedRing M.carrier := M.toIsStrictOrderedRing
  intro a ha
  by_contra hnsq
  let f : M.carrier[X] := X ^ 2 - C a
  have hfdeg : f.natDegree = 2 := by
    change (X ^ 2 - C a).natDegree = 2
    compute_degree!
  have hf_noroot : ∀ r : M.carrier, ¬ f.IsRoot r := by
    intro r hr
    simp only [f, IsRoot.def, eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] at hr
    exact hnsq ⟨r, by rw [← sq, hr]⟩
  have hfirr : Irreducible f := by
    refine ⟨?_, ?_⟩
    · intro hu
      have := Polynomial.natDegree_eq_zero_of_isUnit hu
      omega
    · intro p q hpq
      by_contra hnu
      push_neg at hnu
      rcases hnu with ⟨hpu, hqu⟩
      have hp0 : p ≠ 0 := by
        intro h0
        rw [h0, zero_mul] at hpq
        have := congrArg natDegree hpq
        simp [hfdeg] at this
      have hq0 : q ≠ 0 := by
        intro h0
        rw [h0, mul_zero] at hpq
        have := congrArg natDegree hpq
        simp [hfdeg] at this
      have hpdeg : 1 ≤ p.natDegree := by
        by_contra h
        have h0 : p.natDegree = 0 := by omega
        exact hpu (isUnit_iff_degree_eq_zero.mpr (degree_eq_iff_natDegree_eq hp0 |>.mpr h0))
      have hqdeg : 1 ≤ q.natDegree := by
        by_contra h
        have h0 : q.natDegree = 0 := by omega
        exact hqu (isUnit_iff_degree_eq_zero.mpr (degree_eq_iff_natDegree_eq hq0 |>.mpr h0))
      have hsum : p.natDegree + q.natDegree = 2 := by
        rw [← natDegree_mul hp0 hq0, ← hpq, hfdeg]
      have hp1 : p.natDegree = 1 := by omega
      have hrootp : ∃ r : M.carrier, p.IsRoot r := by
        refine ⟨-(p.coeff 0) / p.coeff 1, ?_⟩
        have h1ne : p.coeff 1 ≠ 0 := by
          rw [← hp1]
          exact leadingCoeff_ne_zero.mpr hp0
        rw [IsRoot.def, eq_X_add_C_of_natDegree_le_one (le_of_eq hp1)]
        simp [eval_add, eval_mul, eval_C, eval_X]
        field_simp [h1ne]
        ring
      obtain ⟨r, hr⟩ := hrootp
      exact hf_noroot r (by rw [hpq, IsRoot.def, eval_mul, hr.eq_zero, zero_mul])
  have hdeg_map : (f.map M.carrier.subtype).degree ≠ 0 := by
    rw [degree_map_eq_of_injective M.carrier.subtype_injective,
      degree_eq_natDegree hfirr.ne_zero, hfdeg]
    decide
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_root (f.map M.carrier.subtype) hdeg_map
  have hα' : f.eval₂ M.carrier.subtype α = 0 := by
    simpa [IsRoot.def, eval_map] using hα
  have hneg1 : ¬ ConeGen M.pos (adjoinRootSubfield M.carrier f hfirr α hα') (-1 : AlgebraicClosure K) := by
    intro hmem
    obtain ⟨H, hHev, hHinv⟩ := coneGen_lift_evenPosPoly M f hfirr (by omega) α hα' hmem
    let H' : M.carrier[X] := 1 + H
    have hH'ev : H'.eval₂ M.carrier.subtype α = 0 := by
      simp [H', eval₂_add, eval₂_one, hHev]
    have hH'inv : EvenPosPoly 2 H' := by
      have h2 : 2 * (f.natDegree - 1) = 2 := by omega
      rw [h2] at hHinv
      exact evenPosPoly_add (evenPosPoly_one 2) hHinv
    have hH'ne0 : H' ≠ 0 := by
      intro h0
      have hval : H'.eval 0 = 0 := by simp [h0]
      have hpos : (0 : M.carrier) < H'.eval 0 := by
        simp only [H', eval_add, eval_one]
        linarith [hHinv.1 0]
      linarith
    have hdiv : f ∣ H' := by
      by_contra hndiv
      rcases hfirr.coprime_iff_not_dvd.mpr hndiv with ⟨u, v, huv⟩
      have hev := congrArg (Polynomial.eval₂ M.carrier.subtype α) huv
      simp only [eval₂_add, eval₂_mul, eval₂_one, hα', hH'ev, mul_zero, add_zero] at hev
      exact zero_ne_one hev
    rcases hdiv with ⟨q, hq⟩
    have hq0 : q ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hq
      exact hH'ne0 hq
    rcases hH'inv.2 with h0 | ⟨_, hdle, hlcpos⟩
    · exact hH'ne0 h0
    have hqdeg : q.natDegree = 0 := by
      have hsum : H'.natDegree = f.natDegree + q.natDegree := by
        rw [hq, natDegree_mul hfirr.ne_zero hq0]
      omega
    have hqC : q = C (q.coeff 0) := eq_C_of_natDegree_eq_zero hqdeg
    have hqc0 : q.coeff 0 ≠ 0 := by
      intro h0
      apply hq0
      rw [hqC, h0, map_zero]
    have hflc : f.leadingCoeff = 1 :=
      (monic_X_pow_sub_C a (by decide : (2 : ℕ) ≠ 0)).leadingCoeff
    have hqpos : 0 < q.coeff 0 := by
      have hlc : H'.leadingCoeff = f.leadingCoeff * q.leadingCoeff := by
        rw [hq, leadingCoeff_mul]
      rw [hflc, one_mul, hqC, leadingCoeff_C] at hlc
      exact hlc ▸ hlcpos
    have hH'0 : H'.eval 0 = (-a) * q.coeff 0 := by
      rw [hq, eval_mul, hqC, eval_C]
      simp [f]
    have hH'0_pos : (0 : M.carrier) < H'.eval 0 := by
      simp only [H', eval_add, eval_one]
      linarith [hHinv.1 0]
    have hH'0_nonpos : H'.eval 0 ≤ 0 := by
      rw [hH'0]
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha) hqpos.le
    linarith
  have hαM : α ∈ M.carrier := root_mem_of_not_neg_one_mem_coneGen M hM f hfirr α hα' hneg1
  refine hnsq ⟨⟨α, hαM⟩, ?_⟩
  apply Subtype.ext
  have hsq : α ^ 2 - (a : AlgebraicClosure K) = 0 := by
    simpa [f, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C] using hα'
  have heq : (a : AlgebraicClosure K) = α * α := by
    linear_combination -hsq
  exact heq

lemma maximal_exists_isRoot_of_odd_natDegree (M : OrderedSubfield K) (hM : IsMax M) :
    letI : LinearOrder M.carrier := M.toLinearOrder
    letI : IsStrictOrderedRing M.carrier := M.toIsStrictOrderedRing
    ∀ {n : ℕ}, Odd n → ∀ f : M.carrier[X], f.natDegree = n → ∃ x : M.carrier, f.IsRoot x := by
  letI : LinearOrder M.carrier := M.toLinearOrder
  letI : IsStrictOrderedRing M.carrier := M.toIsStrictOrderedRing
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hodd f hfdeg
    by_cases hn1 : n = 1
    · have hf1 : f.natDegree = 1 := hfdeg.trans hn1
      have hf0 : f ≠ 0 := by
        intro h0
        rw [h0, natDegree_zero] at hf1
        omega
      refine ⟨-(f.coeff 0) / f.coeff 1, ?_⟩
      have h1ne : f.coeff 1 ≠ 0 := by
        rw [← hf1]
        exact leadingCoeff_ne_zero.mpr hf0
      rw [IsRoot.def, eq_X_add_C_of_natDegree_le_one (le_of_eq hf1)]
      simp [eval_add, eval_mul, eval_C, eval_X]
      field_simp [h1ne]
      ring
    · have hn_ge3 : 3 ≤ n := by
        rcases hodd with ⟨k, rfl⟩
        omega
      by_cases hfirr : Irreducible f
      · have hdeg_map : (f.map M.carrier.subtype).degree ≠ 0 := by
          rw [degree_map_eq_of_injective M.carrier.subtype_injective,
            degree_eq_natDegree hfirr.ne_zero, hfdeg]
          intro h
          have hn0 : n = 0 := by exact_mod_cast h
          omega
        obtain ⟨α, hα⟩ := IsAlgClosed.exists_root (f.map M.carrier.subtype) hdeg_map
        have hα' : f.eval₂ M.carrier.subtype α = 0 := by
          simpa [IsRoot.def, eval_map] using hα
        have hneg1 : ¬ ConeGen M.pos (adjoinRootSubfield M.carrier f hfirr α hα') (-1 : AlgebraicClosure K) := by
          intro hmem
          obtain ⟨H, hHev, hHinv⟩ := coneGen_lift_evenPosPoly M f hfirr (by omega) α hα' hmem
          let H' : M.carrier[X] := 1 + H
          have hH'ev : H'.eval₂ M.carrier.subtype α = 0 := by
            simp [H', eval₂_add, eval₂_one, hHev]
          have hH'inv : EvenPosPoly (2 * (f.natDegree - 1)) H' :=
            evenPosPoly_add (evenPosPoly_one _) hHinv
          have hH'pos : ∀ r : M.carrier, 0 < H'.eval r := fun r => by
            simp only [H', eval_add, eval_one]
            linarith [hHinv.1 r]
          have hH'ne0 : H' ≠ 0 := by
            intro h0
            have := hH'pos 0
            simp [h0] at this
          have hdiv : f ∣ H' := by
            by_contra hndiv
            rcases hfirr.coprime_iff_not_dvd.mpr hndiv with ⟨u, v, huv⟩
            have hev := congrArg (Polynomial.eval₂ M.carrier.subtype α) huv
            simp only [eval₂_add, eval₂_mul, eval₂_one, hα', hH'ev, mul_zero, add_zero] at hev
            exact zero_ne_one hev
          rcases hdiv with ⟨q, hq⟩
          have hq0 : q ≠ 0 := by
            intro h0
            rw [h0, mul_zero] at hq
            exact hH'ne0 hq
          rcases hH'inv.2 with h0 | ⟨heven, hdle, _⟩
          · exact hH'ne0 h0
          have hsum : H'.natDegree = n + q.natDegree := by
            rw [hq, natDegree_mul hfirr.ne_zero hq0, hfdeg]
          have hq_lt : q.natDegree < n := by omega
          have hq_odd : Odd q.natDegree := by
            rcases heven with ⟨m, hm⟩
            rcases hodd with ⟨k, hk⟩
            refine ⟨m - k - 1, ?_⟩
            omega
          obtain ⟨r, hr⟩ := ih q.natDegree hq_lt hq_odd q rfl
          have h0 : H'.eval r = 0 := by
            rw [hq, eval_mul, hr.eq_zero, mul_zero]
          linarith [hH'pos r]
        have hαM : α ∈ M.carrier := root_mem_of_not_neg_one_mem_coneGen M hM f hfirr α hα' hneg1
        refine ⟨⟨α, hαM⟩, ?_⟩
        rw [IsRoot.def]
        apply Subtype.ext
        have hev : ((f.eval (⟨α, hαM⟩ : M.carrier) : M.carrier) : AlgebraicClosure K) =
            f.eval₂ M.carrier.subtype α := by
          change M.carrier.subtype (f.eval₂ (RingHom.id _) (⟨α, hαM⟩ : M.carrier)) =
            f.eval₂ M.carrier.subtype α
          rw [Polynomial.hom_eval₂]
          rfl
        rw [hev, hα']
        rfl
      · have hnu : ¬ IsUnit f := by
          intro hu
          have := natDegree_eq_zero_of_isUnit hu
          omega
        have hfac : ∃ p q : M.carrier[X], f = p * q ∧ ¬ IsUnit p ∧ ¬ IsUnit q := by
          by_contra h
          push_neg at h
          apply hfirr
          refine ⟨hnu, fun p q hpq => ?_⟩
          by_contra hboth
          push_neg at hboth
          exact hboth.2 (h p q hpq hboth.1)
        obtain ⟨p, q, hpq, hpu, hqu⟩ := hfac
        have hp0 : p ≠ 0 := by
          intro h0
          rw [h0, zero_mul] at hpq
          have := congrArg natDegree hpq
          simp [hfdeg] at this
          omega
        have hq0 : q ≠ 0 := by
          intro h0
          rw [h0, mul_zero] at hpq
          have := congrArg natDegree hpq
          simp [hfdeg] at this
          omega
        have hp_pos : 1 ≤ p.natDegree := by
          by_contra h
          have h0 : p.natDegree = 0 := by omega
          exact hpu (isUnit_iff_degree_eq_zero.mpr (degree_eq_iff_natDegree_eq hp0 |>.mpr h0))
        have hq_pos : 1 ≤ q.natDegree := by
          by_contra h
          have h0 : q.natDegree = 0 := by omega
          exact hqu (isUnit_iff_degree_eq_zero.mpr (degree_eq_iff_natDegree_eq hq0 |>.mpr h0))
        have hsum : p.natDegree + q.natDegree = n := by
          rw [← natDegree_mul hp0 hq0, ← hpq, hfdeg]
        rcases Nat.even_or_odd p.natDegree with hpe | hpo
        · have hqo : Odd q.natDegree := by
            rcases hpe with ⟨a, ha⟩
            rcases hodd with ⟨k, hk⟩
            refine ⟨k - a, ?_⟩
            omega
          obtain ⟨r, hr⟩ := ih q.natDegree (by omega) hqo q rfl
          exact ⟨r, by rw [hpq, IsRoot.def, eval_mul, hr.eq_zero, mul_zero]⟩
        · obtain ⟨r, hr⟩ := ih p.natDegree (by omega) hpo p rfl
          exact ⟨r, by rw [hpq, IsRoot.def, eval_mul, hr.eq_zero, zero_mul]⟩

end RealClosedProof

end Hilbert17H2

theorem OMA.solution : OMA.R_Hilbert17_hilbert_17th_problem_R1.H2 := by
  intro K _ _ _
  obtain ⟨M, hM⟩ := Hilbert17H2.exists_maximal_orderedSubfield (K := K)
  letI : LinearOrder M.carrier := M.toLinearOrder
  letI : IsStrictOrderedRing M.carrier := M.toIsStrictOrderedRing
  have hrc : IsRealClosed M.carrier :=
    IsRealClosed.of_linearOrderedField
      (Hilbert17H2.maximal_isSquare_of_nonneg M hM)
      (fun {f} hf => Hilbert17H2.maximal_exists_isRoot_of_odd_natDegree M hM hf f rfl)
  let ι : K →+* M.carrier :=
    { toFun := fun x => ⟨algebraMap K (AlgebraicClosure K) x, by
        rcases le_total (0 : K) x with h | h
        · exact M.pos_sub (M.base_pos x h)
        · have hneg := M.pos_sub (M.base_pos (-x) (neg_nonneg.mpr h))
          rw [map_neg] at hneg
          simpa using M.carrier.neg_mem hneg⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun x y => Subtype.ext (map_mul _ _ _)
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun x y => Subtype.ext (map_add _ _ _) }
  refine ⟨M.carrier, inferInstance, M.toLinearOrder, M.toIsStrictOrderedRing, hrc, ι, ?_⟩
  intro x hx
  change ((ι x : M.carrier) : AlgebraicClosure K) - 0 ∈ M.pos
  simpa [ι] using M.base_pos x hx
