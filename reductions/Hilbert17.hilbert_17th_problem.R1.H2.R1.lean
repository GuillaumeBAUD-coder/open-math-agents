import OMAReductions.R_Hilbert17_hilbert_17th_problem_R1
import Mathlib

/-! A maximal cone of an ordered subfield inside an algebraic closure
absorbs every compatible ordered algebraic extension. Consequently
one-element extension theorems for square roots and odd-degree roots are
sufficient for existence of the real closure. -/

open Polynomial
namespace OMA.R_Hilbert17_hilbert_17th_problem_R1_H2_R1

def H1 : Prop := ∀ {F : Type} [Field F] [LinearOrder F] [IsStrictOrderedRing F],
  ∀ a : F, 0 ≤ a → ¬ IsSquare a →
    ∃ (E : Type) (_ : Field E) (_ : LinearOrder E) (_ : IsStrictOrderedRing E)
      (_ : Algebra F E) (_ : Algebra.IsAlgebraic F E),
      (∀ x : F, 0 ≤ x → 0 ≤ algebraMap F E x) ∧ IsSquare (algebraMap F E a)

def H2 : Prop := ∀ {F : Type} [Field F] [LinearOrder F] [IsStrictOrderedRing F],
  (∀ a : F, 0 ≤ a → IsSquare a) → ∀ f : F[X], Odd f.natDegree →
    ∃ (E : Type) (_ : Field E) (_ : LinearOrder E) (_ : IsStrictOrderedRing E)
      (_ : Algebra F E) (_ : Algebra.IsAlgebraic F E),
      (∀ x : F, 0 ≤ x → 0 ≤ algebraMap F E x) ∧ ∃ y : E, f.aeval y = 0

lemma image_properties {F Ω : Type} [Field F] [LinearOrder F] [IsStrictOrderedRing F] [Field Ω]
    (j : F →+* Ω) :
    let P := (RingCone.nonneg F).toSubsemiring.map j
    (∀ x ∈ P, -x ∈ P → x = 0) ∧ (∀ x ∈ P, x⁻¹ ∈ P) ∧
    ∀ x ∈ P, ∀ y ∈ P, x-y ∈ P ∨ y-x ∈ P := by
  constructor
  · rintro _ ⟨a,ha,rfl⟩ ⟨b,hb,e⟩
    change 0 ≤ a at ha
    change 0 ≤ b at hb
    have he : b = -a := j.injective (by simpa using e)
    rw [he] at hb
    simp [show a=0 by linarith]
  constructor
  · rintro _ ⟨a,ha,rfl⟩
    exact ⟨a⁻¹, inv_nonneg.mpr ha, map_inv₀ _ _⟩
  · rintro _ ⟨a,ha,rfl⟩ _ ⟨b,hb,rfl⟩
    rcases le_total b a with h|h
    · exact Or.inl ⟨a-b, sub_nonneg.mpr h, map_sub _ _ _⟩
    · exact Or.inr ⟨b-a, sub_nonneg.mpr h, map_sub _ _ _⟩

lemma cone_field {Ω : Type} [Field Ω] (P : Subsemiring Ω)
    (hinv : ∀ x ∈ P, x⁻¹ ∈ P) (hdiff : ∀ x ∈ P, ∀ y ∈ P, x-y ∈ P ∨ y-x ∈ P) :
    ∃ L : Subfield Ω, ∀ x : Ω, x ∈ L ↔ x ∈ P ∨ -x ∈ P := by
  refine ⟨{
    carrier := {x | x ∈ P ∨ -x ∈ P}
    zero_mem' := Or.inl P.zero_mem
    one_mem' := Or.inl P.one_mem
    neg_mem' := fun h => by rcases h with h|h; exact Or.inr (by simpa only [neg_neg] using h); exact Or.inl h
    inv_mem' := fun x h => by rcases h with h|h; exact Or.inl (hinv _ h); exact Or.inr (by simpa only [inv_neg] using hinv _ h)
    mul_mem' := fun {a b} ha hb => by
      rcases ha with h|h <;> rcases hb with k|k
      · exact Or.inl (P.mul_mem h k)
      · exact Or.inr (by simpa only [mul_neg,neg_mul,neg_neg] using P.mul_mem h k)
      · exact Or.inr (by simpa only [mul_neg,neg_mul,neg_neg] using P.mul_mem h k)
      · exact Or.inl (by simpa only [mul_neg,neg_mul,neg_neg] using P.mul_mem h k)
    add_mem' := fun {a b} ha hb => by
      rcases ha with h|h <;> rcases hb with k|k
      · exact Or.inl (P.add_mem h k)
      · simpa [sub_eq_add_neg, neg_add, neg_neg, add_comm] using hdiff _ h _ k
      · simpa [sub_eq_add_neg, neg_add, neg_neg, add_comm] using hdiff _ k _ h
      · exact Or.inr (by simpa [neg_add, add_comm] using P.add_mem h k) },fun _ => Iff.rfl⟩

lemma maximal_extension (K : Type) [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    ∃ (F : Type) (_ : Field F) (_ : LinearOrder F) (_ : IsStrictOrderedRing F)
      (j : K →+* F), (∀ a : K, 0 ≤ a → 0 ≤ j a) ∧
      ∀ (E : Type) [Field E] [LinearOrder E] [IsStrictOrderedRing E] [Algebra F E]
      [Algebra.IsAlgebraic F E], (∀ a : F, 0 ≤ a → 0 ≤ algebraMap F E a) →
        Function.Surjective (algebraMap F E) := by
  classical
  let Ω := AlgebraicClosure K
  let j := algebraMap K Ω
  let good (P : Subsemiring Ω) : Prop :=
    (∀ x ∈ P, -x ∈ P → x = 0) ∧ (∀ x ∈ P, x⁻¹ ∈ P) ∧
    ∀ x ∈ P, ∀ y ∈ P, x-y ∈ P ∨ y-x ∈ P
  let P₀ := (RingCone.nonneg K).toSubsemiring.map j
  have init : good P₀ := image_properties j
  have chain : ∀ c ⊆ {P | good P}, IsChain (· ≤ ·) c → ∀ y ∈ c,
      ∃ ub ∈ {P | good P}, ∀ z ∈ c, z ≤ ub := by
    intro c hc hchain y hy
    letI : Nonempty c := ⟨⟨y,hy⟩⟩
    let U := ⨆ u : c, u.val
    have dir : Directed (· ≤ ·) (fun u : c => u.val) := hchain.directedOn.directed_val
    have mem (x : Ω) : x ∈ U ↔ ∃ u : c, x ∈ u.val := Subsemiring.mem_iSup_of_directed dir
    have both {a b : Ω} (ha : a ∈ U) (hb : b ∈ U) :
        ∃ u : c, a ∈ u.val ∧ b ∈ u.val := by
      obtain ⟨A,hA⟩ := (mem a).mp ha
      obtain ⟨B,hB⟩ := (mem b).mp hb
      obtain ⟨C,hAC,hBC⟩ := dir A B
      exact ⟨C,hAC hA,hBC hB⟩
    refine ⟨U, ⟨?_,?_,?_⟩, fun z hz => le_iSup (fun u : c => u.val) ⟨z,hz⟩⟩
    · intro x hx hn
      obtain ⟨u,ha,hb⟩ := both hx hn
      exact (hc u.property).1 x ha hb
    · intro x hx
      obtain ⟨u,hx⟩ := (mem x).mp hx
      exact (mem _).mpr ⟨u,(hc u.property).2.1 _ hx⟩
    · intro x hx y hy
      obtain ⟨u,ha,hb⟩ := both hx hy
      exact ((hc u.property).2.2 _ ha _ hb).imp (fun h => (mem _).mpr ⟨u,h⟩)
        (fun h => (mem _).mpr ⟨u,h⟩)
  obtain ⟨P,hP₀,hmax⟩ := zorn_le_nonempty₀ {P | good P} chain P₀ init
  obtain ⟨hpt,hinv,hdiff⟩ := hmax.prop
  obtain ⟨L,hL⟩ := cone_field P hinv hdiff
  let C : RingCone L := ⟨P.comap L.subtype, fun {a} ha hn => Subtype.ext (hpt a ha hn)⟩
  letI : HasMemOrNegMem C := ⟨fun x => (hL _).mp x.property⟩
  letI : LinearOrder L := .mkOfAddGroupCone C
  letI : IsOrderedRing L := IsOrderedRing.mkOfCone C
  have nonneg (x : L) : 0 ≤ x ↔ x.val ∈ P := by
    change (x-0 : L).val ∈ P ↔ _
    simp
  have base {x : K} (hx : 0≤x) : j x ∈ P := hP₀ ⟨x,hx,rfl⟩
  let ι : K →+* L := j.codRestrict L fun x => by
    apply (hL _).mpr
    rcases le_total 0 x with h|h
    · exact Or.inl (base h)
    · exact Or.inr (by simpa using base (neg_nonneg.mpr h))
  refine ⟨L,inferInstance,inferInstance,inferInstance,ι,fun a ha => (nonneg _).mpr (base ha), ?_⟩
  intro E _ _ _ _ _ hE
  let e : E →ₐ[L] Ω := IsAlgClosed.lift
  let Q := (RingCone.nonneg E).toSubsemiring.map (e : E →+* Ω)
  have hPQ : P ≤ Q := by
    intro x hx
    let a : L := ⟨x,(hL _).mpr (Or.inl hx)⟩
    exact ⟨algebraMap L E a,hE a ((nonneg a).mpr hx),e.commutes a⟩
  have hQP : Q ≤ P := hmax.le_of_ge (image_properties (e : E →+* Ω)) hPQ
  intro y
  have hy : e y ∈ L := by
    apply (hL _).mpr
    rcases le_total 0 y with h|h
    · exact Or.inl (hQP ⟨y,h,rfl⟩)
    · exact Or.inr (hQP ⟨-y,neg_nonneg.mpr h,map_neg _ _⟩)
  exact ⟨⟨e y,hy⟩, e.injective (e.commutes _)⟩

theorem main : H1 → H2 → OMA.R_Hilbert17_hilbert_17th_problem_R1.H2 := by
  intro hroot hodd K _ _ _
  obtain ⟨F,_,_,_,ι,hi,hmax⟩ := maximal_extension K
  have sq (a : F) (ha : 0 ≤ a) : IsSquare a := by
    by_contra h
    obtain ⟨E,_,_,_,_,_,hE,y,hy⟩ := hroot a ha h
    obtain ⟨r,hr⟩ := hmax E hE y
    exact h ⟨r,(algebraMap F E).injective (by simpa [map_mul,hr] using hy)⟩
  refine ⟨F,inferInstance,inferInstance,inferInstance,IsRealClosed.of_linearOrderedField
    (fun h => sq _ h) (fun {f} hf => ?_),ι,hi⟩
  obtain ⟨E,_,_,_,_,_,hE,y,hy⟩ := hodd sq f hf
  obtain ⟨r,hr⟩ := hmax E hE y
  refine ⟨r,(algebraMap F E).injective ?_⟩
  simpa [Polynomial.IsRoot, ← hr, Polynomial.aeval_algebraMap_apply] using hy

end OMA.R_Hilbert17_hilbert_17th_problem_R1_H2_R1
