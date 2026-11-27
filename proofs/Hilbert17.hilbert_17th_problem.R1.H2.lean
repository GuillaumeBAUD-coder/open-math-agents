import OMAReductions.R_Hilbert17_hilbert_17th_problem_R1
import Mathlib

/- The preordering argument and odd irreducible factor lemma adapt work of
Florent Schaffhauser and Artie Khovanov in artie2000/real_closed_field,
RealClosedField/Algebra/Order/Ring/Ordering/Extend.lean and RealClosedField/Upstream.lean,
revision 24ec7b819140a17848e88e7d6decde198a140918. Used under Apache-2.0.
Copyright (c) 2024 Florent Schaffhauser. All rights reserved.
Copyright (c) 2025 Artie Khovanov. All rights reserved.

For odd-degree extensions, lift a putative sum of squares equal to negative one
to a positive polynomial. A smaller odd-degree factor would vanish in an
ordered extension by induction, contradicting positivity there.
Finally use Zorn on signed cones in an algebraic closure to absorb both kinds
of ordered algebraic extensions. -/
open Polynomial
namespace LocalReal17

lemma order_preordering {F : Type} [Field F] (P : RingPreordering F) :
    ∃ (_ : LinearOrder F) (_ : IsStrictOrderedRing F), ∀ z ∈ P, 0 ≤ z := by
  classical
  let good (B : Subsemiring F) := (∀ x : F, x*x ∈ B) ∧ -1 ∉ B
  have chain : ∀ c ⊆ {B | good B}, IsChain (· ≤ ·) c → ∀ y ∈ c,
      ∃ B ∈ {B | good B}, ∀ u ∈ c, u ≤ B := by
    intro c hc hdir y hy
    letI : Nonempty c := ⟨⟨y,hy⟩⟩
    let B := ⨆ u : c, u.val
    have mem (x : F) : x ∈ B ↔ ∃ u : c, x ∈ u.val :=
      Subsemiring.mem_iSup_of_directed hdir.directedOn.directed_val
    refine ⟨B,⟨fun x => (mem _).mpr ⟨⟨y,hy⟩,(hc hy).1 x⟩,?_⟩,fun u hu => le_iSup (fun v : c => v.val) ⟨u,hu⟩⟩
    intro h
    obtain ⟨u,hu⟩ := (mem _).mp h
    exact (hc u.property).2 hu
  obtain ⟨B,hPB,hB⟩ := zorn_le_nonempty₀ {B | good B} chain P.toSubsemiring
    ⟨P.mul_self_mem,P.neg_one_notMem⟩
  let M := RingPreordering.mk' (B : Set F) B.add_mem B.mul_mem hB.prop.1 hB.prop.2
  have total (a : F) : a ∈ B ∨ -a ∈ B := by
    by_cases ha : -a ∈ B
    · exact Or.inr ha
    let T := Subsemiring.closure (insert a (B : Set F))
    have inc : B ≤ T := fun x hx => Subsemiring.subset_closure (Set.mem_insert_of_mem _ hx)
    have repr {x : F} (hx : x ∈ T) : ∃ u ∈ B, ∃ v ∈ B, x = u+a*v := by
      induction hx using Subsemiring.closure_induction with
      | mem x hx =>
        rcases hx with rfl|hx
        · exact ⟨0,B.zero_mem,1,B.one_mem,by ring⟩
        · exact ⟨x,hx,0,B.zero_mem,by ring⟩
      | zero => exact ⟨0,B.zero_mem,0,B.zero_mem,by ring⟩
      | one => exact ⟨1,B.one_mem,0,B.zero_mem,by ring⟩
      | add x y _ _ hx hy =>
        obtain ⟨u,hu,v,hv,rfl⟩ := hx
        obtain ⟨s,hs,t,ht,rfl⟩ := hy
        exact ⟨u+s,B.add_mem hu hs,v+t,B.add_mem hv ht,by ring⟩
      | mul x y _ _ hx hy =>
        obtain ⟨u,hu,v,hv,rfl⟩ := hx
        obtain ⟨s,hs,t,ht,rfl⟩ := hy
        exact ⟨u*s + a*a*(v*t),B.add_mem (B.mul_mem hu hs) (B.mul_mem (hB.prop.1 a) (B.mul_mem hv ht)),
          u*t+s*v,B.add_mem (B.mul_mem hu ht) (B.mul_mem hs hv),by ring⟩
    have proper : -1 ∉ T := by
      intro h
      obtain ⟨u,hu,v,hv,e⟩ := repr h
      by_cases h0 : v = 0
      · have hu' : (-1 : F) = u := by simpa [h0] using e
        exact hB.prop.2 (hu' ▸ hu)
      · have eq : -a = (1+u)*v⁻¹ := by field_simp; linear_combination e
        exact ha (eq ▸ B.mul_mem (B.add_mem B.one_mem hu) (RingPreordering.inv_mem (P := M) hv))
    exact Or.inl <| hB.le_of_ge ⟨fun x => inc (hB.prop.1 x),proper⟩ inc
      (Subsemiring.subset_closure (Set.mem_insert a _))
  let C : RingCone F := ⟨B,fun hx hn => M.eq_zero_of_mem_of_neg_mem hx hn⟩
  letI : HasMemOrNegMem C := ⟨total⟩
  letI : LinearOrder F := .mkOfAddGroupCone C
  letI : IsOrderedRing F := IsOrderedRing.mkOfCone C
  refine ⟨inferInstance,inferInstance,fun z hz => ?_⟩
  change z-0 ∈ B
  simpa using hPB hz

lemma quad_re_nonneg {F : Type} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    {a c : F} (ha : 0 ≤ a) (hc : 0 ≤ c) (y : QuadraticAlgebra F a 0) :
    0 ≤ ((algebraMap F (QuadraticAlgebra F a 0) c) * (y*y)).re := by
  rw [QuadraticAlgebra.re_mul, QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.algebraMap_im,
    mul_zero, zero_mul, add_zero, QuadraticAlgebra.re_mul]
  exact mul_nonneg hc (add_nonneg (mul_self_nonneg _) (by nlinarith [mul_nonneg ha (mul_self_nonneg y.im)]))

lemma square_extension (order : ∀ {E : Type} [Field E] (P : RingPreordering E),
    ∃ (_ : LinearOrder E) (_ : IsStrictOrderedRing E), ∀ z ∈ P, 0 ≤ z)
    {F : Type} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    (a : F) (ha : 0 ≤ a) (hns : ¬ IsSquare a) :
    ∃ (E : Type) (_ : Field E) (_ : LinearOrder E) (_ : IsStrictOrderedRing E)
      (_ : Algebra F E) (_ : Algebra.IsAlgebraic F E),
      (∀ x : F, 0 ≤ x → 0 ≤ algebraMap F E x) ∧ IsSquare (algebraMap F E a) := by
  classical
  letI : Fact (∀ r : F, r ^ 2 ≠ a + 0 * r) := ⟨fun r h => hns ⟨r,by simpa [pow_two] using h.symm⟩⟩
  let E := QuadraticAlgebra F a 0
  let W : Set E := {z | ∃ c : F, 0 ≤ c ∧ ∃ y : E, z = algebraMap F E c * (y*y)}
  let S := AddSubmonoid.closure W
  have mulc {x y : E} (hx : x ∈ S) (hy : y ∈ S) : x*y ∈ S := by
    apply AddSubmonoid.closure_induction₂ (motive := fun x y _ _ => x*y ∈ S) ?_ ?_ ?_ ?_ ?_ hx hy
    · rintro _ _ ⟨c,hc,u,rfl⟩ ⟨d,hd,v,rfl⟩
      exact AddSubmonoid.subset_closure ⟨c*d,mul_nonneg hc hd,u*v,by rw [map_mul]; ring⟩
    · intro y _; simpa using S.zero_mem
    · intro x _; simpa using S.zero_mem
    · intro x y z _ _ _ h k; simpa [add_mul] using S.add_mem h k
    · intro x y z _ _ _ h k; simpa [mul_add] using S.add_mem h k
  have positive {x : E} (hx : x ∈ S) : 0 ≤ x.re := by
    induction hx using AddSubmonoid.closure_induction with
    | mem x hx =>
      obtain ⟨c,hc,y,rfl⟩ := hx
      exact quad_re_nonneg ha hc y
    | zero => exact le_rfl
    | add x y _ _ hx hy => exact add_nonneg hx hy
  let P := RingPreordering.mk' (S : Set E) S.add_mem mulc
    (fun y => AddSubmonoid.subset_closure ⟨1,zero_le_one,y,by simp⟩)
    (fun h => by have h' := positive h; change (0 : F) ≤ -1 at h'; linarith)
  obtain ⟨lo,strict,hP⟩ := order P
  refine ⟨E,inferInstance,lo,strict,inferInstance,inferInstance,?_,?_⟩
  · intro x hx
    exact hP _ (AddSubmonoid.subset_closure ⟨x,hx,1,by simp⟩)
  · refine ⟨QuadraticAlgebra.omega,?_⟩
    exact (QuadraticAlgebra.omega_mul_omega_eq_mk (R := F) (a := a) (b := 0)).symm

lemma odd_factor {F : Type} [Field F] {f : F[X]} (hf : Odd f.natDegree) :
    ∃ g : F[X], Odd g.natDegree ∧ g.Monic ∧ Irreducible g ∧ g ∣ f := by
  induction h : f.natDegree using Nat.strong_induction_on generalizing f with | h n ih =>
    have hu : ¬ IsUnit f := not_isUnit_of_natDegree_pos _ (Odd.pos hf)
    rcases exists_monic_irreducible_factor f hu with ⟨g,gm,gi,gd⟩
    by_cases ho : Odd g.natDegree
    · exact ⟨g,ho,gm,gi,gd⟩
    · rcases gd with ⟨k,rfl⟩
      have ke : k ≠ 0 := by rintro rfl; simp at hf
      have deg := natDegree_mul gi.ne_zero ke
      have kg : Odd k.natDegree := by grind
      obtain ⟨p,hp,pm,pi,pd⟩ := ih k.natDegree (by have := gi.natDegree_pos; omega) kg rfl
      exact ⟨p,hp,pm,pi,dvd_trans pd (dvd_mul_left ..)⟩

lemma pos_even_add {F : Type} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    {p q : F[X]} (hp : 0 < p.leadingCoeff) (hq : 0 < q.leadingCoeff)
    (he : Even p.natDegree) (hf : Even q.natDegree) :
    0 < (p+q).leadingCoeff ∧ Even (p+q).natDegree := by
  rcases lt_trichotomy p.degree q.degree with h|h|h
  · simpa [leadingCoeff_add_of_degree_lt h,natDegree_add_eq_right_of_degree_lt h] using And.intro hq hf
  · have hn := (add_pos hp hq).ne'
    have hd : (p+q).degree = p.degree := by rw [degree_add_eq_of_leadingCoeff_add_ne_zero hn,h,max_self]
    exact ⟨by rw [leadingCoeff_add_of_degree_eq h hn]; exact add_pos hp hq,
      by rwa [natDegree,hd]⟩
  · simpa [leadingCoeff_add_of_degree_lt' h,natDegree_add_eq_left_of_degree_lt h] using And.intro hp he

lemma lift_positive {F : Type} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    {f : F[X]} (hf : f.Monic) (hi : Irreducible f) {s : AdjoinRoot f} (hs : IsSumSq s) :
    ∃ p : F[X], AdjoinRoot.mk f p = 1+s ∧ 0 < p.leadingCoeff ∧ Even p.natDegree ∧
      p.natDegree < 2*f.natDegree ∧
      ∀ (E : Type) [Field E] [LinearOrder E] [IsStrictOrderedRing E] [Algebra F E]
        (r : E), 0 < p.aeval r := by
  have hn := hi.natDegree_pos
  induction hs with
  | zero =>
    refine ⟨1,by simp,by simp,by simp,by simp; omega,?_⟩
    intro E _ _ _ _ r; simp
  | @sq_add y s _ ih =>
    obtain ⟨p,hp,hc,he,hd,hpos⟩ := ih
    obtain ⟨b,hb⟩ := AdjoinRoot.mk_surjective (g := f) y
    let t := b %ₘ f
    have hdeg : t.natDegree < f.natDegree := natDegree_modByMonic_lt b hf (fun e => hi.not_isUnit (e ▸ isUnit_one))
    have ht : AdjoinRoot.mk f t = y := by
      rw [← hb]; simpa [t] using AdjoinRoot.mk_leftInverse hf (AdjoinRoot.mk f b)
    refine ⟨t*t+p,by rw [map_add,map_mul,ht,hp]; ring,?_,?_,?_,?_⟩
    · by_cases hz : t = 0
      · simpa [hz] using hc
      · exact (pos_even_add (p := t*t) (by rw [leadingCoeff_mul]; exact mul_self_pos.mpr (leadingCoeff_ne_zero.mpr hz)) hc
          (by rw [natDegree_mul hz hz]; exact Even.add_self _) he).1
    · by_cases hz : t = 0
      · simpa [hz] using he
      · exact (pos_even_add (p := t*t) (by rw [leadingCoeff_mul]; exact mul_self_pos.mpr (leadingCoeff_ne_zero.mpr hz)) hc
          (by rw [natDegree_mul hz hz]; exact Even.add_self _) he).2
    · apply lt_of_le_of_lt (natDegree_add_le ..)
      exact max_lt (by have := natDegree_mul_le (p := t) (q := t); omega) hd
    · intro E _ _ _ _ r
      simpa only [map_add,map_mul] using add_pos_of_nonneg_of_pos (mul_self_nonneg (t.aeval r)) (hpos E r)

lemma odd_extension (order : ∀ {E : Type} [Field E] (P : RingPreordering E),
    ∃ (_ : LinearOrder E) (_ : IsStrictOrderedRing E), ∀ z ∈ P, 0 ≤ z)
    {F : Type} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    (sq : ∀ a : F, 0 ≤ a → IsSquare a) (f : F[X]) (hf : Odd f.natDegree) :
    ∃ (E : Type) (_ : Field E) (_ : LinearOrder E) (_ : IsStrictOrderedRing E)
      (_ : Algebra F E) (_ : Algebra.IsAlgebraic F E),
      (∀ x : F, 0 ≤ x → 0 ≤ algebraMap F E x) ∧ ∃ y : E, f.aeval y = 0 := by
  classical
  induction n : f.natDegree using Nat.strong_induction_on generalizing f with | h n ih =>
    obtain ⟨g,go,gm,gi,gd⟩ := odd_factor hf
    have fne : f ≠ 0 := by rintro rfl; simp at hf
    have gle := natDegree_le_of_dvd gd fne
    letI : Fact (Irreducible g) := ⟨gi⟩
    have proper : ¬ IsSumSq (-1 : AdjoinRoot g) := by
      intro hs
      obtain ⟨p,hp,hc,he,hd,hpos⟩ := lift_positive gm gi hs
      obtain ⟨q,hq⟩ := AdjoinRoot.mk_eq_zero.mp (show AdjoinRoot.mk g p = 0 by simpa using hp)
      have pne : p ≠ 0 := by intro h; simp [h] at hc
      have qne : q ≠ 0 := by rintro rfl; simp_all
      have ds : p.natDegree = g.natDegree + q.natDegree := by rw [hq,natDegree_mul gi.ne_zero qne]
      have qo : Odd q.natDegree := by grind
      obtain ⟨E,_,_,_,_,_,_,r,hr⟩ := ih q.natDegree (by omega) q qo rfl
      have hz : p.aeval r = 0 := by rw [hq,map_mul,hr,mul_zero]
      exact (hpos E r).ne' hz
    let P := RingPreordering.mk' {z : AdjoinRoot g | IsSumSq z}
      (fun h k => IsSumSq.add h k) (fun h k => IsSumSq.mul h k) IsSumSq.mul_self proper
    obtain ⟨lo,strict,hP⟩ := order P
    letI : Module.Finite F (AdjoinRoot g) := Module.Finite.of_basis (AdjoinRoot.powerBasis gi.ne_zero).basis
    refine ⟨AdjoinRoot g,inferInstance,lo,strict,inferInstance,inferInstance,?_,AdjoinRoot.root g,?_⟩
    · intro x hx
      obtain ⟨r,hr⟩ := sq x hx
      rw [hr,map_mul]
      exact mul_self_nonneg _
    · rw [AdjoinRoot.aeval_eq]
      exact AdjoinRoot.mk_eq_zero.mpr gd

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

end LocalReal17
open LocalReal17

theorem OMA.solution : OMA.R_Hilbert17_hilbert_17th_problem_R1.H2 := by
  intro K _ _ _
  obtain ⟨F,_,_,_,ι,hi,hmax⟩ := maximal_extension K
  have sq (a : F) (ha : 0 ≤ a) : IsSquare a := by
    by_contra h
    obtain ⟨E,_,_,_,_,_,hE,y,hy⟩ := square_extension order_preordering a ha h
    obtain ⟨r,hr⟩ := hmax E hE y
    exact h ⟨r,(algebraMap F E).injective (by simpa [map_mul,hr] using hy)⟩
  refine ⟨F,inferInstance,inferInstance,inferInstance,IsRealClosed.of_linearOrderedField
    (fun h => sq _ h) (fun {f} hf => ?_),ι,hi⟩
  obtain ⟨E,_,_,_,_,_,hE,y,hy⟩ := odd_extension order_preordering sq f hf
  obtain ⟨r,hr⟩ := hmax E hE y
  refine ⟨r,(algebraMap F E).injective ?_⟩
  simpa [Polynomial.IsRoot, ← hr, Polynomial.aeval_algebraMap_apply] using hy

