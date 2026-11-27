import FormalConjectures.ErdosProblems.«19»

/-!
Reduce the Erdős–Faber–Lovász conjecture to critical finite linear families
of clique-index supports. Private vertices extend independently, as in the
pinned source. Passing to a smallest uncolorable family forces every support
to meet at least n others. A double count bounds its minimum rank.

If the large supports are intervals in one order, color each support by its
endpoint sum modulo n. This handles arbitrary pairs and, after permuting the
ground set, every family with at most two larger supports. The remaining cases
distinguish a family containing a pair from one of higher minimum rank.

For the dual formulation by linear set families and the use of modular colors
on pairs, see N. Hindman, Canadian Journal of Mathematics 33 (1981), 563–570.
-/

-- Credit: @zarnab222-dev

section

open Erdos19 Finset
namespace E19Transfer

private theorem support_transfer {V : Type*} {n : ℕ} (C : EFLConfig V n) (e : Fin n ≃ Fin n) :
    ∃ (S : V → Finset (Fin n)) (H : Finset (Finset (Fin n))),
      (∀ v i, e i ∈ S v ↔ v ∈ C.A i) ∧
      (∀ u v, u ≠ v → (S u ∩ S v).card ≤ 1) ∧
      (∀ A, A ∈ H ↔ ∃ v, S v = A ∧ 2 ≤ A.card) ∧
      (∀ A ∈ H, 2 ≤ A.card) ∧
      (∀ A ∈ H, ∀ B ∈ H, A ≠ B → (A ∩ B).card ≤ 1) ∧
      ((∃ c : H → Fin n, ∀ A B : H, A ≠ B → (A.val ∩ B.val).Nonempty → c A ≠ c B) →
        C.graph.chromaticNumber = n) := by
  classical
  let S (v : V) := ((univ : Finset (Fin n)).filter (fun i => v ∈ C.A i)).map e.toEmbedding
  let U := (univ : Finset (Fin n)).biUnion C.A
  let H := (U.image S).filter (fun A => 2 ≤ A.card)
  have mem (v : V) (i : Fin n) : e i ∈ S v ↔ v ∈ C.A i := by simp [S]
  have inv (v : V) (i : Fin n) : i ∈ S v ↔ v ∈ C.A (e.symm i) := by
    simpa only [e.apply_symm_apply] using mem v (e.symm i)
  have small (u v : V) (hne : u ≠ v) : (S u ∩ S v).card ≤ 1 := by
    apply card_le_one.mpr
    intro i hi j hj
    by_contra hn
    have h := C.inter_le (e.symm i) (e.symm j) (fun eq => hn (e.symm.injective eq))
    have hu : u ∈ C.A (e.symm i) ∩ C.A (e.symm j) :=
      mem_inter.mpr ⟨(inv u i).mp (mem_inter.mp hi).1,(inv u j).mp (mem_inter.mp hj).1⟩
    have hv : v ∈ C.A (e.symm i) ∩ C.A (e.symm j) :=
      mem_inter.mpr ⟨(inv v i).mp (mem_inter.mp hi).2,(inv v j).mp (mem_inter.mp hj).2⟩
    exact hne (card_le_one.mp h u hu v hv)
  have allU (v : V) : v ∈ U := by
    obtain ⟨i,hi⟩ := C.cover v
    exact mem_biUnion.mpr ⟨i,mem_univ _,hi⟩
  have memH (A) : A ∈ H ↔ ∃ v, S v = A ∧ 2 ≤ A.card := by
    constructor
    · intro h
      obtain ⟨v,_,hv⟩ := mem_image.mp (mem_filter.mp h).1
      exact ⟨v,hv,(mem_filter.mp h).2⟩
    · rintro ⟨v,rfl,hv⟩
      exact mem_filter.mpr ⟨mem_image_of_mem S (allU v),hv⟩
  have sz (A) (h : A ∈ H) : 2 ≤ A.card := (mem_filter.mp h).2
  have linear (A) (hA : A ∈ H) (B) (hB : B ∈ H) (hne : A ≠ B) : (A ∩ B).card ≤ 1 := by
    obtain ⟨u,rfl,_⟩ := (memH A).mp hA
    obtain ⟨v,rfl,_⟩ := (memH B).mp hB
    exact small u v (fun eq => hne (congrArg S eq))
  have shared (v : V) (h : C.IsShared v) : S v ∈ H := by
    obtain ⟨i,j,hn,hi,hj⟩ := h
    apply (memH _).mpr
    exact ⟨v,rfl,one_lt_card.mpr ⟨e i,(mem v i).mpr hi,e j,(mem v j).mpr hj,
      fun eq => hn (e.injective eq)⟩⟩
  refine ⟨S,H,mem,small,memH,sz,linear,?_⟩
  rintro ⟨c,hc⟩
  let col (v : V) := if h : S v ∈ H then c ⟨S v,h⟩ else e (C.cover v).choose
  refine le_antisymm (C.colorable_of_sharedColoring col ?_).chromaticNumber_le C.le_chromaticNumber
  intro i u v hu hv su sv heq
  by_contra hne
  have huH := shared u su
  have hvH := shared v sv
  have unequal : S u ≠ S v := by
    intro eq
    have bound := small u v hne
    rw [← eq,inter_self] at bound
    have := sz _ huH
    omega
  have diff := hc ⟨S u,huH⟩ ⟨S v,hvH⟩ (fun eq => unequal (congrArg Subtype.val eq))
    ⟨e i,mem_inter.mpr ⟨(mem u i).mpr hu,(mem v i).mpr hv⟩⟩
  exact diff (by simpa only [col,dif_pos huH,dif_pos hvH] using heq)

private theorem pullback_support_coloring {n : ℕ} (H : Finset (Finset (Fin n))) (e : Fin n ≃ Fin n)
    (hc : let K := H.image (Finset.map e.toEmbedding)
      ∃ c : K → Fin n, ∀ A B : K, A ≠ B → (A.val ∩ B.val).Nonempty → c A ≠ c B) :
    ∃ c : H → Fin n, ∀ A B : H, A ≠ B → (A.val ∩ B.val).Nonempty → c A ≠ c B := by
  classical
  let K := H.image (Finset.map e.toEmbedding)
  obtain ⟨c,proper⟩ := hc
  let f (A : H) : K := ⟨A.val.map e.toEmbedding,mem_image_of_mem _ A.property⟩
  refine ⟨fun A => c (f A),?_⟩
  intro A B hne hi
  apply proper (f A) (f B)
  · intro eq
    exact hne (Subtype.ext (Finset.map_injective _ (congrArg Subtype.val eq)))
  · obtain ⟨x,hx⟩ := hi
    exact ⟨e x,mem_inter.mpr ⟨mem_map_of_mem _ (mem_inter.mp hx).1,
      mem_map_of_mem _ (mem_inter.mp hx).2⟩⟩

private theorem relabel_support_bounds {n : ℕ} (H : Finset (Finset (Fin n))) (e : Fin n ≃ Fin n)
    (sz : ∀ A ∈ H, 2 ≤ A.card)
    (linear : ∀ A ∈ H, ∀ B ∈ H, A ≠ B → (A ∩ B).card ≤ 1) :
    let K := H.image (Finset.map e.toEmbedding)
    (∀ A ∈ K, 2 ≤ A.card) ∧ (∀ A ∈ K, ∀ B ∈ K, A ≠ B → (A ∩ B).card ≤ 1) := by
  constructor
  · intro A hA
    obtain ⟨U,hu,rfl⟩ := mem_image.mp hA
    simpa only [card_map] using sz U hu
  · intro A hA B hB hne
    obtain ⟨U,hu,rfl⟩ := mem_image.mp hA
    obtain ⟨W,hw,rfl⟩ := mem_image.mp hB
    rw [← Finset.map_inter,card_map]
    exact linear U hu W hw (fun eq => hne (congrArg (Finset.map e.toEmbedding) eq))

end E19Transfer

end

section

open Finset

namespace EFLInterval

private theorem reflect_support {n : ℕ} {s : Finset (Fin n)} {l r i : Fin n}
    (hlr : l < r) (shape : s = {l,r} ∨ s = Finset.Icc l r) (hi : i ∈ s) :
    ∃ j ∈ s, j+i = l+r ∧ (j=i → ∃ z ∈ s, z.val = i.val+1) := by
  rcases shape with rfl | rfl
  · rcases Finset.mem_insert.mp hi with h | h
    · subst i
      exact ⟨r, by simp, add_comm _ _, fun h => (hlr.ne' h).elim⟩
    · obtain rfl := Finset.mem_singleton.mp h
      exact ⟨l, by simp, rfl, fun h => (hlr.ne h).elim⟩
  · obtain ⟨hil, hir⟩ := Finset.mem_Icc.mp hi
    change l.val ≤ i.val at hil
    change i.val ≤ r.val at hir
    change l.val < r.val at hlr
    have hr := r.isLt
    let j : Fin n := ⟨l.val+r.val-i.val, by omega⟩
    have hjl : l ≤ j := by change l.val ≤ l.val+r.val-i.val; omega
    have hjr : j ≤ r := by change l.val+r.val-i.val ≤ r.val; omega
    have hsum : j.val+i.val = l.val+r.val := by dsimp [j]; omega
    refine ⟨j, Finset.mem_Icc.mpr ⟨hjl,hjr⟩, Fin.ext ?_, ?_⟩
    · simp only [Fin.val_add, hsum]
    · intro h
      have hfix := congrArg Fin.val h
      have hright : i.val+1 ≤ r.val := by omega
      let z : Fin n := ⟨i.val+1, by omega⟩
      exact ⟨z, Finset.mem_Icc.mpr ⟨show l.val ≤ i.val+1 by omega, hright⟩, rfl⟩

/-- Two intersecting blocks with at least two members and at most one shared member
have distinct endpoint sums modulo n, if each block is a pair or a full interval. -/
private theorem endpoint_sums_ne {n : ℕ} (hn : 0 < n)
    {A B : Finset (Fin n)} {l r u v i : Fin n}
    (hlr : l < r) (huv : u < v)
    (hA : A = {l,r} ∨ A = Finset.Icc l r) (hB : B = {u,v} ∨ B = Finset.Icc u v)
    (hiA : i ∈ A) (hiB : i ∈ B) (hlin : (A ∩ B).card ≤ 1) :
    l+r ≠ u+v := by
  let _ : NeZero n := ⟨hn.ne'⟩
  intro hcol
  obtain ⟨a,ha,hsa,hfa⟩ := reflect_support hlr hA hiA
  obtain ⟨b,hb,hsb,hfb⟩ := reflect_support huv hB hiB
  have heq : a=b := add_right_cancel ((hsa.trans hcol).trans hsb.symm)
  subst b
  have unique (x : Fin n) (hx : x ∈ A) (hy : x ∈ B) : x=i :=
    Finset.card_le_one.mp hlin _ (Finset.mem_inter.mpr ⟨hx,hy⟩) _ (Finset.mem_inter.mpr ⟨hiA,hiB⟩)
  have he := unique a ha hb
  obtain ⟨x,hx,hx'⟩ := hfa he
  obtain ⟨y,hy,hy'⟩ := hfb he
  have he' : x=y := Fin.ext (hx'.trans hy'.symm)
  subst y
  have hxi := congrArg Fin.val (unique x hx hy)
  omega

/-- Color every shared support by the sum modulo n of its two endpoints. -/
theorem color_shared {V : Type*} {n : ℕ} (hn : 0 < n) (S : V → Finset (Fin n))
    (linear : ∀ a b : V, a ≠ b → (S a ∩ S b).card ≤ 1)
    (interval : ∀ v : V, 3 ≤ (S v).card → ∃ l r : Fin n, S v = Finset.Icc l r) :
    ∃ c : V → Fin n,
      (∀ v (h : (S v).Nonempty), c v = (S v).min' h + (S v).max' h) ∧
      ∀ a b : V, a ≠ b → 2 ≤ (S a).card → 2 ≤ (S b).card →
        (S a ∩ S b).Nonempty → c a ≠ c b := by
  classical
  let c (v : V) := if h : (S v).Nonempty then (S v).min' h + (S v).max' h else ⟨0,hn⟩
  have color (v : V) (h : (S v).Nonempty) : c v = (S v).min' h + (S v).max' h := by simp [c,h]
  refine ⟨c, color, ?_⟩
  have structure_of (v : V) (h₂ : 2 ≤ (S v).card) (hne : (S v).Nonempty) :
      let l := (S v).min' hne
      let r := (S v).max' hne
      l < r ∧ (S v = {l,r} ∨ S v = Finset.Icc l r) := by
    let l := (S v).min' hne
    let r := (S v).max' hne
    change l < r ∧ (S v = {l,r} ∨ S v = Finset.Icc l r)
    have hl : l ∈ S v := (S v).min'_mem hne
    have hr : r ∈ S v := (S v).max'_mem hne
    have range_of (x : Fin n) (hx : x ∈ S v) : l ≤ x ∧ x ≤ r :=
      ⟨(S v).min'_le x hx, (S v).le_max' x hx⟩
    have hlt : l < r := by
      by_contra! h
      have hsmall : (S v).card ≤ 1 := Finset.card_le_one.mpr fun x hx y hy =>
        le_antisymm ((range_of x hx).2.trans (h.trans (range_of y hy).1))
          ((range_of y hy).2.trans (h.trans (range_of x hx).1))
      omega
    refine ⟨hlt, ?_⟩
    by_cases h : (S v).card = 2
    · left
      apply Eq.symm
      apply Finset.eq_of_subset_of_card_le
      · exact Finset.insert_subset hl (Finset.singleton_subset_iff.mpr hr)
      · rw [Finset.card_pair hlt.ne, h]
    · right
      obtain ⟨a,b,hs⟩ := interval v (by omega)
      have hleft := Finset.mem_Icc.mp (hs ▸ hl)
      have hright := Finset.mem_Icc.mp (hs ▸ hr)
      ext x
      constructor
      · intro hx
        exact Finset.mem_Icc.mpr (range_of x hx)
      · intro hx
        rw [hs]
        exact Finset.mem_Icc.mpr ⟨hleft.1.trans (Finset.mem_Icc.mp hx).1,
          (Finset.mem_Icc.mp hx).2.trans hright.2⟩
  intro a b hab ha hb hi
  obtain ⟨i,hi⟩ := hi
  obtain ⟨hiA,hiB⟩ := Finset.mem_inter.mp hi
  have ha' : (S a).Nonempty := ⟨i,hiA⟩
  have hb' : (S b).Nonempty := ⟨i,hiB⟩
  obtain ⟨al,ashape⟩ := structure_of a ha ha'
  obtain ⟨bl,bshape⟩ := structure_of b hb hb'
  rw [color a ha', color b hb']
  exact endpoint_sums_ne hn al bl ashape bshape hiA hiB (linear a b hab)

/-- The finite-family form of the coloring. -/
theorem color_family {n : ℕ} (hn : 0 < n) (H : Finset (Finset (Fin n)))
    (linear : ∀ A ∈ H, ∀ B ∈ H, A ≠ B → (A ∩ B).card ≤ 1)
    (lower : ∀ A ∈ H, 2 ≤ A.card)
    (interval : ∀ A ∈ H, 3 ≤ A.card → ∃ l r : Fin n, A = Finset.Icc l r) :
    ∃ c : H → Fin n, ∀ A B : H, A ≠ B → (A.val ∩ B.val).Nonempty → c A ≠ c B := by
  obtain ⟨c, _, hc⟩ := color_shared hn (fun A : H => A.val)
    (fun A B h => linear _ A.property _ B.property (fun he => h (Subtype.ext he)))
    (fun A => interval _ A.property)
  exact ⟨c, fun A B h => hc A B h (lower _ A.property) (lower _ B.property)⟩

end EFLInterval

end

section

open Finset

namespace EFLInterval

private theorem interval_of_convex {n : ℕ} (U : Finset (Fin n)) (hne : U.Nonempty)
    (convex : ∀ a ∈ U, ∀ b ∈ U, ∀ x, a ≤ x → x ≤ b → x ∈ U) :
    ∃ l r : Fin n, U = Finset.Icc l r := by
  refine ⟨U.min' hne, U.max' hne, ?_⟩
  ext x
  constructor
  · exact fun hx => Finset.mem_Icc.mpr ⟨U.min'_le x hx, U.le_max' x hx⟩
  · exact fun hx => convex _ (U.min'_mem hne) _ (U.max'_mem hne) x
      (Finset.mem_Icc.mp hx).1 (Finset.mem_Icc.mp hx).2

/-- Sort by membership class (A only, both, B only, neither), preserving index order
inside each class. Each designated nonempty set then occupies one interval. -/
theorem relabel_two_sets {n : ℕ} (A B : Finset (Fin n)) :
    ∃ e : Fin n ≃ Fin n, ∀ U : Finset (Fin n), U = A ∨ U = B → U.Nonempty →
      ∃ l r : Fin n, U.map e.toEmbedding = Finset.Icc l r := by
  classical
  let tag (x : Fin n) : ℕ := if x ∈ A then (if x ∈ B then 1 else 0) else (if x ∈ B then 2 else 3)
  let key (x : Fin n) := tag x * n + x.val
  have residue (x : Fin n) : key x % n = x.val := by
    simp [key, Nat.mod_eq_of_lt x.isLt]
  have inj : Function.Injective key := by
    intro x y h
    exact Fin.ext ((residue x).symm.trans ((congrArg (· % n) h).trans (residue y)))
  let emb : Fin n ↪ ℕ := ⟨key, inj⟩
  let T := (Finset.univ : Finset (Fin n)).map emb
  let t (x : Fin n) : T := ⟨key x, Finset.mem_map_of_mem emb (Finset.mem_univ x)⟩
  have bij : Function.Bijective t := by
    constructor
    · intro x y h
      exact inj (congrArg Subtype.val h)
    · intro y
      obtain ⟨x, _, hx⟩ := Finset.mem_map.mp y.property
      exact ⟨x, Subtype.ext hx⟩
  have cardT : T.card = n := by simp [T]
  let iso := T.orderIsoOfFin cardT
  let e := (Equiv.ofBijective t bij).trans iso.symm.toEquiv
  have back (x : Fin n) : iso (e x) = t x := iso.apply_symm_apply _
  have ordered (x y : Fin n) (h : e x ≤ e y) : tag x ≤ tag y := by
    have hkey := iso.monotone h
    rw [back,back] at hkey
    change tag x * n + x.val ≤ tag y * n + y.val at hkey
    by_contra! hbad
    have hh := Nat.mul_le_mul_right n (show tag y+1 ≤ tag x by omega)
    rw [Nat.add_mul, one_mul] at hh
    have := y.isLt
    omega
  have memA (x : Fin n) : x ∈ A ↔ tag x ≤ 1 := by
    dsimp [tag]
    split_ifs <;> simp_all
  have memB (x : Fin n) : x ∈ B ↔ 1 ≤ tag x ∧ tag x ≤ 2 := by
    dsimp [tag]
    split_ifs <;> simp_all
  refine ⟨e, ?_⟩
  intro U hU hne
  apply interval_of_convex _ hne.map
  intro a ha b hb x hl hr
  obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp ha
  obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hb
  have h₁ := ordered u (e.symm x) (by simpa using hl)
  have h₂ := ordered (e.symm x) v (by simpa using hr)
  refine Finset.mem_map.mpr ⟨e.symm x, ?_, by simp⟩
  rcases hU with rfl | rfl
  · exact (memA _).mpr (h₂.trans ((memA _).mp hv))
  · exact (memB _).mpr ⟨((memB _).mp hu).1.trans h₁, h₂.trans ((memB _).mp hv).2⟩

/-- At most two large supports imply that a single permutation intervalizes all large supports. -/
theorem relabel_at_most_two {n : ℕ} (H : Finset (Finset (Fin n)))
    (two : (H.filter fun A => 3 ≤ A.card).card ≤ 2) :
    ∃ e : Fin n ≃ Fin n, let K := H.image (Finset.map e.toEmbedding)
      ∀ A ∈ K, 3 ≤ A.card → ∃ l r : Fin n, A = Finset.Icc l r := by
  classical
  let F := H.filter fun A => 3 ≤ A.card
  have cover : ∃ A B : Finset (Fin n), ∀ U ∈ F, U = A ∨ U = B := by
    by_cases h : F.card = 2
    · obtain ⟨A,B,_,hF⟩ := Finset.card_eq_two.mp h
      exact ⟨A,B,fun U hU => by simpa [hF] using hU⟩
    · by_cases hne : F.Nonempty
      · obtain ⟨A,hA⟩ := hne
        have small : F.card ≤ 1 := by change F.card ≤ 2 at two; omega
        exact ⟨A,A,fun U hU => Or.inl (Finset.card_le_one.mp small U hU A hA)⟩
      · exact ⟨∅,∅,fun U hU => (hne ⟨U,hU⟩).elim⟩
  obtain ⟨A,B,hcov⟩ := cover
  obtain ⟨e,he⟩ := relabel_two_sets A B
  refine ⟨e, ?_⟩
  dsimp only
  intro S hS hs
  obtain ⟨U,hU,rfl⟩ := Finset.mem_image.mp hS
  rw [Finset.card_map] at hs
  exact he U (hcov U (Finset.mem_filter.mpr ⟨hU,hs⟩))
    (Finset.card_pos.mp (by omega))

end EFLInterval

end

section

open Finset
namespace E19Critical

/-- In a smallest uncolorable subfamily every support meets at least n others. -/
private theorem critical {n : ℕ} (hn : 0 < n) (H : Finset (Finset (Fin n)))
    (bad : ¬ ∃ c : H → Fin n, ∀ A B : H, A ≠ B →
      (A.val ∩ B.val).Nonempty → c A ≠ c B) :
    ∃ K ⊆ H, K.Nonempty ∧
      (¬ ∃ c : K → Fin n, ∀ A B : K, A ≠ B → (A.val ∩ B.val).Nonempty → c A ≠ c B) ∧
      ∀ T ∈ K, n ≤ ((K.erase T).filter (fun A => (T ∩ A).Nonempty)).card := by
  classical
  let Good (J : Finset (Finset (Fin n))) : Prop :=
    ∃ c : J → Fin n, ∀ A B : J, A ≠ B → (A.val ∩ B.val).Nonempty → c A ≠ c B
  let candidates := H.powerset.filter (fun J => ¬ Good J)
  have hm : H ∈ candidates := mem_filter.mpr ⟨mem_powerset.mpr Subset.rfl, bad⟩
  obtain ⟨K,hK,hmin⟩ := exists_min_image candidates Finset.card ⟨H,hm⟩
  obtain ⟨hsub,hbad⟩ := mem_filter.mp hK
  have neK : K.Nonempty := by
    by_contra! empty
    subst K
    exact hbad ⟨fun A => False.elim (notMem_empty A.val A.property),
      fun A => False.elim (notMem_empty A.val A.property)⟩
  refine ⟨K,mem_powerset.mp hsub,neK,hbad,?_⟩
  intro T hT
  have smaller : Good (K.erase T) := by
    by_contra b
    have hm' : K.erase T ∈ candidates := mem_filter.mpr
      ⟨mem_powerset.mpr (Subset.trans (erase_subset T K) (mem_powerset.mp hsub)), b⟩
    exact (Nat.not_lt_of_ge (hmin _ hm')) (card_erase_lt_of_mem hT)
  obtain ⟨c,hc⟩ := smaller
  let f (A : Finset (Fin n)) : Fin n :=
    if h : A ∈ K.erase T then c ⟨A,h⟩ else ⟨0,hn⟩
  let N := (K.erase T).filter (fun A => (T ∩ A).Nonempty)
  by_contra! few
  have short : (N.image f).card < (univ : Finset (Fin n)).card := by
    simpa using (card_image_le.trans_lt few)
  obtain ⟨z,_,hz⟩ := exists_mem_notMem_of_card_lt_card short
  have fresh (A : Finset (Fin n)) (hA : A ∈ K.erase T) (hi : (T ∩ A).Nonempty) :
      z ≠ f A := by
    intro eq
    exact hz (eq ▸ mem_image_of_mem f (mem_filter.mpr ⟨hA,hi⟩ : A ∈ N))
  apply hbad
  refine ⟨fun A => if A.val = T then z else f A.val, ?_⟩
  intro A B hne hi
  have ne : A.val ≠ B.val := fun h => hne (Subtype.ext h)
  by_cases ha : A.val = T
  · have hb : B.val ≠ T := fun h => ne (ha.trans h.symm)
    simpa only [if_pos ha,if_neg hb] using
      fresh B.val (mem_erase.mpr ⟨hb,B.property⟩) (ha ▸ hi)
  · have ma := mem_erase.mpr ⟨ha,A.property⟩
    by_cases hb : B.val = T
    · have hi' : (T ∩ A.val).Nonempty := by simpa only [← hb,inter_comm] using hi
      simpa only [if_neg ha,if_pos hb] using (fresh A.val ma hi').symm
    · have mb := mem_erase.mpr ⟨hb,B.property⟩
      simpa only [if_neg ha,if_neg hb,f,dif_pos ma,dif_pos mb] using
        hc ⟨A.val,ma⟩ ⟨B.val,mb⟩ (fun eq => ne (congrArg (fun X : K.erase T => X.val) eq)) hi

end E19Critical

end

section

open Finset

namespace E19Rank

theorem rank_bound {n r : ℕ} (H : Finset (Finset (Fin n))) (hr : 2 ≤ r)
    (hsize : ∀ A ∈ H, r ≤ A.card)
    (hlin : ∀ A ∈ H, ∀ B ∈ H, A ≠ B → (A ∩ B).card ≤ 1)
    {T : Finset (Fin n)} (hT : T ∈ H) (hcard : T.card = r)
    (hmeet : n ≤ ((H.erase T).filter fun A => (T ∩ A).Nonempty).card) :
    r * r ≤ n := by
  classical
  let J := (H.erase T).filter fun A => (T ∩ A).Nonempty
  let through (x : Fin n) := J.filter fun A => x ∈ A
  have rows {x : Fin n} {A : Finset (Fin n)} (h : A ∈ through x) :
      A ∈ H ∧ A ≠ T ∧ x ∈ A := by
    obtain ⟨hJ,hx⟩ := mem_filter.mp h
    obtain ⟨hne,ha⟩ := mem_erase.mp (mem_filter.mp hJ).1
    exact ⟨ha,hne,hx⟩
  have localBound (x : Fin n) (hx : x ∈ T) : (through x).card * (r - 1) ≤ n - r := by
    have dis : (through x : Set (Finset (Fin n))).PairwiseDisjoint (fun A => A \ T) := by
      intro A hA B hB hAB
      apply disjoint_left.mpr
      intro y hyA hyB
      have hxy : x ≠ y := fun heq => (mem_sdiff.mp hyA).2 (heq ▸ hx)
      have both : {x,y} ⊆ A ∩ B := by
        rw [insert_subset_iff,singleton_subset_iff]
        exact ⟨mem_inter.mpr ⟨(rows hA).2.2,(rows hB).2.2⟩,
          mem_inter.mpr ⟨(mem_sdiff.mp hyA).1,(mem_sdiff.mp hyB).1⟩⟩
      have size := (card_le_card both).trans (hlin A (rows hA).1 B (rows hB).1 hAB)
      simp [card_pair hxy] at size
    have lower (A : Finset (Fin n)) (hA : A ∈ through x) : r - 1 ≤ (A \ T).card := by
      have a := rows hA
      have := hlin A a.1 T hT a.2.1
      have := hsize A a.1
      have := card_sdiff_add_card_inter A T
      omega
    have incl : (through x).biUnion (fun A => A \ T) ⊆ univ \ T := by
      intro y hy
      obtain ⟨A,_,hyA⟩ := mem_biUnion.mp hy
      exact mem_sdiff.mpr ⟨mem_univ _,(mem_sdiff.mp hyA).2⟩
    have bound := card_le_card incl
    rw [card_biUnion dis,card_sdiff_of_subset (subset_univ T),card_univ,Fintype.card_fin,hcard] at bound
    simpa only [sum_const,smul_eq_mul] using (sum_le_sum lower).trans bound
  have incl : J ⊆ T.biUnion through := by
    intro A ha
    obtain ⟨x,hx⟩ := (mem_filter.mp ha).2
    exact mem_biUnion.mpr ⟨x,(mem_inter.mp hx).1,mem_filter.mpr ⟨ha,(mem_inter.mp hx).2⟩⟩
  have count : n ≤ ∑ x ∈ T, (through x).card :=
    hmeet.trans ((card_le_card incl).trans card_biUnion_le)
  have combined := Nat.mul_le_mul_right (r-1) count
  rw [sum_mul] at combined
  have bound := combined.trans (sum_le_sum localBound)
  rw [sum_const,smul_eq_mul,hcard] at bound
  have hrn : r ≤ n := by simpa [hcard] using card_le_univ T
  have left := congrArg (n * ·) (show r - 1 + 1 = r by omega)
  have right := congrArg (r * ·) (show n - r + r = n by omega)
  simp only [Nat.mul_add,Nat.mul_one] at left right
  rw [Nat.mul_comm r n] at right
  omega

end E19Rank

end

section

open Finset
namespace E19Parallel

private theorem parallel_trans {n : ℕ} {H : Finset (Finset (Fin n))}
    (unique : ∀ T ∈ H, ∀ x : Fin n, x ∉ T → ∀ A ∈ H, ∀ B ∈ H,
      x ∈ A → x ∈ B → Disjoint A T → Disjoint B T → A = B)
    {A B D : Finset (Fin n)} (hA : A ∈ H) (hB : B ∈ H) (hD : D ∈ H)
    (hab : A = B ∨ Disjoint A B) (hbd : B = D ∨ Disjoint B D) :
    A = D ∨ Disjoint A D := by
  rcases hab with rfl|hab
  · exact hbd
  rcases hbd with rfl|hbd
  · exact Or.inr hab
  by_cases h : Disjoint A D
  · exact Or.inr h
  obtain ⟨x,hxA,hxD⟩ := not_disjoint_iff.mp h
  exact Or.inl (unique B hB x (fun hxB => disjoint_left.mp hab hxA hxB)
    A hA D hD hxA hxD hab hbd.symm)

private theorem color_parallel {n : ℕ} (H : Finset (Finset (Fin n)))
    (linear : ∀ A ∈ H, ∀ B ∈ H, A ≠ B → (A ∩ B).card ≤ 1)
    (lower : ∀ A ∈ H, 2 ≤ A.card)
    (through : ∀ T ∈ H, ∀ x : Fin n, x ∉ T →
      ∃! U : Finset (Fin n), U ∈ H ∧ x ∈ U ∧ Disjoint U T) :
    ∃ c : H → Fin n, ∀ A B : H, A ≠ B → (A.val ∩ B.val).Nonempty → c A ≠ c B := by
  classical
  by_cases empty : H = ∅
  · subst H
    exact ⟨fun A => False.elim (notMem_empty _ A.property),
      fun A => False.elim (notMem_empty _ A.property)⟩
  obtain ⟨T,hT⟩ := nonempty_iff_ne_empty.mpr empty
  obtain ⟨x,hx⟩ := card_pos.mp (show 0 < T.card by have := lower T hT; omega)
  have unique (T) (hT : T ∈ H) (y : Fin n) (hy : y ∉ T) (A) (hA : A ∈ H)
      (B) (hB : B ∈ H) (hya : y ∈ A) (hyb : y ∈ B) (da : Disjoint A T) (db : Disjoint B T) :
      A = B := (through T hT y hy).unique ⟨hA,hya,da⟩ ⟨hB,hyb,db⟩
  have rep (A : H) : ∃ R ∈ H, x ∈ R ∧ (A.val = R ∨ Disjoint A.val R) := by
    by_cases onLine : x ∈ A.val
    · exact ⟨A.val,A.property,onLine,Or.inl rfl⟩
    obtain ⟨R,⟨hr,hx,dis⟩,_⟩ := through A.val A.property x onLine
    exact ⟨R,hr,hx,Or.inr dis.symm⟩
  choose R line anchor parallel using rep
  have off (A : H) : ∃ y ∈ R A, y ≠ x := by
    by_contra! h
    have sub : R A ⊆ {x} := fun y hy => mem_singleton.mpr (h y hy)
    have small := card_le_card sub
    rw [card_singleton] at small
    have := lower _ (line A)
    omega
  choose c memc distinct using off
  refine ⟨c,?_⟩
  intro A B hne meet eq
  have same : R A = R B := by
    by_contra different
    have h := linear _ (line A) _ (line B) different
    have hx : x ∈ R A ∩ R B := mem_inter.mpr ⟨anchor A,anchor B⟩
    have hc : c A ∈ R A ∩ R B := mem_inter.mpr ⟨memc A,eq ▸ memc B⟩
    exact distinct A (card_le_one.mp h _ hc _ hx)
  have back : R A = B.val ∨ Disjoint (R A) B.val := by
    rw [same]
    exact (parallel B).elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)
  rcases parallel_trans unique A.property (line A) B.property (parallel A) back with equal|dis
  · exact hne (Subtype.ext equal)
  · obtain ⟨y,hy⟩ := meet
    exact disjoint_left.mp dis (mem_inter.mp hy).1 (mem_inter.mp hy).2

end E19Parallel

end

section

open Finset

namespace E19Equality

private theorem saturated {n r : ℕ} (H : Finset (Finset (Fin n))) (hr : 2 ≤ r)
    (hn : n = r*r) (hsize : ∀ A ∈ H, r ≤ A.card)
    (hlin : ∀ A ∈ H, ∀ B ∈ H, A ≠ B → (A ∩ B).card ≤ 1)
    {T : Finset (Fin n)} (hT : T ∈ H) (hcard : T.card = r)
    (hmeet : n ≤ ((H.erase T).filter fun A => (T ∩ A).Nonempty).card) :
    ∀ x ∈ T, let L := (H.erase T).filter (x ∈ ·)
      L.card = r ∧ L.biUnion (fun A => A \ T) = univ \ T ∧ ∀ A ∈ L, A.card = r := by
  classical
  let L (x : Fin n) := (H.erase T).filter (x ∈ ·)
  let outside (A : Finset (Fin n)) := A \ T
  have rows {x : Fin n} {A : Finset (Fin n)} (h : A ∈ L x) : A ∈ H ∧ A ≠ T ∧ x ∈ A := by
    obtain ⟨he,hx⟩ := mem_filter.mp h
    exact ⟨mem_of_mem_erase he,(mem_erase.mp he).1,hx⟩
  have dis (x : Fin n) (hx : x ∈ T) : (L x : Set (Finset (Fin n))).PairwiseDisjoint outside := by
    intro A hA B hB hAB
    apply disjoint_left.mpr
    intro y hyA hyB
    have same := card_le_one.mp (hlin A (rows hA).1 B (rows hB).1 hAB)
      x (mem_inter.mpr ⟨(rows hA).2.2,(rows hB).2.2⟩)
      y (mem_inter.mpr ⟨(mem_sdiff.mp hyA).1,(mem_sdiff.mp hyB).1⟩)
    exact (mem_sdiff.mp hyA).2 (same ▸ hx)
  have lower {x : Fin n} (A : Finset (Fin n)) (hA : A ∈ L x) : r - 1 ≤ (outside A).card := by
    have := hlin A (rows hA).1 T hT (rows hA).2.1
    have := hsize A (rows hA).1
    have := card_sdiff_add_card_inter A T
    dsimp [outside]
    omega
  have sub (x : Fin n) : (L x).biUnion outside ⊆ univ \ T := by
    intro y hy
    obtain ⟨A,_,hyA⟩ := mem_biUnion.mp hy
    exact mem_sdiff.mpr ⟨mem_univ _,(mem_sdiff.mp hyA).2⟩
  have complement : (univ \ T).card = r*(r-1) := by
    rw [card_sdiff_of_subset (subset_univ _),card_univ,Fintype.card_fin,hcard,hn,Nat.mul_sub_left_distrib,Nat.mul_one]
  have cap (x : Fin n) (hx : x ∈ T) : (∑ A ∈ L x, (outside A).card) ≤ r*(r-1) := by
    rw [← card_biUnion (dis x hx),← complement]
    exact card_le_card (sub x)
  have atMost (x : Fin n) (hx : x ∈ T) : (L x).card ≤ r := by
    apply Nat.le_of_mul_le_mul_right _ (show 0 < r-1 by omega)
    simpa only [sum_const,smul_eq_mul] using (sum_le_sum (fun A hA => lower A hA)).trans (cap x hx)
  let J := (H.erase T).filter fun A => (T ∩ A).Nonempty
  have inc : J ⊆ T.biUnion L := by
    intro A hA
    obtain ⟨he,x,hx⟩ := mem_filter.mp hA
    exact mem_biUnion.mpr ⟨x,(mem_inter.mp hx).1,mem_filter.mpr ⟨he,(mem_inter.mp hx).2⟩⟩
  have count : n ≤ ∑ x ∈ T, (L x).card := hmeet.trans ((card_le_card inc).trans card_biUnion_le)
  intro x hx
  have hEq : (L x).card = r := by
    apply (atMost x hx).antisymm
    by_contra! h
    have z := sum_lt_sum atMost ⟨x,hx,h⟩
    rw [sum_const,smul_eq_mul,hcard,← hn] at z
    omega
  refine ⟨hEq,?_,?_⟩
  · apply eq_of_subset_of_card_le (sub x)
    rw [complement,card_biUnion (dis x hx),← hEq]
    have := sum_le_sum (fun A hA => lower (x := x) A hA)
    simpa only [sum_const,smul_eq_mul,hEq] using this
  · intro A hA
    apply le_antisymm _ (hsize A (rows hA).1)
    have small : (outside A).card ≤ r-1 := by
      by_contra! h
      have z := sum_lt_sum (fun B hB => lower (x := x) B hB) ⟨A,hA,h⟩
      rw [sum_const,smul_eq_mul,hEq] at z
      exact z.not_ge (cap x hx)
    have := hlin A (rows hA).1 T hT (rows hA).2.1
    have := card_sdiff_add_card_inter A T
    change (A \ T).card ≤ r-1 at small
    omega

theorem uniform {n r : ℕ} (H : Finset (Finset (Fin n))) (hr : 2 ≤ r) (hn : n = r*r)
    (hsize : ∀ A ∈ H, r ≤ A.card)
    (hlin : ∀ A ∈ H, ∀ B ∈ H, A ≠ B → (A ∩ B).card ≤ 1)
    {T : Finset (Fin n)} (hT : T ∈ H) (hcard : T.card = r)
    (hmeet : n ≤ ((H.erase T).filter fun A => (T ∩ A).Nonempty).card) :
    ∀ A ∈ H, A.card = r := by
  classical
  have sat := saturated H hr hn hsize hlin hT hcard hmeet
  intro A hA
  by_cases hAT : A = T
  · exact hAT ▸ hcard
  by_cases hm : (T ∩ A).Nonempty
  · obtain ⟨x,hx⟩ := hm
    exact (sat x (mem_inter.mp hx).1).2.2 A (mem_filter.mpr ⟨mem_erase.mpr ⟨hAT,hA⟩,(mem_inter.mp hx).2⟩)
  obtain ⟨x,hx⟩ := card_pos.mp (by omega : 0 < T.card)
  let L := (H.erase T).filter (x ∈ ·)
  obtain ⟨num,covers,_⟩ := sat x hx
  have inc : A ⊆ L.biUnion (fun B => B ∩ A) := by
    intro y hy
    have hyt : y ∉ T := fun h => hm ⟨y,mem_inter.mpr ⟨h,hy⟩⟩
    have hyC : y ∈ univ \ T := mem_sdiff.mpr ⟨mem_univ _,hyt⟩
    rw [← covers] at hyC
    obtain ⟨B,hB,hyB⟩ := mem_biUnion.mp hyC
    exact mem_biUnion.mpr ⟨B,hB,mem_inter.mpr ⟨(mem_sdiff.mp hyB).1,hy⟩⟩
  have cap (B : Finset (Fin n)) (hB : B ∈ L) : (B ∩ A).card ≤ 1 := by
    obtain ⟨he,hxb⟩ := mem_filter.mp hB
    exact hlin B (mem_of_mem_erase he) A hA (fun h => hm ⟨x,mem_inter.mpr ⟨hx,h ▸ hxb⟩⟩)
  have ub := (card_le_card inc).trans (card_biUnion_le_card_mul L _ 1 cap)
  change L.card = r at num
  rw [num,mul_one] at ub
  exact ub.antisymm (hsize A hA)

theorem parallel {n r : ℕ} (H : Finset (Finset (Fin n))) (hr : 2 ≤ r) (hn : n = r*r)
    (sizes : ∀ A ∈ H, A.card = r)
    (hlin : ∀ A ∈ H, ∀ B ∈ H, A ≠ B → (A ∩ B).card ≤ 1)
    (meets : ∀ T ∈ H, n ≤ ((H.erase T).filter fun A => (T ∩ A).Nonempty).card) :
    ∀ T ∈ H, ∀ y : Fin n, y ∉ T →
      ∃! U : Finset (Fin n), U ∈ H ∧ y ∈ U ∧ Disjoint U T := by
  classical
  have sat (T : Finset (Fin n)) (hT : T ∈ H) :=
    saturated H hr hn (fun A hA => (sizes A hA).ge) hlin hT (sizes T hT) (meets T hT)
  intro T hT y hyt
  let P := H.filter (y ∈ ·)
  let I := P.filter (fun U => ¬ Disjoint U T)
  let L (x : Fin n) := P.filter (x ∈ ·)
  have join (x : Fin n) (hx : x ∈ T) : ∃ U ∈ P, x ∈ U := by
    have hy : y ∈ univ \ T := mem_sdiff.mpr ⟨mem_univ _,hyt⟩
    rw [← (sat T hT x hx).2.1] at hy
    obtain ⟨U,hU,hyU⟩ := mem_biUnion.mp hy
    exact ⟨U,mem_filter.mpr ⟨mem_of_mem_erase (mem_filter.mp hU).1,(mem_sdiff.mp hyU).1⟩,(mem_filter.mp hU).2⟩
  have psize : P.card = r+1 := by
    obtain ⟨x,hx⟩ := card_pos.mp (by have := sizes T hT; omega : 0 < T.card)
    obtain ⟨U,hU,_⟩ := join x hx
    have he := (sat U (mem_filter.mp hU).1 y (mem_filter.mp hU).2).1
    rw [filter_erase] at he
    change (P.erase U).card = r at he
    rw [card_erase_of_mem hU] at he
    omega
  have atMost (x : Fin n) (hx : x ∈ T) : (L x).card ≤ 1 := by
    apply card_le_one.mpr
    intro A hA B hB
    obtain ⟨aP,xa⟩ := mem_filter.mp hA
    obtain ⟨bP,xb⟩ := mem_filter.mp hB
    by_contra h
    have same := card_le_one.mp (hlin A (mem_filter.mp aP).1 B (mem_filter.mp bP).1 h)
      x (mem_inter.mpr ⟨xa,xb⟩) y (mem_inter.mpr ⟨(mem_filter.mp aP).2,(mem_filter.mp bP).2⟩)
    exact hyt (same ▸ hx)
  have inc : I ⊆ T.biUnion L := by
    intro U hU
    obtain ⟨up,hm⟩ := mem_filter.mp hU
    obtain ⟨x,hx⟩ := not_disjoint_iff_nonempty_inter.mp hm
    exact mem_biUnion.mpr ⟨x,(mem_inter.mp hx).2,mem_filter.mpr ⟨up,(mem_inter.mp hx).1⟩⟩
  have back : T ⊆ I.biUnion (fun U => U ∩ T) := by
    intro x hx
    obtain ⟨U,up,xu⟩ := join x hx
    have hm : (U ∩ T).Nonempty := ⟨x,mem_inter.mpr ⟨xu,hx⟩⟩
    exact mem_biUnion.mpr ⟨U,mem_filter.mpr ⟨up,hm.not_disjoint⟩,mem_inter.mpr ⟨xu,hx⟩⟩
  have each (U : Finset (Fin n)) (hU : U ∈ I) : (U ∩ T).card ≤ 1 := by
    obtain ⟨up,_⟩ := mem_filter.mp hU
    obtain ⟨uh,yu⟩ := mem_filter.mp up
    exact hlin U uh T hT (fun h => hyt (h ▸ yu))
  have one := (card_le_card inc).trans (card_biUnion_le_card_mul T L 1 atMost)
  have two := (card_le_card back).trans (card_biUnion_le_card_mul I _ 1 each)
  simp only [mul_one,sizes T hT] at one two
  have both := P.card_filter_add_card_filter_not (fun U => Disjoint U T)
  change (P.filter (fun U => Disjoint U T)).card + I.card = P.card at both
  obtain ⟨U,hU⟩ := card_eq_one.mp (by omega : (P.filter fun U => Disjoint U T).card = 1)
  have iffMem (A : Finset (Fin n)) : (A ∈ H ∧ y ∈ A ∧ Disjoint A T) ↔ A = U := by
    rw [← mem_singleton,← hU]
    simp [P,and_assoc]
  exact ⟨U,(iffMem U).mpr rfl,fun A hA => (iffMem A).mp hA⟩

end E19Equality

end

open Finset Erdos19
open scoped Classical

namespace OMA.R_Erdos19_erdos_19_R1

/-- Families containing a pair, with at least three larger supports that cannot all be
made intervals in a single order. Each support meets at least n others. -/
def H1 : Prop := ∀ (n : ℕ) (K : Finset (Finset (Fin n))), 4 < n →
    (∃ T ∈ K, T.card = 2) → (∀ A ∈ K, 2 ≤ A.card) →
    (∀ A ∈ K, ∀ B ∈ K, A ≠ B → (A ∩ B).card ≤ 1) →
    (∀ T ∈ K, n ≤ ((K.erase T).filter fun A => (T ∩ A).Nonempty).card) →
    3 ≤ (K.filter fun A => 3 ≤ A.card).card →
    (¬ ∃ e : Fin n ≃ Fin n, ∀ A ∈ K.image (Finset.map e.toEmbedding),
      3 ≤ A.card → ∃ l r : Fin n, A = Finset.Icc l r) →
    ∃ c : K → Fin n, ∀ A B : K, A ≠ B → (A.val ∩ B.val).Nonempty → c A ≠ c B

/-- Families of minimum rank r at least three, with the same order obstruction
and a strict upper bound on the square of the minimum rank. -/
def H2 : Prop := ∀ (n r : ℕ) (K : Finset (Finset (Fin n))), 3 ≤ r → r*r < n →
    (∃ T ∈ K, T.card = r) → (∀ A ∈ K, r ≤ A.card) →
    (∀ A ∈ K, ∀ B ∈ K, A ≠ B → (A ∩ B).card ≤ 1) →
    (∀ T ∈ K, n ≤ ((K.erase T).filter fun A => (T ∩ A).Nonempty).card) →
    3 ≤ (K.filter fun A => 3 ≤ A.card).card →
    (¬ ∃ e : Fin n ≃ Fin n, ∀ A ∈ K.image (Finset.map e.toEmbedding),
      3 ≤ A.card → ∃ l r : Fin n, A = Finset.Icc l r) →
    ∃ c : K → Fin n, ∀ A B : K, A ≠ B → (A.val ∩ B.val).Nonempty → c A ≠ c B

section

theorem main : H1 → H2 → type_of% @Erdos19.erdos_19 := by
  intro pairs higher V n C
  classical
  by_cases sm : n ≤ 3
  · exact Erdos19.erdos_19.variants.le_three C sm
  have hn : 0 < n := by omega
  obtain ⟨_,H,_,_,_,sz,lin,finish⟩ := E19Transfer.support_transfer C (Equiv.refl _)
  apply finish
  by_contra fail
  obtain ⟨K,hK,nonempty,bad,degree⟩ := E19Critical.critical hn H fail
  have sizeK (A) (ha : A ∈ K) := sz A (hK ha)
  have linK (A) (ha : A ∈ K) (B) (hb : B ∈ K) := lin A (hK ha) B (hK hb)
  have noOrder : ¬ ∃ e : Fin n ≃ Fin n, ∀ A ∈ K.image (Finset.map e.toEmbedding),
      3 ≤ A.card → ∃ l r : Fin n, A = Finset.Icc l r := by
    rintro ⟨e,ord⟩
    apply bad
    apply E19Transfer.pullback_support_coloring K e
    obtain ⟨s,l⟩ := E19Transfer.relabel_support_bounds K e sizeK linK
    exact EFLInterval.color_family hn _ l s ord
  have big : 3 ≤ (K.filter fun A => 3 ≤ A.card).card := by
    by_contra! few
    exact noOrder (EFLInterval.relabel_at_most_two K (by omega))
  obtain ⟨T,hT,smallest⟩ := exists_min_image K Finset.card nonempty
  have hr := sizeK T hT
  have bound := E19Rank.rank_bound K hr smallest linK hT rfl (degree T hT)
  have strict : T.card*T.card < n := by
    apply lt_of_le_of_ne bound
    intro eq
    apply bad
    apply E19Parallel.color_parallel K linK sizeK
    exact E19Equality.parallel K hr eq.symm
      (E19Equality.uniform K hr eq.symm smallest linK hT rfl (degree T hT)) linK degree
  by_cases two : T.card = 2
  · exact bad (pairs n K (by simpa [two] using strict) ⟨T,hT,two⟩ sizeK linK degree big noOrder)
  · exact bad (higher n T.card K (by omega) strict ⟨T,hT,rfl⟩ smallest linK degree big noOrder)

end

end OMA.R_Erdos19_erdos_19_R1
