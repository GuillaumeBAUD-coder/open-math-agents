import FormalConjectures.ErdosProblems.«596»
import Mathlib.NumberTheory.Bertrand
import Mathlib.Algebra.Field.ZMod

/-! An exceptional pair of finite graphs: `(C₄, C₆)`.
Credit: @JaviSoto.

In the finite-color direction, a large affine incidence graph has many three-edge paths through
middle edges with large degrees at both ends. In the countable-color direction, close initial
segments of a well-order under the unique common-neighbor operation, then color by cardinal induction.

The finite-color theorem is due to Nešetřil and Rödl. Ian Qvist (@Genbox) previously formalized it
for LeftToSolve in PR #1405. The finite proof below is an independent argument and implementation.
The countable-color theorem is due to Erdős and Hajnal.
-/

-- Credit: @JaviSoto

namespace OMA.Finite596

open Finset SimpleGraph
open scoped Classical

private def fiber {X Y : Type} [DecidableEq Y] (E : Finset X) (f : X → Y) (y : Y) :=
  E.filter (fun x => f x = y)

private def small {X Y : Type} [DecidableEq Y] (E : Finset X) (f : X → Y) (d : ℕ) :=
  E.filter (fun x => (fiber E f (f x)).card ≤ d)

private lemma small_card {X Y : Type} [Fintype Y] [DecidableEq Y]
    (E : Finset X) (f : X → Y) (d : ℕ) :
    (small E f d).card ≤ Fintype.card Y * d := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := f) (t := univ) (fun _ _ => mem_univ _)]
  calc
    _ ≤ ∑ _y : Y, d := by
      apply sum_le_sum
      intro y _
      by_cases h : (fiber E f y).card ≤ d
      · apply (card_le_card (t := fiber E f y) ?_).trans h
        intro x hx
        obtain ⟨h1,h2⟩ := mem_filter.mp hx
        exact mem_filter.mpr ⟨(mem_filter.mp h1).1,h2⟩
      · have hempty : {x ∈ small E f d | f x = y} = ∅ := by
          apply eq_empty_iff_forall_notMem.mpr
          intro x hx
          obtain ⟨hm,hxy⟩ := mem_filter.mp hx
          exact h (hxy ▸ (mem_filter.mp hm).2)
        simp [hempty]
    _ = _ := by simp

private lemma neighbors {X Y : Type} [DecidableEq X] [DecidableEq Y]
    {E : Finset X} {f : X → Y} {d : ℕ} {x : X} (hx : x ∈ E)
    (hx' : x ∉ small E f d) :
    Nonempty (Fin d ↪ ((fiber E f (f x)).erase x : Finset X)) := by
  have h : d < (fiber E f (f x)).card := by
    by_contra! hn
    exact hx' (mem_filter.mpr ⟨hx,hn⟩)
  apply Function.Embedding.nonempty_of_card_le
  simpa [card_erase_of_mem (show x ∈ fiber E f (f x) from mem_filter.mpr ⟨hx,rfl⟩)]
    using (show d ≤ (fiber E f (f x)).card - 1 by omega)

private theorem packed_paths {A B : Type} [Fintype A] [Fintype B]
    (E : Finset (A × B)) (d : ℕ)
    (unique_path : ∀ {x x₁ x₂ : A} {y y₁ y₂ : B},
      (x,y₁) ∈ E → (x₁,y₁) ∈ E → (x₁,y) ∈ E →
      (x,y₂) ∈ E → (x₂,y₂) ∈ E → (x₂,y) ∈ E →
      x₁ ≠ x → x₂ ≠ x → y₁ ≠ y → y₂ ≠ y → x₁ = x₂ ∧ y₁ = y₂) :
    (E.card - (Fintype.card A + Fintype.card B) * d) * d^2 ≤
      Fintype.card A * Fintype.card B := by
  classical
  let L := small E Prod.fst d
  let R := small E Prod.snd d
  let M := E \ (L ∪ R)
  have hM : E.card - (Fintype.card A + Fintype.card B) * d ≤ M.card := by
    have hu := card_union_le L R
    have hu' := card_le_card (show E ⊆ M ∪ (L ∪ R) by
      intro x hx
      by_cases h : x ∈ L ∪ R
      · exact mem_union_right _ h
      · exact mem_union_left _ (mem_sdiff.mpr ⟨hx,h⟩))
    have htot := card_union_le M (L ∪ R)
    have hl := small_card E Prod.fst d
    have hr := small_card E Prod.snd d
    change L.card ≤ _ at hl
    change R.card ≤ _ at hr
    rw [add_mul]
    omega
  have hmem (m : M) : m.val ∈ E := (mem_sdiff.mp m.2).1
  let F (m : M) := (neighbors (f := Prod.fst) (d := d) (hmem m)
    (fun h => (mem_sdiff.mp m.2).2 (mem_union_left _ h))).some
  let H (m : M) := (neighbors (f := Prod.snd) (d := d) (hmem m)
    (fun h => (mem_sdiff.mp m.2).2 (mem_union_right _ h))).some
  let a (m : M) (i : Fin d) := (H m i).val.1
  let b (m : M) (i : Fin d) := (F m i).val.2
  have fa (m : M) (i : Fin d) : (H m i).val = (a m i,m.val.2) := by
    exact Prod.ext rfl (mem_filter.mp (mem_erase.mp (H m i).2).2).2
  have fb (m : M) (i : Fin d) : (F m i).val = (m.val.1,b m i) := by
    exact Prod.ext (mem_filter.mp (mem_erase.mp (F m i).2).2).2 rfl
  have adjA (m : M) (i : Fin d) : (a m i,m.val.2) ∈ E := by
    rw [← fa]
    exact (mem_filter.mp (mem_erase.mp (H m i).2).2).1
  have adjB (m : M) (i : Fin d) : (m.val.1,b m i) ∈ E := by
    rw [← fb]
    exact (mem_filter.mp (mem_erase.mp (F m i).2).2).1
  have neA (m : M) (i : Fin d) : m.val.1 ≠ a m i := by
    intro h
    exact (mem_erase.mp (H m i).2).1 ((fa m i).trans (Prod.ext h.symm rfl))
  have neB (m : M) (i : Fin d) : m.val.2 ≠ b m i := by
    intro h
    exact (mem_erase.mp (F m i).2).1 ((fb m i).trans (Prod.ext rfl h.symm))
  let ends (s : M × Fin d × Fin d) := (a s.1 s.2.1,b s.1 s.2.2)
  have inj : Function.Injective ends := by
    rintro ⟨m,i,j⟩ ⟨m',i',j'⟩ he
    change (a m i, b m j) = (a m' i', b m' j') at he
    obtain ⟨ha,hb⟩ := Prod.mk.inj he
    obtain ⟨h1,h2⟩ := unique_path (adjA m i) (hmem m) (adjB m j)
      (ha ▸ adjA m' i') (hmem m') (hb ▸ adjB m' j')
      (neA m i) (ha ▸ neA m' i') (neB m j) (hb ▸ neB m' j')
    have hm : m = m' := Subtype.ext (Prod.ext h1 h2)
    subst m'
    have hi : i = i' := (H m).injective (Subtype.ext (by rw [fa,fa,ha]))
    have hj : j = j' := (F m).injective (Subtype.ext (by rw [fb,fb,hb]))
    simp [hi,hj]
  have hcount := Fintype.card_le_of_injective ends inj
  exact (Nat.mul_le_mul_right _ hM).trans (by simpa [sq] using hcount)

private def bip {A B : Type} (R : A → B → Prop) : SimpleGraph (A ⊕ B) where
  Adj
    | .inl a, .inr b => R a b
    | .inr b, .inl a => R a b
    | _, _ => False
  symm := ⟨by rintro (a|b) (a'|b') h <;> exact h⟩
  loopless := ⟨by rintro (a|b) h <;> exact h⟩

private def RectFree {A B : Type} (R : A → B → Prop) : Prop :=
  ∀ {a b u v}, R a u → R a v → R b u → R b v → a = b ∨ u = v

private lemma no_four {A B : Type} {R : A → B → Prop} (h : RectFree R) :
    (cycleGraph 4).Free (bip R) := by
  rintro ⟨f⟩
  have adj (i : Fin 4) := f.toHom.map_adj ((by decide : ∀ i : Fin 4, (cycleGraph 4).Adj i (i+1)) i)
  have h0 : (bip R).Adj (f 0) (f 1) := adj 0
  have h1 : (bip R).Adj (f 1) (f 2) := adj 1
  have h2 : (bip R).Adj (f 2) (f 3) := adj 2
  have h3 : (bip R).Adj (f 3) (f 0) := adj 3
  have ne02 : f 0 ≠ f 2 := fun eq => (by decide : (0 : Fin 4) ≠ 2) (f.injective eq)
  have ne13 : f 1 ≠ f 3 := fun eq => (by decide : (1 : Fin 4) ≠ 3) (f.injective eq)
  cases f 0 <;> cases f 1 <;> cases f 2 <;> cases f 3 <;>
    simp_all only [bip] <;> grind [RectFree]

private lemma no_hex_paths {A B : Type} {G : SimpleGraph (A ⊕ B)}
    (h : (cycleGraph 6).Free G)
    {x x₁ x₂ : A} {y y₁ y₂ : B}
    (st : G.Adj (.inl x) (.inr y₁)) (c1 : G.Adj (.inl x₁) (.inr y₁))
    (en : G.Adj (.inl x₁) (.inr y))
    (st' : G.Adj (.inl x) (.inr y₂)) (c2 : G.Adj (.inl x₂) (.inr y₂))
    (en' : G.Adj (.inl x₂) (.inr y))
    (hx1 : x₁ ≠ x) (hx2 : x₂ ≠ x) (hy1 : y₁ ≠ y) (hy2 : y₂ ≠ y)
    (rect : RectFree (fun a b => G.Adj (.inl a) (.inr b))) : x₁ = x₂ ∧ y₁ = y₂ := by
  by_cases he : x₁ = x₂
  · refine ⟨he,?_⟩
    subst x₂
    exact (rect c1 c2 st st').resolve_left hx1
  by_cases he' : y₁ = y₂
  · subst y₂
    exact ((rect c1 en c2 en').elim he hy1).elim
  exfalso
  apply h
  let f : Fin 6 → A ⊕ B := ![.inl x,.inr y₁,.inl x₁,.inr y,.inl x₂,.inr y₂]
  refine ⟨⟨⟨f,?_⟩,?_⟩⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> first
      | exact st | exact st.symm | exact c1 | exact c1.symm | exact en | exact en.symm
      | exact st' | exact st'.symm | exact c2 | exact c2.symm | exact en' | exact en'.symm
      | exact False.elim ((by decide : ¬ _) hij)
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [f] <;> grind

private def incidence {F : Type} [Field F] (a b : F × F) : Prop :=
  a.1 * b.1 = a.2 + b.2

private lemma incidence_free {F : Type} [Field F] : RectFree (@incidence F _) := by
  intro a b u v h1 h2 h3 h4
  unfold incidence at *
  have hprod : (a.1 - b.1) * (u.1 - v.1) = 0 := by
    linear_combination h1 - h2 - h3 + h4
  rcases mul_eq_zero.mp hprod with h | h
  · left
    have he := sub_eq_zero.mp h
    apply Prod.ext he
    rw [he] at h1
    linear_combination h3 - h1
  · right
    have he := sub_eq_zero.mp h
    apply Prod.ext he
    rw [he] at h1
    linear_combination h2 - h1

theorem finite : type_of% @Erdos596.erdos_596.variants.C4_C6_finite_ramsey := by
  classical
  intro r hr
  have hr' : 0 < r := hr
  let d := 64*r^2
  have hd : 0 < d := by dsimp [d]; positivity
  obtain ⟨p,hp,lo,hi⟩ := Nat.exists_prime_lt_and_le_two_mul (4*r*d) (by positivity)
  have : Fact (Nat.Prime p) := ⟨hp⟩
  let F := ZMod p
  let V := F × F
  have hF : Fintype.card F = p := ZMod.card p
  have hV : Fintype.card V = p^2 := by simp [V,hF,sq]
  let G : SimpleGraph (V ⊕ V) := bip incidence
  refine ⟨V ⊕ V,G,no_four incidence_free,?_⟩
  intro C hC
  let flag (z : V × F) : V × V := (z.1, (z.2, z.1.1*z.2 - z.1.2))
  have flag_inj : Function.Injective flag := by
    intro z z' h
    have h1 := congrArg (fun t : V × V => t.1) h
    have h2 := congrArg (fun t : V × V => t.2.1) h
    exact Prod.ext h1 h2
  have flag_adj (z : V × F) : G.Adj (.inl (flag z).1) (.inr (flag z).2) := by
    change z.1.1*z.2 = z.1.2 + (z.1.1*z.2-z.1.2)
    ring
  have cover (z : V × F) : ∃ i, (C i).Adj (.inl (flag z).1) (.inr (flag z).2) := by
    have h := flag_adj z
    rwa [hC.1, SimpleGraph.iSup_adj] at h
  choose color hc using cover
  have hden : (univ : Finset (Fin r)).card * (4*d*p^2) <
      (univ : Finset (V × F)).card := by
    simp only [card_univ,Fintype.card_fin,Fintype.card_prod,hF,hV]
    calc
      r * (4*d*p^2) = p^2*(4*r*d) := by ring
      _ < p^2*p := Nat.mul_lt_mul_of_pos_left lo (pow_pos hp.pos _)
  obtain ⟨i,_,hiC⟩ := exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (f := color) (fun _ _ => mem_univ _) hden
  let E := (univ.filter fun z => color z = i).image flag
  have ecard : 4*d*p^2 < E.card := by
    simpa [E,card_image_of_injective _ flag_inj] using hiC
  have eco {x y : V} (h : (x,y) ∈ E) : (C i).Adj (.inl x) (.inr y) := by
    obtain ⟨z,hz,hflag⟩ := mem_image.mp h
    have h1 : (flag z).1 = x := congrArg Prod.fst hflag
    have h2 : (flag z).2 = y := congrArg Prod.snd hflag
    simpa [h1,h2,(mem_filter.mp hz).2] using hc z
  refine ⟨i, ?_⟩
  by_contra hno
  have hsub : C i ≤ G := hC.1.symm ▸ le_iSup C i
  have rect : RectFree (fun a b : V => (C i).Adj (.inl a) (.inr b)) := by
    intro a b u v h1 h2 h3 h4
    exact incidence_free (hsub h1) (hsub h2) (hsub h3) (hsub h4)
  have bound := packed_paths E d (fun h1 h2 h3 h4 h5 h6 ne1 ne2 ne3 ne4 =>
    no_hex_paths hno (eco h1) (eco h2) (eco h3) (eco h4) (eco h5) (eco h6)
      ne1 ne2 ne3 ne4 rect)
  rw [hV] at bound
  have hgood : 2*d*p^2 < E.card - (p^2+p^2)*d := by
    have heq : (p^2+p^2)*d = 2*d*p^2 := by ring
    have heq' : 4*d*p^2 = 2*(2*d*p^2) := by ring
    rw [heq'] at ecard
    rw [heq]
    omega
  have hp2 : p^2 < 2*d*d^2 := by
    have ha := Nat.pow_le_pow_left hi 2
    have hb : 0 < r^2 := by positivity
    have hstep : 64*r^2 < 2*d := by dsimp [d]; omega
    calc
      p^2 ≤ (2*(4*r*d))^2 := ha
      _ = 64*r^2*d^2 := by ring
      _ < 2*d*d^2 := Nat.mul_lt_mul_of_pos_right hstep (pow_pos hd 2)
  have contra' : p^2*p^2 < (E.card - (p^2+p^2)*d)*d^2 := calc
    _ < p^2*(2*d*d^2) := Nat.mul_lt_mul_of_pos_left hp2 (pow_pos hp.pos 2)
    _ = (2*d*p^2)*d^2 := by ring
    _ < _ := Nat.mul_lt_mul_of_pos_right hgood (pow_pos hd 2)
  exact contra'.not_ge bound

end OMA.Finite596

namespace OMA.Escape596

open Cardinal Set SimpleGraph
open scoped Cardinal

variable {W : Type}

private def iter (op : W → W → W) (U : Set W) : ℕ → Set W
  | 0 => U
  | n+1 => iter op U n ∪ Set.range (fun p : (iter op U n) × (iter op U n) => op p.1 p.2)

private def cl (op : W → W → W) (U : Set W) : Set W := ⋃ n, iter op U n

private lemma iter_step (op : W → W → W) (U : Set W) :
    Monotone (iter op U) := monotone_nat_of_le_succ fun _ => Set.subset_union_left

private lemma cl_mono (op : W → W → W) : Monotone (cl op) := by
  intro U V hUV
  apply Set.iUnion_mono
  intro n
  induction n with
  | zero => exact hUV
  | succ n ih =>
    apply Set.union_subset_union ih
    rintro _ ⟨⟨x,y⟩,rfl⟩
    exact ⟨(⟨x,ih x.2⟩,⟨y,ih y.2⟩),rfl⟩

private lemma generator (op : W → W → W) (U : Set W) : U ⊆ cl op U :=
  fun _ hx => Set.mem_iUnion.mpr ⟨0,hx⟩

private lemma cl_closed (op : W → W → W) {U : Set W} {x y : W}
    (hx : x ∈ cl op U) (hy : y ∈ cl op U) : op x y ∈ cl op U := by
  obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hx
  obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hy
  let k := max i j
  exact Set.mem_iUnion.mpr ⟨k+1, Or.inr ⟨(⟨x,iter_step op U (le_max_left i j) hi⟩,
    ⟨y,iter_step op U (le_max_right i j) hj⟩),rfl⟩⟩

private lemma cl_small (op : W → W → W) (U : Set W) :
    #(cl op U) ≤ max ℵ₀ #U := by
  let k := max ℵ₀ #U
  have hk : ℵ₀ ≤ k := le_max_left _ _
  have h (n : ℕ) : #(iter op U n) ≤ k := by
    induction n with
    | zero => exact le_max_right _ _
    | succ n ih =>
      apply (Cardinal.mk_union_le _ _).trans
      apply (add_le_add ih ?_).trans_eq (Cardinal.add_eq_self hk)
      apply Cardinal.mk_range_le.trans
      rw [Cardinal.mk_prod]
      simpa using (mul_le_mul' ih ih).trans_eq (Cardinal.mul_eq_self hk)
  apply (Cardinal.mk_iUnion_le _).trans
  rw [Cardinal.mk_nat]
  exact (mul_le_mul' hk (ciSup_le h)).trans_eq (Cardinal.mul_eq_self hk)

private lemma split_set (op : W → W → W) (S : Set W) (hS : ℵ₀ < #S) :
    ∃ (I : Type) (_ : LinearOrder I) (rank : W → I),
      (∀ i, #(S ∩ {x | rank x = i} : Set W) < #S) ∧
      (∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, op x y = z →
        ¬ (rank x < rank z ∧ rank y < rank z)) := by
  classical
  let I := (Cardinal.ord #S).ToType
  have hi : #I = #S := by simp [I]
  let e : I ≃ S := (Cardinal.eq.mp hi).some
  have : Nonempty S := by
    by_contra! h
    simp at hS
  have : Nonempty I := Nonempty.map e.symm ‹Nonempty S›
  let U (i : I) : Set W := (fun j : I => (e j : W)) '' Set.Iic i
  have mono : Monotone U := fun _ _ hij => Set.image_mono (Set.Iic_subset_Iic.mpr hij)
  let F (i : I) := cl op (U i)
  have fm : Monotone F := (cl_mono op).comp mono
  have exists_stage (x : S) : ({i | x.val ∈ F i} : Set I).Nonempty := by
    refine ⟨e.symm x, generator op _ ?_⟩
    exact ⟨e.symm x,Set.mem_Iic.mpr le_rfl,by simp⟩
  let r (x : S) := (wellFounded_lt (α := I)).min _ (exists_stage x)
  have hr (x : S) : x.val ∈ F (r x) :=
    (wellFounded_lt (α := I)).min_mem {i | x.val ∈ F i} (exists_stage x)
  have least (x : S) (i : I) (hx : x.val ∈ F i) : r x ≤ i :=
    le_of_not_gt ((wellFounded_lt (α := I)).not_lt_min {i | x.val ∈ F i} hx)
  let rank (x : W) : I := if h : x ∈ S then r ⟨x,h⟩ else Classical.choice ‹Nonempty I›
  have rank_mem {x : W} (hx : x ∈ S) : x ∈ F (rank x) := by simpa [rank,hx] using hr ⟨x,hx⟩
  have rank_le {x : W} (hx : x ∈ S) {i : I} (hi : x ∈ F i) : rank x ≤ i := by
    simpa [rank,hx] using least ⟨x,hx⟩ i hi
  refine ⟨I, inferInstance, rank, ?_, ?_⟩
  · intro i
    have sub : S ∩ {x | rank x = i} ⊆ F i := by
      intro x hx
      rw [← (show rank x = i from hx.2)]
      exact rank_mem hx.1
    apply (Cardinal.mk_le_mk_of_subset sub).trans_lt
    apply (cl_small op (U i)).trans_lt
    apply max_lt hS
    apply Cardinal.mk_image_le.trans_lt
    have hI := Cardinal.mk_Iic_lt i (by simp [I])
      (hi ▸ hS.le)
    simpa only [hi] using hI
  · intro x hx y hy z hz hop ⟨h1,h2⟩
    let j := max (rank x) (rank y)
    have hx' : x ∈ F j := fm (le_max_left _ _) (rank_mem hx)
    have hy' : y ∈ F j := fm (le_max_right _ _) (rank_mem hy)
    have hz' : z ∈ F j := hop ▸ cl_closed op hx' hy'
    exact (max_lt h1 h2).not_ge (rank_le hz hz')

private lemma unique_common (G : SimpleGraph W) (hG : (cycleGraph 4).Free G)
    {x y u v : W} (hxy : x ≠ y) (hxu : G.Adj x u) (hyu : G.Adj y u)
    (hxv : G.Adj x v) (hyv : G.Adj y v) : u = v := by
  by_contra huv
  let f : Fin 4 → W := ![x,u,y,v]
  have hf : Function.Injective f := by
    have h1 := hxu.ne
    have h2 := hxv.ne
    have h3 := hyu.ne
    have h4 := hyv.ne
    intro i j
    fin_cases i <;> fin_cases j <;> simp [f] <;> grind
  apply hG
  refine ⟨⟨⟨f,?_⟩,hf⟩⟩
  intro i j hij
  fin_cases i <;> fin_cases j <;> first
    | exact hxu | exact hxu.symm | exact hyu | exact hyu.symm
    | exact hxv | exact hxv.symm | exact hyv | exact hyv.symm
    | exact (by decide : ¬ _ ) hij | contradiction

/-- Within a vertex subset, color adjacent pairs symmetrically so a six-cycle cannot be monochrome. -/
private def Colored (G : SimpleGraph W) (S : Set W) : Prop :=
  ∃ c : W → W → ℕ, (∀ x y, c x y = c y x) ∧
    ∀ f : Fin 6 ↪ W, (∀ i, f i ∈ S) → (∀ i, G.Adj (f i) (f (i+1))) →
      ∀ j, ¬ (∀ i, c (f i) (f (i+1)) = j)

private lemma colored_countable (G : SimpleGraph W) (S : Set W) (hS : #S ≤ ℵ₀) :
    Colored G S := by
  classical
  have : Countable S := Cardinal.mk_le_aleph0_iff.mp hS
  obtain ⟨label, inj⟩ := Countable.exists_injective_nat S
  let l (x : W) : ℕ := if hx : x ∈ S then label ⟨x,hx⟩ else 0
  have unique {x y : W} (hx : x ∈ S) (hy : y ∈ S) (h : l x = l y) : x = y :=
    congrArg Subtype.val (inj (by simpa [l,hx,hy] using h))
  refine ⟨fun x y => min (l x) (l y), fun _ _ => min_comm _ _, ?_⟩
  intro f hf _ j h
  have hj : min (l (f 0)) (l (f 1)) = min (l (f 2)) (l (f 3)) := (h 0).trans (h 2).symm
  have disj (i k : Fin 6) (hik : i ≠ k) : l (f i) ≠ l (f k) :=
    fun h' => hik (f.injective (unique (hf i) (hf k) h'))
  have h02 := disj 0 2 (by decide)
  have h03 := disj 0 3 (by decide)
  have h12 := disj 1 2 (by decide)
  have h13 := disj 1 3 (by decide)
  omega

private lemma colored_join (G : SimpleGraph W) (S : Set W) {I : Type} [LinearOrder I]
    (r : W → I)
    (hlower : ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x ≠ y → G.Adj x z → G.Adj y z →
      ¬ (r x < r z ∧ r y < r z))
    (hC : ∀ i, Colored G (S ∩ {x | r x = i})) : Colored G S := by
  classical
  choose c symm good using hC
  let d (x y : W) := if r x = r y then c (r x) x y + 1 else 0
  refine ⟨d, ?_, ?_⟩
  · intro x y
    by_cases he : r x = r y
    · simp [d,he,symm (r y) x y]
    · simp [d,he,Ne.symm he]
  intro f hf adj j hj
  cases j with
  | zero =>
    have diff (i : Fin 6) : r (f i) ≠ r (f (i+1)) := by
      intro h
      simpa [d,h] using hj i
    obtain ⟨i, _, hmax⟩ := Finset.exists_max_image Finset.univ (fun i : Fin 6 => r (f i))
      (by simp)
    have hpred : i-1+1 = i := sub_add_cancel ..
    have hpre : r (f (i-1)) < r (f i) := lt_of_le_of_ne (hmax _ (by simp))
      (by simpa only [hpred] using diff (i-1))
    have hnxt : r (f (i+1)) < r (f i) := lt_of_le_of_ne (hmax _ (by simp)) (diff i).symm
    exact hlower _ (hf (i-1)) _ (hf (i+1)) _ (hf i)
      (fun h => (show ∀ k : Fin 6, k-1 ≠ k+1 by decide) i (f.injective h))
      (by simpa only [hpred] using adj (i-1)) (adj i).symm ⟨hpre, hnxt⟩
  | succ j =>
    have same (i : Fin 6) : r (f i) = r (f (i+1)) := by
      by_contra h
      simpa [d,h] using hj i
    have hsame : ∀ i : Fin 6, r (f i) = r (f 0) := by
      have h0 : r (f 0) = r (f 1) := same 0
      have h1 : r (f 1) = r (f 2) := same 1
      have h2 : r (f 2) = r (f 3) := same 2
      have h3 : r (f 3) = r (f 4) := same 3
      have h4 : r (f 4) = r (f 5) := same 4
      intro i
      fin_cases i
      · rfl
      · exact h0.symm
      · exact (h0.trans h1).symm
      · exact ((h0.trans h1).trans h2).symm
      · exact (((h0.trans h1).trans h2).trans h3).symm
      · exact ((((h0.trans h1).trans h2).trans h3).trans h4).symm
    apply good (r (f 0)) f (fun i => ⟨hf i, hsame i⟩) adj j
    intro i
    simpa only [d, if_pos (same i), Nat.add_right_cancel_iff, hsame i] using hj i

private theorem colored_all (G : SimpleGraph W) (hG : (cycleGraph 4).Free G) (S : Set W) :
    Colored G S := by
  classical
  let op (x y : W) : W :=
    if h : ∃ z, G.Adj x z ∧ G.Adj y z then h.choose else x
  have hop {x y z : W} (hne : x ≠ y) (hx : G.Adj x z) (hy : G.Adj y z) : op x y = z := by
    have h : ∃ z, G.Adj x z ∧ G.Adj y z := ⟨z,hx,hy⟩
    exact (show op x y = h.choose by simp [op,h]).trans
      (unique_common G hG hne h.choose_spec.1 h.choose_spec.2 hx hy)
  generalize hsize : #S = k
  induction k using WellFoundedLT.induction generalizing S with
  | ind k ih =>
    subst k
    by_cases h : #S ≤ ℵ₀
    · exact colored_countable G S h
    obtain ⟨I, inst, rank, small, order⟩ := split_set op S (lt_of_not_ge h)
    let _ := inst
    apply colored_join G S rank
    · intro x hx y hy z hz hxy hxz hyz
      exact order x hx y hy z hz (hop hxy hxz hyz)
    · intro i
      exact ih _ (small i) _ rfl

theorem escape : type_of% @Erdos596.erdos_596.variants.C4_free_countable_escape := by
  intro W G hG
  obtain ⟨c,cs,good⟩ := colored_all G hG Set.univ
  let d (j : ℕ) : SimpleGraph W := {
    Adj := fun x y => G.Adj x y ∧ c x y = j
    symm := ⟨fun x y h => ⟨h.1.symm, (cs y x).trans h.2⟩⟩
    loopless := ⟨fun x h => G.loopless.irrefl x h.1⟩ }
  refine ⟨d, ⟨?_,?_⟩, ?_⟩
  · ext x y
    simp [SimpleGraph.iSup_adj,d]
  · intro i j hij
    apply disjoint_iff_inf_le.mpr
    intro x y h
    exact (hij (h.1.2.symm.trans h.2.2)).elim
  · rintro j ⟨f⟩
    have hedge (i : Fin 6) : (d j).Adj (f i) (f (i+1)) :=
      f.toHom.map_adj ((by decide : ∀ i : Fin 6, (cycleGraph 6).Adj i (i+1)) i)
    exact good f.toEmbedding (fun _ => Set.mem_univ _) (fun i => (hedge i).1) j
      (fun i => (hedge i).2)

end OMA.Escape596

theorem OMA.solution : type_of% @Erdos596.erdos_596.variants.exists_exceptional := by
  exact ⟨Fin 4, Fin 6, inferInstance, inferInstance, SimpleGraph.cycleGraph 4,
    SimpleGraph.cycleGraph 6, OMA.Finite596.finite, OMA.Escape596.escape⟩
