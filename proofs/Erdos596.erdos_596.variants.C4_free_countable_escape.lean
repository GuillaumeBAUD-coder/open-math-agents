import FormalConjectures.ErdosProblems.«596»
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.SetTheory.Ordinal.Basic

/-! # Countable edge colorings of graphs without a four-cycle -/

namespace OMA.Erdos596Proof

open SimpleGraph Set Function Cardinal

private theorem commonNeighbor_unique {W : Type} {G : SimpleGraph W}
    (hfree : (cycleGraph 4).Free G) {a b x y : W}
    (hab : a ≠ b) (hax : G.Adj a x) (hbx : G.Adj b x)
    (hay : G.Adj a y) (hby : G.Adj b y) : x = y := by
  classical
  by_contra hxy
  have hyx : y ≠ x := fun h => hxy h.symm
  let f : Fin 4 → W := ![a, x, b, y]
  have hinj : Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [f, hab, hab.symm, hxy, hyx, hax.ne, hax.ne.symm, hbx.ne,
        hbx.ne.symm, hay.ne, hay.ne.symm, hby.ne, hby.ne.symm] at hij ⊢
  refine hfree ⟨⟨⟨f, ?_⟩, hinj⟩⟩
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    first | exact hax | exact hax.symm | exact hbx | exact hbx.symm |
      exact hay | exact hay.symm | exact hby | exact hby.symm |
      exact False.elim (by revert hij; decide)

-- The fallback keeps this operation total without any nonemptiness assumption.
private noncomputable def commonNeighbor {W : Type} (G : SimpleGraph W) (a b : W) : W := by
  classical
  exact if h : a ≠ b ∧ ∃ x, G.Adj a x ∧ G.Adj b x then h.2.choose else a

private theorem commonNeighbor_eq {W : Type} {G : SimpleGraph W}
    (hfree : (cycleGraph 4).Free G) {a b x : W} (hab : a ≠ b)
    (ha : G.Adj a x) (hb : G.Adj b x) : commonNeighbor G a b = x := by
  classical
  have h : a ≠ b ∧ ∃ x, G.Adj a x ∧ G.Adj b x := ⟨hab, x, ha, hb⟩
  rw [commonNeighbor, dif_pos h]
  exact commonNeighbor_unique hfree hab h.2.choose_spec.1 h.2.choose_spec.2 ha hb

private def step {W : Type} (g : W → W → W) (s : Set W) : Set W :=
  s ∪ range (fun p : s × s => g p.1 p.2)

private def layers {W : Type} (g : W → W → W) (s : Set W) : ℕ → Set W
  | 0 => s
  | n + 1 => step g (layers g s n)

private def closure {W : Type} (g : W → W → W) (s : Set W) : Set W :=
  ⋃ n, layers g s n

private theorem subset_closure {W : Type} (g : W → W → W) (s : Set W) :
    s ⊆ closure g s :=
  fun _ hx => mem_iUnion.2 ⟨0, hx⟩

private theorem layers_mono {W : Type} (g : W → W → W) (s : Set W) :
    Monotone (layers g s) :=
  monotone_nat_of_le_succ fun _ _ hx => Or.inl hx

private theorem closure_mono {W : Type} (g : W → W → W) :
    Monotone (closure g) := by
  intro s t h x hx
  obtain ⟨n, hn⟩ := mem_iUnion.1 hx
  apply mem_iUnion.2
  refine ⟨n, ?_⟩
  have hm : ∀ n, layers g s n ⊆ layers g t n := by
    intro n
    induction n with
    | zero => exact h
    | succ n ih =>
      intro y hy
      change y ∈ step g (layers g s n) at hy
      change y ∈ step g (layers g t n)
      rcases hy with hy | ⟨⟨a,b⟩,rfl⟩
      · exact Or.inl (ih hy)
      · exact Or.inr ⟨(⟨a,ih a.property⟩, ⟨b,ih b.property⟩), rfl⟩
  exact hm n hn

private theorem closed_under {W : Type} (g : W → W → W) (s : Set W)
    {x y : W} (hx : x ∈ closure g s) (hy : y ∈ closure g s) :
    g x y ∈ closure g s := by
  obtain ⟨m, hm⟩ := mem_iUnion.1 hx
  obtain ⟨n, hn⟩ := mem_iUnion.1 hy
  let k := max m n
  refine mem_iUnion.2 ⟨k+1, Or.inr ?_⟩
  exact ⟨(⟨x,layers_mono g s (le_max_left m n) hm⟩,
    ⟨y,layers_mono g s (le_max_right m n) hn⟩), rfl⟩

private theorem closure_card {W : Type} (g : W → W → W) (s : Set W) :
    #(closure g s) ≤ max ℵ₀ #s := by
  let c := max ℵ₀ #s
  have hc : ℵ₀ ≤ c := le_max_left _ _
  have hstage : ∀ n, #(layers g s n) ≤ c := by
    intro n
    induction n with
    | zero => exact le_max_right _ _
    | succ n ih =>
      change #(step g (layers g s n)) ≤ c
      let t := layers g s n
      have hr : #(range (fun p : t × t => g p.1 p.2)) ≤ c := calc
        _ ≤ #(t × t) := mk_range_le
        _ = #t * #t := by simp
        _ ≤ c * c := mul_le_mul' ih ih
        _ = c := mul_eq_self hc
      calc
        _ ≤ #t + #(range (fun p : t × t => g p.1 p.2)) := mk_union_le _ _
        _ ≤ c + c := add_le_add ih hr
        _ = c := add_eq_self hc
  calc
    #(closure g s) ≤ #ℕ * ⨆ n, #(layers g s n) := mk_iUnion_le _
    _ ≤ ℵ₀ * c := by
      rw [mk_nat]
      exact mul_le_mul_right (ciSup_le' hstage) _
    _ = c := aleph0_mul_eq hc

private theorem cycle_succ_adj (i : Fin 6) : (cycleGraph 6).Adj i (i + 1) := by
  fin_cases i <;> decide

private theorem cycle_neighbors_ne (i : Fin 6) : i + 1 ≠ i - 1 := by
  fin_cases i <;> decide

private def IsCycleFreeLabel {W : Type} (G : SimpleGraph W) (c : W → W → ℕ) : Prop :=
  (∀ x y, c x y = c y x) ∧
    ∀ (f : Fin 6 ↪ W) (j : ℕ),
      (∀ i, (cycleGraph 6).Adj i (i + 1) → G.Adj (f i) (f (i + 1)) ∧
        c (f i) (f (i + 1)) = j) → False

private theorem label_exists (k : Cardinal.{0}) :
    ∀ (W : Type) (G : SimpleGraph W), #W = k → (cycleGraph 4).Free G →
      ∃ c, IsCycleFreeLabel G c := by
  classical
  induction k using WellFoundedLT.induction with
  | ind k ih =>
    intro W G hk hfree
    by_cases hcount : k ≤ ℵ₀
    · have : Countable W := mk_le_aleph0_iff.1 (hk ▸ hcount)
      obtain ⟨code, hinj⟩ := exists_injective_nat W
      refine ⟨fun x y => code x + code y, fun _ _ => Nat.add_comm _ _, ?_⟩
      intro f j hf
      have h0 := (hf 0 (cycle_succ_adj 0)).2
      have h1 := (hf 1 (cycle_succ_adj 1)).2
      change code (f 0) + code (f 1) = j at h0
      change code (f 1) + code (f 2) = j at h1
      have hn : (0 : Fin 6) ≠ 2 := by decide
      exact hn (f.injective (hinj (by omega)))
    -- Initial segments of the initial ordinal of k have cardinality below k.
    let I := k.ord.ToType
    have e : W ≃ I := Classical.choice (Cardinal.eq.mp (hk.trans (mk_ord_toType k).symm))
    let stages : I → Set W := fun i => closure (commonNeighbor G) (e ⁻¹' Iic i)
    have stages_mono : Monotone stages :=
      fun _ _ hij => closure_mono _ (preimage_mono (Iic_subset_Iic.2 hij))
    have small : ∀ i, #(stages i) < k := by
      intro i
      have hi : #(Iio i) < k := by
        have hcard : #I = k := mk_ord_toType k
        have htype : (#I).ord = Ordinal.type (fun x y : I => x < y) :=
          (congrArg Cardinal.ord hcard).trans (Ordinal.type_toType k.ord).symm
        simpa only [hcard] using mk_Iio_lt i htype
      have hle : ℵ₀ ≤ k := le_of_lt (lt_of_not_ge hcount)
      have hiic : Iic i = Iio i ∪ {i} := by
        ext x
        simp only [mem_Iic, mem_union, mem_Iio, mem_singleton_iff]
        exact le_iff_lt_or_eq
      have hc : #(Iic i) < k := by
        rw [hiic]
        apply (mk_union_le _ _).trans_lt
        rw [mk_singleton]
        exact add_lt_of_lt hle hi (one_lt_aleph0.trans_le hle)
      exact (closure_card _ _).trans_lt (max_lt (lt_of_not_ge hcount)
        (by rwa [mk_preimage_equiv]))
    have hex : ∀ x : W, ∃ i : I, x ∈ stages i ∧ ∀ j : I, j < i → x ∉ stages j := by
      intro x
      have hn : {i : I | x ∈ stages i}.Nonempty :=
        ⟨e x, subset_closure _ _ (show e x ≤ e x from le_rfl)⟩
      obtain ⟨i, hi, hm⟩ := wellFounded_lt.has_min _ hn
      exact ⟨i,hi,fun j hj hmem => hm j hmem hj⟩
    choose block hmem hmin using hex
    let S : I → Set W := fun i => {x | block x = i}
    -- Two distinct earlier neighbors would put x in an earlier closed set.
    have crosses : ∀ {x y z : W}, block y < block x → block z < block x →
        G.Adj x y → G.Adj x z → y = z := by
      intro x y z hy hz hxy hxz
      by_contra hne
      let i := max (block y) (block z)
      have hb : i < block x := max_lt hy hz
      have hmy : y ∈ stages i := stages_mono (le_max_left _ _) (hmem y)
      have hmz : z ∈ stages i := stages_mono (le_max_right _ _) (hmem z)
      have hc : commonNeighbor G y z ∈ stages i := closed_under _ _ hmy hmz
      rw [commonNeighbor_eq hfree hne hxy.symm hxz.symm] at hc
      exact hmin x i hb hc
    have hlabels : ∀ i : I, ∃ c, IsCycleFreeLabel (G.induce (S i)) c := by
      intro i
      have hs : S i ⊆ stages i := by
        intro x hx
        change block x = i at hx
        exact hx ▸ hmem x
      have hs' : #(S i) < k := (mk_le_mk_of_subset hs).trans_lt (small i)
      exact ih _ hs' (S i) (G.induce (S i)) rfl
        (fun ⟨f⟩ => hfree ⟨(Copy.induce G (S i)).comp f⟩)
    choose color hcolor using hlabels
    let extColor (i : I) (x y : W) :=
      if h : x ∈ S i ∧ y ∈ S i then color i ⟨x,h.1⟩ ⟨y,h.2⟩ else 0
    have ext_symm (i : I) (x y : W) : extColor i x y = extColor i y x := by
      by_cases hx : x ∈ S i <;> by_cases hy : y ∈ S i <;>
        simp [extColor, hx, hy, (hcolor i).1]
    let c (x y : W) := if block x = block y then extColor (block x) x y + 1 else 0
    have hsymm (x y : W) : c x y = c y x := by
      by_cases h : block x = block y
      · simp only [c, if_pos h, if_pos h.symm, ext_symm (block x) x y]
        rw [h]
      · simp [c, h, Ne.symm h]
    refine ⟨c,hsymm,?_⟩
    intro f j hf
    have hf' (i : Fin 6) := hf i (cycle_succ_adj i)
    by_cases hzero : j = 0
    · have hcross (i : Fin 6) : block (f i) ≠ block (f (i + 1)) := by
        intro heq
        have hi := (hf' i).2
        simp only [c, if_pos heq, hzero] at hi
        omega
      obtain ⟨i, _, hmax⟩ := Finset.exists_max_image Finset.univ
        (fun i : Fin 6 => block (f i)) Finset.univ_nonempty
      have hnext := hmax (i+1) (Finset.mem_univ _)
      have hprev := hmax (i-1) (Finset.mem_univ _)
      have hcancel : i - 1 + 1 = i := sub_add_cancel _ _
      have hcrossprev := hcross (i-1)
      rw [hcancel] at hcrossprev
      have hadjprev := (hf' (i-1)).1
      rw [hcancel] at hadjprev
      exact cycle_neighbors_ne i (f.injective (crosses
        (lt_of_le_of_ne hnext (Ne.symm (hcross i)))
        (lt_of_le_of_ne hprev hcrossprev)
        (hf' i).1 hadjprev.symm))
    · have hsame (i : Fin 6) : block (f i) = block (f (i + 1)) := by
        by_contra hne
        exact hzero (by simpa [c, hne] using (hf' i).2.symm)
      have hall (i : Fin 6) : block (f i) = block (f 0) := by
        fin_cases i
        · rfl
        · exact (hsame 0).symm
        · exact ((hsame 0).trans (hsame 1)).symm
        · exact ((hsame 0).trans ((hsame 1).trans (hsame 2))).symm
        · exact ((hsame 0).trans ((hsame 1).trans ((hsame 2).trans (hsame 3)))).symm
        · exact (hsame 5)
      let f' : Fin 6 ↪ S (block (f 0)) :=
        ⟨fun i => ⟨f i, hall i⟩, fun _ _ h => f.injective (congrArg Subtype.val h)⟩
      apply (hcolor (block (f 0))).2 f' (j-1)
      intro i _
      refine ⟨(hf' i).1, ?_⟩
      have hi := (hf' i).2
      change (if block (f i) = block (f (i + 1))
        then extColor (block (f i)) (f i) (f (i + 1)) + 1 else 0) = j at hi
      rw [if_pos (hsame i), hall i] at hi
      rw [show extColor (block (f 0)) (f i) (f (i + 1)) =
          color (block (f 0)) ⟨f i,hall i⟩ ⟨f (i + 1),hall (i + 1)⟩ from
        dif_pos ⟨hall i, hall (i + 1)⟩] at hi
      change color (block (f 0)) ⟨f i,hall i⟩ ⟨f (i + 1),hall (i + 1)⟩ = j - 1
      omega

end OMA.Erdos596Proof

open SimpleGraph

theorem OMA.solution : type_of% @Erdos596.erdos_596.variants.C4_free_countable_escape := by
  intro W G hfree
  obtain ⟨c, hsymm, hvalid⟩ := OMA.Erdos596Proof.label_exists (Cardinal.mk W) W G rfl hfree
  let d (j : ℕ) : SimpleGraph W :=
    { Adj := fun x y => G.Adj x y ∧ c x y = j
      symm.symm := fun x y h => ⟨h.1.symm, (hsymm x y).symm.trans h.2⟩
      loopless := ⟨fun _ h => h.1.ne rfl⟩ }
  refine ⟨d, ⟨?_, ?_⟩, ?_⟩
  · ext x y
    rw [iSup_adj]
    exact ⟨fun h => ⟨c x y,h,rfl⟩, fun ⟨_,h,_⟩ => h⟩
  · intro i j hne
    exact disjoint_left.2 (fun _ _ hi hj => hne (hi.2.symm.trans hj.2))
  · intro j ⟨f⟩
    exact hvalid f.toEmbedding j (fun _ h => f.toHom.map_rel h)
