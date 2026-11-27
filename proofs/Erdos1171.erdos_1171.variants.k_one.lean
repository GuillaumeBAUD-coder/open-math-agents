import FormalConjectures.ErdosProblems.«1171»

/-!
# The Erdős–Hajnal relation on the ordinal square

View the ordinal square as a lexicographically ordered grid. In a triangle-free
graph, each neighborhood is independent. If one neighborhood meets infinitely
many rows in uncountable sets, it contains a copy of the desired order type.

Otherwise each vertex has only finitely many such rows. In each row, thin to
an uncountable set on which all but finitely many target rows occur only
countably often among these exceptions. Choose countably many rows avoiding
one another's exceptional targets, and remove the remaining countably many
exceptions. A transfinite recursion now chooses uncountably many vertices per
row with no edges among the chosen vertices.
-/
open Set Ordinal Cardinal
universe u
namespace EH1171

private abbrev W := (ω₁ : Ordinal.{u}).ToType
private abbrev V := (ω : Ordinal.{u}).ToType

private theorem w_big : ¬ (univ : Set W.{u}).Countable := by
  rw [← Cardinal.le_aleph0_iff_set_countable, Cardinal.mk_univ, Cardinal.mk_toType, Ordinal.card_omega]
  exact not_le.mpr Cardinal.aleph0_lt_aleph_one

private theorem w_iic (x : W) : (Iic x).Countable := by
  have h : (Iio x).Countable := by
    apply Cardinal.le_aleph0_iff_set_countable.mp
    apply Cardinal.lt_aleph_one_iff.mp
    have a := Cardinal.mk_Iio_lt x (by simp [W])
    simpa [W] using a
  simpa only [Set.Iio_insert] using h.insert x

private instance v_count : Countable V.{u} := by
  apply Cardinal.mk_le_aleph0_iff.mp
  simp [V]

private theorem count_slice {α : Type*} (X : Set α) (hX : ¬X.Countable) (f : α → ℕ) :
    ∃ n : ℕ, ¬ {x ∈ X | f x = n}.Countable := by
  by_contra! h
  apply hX
  apply (countable_iUnion h).mono
  intro a ha
  exact mem_iUnion.mpr ⟨f a, ha, rfl⟩

/-- Thin an uncountable family of finite sets until all but finitely many coordinates
occur only countably often. Maximize the size of a common finite subset. -/
private theorem thin {α β : Type*} (X : Set α) (hX : ¬X.Countable) (F : α → Finset β) :
    ∃ (Y : Set α) (r : Finset β), Y ⊆ X ∧ ¬Y.Countable ∧
      ∀ b ∉ r, {x ∈ Y | b ∈ F x}.Countable := by
  classical
  obtain ⟨n, hn⟩ := count_slice X hX (fun x => (F x).card)
  let U := {x ∈ X | (F x).card = n}
  let P (k : ℕ) := ∃ r : Finset β, r.card = k ∧ ¬ {x ∈ U | r ⊆ F x}.Countable
  have p0 : P 0 := ⟨∅, rfl, by simpa [U] using hn⟩
  obtain ⟨r, hr, hY⟩ := Nat.findGreatest_spec (P := P) (Nat.zero_le n) p0
  refine ⟨_, r, fun x hx => hx.1.1, hY, ?_⟩
  intro b hb
  by_contra H
  let T := {x ∈ U | insert b r ⊆ F x}
  have ht : ¬T.Countable := fun h => H (h.mono (fun x hx =>
    (show x ∈ T from ⟨hx.1.1, Finset.insert_subset_iff.mpr ⟨hx.2, hx.1.2⟩⟩)))
  obtain ⟨x,hx⟩ : T.Nonempty := Set.nonempty_iff_ne_empty.mpr fun h => ht (h ▸ countable_empty)
  have hle : (insert b r).card ≤ n := (Finset.card_le_card hx.2).trans_eq hx.1.2
  refine Nat.findGreatest_is_greatest (P := P) ?_ hle ⟨_, rfl, ht⟩
  rw [Finset.card_insert_of_notMem hb, hr]
  omega

/-- Choose along a well-order with countable initial segments, avoiding countably
many exceptions imposed by each earlier choice. -/
private theorem pick {D : Type*} [LinearOrder D] [WellFoundedLT D]
    (hc : ∀ d : D, (Iio d).Countable) {α : Type*}
    (X : D → Set α) (hX : ∀ d, ¬(X d).Countable)
    (B : D → α → D → Set α) (hB : ∀ i a, a ∈ X i → ∀ j, (B i a j).Countable) :
    ∃ f : D → α, (∀ i, f i ∈ X i) ∧ ∀ i j, i < j → f j ∉ B i (f i) j := by
  classical
  have step (j : D) (g : ∀ i, i < j → X i) :
      ∃ x : X j, ∀ i (h : i < j), x.val ∉ B i (g i h).val j := by
    let T := ⋃ i : Iio j, B i.val (g i.val i.property).val j
    have : Countable (Iio j) := hc j
    have hT : T.Countable := countable_iUnion fun i => hB _ _ (g _ i.property).property _
    have hns : ¬ X j ⊆ T := fun h => hX j (hT.mono h)
    obtain ⟨x, hx, hn⟩ := Set.not_subset.mp hns
    exact ⟨⟨x,hx⟩, fun i hi hm => hn (mem_iUnion.mpr ⟨⟨i,hi⟩,hm⟩)⟩
  let f : (j : D) → X j := wellFounded_lt.fix fun j g => (step j g).choose
  refine ⟨fun j => (f j).val, fun j => (f j).property, ?_⟩
  intro i j hij
  have heq : f j = (step j (fun i _ => f i)).choose := WellFounded.fix_eq _ _ _
  exact (show (f j).val ∉ B i (f i).val j from by
    nth_rw 1 [heq]
    exact (step j (fun i _ => f i)).choose_spec i hij)

private theorem emb_big {X : Set W.{u}} (hX : ¬ X.Countable) :
    ∃ f : W.{u} → W.{u}, StrictMono f ∧ ∀ x, f x ∈ X := by
  have h : typeLT W ≤ typeLT X := by
    calc
      _ = (ℵ₁ : Cardinal.{u}).ord := (Ordinal.type_toType _).trans (Cardinal.ord_aleph 1).symm
      _ ≤ _ := Cardinal.ord_le.mpr (by simpa only [Ordinal.card_type, Cardinal.aleph_one_le_iff, lt_iff_not_ge, Cardinal.le_aleph0_iff_set_countable] using hX)
  obtain ⟨e⟩ := Ordinal.type_le_iff'.mp h
  exact ⟨fun x => (e x).val, fun _ _ h => e.map_rel_iff.mpr h, fun x => (e x).property⟩

private theorem emb_inf {X : Set W.{u}} (hX : X.Infinite) :
    ∃ f : V.{u} → W.{u}, StrictMono f ∧ ∀ x, f x ∈ X := by
  have := hX.to_subtype
  have h : typeLT V.{u} ≤ typeLT X := by
    rw [Ordinal.type_toType, ← Cardinal.ord_aleph0, Cardinal.ord_le, Ordinal.card_type]
    exact Cardinal.aleph0_le_mk _
  obtain ⟨e⟩ := Ordinal.type_le_iff'.mp h
  exact ⟨fun x => (e x).val, fun _ _ h => e.map_rel_iff.mpr h, fun x => (e x).property⟩


private theorem big_diff {α : Type*} {X T : Set α} (hX : ¬X.Countable) (hT : T.Countable) :
    ¬(X \ T).Countable := by
  intro h
  apply hX
  exact (h.union hT).mono (fun x hx => by by_cases ht : x ∈ T <;> simp [hx, ht])

private theorem free_rows (R : W.{u} → Finset W.{u}) :
    ∃ f : V.{u} → W.{u}, StrictMono f ∧ ∀ i j, i ≠ j → f j ∉ R (f i) := by
  classical
  obtain ⟨Y, r, _, hY, hrare⟩ := thin univ w_big R
  let U := Y \ (↑r : Set W)
  have hU : ¬U.Countable := big_diff hY r.finite_toSet.countable
  let B (a : W.{u}) := Iic a ∪ (↑(R a) : Set W) ∪ {x ∈ Y | a ∈ R x}
  have hB (a : W) (ha : a ∈ U) : (B a).Countable :=
    ((w_iic a).union (R a).finite_toSet.countable).union (hrare a ha.2)
  obtain ⟨f,hf,h⟩ := pick (D := V.{u}) (fun _ => to_countable _)
    (fun _ => U) (fun _ => hU) (fun _ a _ => B a) (fun _ a ha _ => hB a ha)
  refine ⟨f, fun i j hij => lt_of_not_ge (fun hle => h i j hij (Or.inl (Or.inl hle))), ?_⟩
  intro i j hij hm
  rcases lt_or_gt_of_ne hij with hl|hl
  · exact h i j hl (Or.inl (Or.inr hm))
  · exact h j i hl (Or.inr ⟨(hf i).1, hm⟩)

private abbrev Edge := W.{u} → W.{u} → W.{u} → W.{u} → Prop

private def Pattern (E : Edge.{u}) : Prop :=
  ∃ (f : V.{u} → W.{u}) (c : V.{u} → W.{u} → W.{u}), StrictMono f ∧
    (∀ i, StrictMono (c i)) ∧ ∀ i a j b, ¬E (f i) (c i a) (f j) (c j b)

/-- If one vertex sees uncountably many points in each of infinitely many rows,
its neighborhood already contains the desired independent rectangle. -/
private theorem many_rows (E : Edge.{u})
    (hn : ∀ i a j b k c, E i a j b → E i a k c → ¬ E j b k c)
    (X : W.{u} → Set W.{u}) (i a : W.{u})
    (hinf : {j | ¬{b ∈ X j | E i a j b}.Countable}.Infinite) : Pattern E := by
  obtain ⟨f, hf, hmem⟩ := emb_inf hinf
  have hx (j : V.{u}) := emb_big (X := {b ∈ X (f j) | E i a (f j) b}) (hmem j)
  choose c hc hm using hx
  exact ⟨f,c,hf,hc,fun j b k d => hn _ _ _ _ _ _ (hm j b).2 (hm k d).2⟩

private theorem lex_initial (d : W.{u} ×ₗ V.{u}) : (Iio d).Countable := by
  have h := ((w_iic (ofLex d).1).prod (countable_univ (α := V.{u}))).image toLex
  refine h.mono ?_
  intro e he
  exact ⟨ofLex e, ⟨(Prod.Lex.lt_iff.mp he).elim le_of_lt (fun h => h.1.le), trivial⟩, rfl⟩

/-- A rectangle of uncountable rows with countable adjacency in every row admits
a monochromatic subrectangle. Enumerate heights before rows, so all prior
constraints form a countable union. -/
private theorem sparse (E : Edge.{u}) (hsym : ∀ i a j b, E i a j b → E j b i a)
    (hloop : ∀ i a, ¬E i a i a)
    (f : V.{u} → W.{u}) (hf : StrictMono f) (X : V.{u} → Set W.{u})
    (hX : ∀ i, ¬(X i).Countable)
    (hs : ∀ i a, a ∈ X i → ∀ j, {b ∈ X j | E (f i) a (f j) b}.Countable) :
    Pattern E := by
  let row (d : W.{u} ×ₗ V.{u}) := (ofLex d).2
  let B (d : W.{u} ×ₗ V.{u}) (a : W) (e : W.{u} ×ₗ V.{u}) :=
    Iic a ∪ {b ∈ X (row e) | E (f (row d)) a (f (row e)) b}
  obtain ⟨c, hc, hb⟩ := pick lex_initial (fun d => X (row d)) (fun d => hX _)
    B (fun d a ha e => (w_iic a).union (hs _ _ ha _))
  refine ⟨f, fun i a => c (toLex (a,i)), hf, ?_, ?_⟩
  · intro i a b hab
    exact lt_of_not_ge fun hn => hb _ _ (Prod.Lex.toLex_lt_toLex.mpr (Or.inl hab)) (Or.inl hn)
  · intro i a j b he
    let d := toLex (a,i)
    let e := toLex (b,j)
    rcases lt_trichotomy d e with h|h|h
    · exact hb d e h (Or.inr ⟨hc e, he⟩)
    · have hij : i = j := congrArg (fun x => (ofLex x).2) h
      have hab : a = b := congrArg (fun x => (ofLex x).1) h
      subst j; subst b
      exact hloop _ _ he
    · exact hb e d h (Or.inr ⟨hc d, hsym _ _ _ _ he⟩)

private theorem rectangle (E : Edge.{u})
    (hsym : ∀ i a j b, E i a j b → E j b i a) (hloop : ∀ i a, ¬E i a i a)
    (hn : ∀ i a j b k c, E i a j b → E i a k c → ¬ E j b k c) :
    Pattern E := by
  classical
  by_contra h
  have row (i : W.{u}) : ∃ X : Set W.{u}, ¬X.Countable ∧
      ∀ a ∈ X, {b ∈ X | E i a i b}.Countable := by
    by_cases hex : ∃ t, ¬ {b | E i t i b}.Countable
    · obtain ⟨t,ht⟩ := hex
      refine ⟨{b | E i t i b}, ht, ?_⟩
      intro a ha
      apply countable_empty.mono
      exact fun b hb => False.elim (hn i t i a i b ha hb.1 hb.2)
    · push Not at hex
      exact ⟨univ, w_big, fun a _ => (hex a).mono (fun _ h => h.2)⟩
  choose X hX hrow using row
  let D (i a : W.{u}) := {j | ¬ {b ∈ X j | E i a j b}.Countable}
  have hD (i a : W.{u}) : (D i a).Finite :=
    by_contra fun hi => h (many_rows E hn X i a hi)
  let F (i a : W.{u}) := (hD i a).toFinset
  have memF (i a j : W.{u}) : j ∈ F i a ↔ ¬ {b ∈ X j | E i a j b}.Countable :=
    (hD i a).mem_toFinset
  have th (i : W.{u}) := thin (X i) (hX i) (F i)
  choose Y r hYX hY hr using th
  obtain ⟨f, hf, hfree⟩ := free_rows r
  let T (i j : V.{u}) := if i = j then (∅ : Set W.{u})
    else {a ∈ Y (f i) | f j ∈ F (f i) a}
  have ht (i j : V.{u}) : (T i j).Countable := by
    by_cases he : i = j
    · simp [T,he]
    · simpa [T,he] using hr (f i) (f j) (hfree i j he)
  let U (i : V.{u}) := Y (f i) \ ⋃ j, T i j
  apply h (sparse E hsym hloop f hf U (fun i => big_diff (hY _) (countable_iUnion (ht i))) ?_)
  intro i a ha j
  have hsub (j : V.{u}) : U j ⊆ X (f j) := fun b hb => hYX _ hb.1
  have hcnt : {b ∈ X (f j) | E (f i) a (f j) b}.Countable := by
    by_cases he : i = j
    · subst j; exact hrow _ _ (hsub _ ha)
    · by_contra H
      exact ha.2 (mem_iUnion.mpr ⟨j, by simpa [T,he] using And.intro ha.1 ((memF ..).mpr H)⟩)
  apply hcnt.mono
  intro b hb
  exact And.intro (hsub _ hb.1) hb.2

private theorem blue_triangle {A : Type u} {G : SimpleGraph A} {x y z : A}
    (hxy : G.Adj x y) (hxz : G.Adj x z) (hyz : G.Adj y z) :
    ∃ S : Set A, G.IsClique S ∧ #S = 3 := by
  classical
  let F : Finset A := {x,y,z}
  refine ⟨(F : Set A), ?_, ?_⟩
  · intro a ha b hb hab
    simp only [F, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl|rfl|rfl <;> rcases hb with rfl|rfl|rfl <;>
      first | exact hxy | exact hxy.symm | exact hxz | exact hxz.symm |
        exact hyz | exact hyz.symm | exact False.elim (hab rfl)
  · simp [F, hxy.ne, hxz.ne, hyz.ne]

private theorem square_rel : OrdinalCardinalRamsey.{u} (ω₁ ^ 2) (ω₁ * ω) 3 := by
  classical
  intro red blue hcomp
  by_cases hex : ∃ s, blue.IsClique s ∧ #s = 3
  · exact Or.inr hex
  left
  let A := (ω₁ ^ 2 : Ordinal.{u}).ToType
  have htype : typeLT (W.{u} ×ₗ W.{u}) = typeLT A := by
    change type (Prod.Lex (α := W.{u}) (β := W.{u}) (· < ·) (· < ·)) = _
    rw [type_prod_lex, type_toType, type_toType]
    simp [pow_two]
  obtain ⟨e⟩ := Ordinal.type_eq.mp htype
  let loc (i a : W.{u}) : A := e (toLex (i,a))
  let E : Edge.{u} := fun i a j b => blue.Adj (loc i a) (loc j b)
  have hn : ∀ i a j b k c, E i a j b → E i a k c → ¬E j b k c :=
    fun _ _ _ _ _ _ hx hy hz => hex (blue_triangle hx hy hz)
  obtain ⟨f, c, hf, hc, hnone⟩ := rectangle E (fun _ _ _ _ h => h.symm)
    (fun _ _ he => he.ne rfl) hn
  let g (x : V.{u} ×ₗ W.{u}) : A := loc (f (ofLex x).1) (c (ofLex x).1 (ofLex x).2)
  have hg : StrictMono g := by
    intro x y h
    apply e.map_rel_iff.mpr
    apply Prod.Lex.toLex_lt_toLex.mpr
    rcases Prod.Lex.lt_iff.mp h with h|⟨he,h⟩
    · exact Or.inl (hf h)
    · exact Or.inr ⟨congrArg f he, by simp only [he]; exact hc _ h⟩
  refine ⟨Set.range g, ?_, ?_⟩
  · rintro _ ⟨x,rfl⟩ _ ⟨y,rfl⟩ hne
    have hab : (red ⊔ blue).Adj (g x) (g y) := by rw [hcomp.sup_eq_top]; exact hne
    exact hab.resolve_right (hnone _ _ _ _)
  · have ht := (hg.orderIso g).toRelIsoLT.ordinalType_congr
    calc
      _ = typeLT (V.{u} ×ₗ W.{u}) := ht.symm
      _ = ω₁ * ω := by
        change type (Prod.Lex (α := V.{u}) (β := W.{u}) (· < ·) (· < ·)) = _
        rw [type_prod_lex, type_toType, type_toType]

end EH1171

theorem OMA.solution : type_of% @Erdos1171.erdos_1171.variants.k_one :=
  (ordinalMultiColorRamsey_one_iff_ordinalCardinalRamsey ..).mpr EH1171.square_rel

