import FormalConjectures.ErdosProblems.«1169»

/-! Transfer Hajnal’s graph on the lexicographic square to the ordinal Ramsey predicate. -/

open Cardinal Ordinal
open scoped Cardinal

namespace HajnalOrdinal

universe u

noncomputable abbrev W := (ω_ (1 : Ordinal.{u})).ToType
noncomputable abbrev WSquare := (ω_ (1 : Ordinal.{u})) ^ (2 : ℕ)

abbrev lexSquare (x y : W.{u} × W.{u}) : Prop :=
  Prod.Lex (· < ·) (· < ·) x y

theorem product_type :
    type (lexSquare.{u}) =
      WSquare := by
  change type (Prod.Lex (α := W.{u}) (β := W.{u}) (· < ·) (· < ·)) = _
  simp [WSquare, pow_two]

noncomputable def model :
    ((· < ·) : (WSquare.{u}).ToType → (WSquare.{u}).ToType → Prop) ≃r
      lexSquare.{u} :=
  Classical.choice (Ordinal.type_eq.mp ((Ordinal.type_toType _).trans product_type.symm))

/-- A triangle-free graph on the lexicographic square suffices when every
full order embedding into the square has two adjacent points in its image. -/
theorem of_graph (G : SimpleGraph (W.{u} × W.{u}))
    (htri : ∀ x y z, G.Adj x y → G.Adj y z → ¬ G.Adj x z)
    (hlarge : ∀ f : lexSquare.{u} ↪r
        lexSquare.{u},
      ∃ a b, G.Adj (f a) (f b)) :
    ∀ k : ℕ, 3 ≤ k → ¬ OrdinalRamsey WSquare.{u} WSquare.{u} (k : Ordinal) := by
  let e := model.{u}
  let H := G.comap e
  have hbase : ¬ OrdinalRamsey WSquare.{u} WSquare.{u} (3 : Ordinal) := by
    intro h
    obtain ⟨s, hred, ht⟩ | ⟨s, hblue, ht⟩ := h Hᶜ H (isCompl_compl.symm)
    · let g : ((· < ·) : (WSquare.{u}).ToType → (WSquare.{u}).ToType → Prop) ≃r
          ((· < ·) : s → s → Prop) :=
        Classical.choice (Ordinal.type_eq.mp ((Ordinal.type_toType _).trans ht.symm))
      let inc : ((· < ·) : s → s → Prop) ↪r
          ((· < ·) : (WSquare.{u}).ToType → (WSquare.{u}).ToType → Prop) :=
        ⟨⟨Subtype.val, Subtype.val_injective⟩, Iff.rfl⟩
      let f := e.symm.toRelEmbedding.trans (g.toRelEmbedding.trans (inc.trans e.toRelEmbedding))
      obtain ⟨a, b, hab⟩ := hlarge f
      change G.Adj (e (g (e.symm a)).val) (e (g (e.symm b)).val) at hab
      have hne : (g (e.symm a)).val ≠ (g (e.symm b)).val :=
        fun heq => G.ne_of_adj hab (congrArg e heq)
      exact ((SimpleGraph.compl_adj _ _ _).mp
        (hred (g (e.symm a)).property (g (e.symm b)).property hne)).2 hab
    · have hfin : type ((· < ·) : ULift.{u} (Fin 3) → ULift.{u} (Fin 3) → Prop) = (3 : Ordinal.{u}) := by
        rw [Ordinal.type_fintype, Fintype.card_ulift, Fintype.card_fin]
        rfl
      let g : ((· < ·) : ULift.{u} (Fin 3) → ULift.{u} (Fin 3) → Prop) ≃r ((· < ·) : s → s → Prop) :=
        Classical.choice (Ordinal.type_eq.mp (hfin.trans ht.symm))
      have hadj {i j : ULift.{u} (Fin 3)} (hij : i ≠ j) :
          G.Adj (e (g i).val) (e (g j).val) :=
        hblue (g i).property (g j).property
          (fun heq => hij (g.injective (Subtype.ext heq)))
      exact htri _ _ _ (hadj (i := ⟨0⟩) (j := ⟨1⟩) (by decide))
        (hadj (i := ⟨1⟩) (j := ⟨2⟩) (by decide)) (hadj (i := ⟨0⟩) (j := ⟨2⟩) (by decide))
  intro k hk h
  have hk' : (3 : Ordinal.{u}) ≤ (k : Ordinal.{u}) := by exact_mod_cast hk
  exact hbase (Erdos1169.ordinalRamsey_mono_blue h hk')


theorem countable_below (b : W.{u}) : (Set.Iio b).Countable := by
  apply Cardinal.le_aleph0_iff_set_countable.mp
  apply Cardinal.lt_aleph_one_iff.mp
  have h := Cardinal.mk_Iio_lt b (by
    change (Cardinal.mk (ω_ (1 : Ordinal.{u})).ToType).ord =
      typeLT (ω_ (1 : Ordinal.{u})).ToType
    rw [Cardinal.mk_toType, Ordinal.card_omega, Cardinal.ord_aleph, Ordinal.type_toType])
  simpa only [W, Cardinal.mk_toType, Ordinal.card_omega] using h

theorem countable_atMost (b : W.{u}) : (Set.Iic b).Countable := by
  refine ((countable_below b).insert b).mono ?_
  intro a ha
  exact ha.lt_or_eq.elim (fun h => Or.inr h) (fun h => Or.inl h)

theorem not_countable_W : ¬ (Set.univ : Set W.{u}).Countable := by
  rw [← Cardinal.le_aleph0_iff_set_countable, ← Cardinal.lt_aleph_one_iff,
    Cardinal.mk_univ, W, Cardinal.mk_toType, Ordinal.card_omega]
  exact lt_irrefl _

def fiber (f : lexSquare.{u} ↪r lexSquare.{u}) (a c : W.{u}) : Set W.{u} :=
  {b | (f (a, b)).1 = c}

theorem exists_large_fiber (f : lexSquare.{u} ↪r lexSquare.{u}) (a : W.{u}) :
    ∃ c, ¬ (fiber f a c).Countable := by
  let hNoMax : NoMaxOrder W.{u} := Ordinal.isSuccPrelimit_type_lt_iff.mp (by
    rw [Ordinal.type_toType]
    exact (Cardinal.isSuccLimit_omega _).isSuccPrelimit)
  obtain ⟨a', haa'⟩ := exists_gt a
  let last := (f (a', a)).1
  have hbound (b : W.{u}) : (f (a, b)).1 ≤ last := by
    have h : lexSquare (f (a, b)) (f (a', a)) :=
      f.map_rel_iff.mpr (Prod.lex_def.mpr (Or.inl haa'))
    exact (Prod.lex_def.mp h).elim le_of_lt (fun h => h.1.le)
  by_contra! h
  let hCount : Countable (Set.Iic last) := (countable_atMost last).to_subtype
  apply not_countable_W
  refine (Set.countable_iUnion fun c : Set.Iic last => h c.val).mono ?_
  intro b _
  exact Set.mem_iUnion.mpr ⟨⟨(f (a, b)).1, hbound b⟩, rfl⟩

theorem large_fiber_unbounded (f : lexSquare.{u} ↪r lexSquare.{u}) (a c b₀ : W.{u})
    (h : ¬ (fiber f a c).Countable) :
    ∃ b ∈ fiber f a c, b₀ < (f (a, b)).2 := by
  by_contra! hn
  let height := fun b : fiber f a c => (f (a, b.val)).2
  have hinj : Function.Injective height := by
    intro i j hij
    apply Subtype.ext
    exact congrArg Prod.snd (f.injective
      (Prod.ext (i.property.trans j.property.symm) hij))
  have hcount : (Set.univ : Set (fiber f a c)).Countable :=
    ((countable_atMost b₀).preimage hinj).mono (fun b _ => hn b.val b.property)
  exact h (Set.countable_univ_iff.mp hcount).to_set

/-- Each source column contributes to a distinct large image column. -/
theorem ordered_large_columns (f : lexSquare.{u} ↪r lexSquare.{u}) :
    ∃ c : W.{u} → W.{u}, StrictMono c ∧
      ∀ a b₀, ∃ b, (f (a, b)).1 = c a ∧ b₀ < (f (a, b)).2 := by
  classical
  choose c hc using exists_large_fiber f
  refine ⟨c, ?_, fun a b₀ => large_fiber_unbounded f a (c a) b₀ (hc a)⟩
  intro a a' haa'
  obtain ⟨b', hc', _⟩ := large_fiber_unbounded f a' (c a') a (hc a')
  obtain ⟨b, hcb, hrow⟩ := large_fiber_unbounded f a (c a) (f (a', b')).2 (hc a)
  have h : lexSquare (f (a, b)) (f (a', b')) :=
    f.map_rel_iff.mpr (Prod.lex_def.mpr (Or.inl haa'))
  rcases Prod.lex_def.mp h with hh | ⟨_, hh⟩
  · exact hcb ▸ hc' ▸ hh
  · exact (hrow.not_gt hh).elim


theorem countable_bddAbove {s : Set W.{u}} (hs : s.Countable) : BddAbove s := by
  by_contra h
  have hbig (b : W.{u}) : ∃ c ∈ s, b < c := by
    by_contra! hn
    exact h ⟨b, fun _ hc => hn _ hc⟩
  let hCount : Countable s := hs.to_subtype
  apply not_countable_W
  refine (Set.countable_iUnion fun c : s => countable_below c.val).mono ?_
  intro b _
  obtain ⟨c, hc, hbc⟩ := hbig b
  exact Set.mem_iUnion.mpr ⟨⟨c, hc⟩, hbc⟩

theorem strictMono_cofinal {c : W.{u} → W.{u}} (h : StrictMono c) (b : W.{u}) :
    ∃ a, b < c a := by
  by_contra! hb
  exact not_countable_W (((countable_atMost b).preimage h.injective).mono (fun a _ => hb a))


/-- A full lexicographic copy of the square contains a countable double-limit demand.
The demand writes each point with its height first, as in the transversal construction. -/
theorem countable_demand (f : lexSquare.{u} ↪r lexSquare.{u}) :
    ∃ (d μ : W.{u}) (Y : Set (W.{u} × W.{u})),
      (∀ h : W.{u}, ∃ a, (f a).1 = d ∧ h < (f a).2) ∧
      Y.Countable ∧ Y ⊆ Set.range (fun p => (f p).swap) ∧
      (∀ p ∈ Y, p.1 < μ ∧ p.2 < μ ∧ d < p.2) ∧
      ((Set.Iio μ).Nonempty ∧ ∀ z < μ, ∃ d, z < d ∧ d < μ ∧
        ∀ y < μ, ∃ t, y < t ∧ t < μ ∧ (t, d) ∈ Y) := by
  classical
  obtain ⟨c, hc, hrows⟩ := ordered_large_columns f
  choose row hcol hrow using hrows
  have hbound (z : W.{u}) : ∃ v, ∀ a, c a ≤ z → (f (a, row a z)).2 ≤ v := by
    let S : Set W.{u} := {a | c a ≤ z}
    have hS : S.Countable := (countable_atMost z).preimage hc.injective
    obtain ⟨v, hv⟩ := countable_bddAbove (hS.image (fun a => (f (a, row a z)).2))
    exact ⟨v, fun a ha => hv (Set.mem_image_of_mem _ ha)⟩
  choose bound hbound using hbound
  choose next hnext using strictMono_cofinal hc
  obtain ⟨a₀⟩ := Ordinal.nonempty_toType_iff.mpr (Ordinal.omega_pos (1 : Ordinal.{u})).ne'
  let index : ℕ → W.{u} := Nat.rec (next (c a₀)) (fun _ a => next (max (c a) (bound (c a))))
  let level : ℕ → W.{u} := c ∘ index
  have hstep (n : ℕ) : max (level n) (bound (level n)) < level (n + 1) :=
    hnext _
  have hlevels : StrictMono level :=
    strictMono_nat_of_lt_succ fun n => (le_max_left _ _).trans_lt (hstep n)
  obtain ⟨z, hz⟩ := countable_bddAbove (Set.countable_range level)
  let B := upperBounds (Set.range level)
  have hB : B.Nonempty := ⟨z, hz⟩
  let μ := wellFounded_lt.min B hB
  have hμ : μ ∈ B := wellFounded_lt.min_mem B hB
  have hlevel (n : ℕ) : level n < μ :=
    (hlevels (Nat.lt_succ_self n)).trans_le (hμ (Set.mem_range_self (n + 1)))
  have hcofinal (a : W.{u}) (ha : a < μ) : ∃ n, a < level n := by
    by_contra! hn
    exact wellFounded_lt.not_lt_min B (show a ∈ B from fun b ⟨n, e⟩ => e ▸ hn n) ha
  let point (i n : ℕ) : W.{u} × W.{u} :=
    ((f (index i, row (index i) (level n))).2, level i)
  let Y := Set.range (fun p : {q : ℕ × ℕ // q.1 ≤ q.2} => point p.val.1 p.val.2)
  have ht (i n : ℕ) (hin : i ≤ n) : (point i n).1 < μ := by
    have hrowBound := hbound (level n) (index i) (hlevels.monotone hin)
    exact hrowBound.trans_lt
      ((le_max_right _ _).trans_lt ((hstep n).trans (hlevel (n + 1))))
  have hfirst : c a₀ < level 0 := hnext _
  refine ⟨c a₀, μ, Y, ?_, Set.countable_range _, ?_, ?_, ⟨level 0, hlevel 0⟩, ?_⟩
  · intro h
    exact ⟨(a₀, row a₀ h), hcol a₀ h, hrow a₀ h⟩
  · rintro _ ⟨⟨⟨i, n⟩, _⟩, rfl⟩
    exact ⟨(index i, row (index i) (level n)), Prod.ext rfl (hcol (index i) (level n))⟩
  · rintro _ ⟨⟨⟨i, n⟩, hin⟩, rfl⟩
    exact ⟨ht i n hin, hlevel i, hfirst.trans_le (hlevels.monotone (Nat.zero_le i))⟩
  · intro z hz
    obtain ⟨i, hi⟩ := hcofinal z hz
    refine ⟨level i, hi, hlevel i, ?_⟩
    intro y hy
    obtain ⟨j, hj⟩ := hcofinal y hy
    let n := max i j
    have hi' : i ≤ n := le_max_left _ _
    have hj' : j ≤ n := le_max_right _ _
    refine ⟨(point i n).1, ?_, ht i n hi', ⟨⟨(i, n), hi'⟩, rfl⟩⟩
    exact hj.trans (hlevels.monotone hj' |>.trans_lt (hrow (index i) (level n)))


/-- A graph that hits every countable tagged demand forces the negative partition relation. -/
theorem of_demand_graph
    (G : SimpleGraph (W.{u} × W.{u}))
    (htri : ∀ x y z, G.Adj x y → G.Adj y z → ¬ G.Adj z x)
    (hhit : ∀ (μ : W.{u}) (Y : Set (W.{u} × W.{u})), Y.Countable →
      (∀ p ∈ Y, p.1 < μ ∧ p.2 < μ) →
      ((Set.Iio μ).Nonempty ∧ ∀ z < μ, ∃ d, z < d ∧ d < μ ∧
        ∀ y < μ, ∃ t, y < t ∧ t < μ ∧ (t, d) ∈ Y) →
      ∃ v : W.{u}, ∀ x : W.{u} × W.{u},
        v < x.1 → (∀ p ∈ Y, x.2 < p.2) → ∃ p ∈ Y, G.Adj x p) :
    ∀ k : ℕ, 3 ≤ k → ¬ OrdinalRamsey WSquare.{u} WSquare.{u} (k : Ordinal) := by
  apply of_graph (G.comap Prod.swap)
  · intro x y z hxy hyz hxz
    change G.Adj (Prod.swap x) (Prod.swap z) at hxz
    exact htri _ _ _ hxy hyz hxz.symm
  · intro f
    obtain ⟨d, μ, Y, hearly, hcount, hY, hbounds, hdouble⟩ := countable_demand f
    obtain ⟨v, hv⟩ := hhit μ Y hcount
      (fun p hp => ⟨(hbounds p hp).1, (hbounds p hp).2.1⟩) hdouble
    obtain ⟨x, hxcol, hxheight⟩ := hearly v
    have hxbelow (q) (hq : q ∈ Y) : (f x).swap.2 < q.2 := by
      change (f x).1 < q.2
      rw [hxcol]
      exact (hbounds q hq).2.2
    obtain ⟨p, hp, hadj⟩ := hv (f x).swap hxheight hxbelow
    obtain ⟨y, rfl⟩ := hY hp
    exact ⟨x, y, hadj⟩

end HajnalOrdinal

/-!
# Hajnal's free transversal

The construction specializes Lemma 3 of A. Hajnal, “A Negative Partition Relation”,
Proc. Natl. Acad. Sci. USA 68 (1971), 142–144, to countable families.
-/

namespace HajnalTransversal

open Set

variable {A : Type*} [LinearOrder A]

def OnePerColumn (X : Set (A × A)) : Prop :=
  X.InjOn Prod.snd

def DoubleLimit (Y : Set (A × A)) (μ : A) : Prop :=
  (Iio μ).Nonempty ∧ ∀ b < μ, ∃ c, b < c ∧ c < μ ∧
    ∀ a < μ, ∃ t, a < t ∧ t < μ ∧ (t, c) ∈ Y

def FreeFor (F : A × A → Set (A × A)) (X : Set (A × A)) : Prop :=
  ∀ ⦃p q⦄, p ∈ X → q ∈ X → p ∉ F q

private theorem finiteBound {μ b : A} (hb : b < μ) {s : Set A} (hs : s.Finite) :
    ∃ t, b ≤ t ∧ t < μ ∧ ∀ x ∈ s, x < μ → x ≤ t := by
  let S := insert b (s ∩ Iio μ)
  have hS : S.Finite := (hs.subset inter_subset_left).insert b
  obtain ⟨t, ht⟩ := hS.exists_maximal (show S.Nonempty from ⟨b, mem_insert _ _⟩)
  refine ⟨t, le_of_not_gt fun h => not_lt_of_ge (ht.2 (mem_insert _ _) h.le) h,
    ?_, fun x hx hxμ => le_of_not_gt fun h =>
      not_lt_of_ge (ht.2 (mem_insert_of_mem _ ⟨hx, hxμ⟩) h.le) h⟩
  rcases ht.1 with rfl | ht'
  · exact hb
  · exact ht'.2

omit [LinearOrder A] in
private theorem finiteForbidden {ι : Type*} [Finite ι] (F : A × A → Set (A × A))
    (hF : ∀ p, OnePerColumn (F p)) (q : ι → A × A) (c : A) :
    {t | ∃ i, (t, c) ∈ F (q i)}.Finite := by
  have h : ∀ i, ({t | (t, c) ∈ F (q i)} : Set A).Finite := by
    intro i
    apply Set.Subsingleton.finite
    intro x hx y hy
    exact congrArg Prod.fst (hF (q i) hx hy rfl)
  simpa only [← Set.ofPred_exists] using Set.finite_iUnion h

theorem restrict_doubleLimit (F : A × A → Set (A × A))
    (hF : ∀ p, OnePerColumn (F p)) {ι : Type*} [Finite ι] (q : ι → A × A)
    {Y : Set (A × A)} {b μ : A} (hY : DoubleLimit Y μ) (hb : b < μ) :
    DoubleLimit {p ∈ Y | b < p.1 ∧ b < p.2 ∧ ∀ i, p ∉ F (q i)} μ := by
  refine ⟨hY.1, fun u hu => ?_⟩
  obtain ⟨c, huc, hcμ, hcol⟩ := hY.2 (max u b) (max_lt hu hb)
  refine ⟨c, (le_max_left _ _).trans_lt huc, hcμ, fun a ha => ?_⟩
  obtain ⟨w, hwab, hwμ, hw⟩ := finiteBound (max_lt ha hb) (finiteForbidden F hF q c)
  obtain ⟨t, hwt, htμ, hty⟩ := hcol w hwμ
  refine ⟨t, (le_max_left _ _).trans hwab |>.trans_lt hwt, htμ, hty,
    (le_max_right _ _).trans hwab |>.trans_lt hwt, (le_max_right _ _).trans_lt huc, ?_⟩
  exact fun i ht => not_lt_of_ge (hw t ⟨i, ht⟩ htμ) hwt

theorem top_ladder (F : A × A → Set (A × A)) (hF : ∀ p, OnePerColumn (F p))
    {μ : A} (e : ℕ → A) (he : ∀ n, e n < μ) (Y : ℕ → Set (A × A))
    (hY : ∀ n, DoubleLimit (Y n) μ) :
    ∃ p : ℕ → A × A,
      (∀ n, p n ∈ Y n ∧ e n < (p n).2 ∧ (p n).2 < (p n).1 ∧ (p n).1 < μ) ∧
      StrictMono (fun n => (p n).2) ∧
      ∀ i j, i < j → p j ∉ F (p i) := by
  classical
  let Below := {p : A × A // p.2 < μ}
  let spec (n : ℕ) (prev : ∀ i < n, Below) (p : Below) : Prop :=
    p.1 ∈ Y n ∧ e n < p.1.2 ∧ p.1.2 < p.1.1 ∧ p.1.1 < μ ∧
      ∀ (i : ℕ) (hi : i < n), (prev i hi).1.2 < p.1.2 ∧ p.1 ∉ F (prev i hi).1
  have hpick (n : ℕ) (prev : ∀ i < n, Below) : ∃ p, spec n prev p := by
    let prevCol : Fin n → A := fun i => (prev i i.2).1.2
    obtain ⟨b, hen, hbμ, hb⟩ := finiteBound (he n) (Set.finite_range prevCol)
    let q : Fin n → A × A := fun i => (prev i i.2).1
    have hR := restrict_doubleLimit F hF q (hY n) hbμ
    obtain ⟨c, hbc, hcμ, hcol⟩ := hR.2 b hbμ
    obtain ⟨t, hct, htμ, htY, _, _, htF⟩ := hcol c hcμ
    refine ⟨⟨(t, c), hcμ⟩, htY, hen.trans_lt hbc, hct, htμ, fun i hi => ⟨?_, htF ⟨i, hi⟩⟩⟩
    exact (hb _ ⟨⟨i, hi⟩, rfl⟩ (prev i hi).2).trans_lt hbc
  let step (n : ℕ) (prev : ∀ i < n, Below) : Below := (hpick n prev).choose
  let p : ℕ → Below := Nat.lt_wfRel.wf.fix step
  have hp (n : ℕ) : spec n (fun i _ => p i) (p n) := by
    have h : p n = step n (fun i _ => p i) := WellFounded.fix_eq _ _ _
    rw [h]
    exact (hpick n (fun i _ => p i)).choose_spec
  exact ⟨fun n => (p n).1, fun n => ⟨(hp n).1, (hp n).2.1, (hp n).2.2.1, (hp n).2.2.2.1⟩,
    fun _ _ h => ((hp _).2.2.2.2 _ h).1, fun _ _ h => ((hp _).2.2.2.2 _ h).2⟩

private theorem doubleLimit_mono {Y Z : Set (A × A)} {μ : A} (h : DoubleLimit Y μ)
    (hYZ : Y ⊆ Z) : DoubleLimit Z μ := by
  refine ⟨h.1, fun b hb => ?_⟩
  obtain ⟨c, hbc, hcμ, hc⟩ := h.2 b hb
  refine ⟨c, hbc, hcμ, fun a ha => ?_⟩
  obtain ⟨t, hat, htμ, ht⟩ := hc a ha
  exact ⟨t, hat, htμ, hYZ ht⟩

private theorem restrict_finite (F : A × A → Set (A × A))
    (hF : ∀ p, OnePerColumn (F p)) {ι : Type*} [Finite ι] (q : ι → A × A)
    (f : ι → A) {Y : Set (A × A)} {μ : A} (hY : DoubleLimit Y μ) (hf : ∀ i, f i < μ) :
    DoubleLimit {p ∈ Y | ∀ i, f i < p.1 ∧ f i < p.2 ∧ p ∉ F (q i)} μ := by
  refine ⟨hY.1, fun u hu => ?_⟩
  obtain ⟨w, _, hwμ, hw⟩ := finiteBound hu (Set.finite_range f)
  have hR := restrict_doubleLimit F hF q hY hwμ
  have hsubset : {p ∈ Y | w < p.1 ∧ w < p.2 ∧ ∀ i, p ∉ F (q i)} ⊆
      {p ∈ Y | ∀ i, f i < p.1 ∧ f i < p.2 ∧ p ∉ F (q i)} := by
    rintro p ⟨hp, h1, h2, h3⟩
    exact ⟨hp, fun i => ⟨(hw _ ⟨i, rfl⟩ (hf i)).trans_lt h1,
      (hw _ ⟨i, rfl⟩ (hf i)).trans_lt h2, h3 i⟩⟩
  exact (doubleLimit_mono hR hsubset).2 u hu

omit [LinearOrder A] in
private theorem combine (F : A × A → Set (A × A)) {ι : Type*} (X : ι → Set (A × A))
    (hX : ∀ i, OnePerColumn (X i) ∧ FreeFor F (X i))
    (hCross : ∀ i j, i ≠ j → ∀ p ∈ X i, ∀ q ∈ X j, p.2 ≠ q.2 ∧ p ∉ F q) :
    OnePerColumn (⋃ i, X i) ∧ FreeFor F (⋃ i, X i) := by
  constructor
  · intro p hp q hq heq
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hp
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hq
    by_cases hij : i = j
    · subst j
      exact (hX i).1 hi hj heq
    · exact ((hCross i j hij p hi q hj).1 heq).elim
  · intro p q hp hq
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hp
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hq
    by_cases hij : i = j
    · subst j
      exact (hX i).2 hi hj
    · exact (hCross i j hij p hi q hj).2

universe v

theorem exists_transversal [WellFoundedLT A] (hCount : ∀ μ : A, (Iio μ).Countable)
    (F : A × A → Set (A × A)) (hF : ∀ p, OnePerColumn (F p))
    (hDir : ∀ p q, p ∈ F q → p.1 < q.1 ∧ q.2 < p.2) (μ : A) :
    ∀ {ι : Type v} [Countable ι] (Y : ι → Set (A × A)) (tag : ι → A),
      (∀ i, tag i ≤ μ) → (∀ i, DoubleLimit (Y i) (tag i)) →
      (∀ i, ∀ p ∈ Y i, p.1 < tag i ∧ p.2 < tag i) →
      ∃ X : Set (A × A), X ⊆ ⋃ i, Y i ∧ OnePerColumn X ∧ FreeFor F X ∧
        ∀ i, (X ∩ Y i).Nonempty := by
  classical
  induction μ using WellFounded.induction (wellFounded_lt (α := A)) with
  | h μ ih =>
    intro ι hι Y tag htag hY hBelow
    by_cases hNonempty : (Iio μ).Nonempty
    · by_cases hAbove : ∀ b < μ, ∃ c, b < c ∧ c < μ
      · let : Countable (Iio μ) := hCount μ
        let : Nonempty (Iio μ) := hNonempty.to_subtype
        obtain ⟨e, he⟩ := exists_surjective_nat (Iio μ)
        let T := {i : ι // tag i = μ}
        obtain ⟨enumerate, henumerate⟩ := exists_surjective_nat (Option T)
        let topDemand (n : ℕ) : Set (A × A) :=
          (enumerate n).elim Set.univ (fun i => Y i)
        have hTopDemand n : DoubleLimit (topDemand n) μ := by
          unfold topDemand
          cases enumerate n with
          | none =>
            refine ⟨hNonempty, fun b hb => ?_⟩
            obtain ⟨c, hbc, hcμ⟩ := hAbove b hb
            refine ⟨c, hbc, hcμ, fun a ha => ?_⟩
            obtain ⟨t, hat, htμ⟩ := hAbove a ha
            exact ⟨t, hat, htμ, Set.mem_univ _⟩
          | some i => simpa only [Option.elim_some, ← i.2] using hY i
        obtain ⟨p, hp, hpmono, hpavoid⟩ :=
          top_ladder F hF (fun n => (e n).1) (fun n => (e n).2) topDemand hTopDemand
        let f (n : ℕ) := (p n).2
        have hf n : f n < μ := (hp n).2.2.1.trans (hp n).2.2.2
        have hmono : StrictMono f := hpmono
        have hCover {t : A} (ht : t < μ) : ∃ n, t ≤ f n := by
          obtain ⟨n, hn⟩ := he ⟨t, ht⟩
          have hn' : (e n).1 = t := congrArg Subtype.val hn
          exact ⟨n, hn' ▸ (hp n).2.1.le⟩
        let gap (n : ℕ) := {i : ι // tag i ≤ f n ∧ ∀ k < n, f k < tag i}
        let gapDemand (n : ℕ) (i : gap n) : Set (A × A) :=
          {q ∈ Y i | ∀ k : Fin n, f k < q.1 ∧ f k < q.2 ∧ q ∉ F (p k)}
        have hGap (n : ℕ) := ih (f n) (hf n) (gapDemand n) (fun i => tag i)
          (fun i => i.2.1) (fun i => restrict_finite F hF (fun k : Fin n => p k)
            (fun k : Fin n => f k) (hY i) (fun k => i.2.2 k k.2))
          (fun i q hq => hBelow i q hq.1)
        choose X hXsub hXone hXfree hXhit using hGap
        have hXlow {n : ℕ} {q : A × A} (hq : q ∈ X n) :
            q.1 < f n ∧ q.2 < f n := by
          obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hXsub n hq)
          obtain ⟨h1, h2⟩ := hBelow i q hi.1
          exact ⟨h1.trans_le i.2.1, h2.trans_le i.2.1⟩
        have hXhigh {n k : ℕ} {q : A × A} (hq : q ∈ X n) (hkn : k < n) :
            f k < q.1 ∧ f k < q.2 ∧ q ∉ F (p k) := by
          obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hXsub n hq)
          exact hi.2 ⟨k, hkn⟩
        let part : Option ℕ → Set (A × A) := fun o => o.elim (Set.range p) X
        have hpart (o : Option ℕ) : OnePerColumn (part o) ∧ FreeFor F (part o) := by
          cases o with
          | none =>
            constructor
            · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hij
              exact congrArg p (hmono.injective hij)
            · rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩ hij
              have hji : f j < f i := (hDir _ _ hij).2
              exact hpavoid j i (hmono.lt_iff_lt.mp hji) hij
          | some n => exact ⟨hXone n, hXfree n⟩
        have hLadderGap {n k : ℕ} {q : A × A} (hq : q ∈ X n) :
            q.2 ≠ f k ∧ q ∉ F (p k) ∧ p k ∉ F q := by
          rcases lt_or_ge k n with hkn | hnk
          · obtain ⟨_, hc, havoid⟩ := hXhigh hq hkn
            exact ⟨hc.ne', havoid, fun h => hc.not_gt (hDir _ _ h).2⟩
          · obtain ⟨hh, hc⟩ := hXlow hq
            have hnk' : f n ≤ f k := hmono.monotone hnk
            exact ⟨(hc.trans_le hnk').ne, fun h => (hc.trans_le hnk').not_gt (hDir _ _ h).2,
              fun h => (hh.trans (hnk'.trans_lt (hp k).2.2.1)).not_gt (hDir _ _ h).1⟩
        have hcross (o o' : Option ℕ) (hne : o ≠ o') (q : A × A) (hq : q ∈ part o)
            (r : A × A) (hr : r ∈ part o') : q.2 ≠ r.2 ∧ q ∉ F r := by
          cases o with
          | none =>
            cases o' with
            | none => exact (hne rfl).elim
            | some n =>
              obtain ⟨k, rfl⟩ := hq
              exact ⟨(hLadderGap hr).1.symm, (hLadderGap hr).2.2⟩
          | some n =>
            cases o' with
            | none =>
              obtain ⟨k, rfl⟩ := hr
              exact ⟨(hLadderGap hq).1, (hLadderGap hq).2.1⟩
            | some m =>
              rcases lt_or_gt_of_ne (fun h => hne (congrArg some h)) with hnm | hmn
              · have hcols := (hXlow hq).2.trans (hXhigh hr hnm).2.1
                exact ⟨hcols.ne, fun h => hcols.not_gt (hDir _ _ h).2⟩
              · have hcols := (hXlow hr).2.trans (hXhigh hq hmn).2.1
                have hrows := (hXlow hr).1.trans (hXhigh hq hmn).1
                exact ⟨hcols.ne', fun h => hrows.not_gt (hDir _ _ h).1⟩
        let U := ⋃ o, part o
        let X' := U ∩ ⋃ i, Y i
        obtain ⟨hUone, hUfree⟩ := combine F part hpart hcross
        refine ⟨X', inter_subset_right, hUone.mono inter_subset_left,
          fun _ _ hq hr => hUfree hq.1 hr.1, fun i => ?_⟩
        rcases lt_or_eq_of_le (htag i) with hi | hi
        · let n := Nat.find (hCover hi)
          let j : gap n := ⟨i, Nat.find_spec (hCover hi), fun k hk =>
            lt_of_not_ge (fun h => not_le_of_gt hk (Nat.find_min' (hCover hi) h))⟩
          obtain ⟨q, hq, hqY⟩ := hXhit n j
          exact ⟨q, ⟨Set.mem_iUnion_of_mem (some n) hq, Set.mem_iUnion_of_mem i hqY.1⟩, hqY.1⟩
        · obtain ⟨n, hn⟩ := henumerate (some ⟨i, hi⟩)
          have hpi : p n ∈ Y i := by simpa only [topDemand, hn, Option.elim_some] using (hp n).1
          exact ⟨p n, ⟨Set.mem_iUnion_of_mem none ⟨n, rfl⟩, Set.mem_iUnion_of_mem i hpi⟩, hpi⟩
      · push Not at hAbove
        obtain ⟨b, hb, hmax⟩ := hAbove
        have hbound i : tag i ≤ b := by
          rcases lt_or_eq_of_le (htag i) with hlt | heq
          · exact le_of_not_gt fun h => hlt.not_ge (hmax _ h)
          · exact (hY i).2 b (heq.symm ▸ hb) |>.elim fun c ⟨hbc, hc, _⟩ =>
              ((show c < μ from heq ▸ hc).not_ge (hmax c hbc)).elim
        exact ih b hb Y tag hbound hY hBelow
    · refine ⟨∅, empty_subset _, Set.injOn_empty _, by simp [FreeFor], fun i => ?_⟩
      obtain ⟨a, ha⟩ := (hY i).1
      exact (hNonempty ⟨a, ha.trans_le (htag i)⟩).elim

theorem exists_graph [WellFoundedLT A] (hCount : ∀ μ : A, (Iio μ).Countable)
    {ι : Type v} (code : ι ↪ A) (Y : ι → Set (A × A)) (tag : ι → A)
    (hY : ∀ i, DoubleLimit (Y i) (tag i))
    (hBelow : ∀ i, ∀ p ∈ Y i, p.1 < tag i ∧ p.2 < tag i) :
    ∃ G : SimpleGraph (A × A),
      (∀ x y z, G.Adj x y → G.Adj y z → G.Adj z x → False) ∧
      ∀ i x, code i < x.1 → tag i ≤ x.1 → (∀ p ∈ Y i, x.2 < p.2) →
        ∃ p ∈ Y i, G.Adj x p := by
  classical
  let Active (x : A × A) :=
    {i : ι // code i < x.1 ∧ tag i ≤ x.1 ∧ ∀ p ∈ Y i, x.2 < p.2}
  let Directed (x y : A × A) := y.1 < x.1 ∧ x.2 < y.2
  let Local (x : A × A) :=
    {N : Set (A × A) // OnePerColumn N ∧ (∀ y ∈ N, Directed x y)}
  let wf : WellFounded (fun a b : A × A => a.1 < b.1) :=
    InvImage.wf Prod.fst wellFounded_lt
  let prior (x : A × A) (prev : ∀ y : A × A, y.1 < x.1 → Local y) (y : A × A) :
      Set (A × A) := if h : y.1 < x.1 then (prev y h).1 else ∅
  have hpick (x : A × A) (prev : ∀ y : A × A, y.1 < x.1 → Local y) :
      ∃ N : Local x, FreeFor (prior x prev) N.1 ∧
        ∀ i : Active x, (N.1 ∩ Y i).Nonempty := by
    have hOne y : OnePerColumn (prior x prev y) := by
      by_cases hy : y.1 < x.1
      · simpa only [prior, dif_pos hy] using (prev y hy).2.1
      · simpa only [OnePerColumn, prior, dif_neg hy] using Set.injOn_empty (Prod.snd : A × A → A)
    have hDir p q (hp : p ∈ prior x prev q) : Directed q p := by
      by_cases hq : q.1 < x.1
      · exact (prev q hq).2.2 p (by simpa only [prior, dif_pos hq] using hp)
      · simp [prior, hq] at hp
    let : Countable (Iio x.1) := hCount x.1
    let toIio (i : Active x) : Iio x.1 := ⟨code i, i.2.1⟩
    have hToIio : Function.Injective toIio := fun _ _ heq =>
      Subtype.ext (code.injective (congrArg Subtype.val heq))
    let : Countable (Active x) := hToIio.countable
    obtain ⟨N, hNsub, hNOne, hNFree, hNHit⟩ :=
      exists_transversal hCount (prior x prev) hOne hDir x.1
        (fun i : Active x => Y i) (fun i => tag i)
        (fun i => i.2.2.1) (fun i => hY i) (fun i => hBelow i)
    refine ⟨⟨N, hNOne, fun y hy => ?_⟩, hNFree, hNHit⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hNsub hy)
    exact ⟨(hBelow i y hi).1.trans_le i.2.2.1, i.2.2.2 y hi⟩
  let step (x : A × A) (prev : ∀ y : A × A, y.1 < x.1 → Local y) : Local x :=
    (hpick x prev).choose
  let N : ∀ x : A × A, Local x := wf.fix step
  have hspec (x : A × A) : FreeFor (prior x (fun y _ => N y)) (N x).1 ∧
      ∀ i : Active x, ((N x).1 ∩ Y i).Nonempty := by
    have h : N x = step x (fun y _ => N y) := WellFounded.fix_eq wf step x
    simpa only [h] using (hpick x (fun y _ => N y)).choose_spec
  have hfree (x y z : A × A) (hy : y ∈ (N x).1) (hz : z ∈ (N x).1) :
      y ∉ (N z).1 := by
    have hzx := ((N x).2.2 z hz).1
    simpa only [prior, dif_pos hzx] using (hspec x).1 hy hz
  let G : SimpleGraph (A × A) :=
    { Adj := fun x y => y ∈ (N x).1 ∨ x ∈ (N y).1
      symm := ⟨fun _ _ => Or.symm⟩
      loopless := ⟨fun x h => Or.elim h
        (fun hh => lt_irrefl _ ((N x).2.2 x hh).1)
        (fun hh => lt_irrefl _ ((N x).2.2 x hh).1)⟩ }
  have hmax (x y z : A × A) (hxy : G.Adj x y) (hxz : G.Adj x z) (hyz : G.Adj y z)
      (hy : y.1 ≤ x.1) (hz : z.1 ≤ x.1) : False := by
    have hy' : y ∈ (N x).1 := hxy.resolve_right fun h => hy.not_gt ((N y).2.2 x h).1
    have hz' : z ∈ (N x).1 := hxz.resolve_right fun h => hz.not_gt ((N z).2.2 x h).1
    exact hyz.elim (hfree x z y hz' hy') (hfree x y z hy' hz')
  refine ⟨G, fun x y z hxy hyz hzx => ?_, fun i x hi htag hcols => ?_⟩
  · by_cases hy : y.1 ≤ x.1
    · by_cases hz : z.1 ≤ x.1
      · exact hmax x y z hxy hzx.symm hyz hy hz
      · exact hmax z x y hzx hyz.symm hxy (le_of_not_ge hz) (hy.trans (le_of_not_ge hz))
    · by_cases hz : z.1 ≤ y.1
      · exact hmax y z x hyz hxy.symm hzx hz (le_of_not_ge hy)
      · exact hmax z x y hzx hyz.symm hxy ((le_of_not_ge hy).trans (le_of_not_ge hz))
          (le_of_not_ge hz)
  · obtain ⟨p, hpx, hpY⟩ := (hspec x).2 ⟨i, hi, htag, hcols⟩
    exact ⟨p, hpY, Or.inl hpx⟩

open scoped Cardinal

def Demand (A : Type*) [LinearOrder A] :=
  {d : A × Set (A × A) // d.2.Countable ∧ DoubleLimit d.2 d.1 ∧
    ∀ p ∈ d.2, p.1 < d.1 ∧ p.2 < d.1}

universe u w

theorem lift_CH (h : (Cardinal.continuum : Cardinal.{w}) = Cardinal.aleph (1 : Ordinal.{w})) :
    (Cardinal.continuum : Cardinal.{u}) = Cardinal.aleph (1 : Ordinal.{u}) := by
  apply (Cardinal.lift_injective :
    Function.Injective (Cardinal.lift.{w, u} : Cardinal.{u} → Cardinal.{max w u}))
  simpa only [Cardinal.lift_continuum, Cardinal.lift_aleph, Ordinal.lift_one] using
    congrArg (Cardinal.lift.{u, w}) h

theorem exists_code {A : Type u} [LinearOrder A] (hA : Cardinal.mk A = Cardinal.aleph (1 : Ordinal.{u}))
    (hCH : (Cardinal.continuum : Cardinal.{u}) = Cardinal.aleph (1 : Ordinal.{u})) :
    Nonempty (Demand A ↪ A) := by
  classical
  have hEnum (d : Demand A) : ∃ s : ℕ → A × A, Set.range s = d.1.2 := by
    obtain ⟨b, hb⟩ := d.2.2.1.1
    obtain ⟨c, _, _, hc⟩ := d.2.2.1.2 b hb
    obtain ⟨t, _, _, ht⟩ := hc b hb
    let : Countable d.1.2 := d.2.1
    let : Nonempty d.1.2 := ⟨⟨(t, c), ht⟩⟩
    obtain ⟨s, hs⟩ := exists_surjective_nat d.1.2
    refine ⟨fun n => (s n).1, Set.Subset.antisymm ?_ ?_⟩
    · rintro _ ⟨n, rfl⟩
      exact (s n).2
    · intro p hp
      obtain ⟨n, hn⟩ := hs ⟨p, hp⟩
      exact ⟨n, congrArg Subtype.val hn⟩
  choose seq hseq using hEnum
  let enc : Demand A ↪ A × (ℕ → A × A) :=
    { toFun := fun d => (d.1.1, seq d)
      inj' := by
        intro a b h
        change (a.1.1, seq a) = (b.1.1, seq b) at h
        have ht : a.1.1 = b.1.1 := congrArg (fun p : A × (ℕ → A × A) => p.1) h
        have hs : seq a = seq b := congrArg (fun p : A × (ℕ → A × A) => p.2) h
        exact Subtype.ext (Prod.ext ht ((hseq a).symm.trans
          ((congrArg Set.range hs).trans (hseq b)))) }
  have hA' : Cardinal.mk A = Cardinal.continuum := hA.trans hCH.symm
  have hInf : Cardinal.aleph0 ≤ (Cardinal.continuum : Cardinal.{u}) :=
    Cardinal.aleph0_le_continuum
  have hPair : Cardinal.mk (A × A) = Cardinal.continuum := by
    simp only [Cardinal.mk_prod, Cardinal.lift_id, hA', Cardinal.mul_eq_self hInf]
  have hSeq : Cardinal.mk (ℕ → A × A) = Cardinal.continuum := by
    simp [hPair, Cardinal.continuum_power_aleph0]
  have hFinal : Cardinal.mk (A × (ℕ → A × A)) = Cardinal.mk A := by
    simp only [Cardinal.mk_prod, Cardinal.lift_id, hA', hSeq, Cardinal.mul_eq_self hInf]
  obtain ⟨dec⟩ := (Cardinal.le_def _ _).mp hFinal.le
  exact ⟨enc.trans dec⟩

end HajnalTransversal

/-- Hajnal's CH construction in the ordinal Ramsey formulation. -/
theorem OMA.solution : type_of% @Erdos1169.erdos_1169.variants.hajnal_under_ch := by
  intro hCH
  have hcard : Cardinal.mk HajnalOrdinal.W = Cardinal.aleph (1 : Ordinal) := by
    rw [HajnalOrdinal.W, Cardinal.mk_toType, Ordinal.card_omega]
  obtain ⟨code⟩ := HajnalTransversal.exists_code hcard (HajnalTransversal.lift_CH hCH)
  obtain ⟨G, htri, hhit⟩ := HajnalTransversal.exists_graph
    HajnalOrdinal.countable_below code (fun d => d.val.2) (fun d => d.val.1)
    (fun d => d.property.2.1) (fun d => d.property.2.2)
  apply HajnalOrdinal.of_demand_graph G htri
  intro μ Y hcount hbounds hdouble
  let d : HajnalTransversal.Demand HajnalOrdinal.W :=
    ⟨(μ, Y), hcount, hdouble, hbounds⟩
  refine ⟨max (code d) μ, ?_⟩
  intro x hx hxcol
  exact hhit d x ((le_max_left _ _).trans_lt hx) ((le_max_right _ _).trans hx.le) hxcol