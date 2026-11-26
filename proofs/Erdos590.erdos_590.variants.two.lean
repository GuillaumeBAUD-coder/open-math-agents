import FormalConjectures.ErdosProblems.«590»

/-!
# Specker's Theorem (`ω^2 → (ω^2, 3)^2`, Erdős Problem 590)

Proof that `OrdinalCardinalRamsey (ω ^ 2) (ω ^ 2) 3` holds: transfer to `ℕ ×ₗ ℕ`, thin each
`ω`-block to a red clique via `ω → (ω, 3)^2`, and use `Filter.hyperfilter ℕ` to either
extract a red `ω^2` inside a blue neighborhood / ultrafilter-blue family or recursively build
a red `ω^2` across an independent sequence of blocks in the triangle-free block graph.
-/

-- Problem: Erdős Problem 590 — two
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/590.lean:52 (declaration Erdos590.erdos_590.variants.two)
-- Credit: @TheWaler (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Cardinal Ordinal Filter Set

open scoped Classical

private lemma exists_strictMono_of_infinite {S : Set ℕ} (hS : S.Infinite) :
    ∃ g : ℕ → ℕ, StrictMono g ∧ ∀ n, g n ∈ S := by
  refine ⟨Nat.nth (· ∈ S), Nat.nth_strictMono hS, fun n => Nat.nth_mem_of_infinite hS n⟩

private lemma exists_strictMono_indep_of_triangleFree (G : SimpleGraph ℕ)
    (htf : ∀ x y z, ¬ (G.Adj x y ∧ G.Adj y z ∧ G.Adj x z)) :
    ∃ g : ℕ → ℕ, StrictMono g ∧ ∀ i j, i ≠ j → ¬ G.Adj (g i) (g j) := by
  by_cases hinf : ∃ v : ℕ, {w : ℕ | G.Adj v w}.Infinite
  · obtain ⟨v, hv⟩ := hinf
    obtain ⟨g, hg_mono, hg_mem⟩ := exists_strictMono_of_infinite hv
    refine ⟨g, hg_mono, fun i j _ hadj => ?_⟩
    exact htf v (g i) (g j) ⟨hg_mem i, hadj, hg_mem j⟩
  · push Not at hinf
    have hstep : ∀ (k : ℕ) (f : Fin k → ℕ),
        ∃ m : ℕ, (∀ i : Fin k, f i < m) ∧ (∀ i : Fin k, ¬ G.Adj (f i) m) := by
      intro k f
      let S : Set ℕ := (⋃ i : Fin k, {w : ℕ | w ≤ f i} ∪ {w : ℕ | G.Adj (f i) w})
      have hSfin : S.Finite := by
        refine Set.finite_iUnion fun i => ?_
        exact (Set.finite_le_nat (f i)).union (hinf (f i))
      obtain ⟨m, _, hm⟩ := (Set.infinite_univ.sdiff hSfin).nonempty
      refine ⟨m, fun i => ?_, fun i hadj => ?_⟩
      · by_contra hle
        exact hm (Set.mem_iUnion.mpr ⟨i, Or.inl (Nat.le_of_not_lt hle)⟩)
      · exact hm (Set.mem_iUnion.mpr ⟨i, Or.inr hadj⟩)
    let build : ∀ k : ℕ, {f : Fin k → ℕ //
        (∀ i j : Fin k, i < j → f i < f j) ∧ (∀ i j : Fin k, i ≠ j → ¬ G.Adj (f i) (f j))} :=
      Nat.rec ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0⟩ fun k prev =>
        let m := Classical.choose (hstep k prev.1)
        let hm := Classical.choose_spec (hstep k prev.1)
        ⟨Fin.snoc prev.1 m,
          by
            intro i j
            refine Fin.lastCases ?_ (fun j' => ?_) j
            · refine Fin.lastCases ?_ (fun i' => ?_) i
              · intro hij; exact (lt_irrefl _ hij).elim
              · intro _
                simp only [Fin.snoc_last, Fin.snoc_castSucc]
                exact hm.1 i'
            · refine Fin.lastCases ?_ (fun i' => ?_) i
              · intro hij; exact (not_lt_of_ge (Fin.le_last _) hij).elim
              · intro hij
                simp only [Fin.snoc_castSucc]
                exact prev.2.1 i' j' (Fin.castSucc_lt_castSucc_iff.mp hij),
          by
            intro i j
            refine Fin.lastCases ?_ (fun j' => ?_) j
            · refine Fin.lastCases ?_ (fun i' => ?_) i
              · intro hij; exact (hij rfl).elim
              · intro _
                simp only [Fin.snoc_last, Fin.snoc_castSucc]
                exact hm.2 i'
            · refine Fin.lastCases ?_ (fun i' => ?_) i
              · intro _
                simp only [Fin.snoc_last, Fin.snoc_castSucc]
                exact fun h => hm.2 j' h.symm
              · intro hij
                simp only [Fin.snoc_castSucc]
                exact prev.2.2 i' j' (fun h => hij (congrArg Fin.castSucc h))⟩
    have hagree : ∀ (k : ℕ) (i : Fin k), (build (k + 1)).1 i.castSucc = (build k).1 i := by
      intro k i
      dsimp only [build]
      exact Fin.snoc_castSucc _ _ i
    have hagree_le : ∀ {k₁ k₂ : ℕ} (h : k₁ ≤ k₂) (i : Fin k₁),
        (build k₂).1 (Fin.castLE h i) = (build k₁).1 i := by
      intro k₁ k₂ h
      induction k₂, h using Nat.le_induction with
      | base => intro i; rfl
      | succ k₂ h ih =>
        intro i
        exact (hagree k₂ (Fin.castLE h i)).trans (ih i)
    let g : ℕ → ℕ := fun n => (build (n + 1)).1 (Fin.last n)
    refine ⟨g, ?_, ?_⟩
    · intro i j hij
      have hi : g i = (build (j + 1)).1 ⟨i, by omega⟩ :=
        (hagree_le (by omega : i + 1 ≤ j + 1) (Fin.last i)).symm
      rw [hi]
      exact (build (j + 1)).2.1 ⟨i, by omega⟩ (Fin.last j) (Fin.mk_lt_mk.mpr hij)
    · intro i j hij
      let k := max i j + 1
      have hi : g i = (build k).1 ⟨i, by omega⟩ :=
        (hagree_le (by omega : i + 1 ≤ k) (Fin.last i)).symm
      have hj : g j = (build k).1 ⟨j, by omega⟩ :=
        (hagree_le (by omega : j + 1 ≤ k) (Fin.last j)).symm
      rw [hi, hj]
      exact (build k).2.2 ⟨i, by omega⟩ ⟨j, by omega⟩ (fun h => hij (congrArg Fin.val h))

private structure Grid {V : Type*} (R : SimpleGraph V) (UB : V → ℕ → Prop)
    (M : ℕ → ℕ) (v : ℕ → ℕ → V) (U : Ultrafilter ℕ) (k : ℕ) (len : ℕ → ℕ) where
  r : ℕ → ℕ
  J : ℕ → ℕ → ℕ
  r_mono : ∀ a b, a < b → b < k → r a < r b
  J_mono : ∀ a, a < k → ∀ c₁ c₂, c₁ < c₂ → c₂ < len a → J a c₁ < J a c₂
  back_good : ∀ a b, a < b → b < k → {j : ℕ | ¬ UB (v (M (r b)) j) (M (r a))} ∈ U
  not_UB : ∀ a b c, a < k → b < k → a ≠ b → c < len a →
    ¬ UB (v (M (r a)) (J a c)) (M (r b))
  red_clique : ∀ a₁ c₁ a₂ c₂, a₁ < k → c₁ < len a₁ → a₂ < k → c₂ < len a₂ →
    (a₁, c₁) ≠ (a₂, c₂) → R.Adj (v (M (r a₁)) (J a₁ c₁)) (v (M (r a₂)) (J a₂ c₂))

private def Grid.castLen {V : Type*} {R : SimpleGraph V} {UB : V → ℕ → Prop}
    {M : ℕ → ℕ} {v : ℕ → ℕ → V} {U : Ultrafilter ℕ} {k : ℕ} {len₁ len₂ : ℕ → ℕ}
    (h : ∀ a < k, len₁ a = len₂ a) (G : Grid R UB M v U k len₁) : Grid R UB M v U k len₂ where
  r := G.r
  J := G.J
  r_mono := G.r_mono
  J_mono := fun a ha c₁ c₂ hc₁₂ hc₂ => G.J_mono a ha c₁ c₂ hc₁₂ (h a ha ▸ hc₂)
  back_good := G.back_good
  not_UB := fun a b c ha hb hab hc => G.not_UB a b c ha hb hab (h a ha ▸ hc)
  red_clique := fun a₁ c₁ a₂ c₂ ha₁ hc₁ ha₂ hc₂ hne =>
    G.red_clique a₁ c₁ a₂ c₂ ha₁ (h a₁ ha₁ ▸ hc₁) ha₂ (h a₂ ha₂ ▸ hc₂) hne

private lemma specker_lex_nat (R B : SimpleGraph (ℕ ×ₗ ℕ)) (hcomp : IsCompl R B)
    (htf : ∀ x y z, ¬ (B.Adj x y ∧ B.Adj y z ∧ B.Adj x z)) :
    ∃ f : ℕ ×ₗ ℕ → ℕ ×ₗ ℕ, StrictMono f ∧ ∀ p q, p ≠ q → R.Adj (f p) (f q) := by
  have hRB : ∀ x y, x ≠ y → ¬ B.Adj x y → R.Adj x y := by
    intro x y hne hnb
    have htop : (R ⊔ B).Adj x y := by
      rw [hcomp.codisjoint.eq_top]
      exact hne
    exact htop.resolve_right hnb
  -- Step 1: thin each block `{m} × ℕ` to an infinite red clique
  have hblock : ∀ m : ℕ, ∃ b : ℕ → ℕ, StrictMono b ∧
      ∀ i j, i ≠ j → R.Adj (toLex (m, b i)) (toLex (m, b j)) := by
    intro m
    let Gm : SimpleGraph ℕ :=
      { Adj := fun i j => B.Adj (toLex (m, i)) (toLex (m, j))
        symm := ⟨fun _ _ h => h.symm⟩
        loopless := ⟨fun _ h => B.loopless.irrefl _ h⟩ }
    have hGtf : ∀ x y z, ¬ (Gm.Adj x y ∧ Gm.Adj y z ∧ Gm.Adj x z) :=
      fun x y z h => htf _ _ _ h
    obtain ⟨b, hb_mono, hb_indep⟩ := exists_strictMono_indep_of_triangleFree Gm hGtf
    refine ⟨b, hb_mono, fun i j hij => hRB _ _ (fun h => hij (hb_mono.injective (by
      have := congrArg (fun p => (ofLex p).2) h
      exact this))) (hb_indep i j hij)⟩
  let b : ℕ → ℕ → ℕ := fun m => Classical.choose (hblock m)
  have hb_mono : ∀ m, StrictMono (b m) := fun m => (Classical.choose_spec (hblock m)).1
  have hb_red : ∀ m i j, i ≠ j → R.Adj (toLex (m, b m i)) (toLex (m, b m j)) :=
    fun m => (Classical.choose_spec (hblock m)).2
  let v : ℕ → ℕ → ℕ ×ₗ ℕ := fun m i => toLex (m, b m i)
  have hv_mono : ∀ m₁ i₁ m₂ i₂, toLex (m₁, i₁) < toLex (m₂, i₂) → v m₁ i₁ < v m₂ i₂ := by
    intro m₁ i₁ m₂ i₂ h
    rw [Prod.Lex.lt_iff] at h ⊢
    rcases h with hlt | ⟨heq, hlt⟩
    · exact Or.inl hlt
    · exact Or.inr ⟨heq, by subst heq; exact hb_mono m₁ hlt⟩
  have hv_inj_i : ∀ m, Function.Injective (v m) := fun m i₁ i₂ h =>
    (hb_mono m).injective (congrArg (fun p => (ofLex p).2) h)
  -- Step 2: fix the nonprincipal ultrafilter `U = hyperfilter ℕ`
  let U : Ultrafilter ℕ := Filter.hyperfilter ℕ
  have hU_inf : ∀ {s : Set ℕ}, s ∈ U → s.Infinite := fun hs hfin =>
    hfin.notMem_hyperfilter hs
  have hU_compl_fin : ∀ {s : Set ℕ}, s.Finite → sᶜ ∈ U := fun hfin =>
    hfin.compl_mem_hyperfilter
  let UB : (ℕ ×ₗ ℕ) → ℕ → Prop := fun y m => {i : ℕ | B.Adj y (v m i)} ∈ U
  have hnotUB_red : ∀ y m, ¬ UB y m → {i : ℕ | R.Adj y (v m i)} ∈ U := by
    intro y m hnot
    have hc : {i : ℕ | ¬ B.Adj y (v m i)} ∈ U := Ultrafilter.compl_mem_iff_notMem.mpr hnot
    have hneq_fin : {i : ℕ | y = v m i}.Finite :=
      Set.Subsingleton.finite (fun i₁ hi₁ i₂ hi₂ => hv_inj_i m (hi₁.symm.trans hi₂))
    have hneq : {i : ℕ | y ≠ v m i} ∈ U := hU_compl_fin hneq_fin
    refine Filter.mem_of_superset (Filter.inter_mem hc hneq) ?_
    intro i ⟨hnb, hne⟩
    exact hRB y (v m i) hne hnb
  have hUB_red : ∀ y₁ y₂ m, y₁ ≠ y₂ → UB y₁ m → UB y₂ m → R.Adj y₁ y₂ := by
    intro y₁ y₂ m hne h1 h2
    have hinter : ({i : ℕ | B.Adj y₁ (v m i)} ∩ {i : ℕ | B.Adj y₂ (v m i)}) ∈ U :=
      Filter.inter_mem h1 h2
    obtain ⟨i, hi1, hi2⟩ := (hU_inf hinter).nonempty
    exact hRB y₁ y₂ hne (fun hb => htf y₁ y₂ (v m i) ⟨hb, hi2, hi1⟩)
  -- Case 0: some vertex `y` has infinitely many blocks with infinitely many blue neighbors
  by_cases hcase0 : ∃ y : ℕ ×ₗ ℕ, {k : ℕ | {i : ℕ | B.Adj y (v k i)}.Infinite}.Infinite
  · obtain ⟨y, hy⟩ := hcase0
    obtain ⟨K, hK_mono, hK_mem⟩ := exists_strictMono_of_infinite hy
    let J : ℕ → ℕ → ℕ := fun a => Classical.choose (exists_strictMono_of_infinite (hK_mem a))
    have hJ_mono : ∀ a, StrictMono (J a) :=
      fun a => (Classical.choose_spec (exists_strictMono_of_infinite (hK_mem a))).1
    have hJ_mem : ∀ a c, B.Adj y (v (K a) (J a c)) :=
      fun a => (Classical.choose_spec (exists_strictMono_of_infinite (hK_mem a))).2
    let f : ℕ ×ₗ ℕ → ℕ ×ₗ ℕ := fun p => v (K (ofLex p).1) (J (ofLex p).1 (ofLex p).2)
    have hf_mono : StrictMono f := by
      intro p q hpq
      refine hv_mono _ _ _ _ ?_
      rw [Prod.Lex.lt_iff] at hpq ⊢
      rcases hpq with hlt | ⟨heq, hlt⟩
      · exact Or.inl (hK_mono hlt)
      · exact Or.inr ⟨congrArg K heq, by rw [heq]; exact hJ_mono _ hlt⟩
    refine ⟨f, hf_mono, fun p q hpq => ?_⟩
    exact hRB (f p) (f q) (hf_mono.injective.ne hpq)
      (fun hb => htf y (f p) (f q) ⟨hJ_mem _ _, hb, hJ_mem _ _⟩)
  -- Not Case 0: for every `y`, `{k | UB y k}` is finite
  push Not at hcase0
  have hUB_fin : ∀ y : ℕ ×ₗ ℕ, {k : ℕ | UB y k}.Finite := by
    intro y
    exact (hcase0 y).subset fun k hk => hU_inf hk
  -- Case A: some block `m` has infinitely many blocks `k` with `S m k = {j | UB (v k j) m}` infinite
  let S : ℕ → ℕ → Set ℕ := fun m k => {j : ℕ | UB (v k j) m}
  by_cases hcaseA : ∃ m : ℕ, {k : ℕ | (S m k).Infinite}.Infinite
  · obtain ⟨m, hm⟩ := hcaseA
    obtain ⟨K, hK_mono, hK_mem⟩ := exists_strictMono_of_infinite hm
    let J : ℕ → ℕ → ℕ := fun a => Classical.choose (exists_strictMono_of_infinite (hK_mem a))
    have hJ_mono : ∀ a, StrictMono (J a) :=
      fun a => (Classical.choose_spec (exists_strictMono_of_infinite (hK_mem a))).1
    have hJ_mem : ∀ a c, UB (v (K a) (J a c)) m :=
      fun a => (Classical.choose_spec (exists_strictMono_of_infinite (hK_mem a))).2
    let f : ℕ ×ₗ ℕ → ℕ ×ₗ ℕ := fun p => v (K (ofLex p).1) (J (ofLex p).1 (ofLex p).2)
    have hf_mono : StrictMono f := by
      intro p q hpq
      refine hv_mono _ _ _ _ ?_
      rw [Prod.Lex.lt_iff] at hpq ⊢
      rcases hpq with hlt | ⟨heq, hlt⟩
      · exact Or.inl (hK_mono hlt)
      · exact Or.inr ⟨congrArg K heq, by rw [heq]; exact hJ_mono _ hlt⟩
    refine ⟨f, hf_mono, fun p q hpq => ?_⟩
    exact hUB_red (f p) (f q) m (hf_mono.injective.ne hpq) (hJ_mem _ _) (hJ_mem _ _)
  -- Case B: not Case 0 and not Case A
  push Not at hcaseA
  -- Define the triangle-free block graph `H`
  let H : SimpleGraph ℕ :=
    { Adj := fun m k =>
        (m < k ∧ {i : ℕ | UB (v m i) k} ∈ U) ∨ (k < m ∧ {i : ℕ | UB (v k i) m} ∈ U)
      symm := ⟨fun _ _ h => h.symm⟩
      loopless := ⟨fun _ h => by rcases h with ⟨h, _⟩ | ⟨h, _⟩ <;> exact lt_irrefl _ h⟩ }
  have hH_tri_ord : ∀ a b c : ℕ, a < b → b < c →
      ¬ (H.Adj a b ∧ H.Adj b c ∧ H.Adj a c) := by
    rintro a b c hab hbc ⟨h1, h2, h3⟩
    have h1' : {i : ℕ | UB (v a i) b} ∈ U :=
      h1.elim And.right (fun h => (lt_asymm hab h.1).elim)
    have h2' : {j : ℕ | UB (v b j) c} ∈ U :=
      h2.elim And.right (fun h => (lt_asymm hbc h.1).elim)
    have h3' : {i : ℕ | UB (v a i) c} ∈ U :=
      h3.elim And.right (fun h => (lt_asymm (hab.trans hbc) h.1).elim)
    obtain ⟨i, hi_b, hi_c⟩ := (hU_inf (Filter.inter_mem h1' h3')).nonempty
    obtain ⟨j, hj_ab, hj_c⟩ := (hU_inf (Filter.inter_mem hi_b h2')).nonempty
    obtain ⟨t, ht_ac, ht_bc⟩ := (hU_inf (Filter.inter_mem hi_c hj_c)).nonempty
    exact htf (v a i) (v b j) (v c t) ⟨hj_ab, ht_bc, ht_ac⟩
  have hH_tf : ∀ x y z, ¬ (H.Adj x y ∧ H.Adj y z ∧ H.Adj x z) := by
    intro x y z ⟨hxy, hyz, hxz⟩
    have hne_xy : x ≠ y := H.ne_of_adj hxy
    have hne_yz : y ≠ z := H.ne_of_adj hyz
    have hne_xz : x ≠ z := H.ne_of_adj hxz
    rcases lt_or_gt_of_ne hne_xy with hxy' | hxy' <;>
    rcases lt_or_gt_of_ne hne_yz with hyz' | hyz' <;>
    rcases lt_or_gt_of_ne hne_xz with hxz' | hxz'
    · exact hH_tri_ord x y z hxy' hyz' ⟨hxy, hyz, hxz⟩
    · exact lt_asymm (hxy'.trans hyz') hxz'
    · exact hH_tri_ord x z y hxz' hyz' ⟨hxz, hyz.symm, hxy⟩
    · exact hH_tri_ord z x y hxz' hxy' ⟨hxz.symm, hxy, hyz.symm⟩
    · exact hH_tri_ord y x z hxy' hxz' ⟨hxy.symm, hxz, hyz⟩
    · exact hH_tri_ord y z x hyz' hxz' ⟨hyz, hxz.symm, hxy.symm⟩
    · exact lt_asymm (hyz'.trans hxy') hxz'
    · exact hH_tri_ord z y x hyz' hxy' ⟨hyz.symm, hxy.symm, hxz.symm⟩
  obtain ⟨M, hM_mono, hM_indep⟩ := exists_strictMono_indep_of_triangleFree H hH_tf
  have hM_fwd : ∀ p q, p < q → {i : ℕ | ¬ UB (v (M p) i) (M q)} ∈ U := by
    intro p q hpq
    have hnot : ¬ H.Adj (M p) (M q) := hM_indep p q (ne_of_lt hpq)
    have hnot_mem : {i : ℕ | UB (v (M p) i) (M q)} ∉ U := fun hm =>
      hnot (Or.inl ⟨hM_mono hpq, hm⟩)
    exact Ultrafilter.compl_mem_iff_notMem.mpr hnot_mem
  -- Helper 1: add one new block to `Grid s (fun _ => s)`
  have addBlock : ∀ (s : ℕ) (G : Grid R UB M v U s (fun _ => s)),
      {G' : Grid R UB M v U (s + 1) (fun a => if a < s then s else 0) //
        (∀ a < s, G'.r a = G.r a) ∧ G'.J = G.J} := by
    intro s G
    let bad : Set ℕ :=
      (⋃ a : Fin s, {r' : ℕ | r' ≤ G.r a.1}) ∪
      (⋃ a : Fin s, {r' : ℕ | (S (M (G.r a.1)) (M r')).Infinite}) ∪
      (⋃ p : Fin s × Fin s, {r' : ℕ | UB (v (M (G.r p.1.1)) (G.J p.1.1 p.2.1)) (M r')})
    have hbad_fin : bad.Finite := by
      refine ((Set.finite_iUnion fun a : Fin s => Set.finite_le_nat (G.r a.1)).union
        (Set.finite_iUnion fun a : Fin s =>
          show (M ⁻¹' {k | (S (M (G.r a.1)) k).Infinite}).Finite from
            (hcaseA (M (G.r a.1))).preimage hM_mono.injective.injOn)).union
        (Set.finite_iUnion fun p : Fin s × Fin s =>
          show (M ⁻¹' {k | UB (v (M (G.r p.1.1)) (G.J p.1.1 p.2.1)) k}).Finite from
            (hUB_fin (v (M (G.r p.1.1)) (G.J p.1.1 p.2.1))).preimage hM_mono.injective.injOn)
    let r_new : ℕ := Classical.choose (Set.infinite_univ.sdiff hbad_fin).nonempty
    have hr_new : r_new ∉ bad := (Classical.choose_spec (Set.infinite_univ.sdiff hbad_fin).nonempty).2
    refine ⟨
      { r := Function.update G.r s r_new
        J := G.J
        r_mono := by
          intro a b hab hbs
          by_cases hb : b < s
          · have ha : a < s := hab.trans hb
            simp only [Function.update_of_ne (ne_of_lt ha), Function.update_of_ne (ne_of_lt hb)]
            exact G.r_mono a b hab hb
          · have hb_eq : b = s := by omega
            have ha : a < s := by omega
            rw [hb_eq]
            simp only [Function.update_self, Function.update_of_ne (ne_of_lt ha)]
            by_contra hle
            exact hr_new (Or.inl (Or.inl (Set.mem_iUnion.mpr ⟨⟨a, ha⟩, Nat.le_of_not_lt hle⟩)))
        J_mono := by
          intro a ha c₁ c₂ hc₁₂ hc₂
          by_cases has : a < s
          · simp only [if_pos has] at hc₂
            exact G.J_mono a has c₁ c₂ hc₁₂ hc₂
          · simp only [if_neg has] at hc₂
            omega
        back_good := by
          intro a b hab hbs
          by_cases hb : b < s
          · have ha : a < s := hab.trans hb
            simp only [Function.update_of_ne (ne_of_lt ha), Function.update_of_ne (ne_of_lt hb)]
            exact G.back_good a b hab hb
          · have hb_eq : b = s := by omega
            have ha : a < s := by omega
            rw [hb_eq]
            simp only [Function.update_self, Function.update_of_ne (ne_of_lt ha)]
            have hfin : (S (M (G.r a)) (M r_new)).Finite := by
              by_contra hinfS
              exact hr_new (Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨⟨a, ha⟩, hinfS⟩)))
            exact hU_compl_fin hfin
        not_UB := by
          intro a b c ha hb hab hc
          have has : a < s := by
            by_contra hna
            simp only [if_neg hna] at hc
            omega
          simp only [if_pos has] at hc
          simp only [Function.update_of_ne (ne_of_lt has)]
          by_cases hbs : b < s
          · simp only [Function.update_of_ne (ne_of_lt hbs)]
            exact G.not_UB a b c has hbs hab hc
          · have hb_eq : b = s := by omega
            subst hb_eq
            simp only [Function.update_self]
            intro hub
            exact hr_new (Or.inr (Set.mem_iUnion.mpr ⟨(⟨a, has⟩, ⟨c, hc⟩), hub⟩))
        red_clique := by
          intro a₁ c₁ a₂ c₂ ha₁ hc₁ ha₂ hc₂ hne
          have ha₁s : a₁ < s := by by_contra h; simp only [if_neg h] at hc₁; omega
          have ha₂s : a₂ < s := by by_contra h; simp only [if_neg h] at hc₂; omega
          simp only [if_pos ha₁s] at hc₁
          simp only [if_pos ha₂s] at hc₂
          simp only [Function.update_of_ne (ne_of_lt ha₁s), Function.update_of_ne (ne_of_lt ha₂s)]
          exact G.red_clique a₁ c₁ a₂ c₂ ha₁s hc₁ ha₂s hc₂ hne },
      fun a ha => Function.update_of_ne (ne_of_lt ha) _ _,
      rfl⟩
  -- Helper 2: add one new vertex to block `a₀ < k` in `Grid k len`
  have addVertex : ∀ {k : ℕ} {len : ℕ → ℕ} (G : Grid R UB M v U k len) (a₀ : ℕ) (ha₀ : a₀ < k),
      {G' : Grid R UB M v U k (Function.update len a₀ (len a₀ + 1)) //
        G'.r = G.r ∧ ∀ a c, a < k → c < len a → G'.J a c = G.J a c} := by
    intro k len G a₀ ha₀
    let S1 : Set ℕ := ⋂ c : Fin (len a₀), {i : ℕ | G.J a₀ c.1 < i}
    have hS1 : S1 ∈ U := Filter.iInter_mem.mpr fun c =>
      Filter.mem_of_superset (hU_compl_fin (Set.finite_le_nat (G.J a₀ c.1)))
        (fun _ hi => Nat.lt_of_not_ge hi)
    let S2 : Set ℕ := ⋂ b : {b : Fin k // b.1 ≠ a₀},
      ⋂ c : Fin (len b.1.1), {i : ℕ | R.Adj (v (M (G.r b.1.1)) (G.J b.1.1 c.1)) (v (M (G.r a₀)) i)}
    have hS2 : S2 ∈ U := Filter.iInter_mem.mpr fun b => Filter.iInter_mem.mpr fun c =>
      hnotUB_red _ _ (G.not_UB b.1.1 a₀ c.1 b.1.2 ha₀ b.2 c.2)
    let S3 : Set ℕ := ⋂ b : {b : Fin k // b.1 ≠ a₀},
      {i : ℕ | ¬ UB (v (M (G.r a₀)) i) (M (G.r b.1.1))}
    have hS3 : S3 ∈ U := Filter.iInter_mem.mpr fun b => by
      rcases lt_or_gt_of_ne b.2 with hba | hab
      · exact G.back_good b.1.1 a₀ hba ha₀
      · exact hM_fwd (G.r a₀) (G.r b.1.1) (G.r_mono a₀ b.1.1 hab b.1.2)
    have hgood : (S1 ∩ S2 ∩ S3) ∈ U := Filter.inter_mem (Filter.inter_mem hS1 hS2) hS3
    let i_new : ℕ := Classical.choose (hU_inf hgood).nonempty
    have hi_spec := Classical.choose_spec (hU_inf hgood).nonempty
    have hi1 : ∀ c < len a₀, G.J a₀ c < i_new := fun c hc =>
      (Set.mem_iInter.mp hi_spec.1.1 ⟨c, hc⟩)
    have hi2 : ∀ b < k, b ≠ a₀ → ∀ c < len b,
        R.Adj (v (M (G.r b)) (G.J b c)) (v (M (G.r a₀)) i_new) := fun b hb hne c hc =>
      Set.mem_iInter.mp (Set.mem_iInter.mp hi_spec.1.2 ⟨⟨b, hb⟩, hne⟩) ⟨c, hc⟩
    have hi3 : ∀ b < k, b ≠ a₀ → ¬ UB (v (M (G.r a₀)) i_new) (M (G.r b)) := fun b hb hne =>
      Set.mem_iInter.mp hi_spec.2 ⟨⟨b, hb⟩, hne⟩
    let J' : ℕ → ℕ → ℕ := fun a c =>
      if a = a₀ ∧ c = len a₀ then i_new else G.J a c
    refine ⟨
      { r := G.r
        J := J'
        r_mono := G.r_mono
        J_mono := by
          intro a ha c₁ c₂ hc₁₂ hc₂
          by_cases ha_eq : a = a₀
          · subst ha_eq
            simp only [Function.update_self] at hc₂
            have hc₁ : c₁ < len a := by omega
            have h1 : J' a c₁ = G.J a c₁ := by simp [J', ne_of_lt hc₁]
            rw [h1]
            by_cases hc₂_eq : c₂ = len a
            · subst hc₂_eq
              simp only [J', and_self, ↓reduceIte]
              exact hi1 c₁ hc₁
            · have hc₂' : c₂ < len a := by omega
              simp only [J', hc₂_eq, and_false, ↓reduceIte]
              exact G.J_mono a ha c₁ c₂ hc₁₂ hc₂'
          · simp only [Function.update_of_ne ha_eq] at hc₂
            simp only [J', ha_eq, false_and, ↓reduceIte]
            exact G.J_mono a ha c₁ c₂ hc₁₂ hc₂
        back_good := G.back_good
        not_UB := by
          intro a b c ha hb hab hc
          by_cases hnew : a = a₀ ∧ c = len a₀
          · rcases hnew with ⟨rfl, rfl⟩
            simp only [J', and_self, ↓reduceIte]
            exact hi3 b hb hab.symm
          · simp only [J', hnew, ↓reduceIte]
            have hc' : c < len a := by
              by_cases ha_eq : a = a₀
              · subst ha_eq
                simp only [Function.update_self] at hc
                have : c ≠ len a := fun h => hnew ⟨rfl, h⟩
                omega
              · simp only [Function.update_of_ne ha_eq] at hc
                exact hc
            exact G.not_UB a b c ha hb hab hc'
        red_clique := by
          intro a₁ c₁ a₂ c₂ ha₁ hc₁ ha₂ hc₂ hne
          by_cases h1 : a₁ = a₀ ∧ c₁ = len a₀
          · rcases h1 with ⟨rfl, rfl⟩
            simp only [J', and_self, ↓reduceIte]
            have h2 : ¬ (a₂ = a₁ ∧ c₂ = len a₁) := fun ⟨h, h'⟩ => hne (by subst h; subst h'; rfl)
            simp only [h2, ↓reduceIte]
            by_cases ha2 : a₂ = a₁
            · subst ha2
              simp only [Function.update_self] at hc₂
              have hc₂' : c₂ < len a₂ := by
                have : c₂ ≠ len a₂ := fun h => h2 ⟨rfl, h⟩
                omega
              exact hb_red (M (G.r a₂)) i_new (G.J a₂ c₂) (ne_of_gt (hi1 c₂ hc₂'))
            · simp only [Function.update_of_ne ha2] at hc₂
              exact (hi2 a₂ ha₂ ha2 c₂ hc₂).symm
          · simp only [J', h1, ↓reduceIte]
            have hc₁' : c₁ < len a₁ := by
              by_cases ha1 : a₁ = a₀
              · subst ha1
                simp only [Function.update_self] at hc₁
                have : c₁ ≠ len a₁ := fun h => h1 ⟨rfl, h⟩
                omega
              · simp only [Function.update_of_ne ha1] at hc₁
                exact hc₁
            by_cases h2 : a₂ = a₀ ∧ c₂ = len a₀
            · rcases h2 with ⟨rfl, rfl⟩
              simp only [and_self, ↓reduceIte]
              by_cases ha1 : a₁ = a₂
              · subst ha1
                exact hb_red (M (G.r a₁)) (G.J a₁ c₁) i_new (ne_of_lt (hi1 c₁ hc₁'))
              · exact hi2 a₁ ha₁ ha1 c₁ hc₁'
            · simp only [h2, ↓reduceIte]
              have hc₂' : c₂ < len a₂ := by
                by_cases ha2 : a₂ = a₀
                · subst ha2
                  simp only [Function.update_self] at hc₂
                  have : c₂ ≠ len a₂ := fun h => h2 ⟨rfl, h⟩
                  omega
                · simp only [Function.update_of_ne ha2] at hc₂
                  exact hc₂
              exact G.red_clique a₁ c₁ a₂ c₂ ha₁ hc₁' ha₂ hc₂' hne },
      rfl,
      fun a c _ hc => by
        have hnot : ¬ (a = a₀ ∧ c = len a₀) := by
          rintro ⟨rfl, rfl⟩
          exact lt_irrefl _ hc
        simp [J', hnot]⟩
  -- Helper 3: grow `Grid s (fun _ => s)` to `Grid (s + 1) (fun _ => s + 1)`
  have extendGrid : ∀ (s : ℕ) (G : Grid R UB M v U s (fun _ => s)),
      {G' : Grid R UB M v U (s + 1) (fun _ => s + 1) //
        (∀ a < s, G'.r a = G.r a) ∧ (∀ a c, a < s → c < s → G'.J a c = G.J a c)} := by
    intro s G
    let G0 := addBlock s G
    -- First fill column `s` in rows `0 .. t-1`
    let fillCols : ∀ (t : ℕ), t ≤ s →
        {Gt : Grid R UB M v U (s + 1) (fun a => if a < t then s + 1 else if a < s then s else 0) //
          (∀ a < s, Gt.r a = G.r a) ∧ (∀ a c, a < s → c < s → Gt.J a c = G.J a c)} :=
      Nat.rec
        (fun _ =>
          ⟨G0.1.castLen (fun a _ => by simp),
           G0.2.1,
           fun a c _ _ => congrFun (congrFun G0.2.2 a) c⟩)
        (fun t ih ht =>
          let prev := ih (by omega)
          let step := addVertex prev.1 t (by omega)
          have hlen : ∀ a < s + 1,
              Function.update (fun a => if a < t then s + 1 else if a < s then s else 0)
                t ((if t < t then s + 1 else if t < s then s else 0) + 1) a =
              (if a < t + 1 then s + 1 else if a < s then s else 0) := by
            intro a _
            by_cases hat : a = t
            · rw [hat, Function.update_self]
              simp [show t < s by omega]
            · rw [Function.update_of_ne hat]
              split_ifs <;> omega
          ⟨step.1.castLen hlen,
           fun a ha => by
             change step.1.r a = G.r a
             rw [step.2.1]
             exact prev.2.1 a ha,
           fun a c ha hc => by
             change step.1.J a c = G.J a c
             rw [step.2.2 a c (by omega) (by split_ifs <;> omega)]
             exact prev.2.2 a c ha hc⟩)
    let G1 := fillCols s le_rfl
    -- Next fill row `s` in columns `0 .. t-1`
    let fillRow : ∀ (t : ℕ), t ≤ s + 1 →
        {Gt : Grid R UB M v U (s + 1) (fun a => if a < s then s + 1 else t) //
          (∀ a < s, Gt.r a = G.r a) ∧ (∀ a c, a < s → c < s → Gt.J a c = G.J a c)} :=
      Nat.rec
        (fun _ =>
          ⟨G1.1.castLen (fun a _ => by split_ifs <;> rfl),
           G1.2.1,
           G1.2.2⟩)
        (fun t ih ht =>
          let prev := ih (by omega)
          let step := addVertex prev.1 s (lt_add_one s)
          have hlen : ∀ a < s + 1,
              Function.update (fun a => if a < s then s + 1 else t)
                s ((if s < s then s + 1 else t) + 1) a =
              (if a < s then s + 1 else t + 1) := by
            intro a ha
            by_cases has : a = s
            · rw [has, Function.update_self]
              simp
            · rw [Function.update_of_ne has]
              have hlt : a < s := by omega
              simp [hlt]
          ⟨step.1.castLen hlen,
           fun a ha => by
             change step.1.r a = G.r a
             rw [step.2.1]
             exact prev.2.1 a ha,
           fun a c ha hc => by
             change step.1.J a c = G.J a c
             rw [step.2.2 a c (by omega) (by simp [ha]; omega)]
             exact prev.2.2 a c ha hc⟩)
    let G2 := fillRow (s + 1) le_rfl
    exact ⟨G2.1.castLen (fun a _ => by simp), G2.2.1, G2.2.2⟩
  -- Build the infinite tower of grids
  let tower : ∀ s : ℕ, Grid R UB M v U s (fun _ => s) :=
    Nat.rec
      { r := fun _ => 0
        J := fun _ _ => 0
        r_mono := fun _ _ _ h => (Nat.not_lt_zero _ h).elim
        J_mono := fun _ h => (Nat.not_lt_zero _ h).elim
        back_good := fun _ _ _ h => (Nat.not_lt_zero _ h).elim
        not_UB := fun _ _ _ h => (Nat.not_lt_zero _ h).elim
        red_clique := fun _ _ _ _ h => (Nat.not_lt_zero _ h).elim }
      fun s prev => (extendGrid s prev).1
  have htower_r : ∀ {s₁ s₂ : ℕ}, s₁ ≤ s₂ → ∀ a < s₁, (tower s₂).r a = (tower s₁).r a := by
    intro s₁ s₂ h
    induction s₂, h using Nat.le_induction with
    | base => intro _ _; rfl
    | succ s₂ h ih =>
      intro a ha
      exact ((extendGrid s₂ (tower s₂)).2.1 a (ha.trans_le h)).trans (ih a ha)
  have htower_J : ∀ {s₁ s₂ : ℕ}, s₁ ≤ s₂ → ∀ a c, a < s₁ → c < s₁ →
      (tower s₂).J a c = (tower s₁).J a c := by
    intro s₁ s₂ h
    induction s₂, h using Nat.le_induction with
    | base => intro _ _ _ _; rfl
    | succ s₂ h ih =>
      intro a c ha hc
      exact ((extendGrid s₂ (tower s₂)).2.2 a c (ha.trans_le h) (hc.trans_le h)).trans (ih a c ha hc)
  let f : ℕ ×ₗ ℕ → ℕ ×ₗ ℕ := fun p =>
    let a := (ofLex p).1
    let c := (ofLex p).2
    let s := max a c + 1
    v (M ((tower s).r a)) ((tower s).J a c)
  have hf_eq : ∀ p s, (ofLex p).1 < s → (ofLex p).2 < s →
      f p = v (M ((tower s).r (ofLex p).1)) ((tower s).J (ofLex p).1 (ofLex p).2) := by
    intro p s ha hc
    have hle : max (ofLex p).1 (ofLex p).2 + 1 ≤ s := by omega
    dsimp only [f]
    rw [htower_r hle _ (by omega), htower_J hle _ _ (by omega) (by omega)]
  refine ⟨f, ?_, ?_⟩
  · intro p q hpq
    let s := max (max (ofLex p).1 (ofLex p).2) (max (ofLex q).1 (ofLex q).2) + 1
    rw [hf_eq p s (by omega) (by omega), hf_eq q s (by omega) (by omega)]
    refine hv_mono _ _ _ _ ?_
    rw [Prod.Lex.lt_iff] at hpq ⊢
    rcases hpq with hlt | ⟨heq, hlt⟩
    · exact Or.inl (hM_mono ((tower s).r_mono _ _ hlt (by omega)))
    · exact Or.inr ⟨by simp [heq], by rw [heq]; exact (tower s).J_mono _ (by omega) _ _ hlt (by omega)⟩
  · intro p q hpq
    let s := max (max (ofLex p).1 (ofLex p).2) (max (ofLex q).1 (ofLex q).2) + 1
    rw [hf_eq p s (by omega) (by omega), hf_eq q s (by omega) (by omega)]
    exact (tower s).red_clique _ _ _ _ (by omega) (by omega) (by omega) (by omega)
      (fun h => hpq (ofLex.injective (Prod.ext (congrArg Prod.fst h) (congrArg Prod.snd h))))

private lemma specker_ordinal.{u} : OrdinalCardinalRamsey.{u} (ω ^ 2) (ω ^ 2) 3 := by
  intro red blue hcomp
  have htype : typeLT (ULift.{u, 0} ℕ ×ₗ ULift.{u, 0} ℕ) = (ω : Ordinal.{u}) ^ 2 := by
    have hnat : typeLT (ULift.{u, 0} ℕ) = (ω : Ordinal.{u}) := by
      rw [Ordinal.type_lt_ulift, Ordinal.type_nat_lt, Ordinal.lift_omega0]
    have hlex : RelIso (Prod.Lex ((· < ·) : ULift.{u, 0} ℕ → _ → Prop) (· < ·))
        ((· < ·) : (ULift.{u, 0} ℕ ×ₗ ULift.{u, 0} ℕ) → _ → Prop) :=
      { toEquiv := toLex
        map_rel_iff' := by
          intro a b
          simp [Prod.Lex.lt_iff, Prod.lex_def] }
    have hprod : typeLT (ULift.{u, 0} ℕ ×ₗ ULift.{u, 0} ℕ) =
        (typeLT (ULift.{u, 0} ℕ)) * (typeLT (ULift.{u, 0} ℕ)) :=
      hlex.symm.ordinalType_congr.trans (Ordinal.type_prod_lex (· < ·) (· < ·))
    rw [hprod, hnat, sq]
  have he_ex : Nonempty (((· < ·) : (ULift.{u, 0} ℕ ×ₗ ULift.{u, 0} ℕ) → _ → Prop) ≃r
      ((· < ·) : ((ω : Ordinal.{u}) ^ 2).ToType → _ → Prop)) :=
    Ordinal.type_eq.mp (htype.trans (Ordinal.type_toType _).symm)
  obtain ⟨e⟩ := he_ex
  let emb : ℕ ×ₗ ℕ → ((ω : Ordinal.{u}) ^ 2).ToType :=
    fun p => e (toLex (ULift.up (ofLex p).1, ULift.up (ofLex p).2))
  have hemb_mono : StrictMono emb := by
    intro p q hpq
    apply e.map_rel_iff.mpr
    rw [Prod.Lex.lt_iff] at hpq ⊢
    rcases hpq with hlt | ⟨heq, hlt⟩
    · exact Or.inl hlt
    · exact Or.inr ⟨congrArg ULift.up heq, hlt⟩
  let R : SimpleGraph (ℕ ×ₗ ℕ) := red.comap emb
  let B : SimpleGraph (ℕ ×ₗ ℕ) := blue.comap emb
  have hRB_comp : IsCompl R B := by
    refine ⟨?_, ?_⟩
    · rw [disjoint_iff]
      ext p q
      simp only [SimpleGraph.inf_adj, SimpleGraph.bot_adj, iff_false, not_and, R, B,
        SimpleGraph.comap_adj]
      intro hr hb
      have hbot : (red ⊓ blue).Adj (emb p) (emb q) := ⟨hr, hb⟩
      rw [hcomp.disjoint.eq_bot] at hbot
      exact hbot
    · rw [codisjoint_iff]
      ext p q
      simp only [SimpleGraph.sup_adj, SimpleGraph.top_adj, R, B, SimpleGraph.comap_adj]
      constructor
      · rintro (hr | hb)
        · exact fun h => red.loopless.irrefl _ (h ▸ hr)
        · exact fun h => blue.loopless.irrefl _ (h ▸ hb)
      · intro hne
        have htop : (red ⊔ blue).Adj (emb p) (emb q) := by
          rw [hcomp.codisjoint.eq_top]
          exact hemb_mono.injective.ne hne
        exact htop
  by_cases htri : ∃ x y z : ℕ ×ₗ ℕ, B.Adj x y ∧ B.Adj y z ∧ B.Adj x z
  · right
    obtain ⟨x, y, z, hxy, hyz, hxz⟩ := htri
    let ex := emb x
    let ey := emb y
    let ez := emb z
    have hne_xy : ex ≠ ey := blue.ne_of_adj hxy
    have hne_yz : ey ≠ ez := blue.ne_of_adj hyz
    have hne_xz : ex ≠ ez := blue.ne_of_adj hxz
    refine ⟨({ex, ey, ez} : Finset _), ?_, ?_⟩
    · intro u hu v hv huv
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hu hv
      rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
      · exact (huv rfl).elim
      · exact hxy
      · exact hxz
      · exact hxy.symm
      · exact (huv rfl).elim
      · exact hyz
      · exact hxz.symm
      · exact hyz.symm
      · exact (huv rfl).elim
    · have hcard : ({ex, ey, ez} : Finset _).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp [hne_xy, hne_xz]),
          Finset.card_insert_of_notMem (by simp [hne_yz]), Finset.card_singleton]
      simp only [Finset.coe_sort_coe, Cardinal.mk_coe_finset, hcard]
      norm_num
  · left
    push Not at htri
    obtain ⟨f, hf_mono, hf_red⟩ :=
      specker_lex_nat R B hRB_comp (fun x y z ⟨h1, h2, h3⟩ => htri x y z h1 h2 h3)
    let g : (ULift.{u, 0} ℕ ×ₗ ULift.{u, 0} ℕ) → ((ω : Ordinal.{u}) ^ 2).ToType :=
      fun p => emb (f (toLex ((ofLex p).1.down, (ofLex p).2.down)))
    have hg_mono : StrictMono g := by
      intro p q hpq
      apply hemb_mono
      apply hf_mono
      rw [Prod.Lex.lt_iff] at hpq ⊢
      rcases hpq with hlt | ⟨heq, hlt⟩
      · exact Or.inl hlt
      · exact Or.inr ⟨congrArg ULift.down heq, hlt⟩
    refine ⟨Set.range g, ?_, ?_⟩
    · rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩ hne
      have hpq : toLex ((ofLex p).1.down, (ofLex p).2.down) ≠
          toLex ((ofLex q).1.down, (ofLex q).2.down) := fun h => hne (by simp [g, h])
      exact hf_red _ _ hpq
    · let iso : (ULift.{u, 0} ℕ ×ₗ ULift.{u, 0} ℕ) ≃o Set.range g :=
        { toEquiv := Equiv.ofBijective (fun p => ⟨g p, p, rfl⟩)
            ⟨fun p q h => hg_mono.injective (congrArg Subtype.val h),
             fun ⟨_, p, hp⟩ => ⟨p, Subtype.ext hp⟩⟩
          map_rel_iff' := by
            intro p q
            exact hg_mono.le_iff_le }
      exact iso.symm.ordinalType_congr.trans htype

theorem OMA.solution : type_of% @Erdos590.erdos_590.variants.two :=
  specker_ordinal
