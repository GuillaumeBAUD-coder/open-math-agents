import FormalConjectures.ErdosProblems.«629»
import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-!
# Bounds on the order of bipartite list-coloring obstructions

A random partition of the available colors rules out small obstructions by counting.
For the upper bound, each split of a suitably sized palette makes a fixed fraction
of all lists monochromatic. Repeatedly taking a list that covers at least the
average number of remaining splits produces an uncolorable family of the
required size. Duplicating its lists on the sides of a complete bipartite
graph gives the obstruction.

Reference: Erdős, Rubin and Taylor, Choosability in graphs, pp. 127–129.
The transfer to a bipartite graph uses Ian Qvist's proof in pull request 80.
-/

/- Transfer uncolorable families to bipartite list-coloring obstructions. -/

open SimpleGraph

lemma OMA.property_b_choosable_mono {V : Type*} {G : SimpleGraph V} {k l : ℕ}
    (hkl : k ≤ l) (hk : G.IsKChoosable k) : G.IsKChoosable l := by
  intro L hL
  have hex (v : V) : ∃ M ⊆ L v, (M : Finset ℕ).card = k :=
    Finset.exists_subset_card_eq (by rw [hL]; exact hkl)
  choose M hM_sub hM_card using hex
  obtain ⟨C, hC⟩ := hk M hM_card
  exact ⟨C, fun v => hM_sub v (hC v)⟩

lemma OMA.property_b_finite_choosable {V : Type*} [Fintype V] (G : SimpleGraph V) :
    G.IsKChoosable (Fintype.card V) := by
  intro L hL
  have hHall (S : Finset V) : S.card ≤ (S.biUnion L).card := by
    by_cases hS : S.Nonempty
    · obtain ⟨v, hv⟩ := hS
      calc
        S.card ≤ Fintype.card V := Finset.card_le_univ S
        _ = (L v).card := (hL v).symm
        _ ≤ (S.biUnion L).card := Finset.card_le_card fun c hc =>
          Finset.mem_biUnion.mpr ⟨v, hv, hc⟩
    · have hEmpty := Finset.not_nonempty_iff_eq_empty.mp hS
      simp [hEmpty]
  obtain ⟨c, hc_inj, hc_mem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_existsInjective' L).mp hHall
  exact ⟨Coloring.mk c (fun h => hc_inj.ne h.ne), hc_mem⟩

lemma OMA.property_b_to_bipartite {k m : ℕ} (H : Finset (Finset (Fin m)))
    (hU : H.IsUniform k) (hNot : ¬ H.HypergraphColorable 2) :
    ∃ G : SimpleGraph (Fin (2 * H.card)), G.Colorable 2 ∧ k < G.listChromaticNumber := by
  classical
  let e : Fin (2 * H.card) ≃ Fin 2 × ↥H :=
    Fintype.equivOfCardEq (by simp [Fintype.card_prod])
  let G : SimpleGraph (Fin (2 * H.card)) :=
    { Adj := fun a b => (e a).1 ≠ (e b).1
      symm := ⟨fun _ _ h => Ne.symm h⟩
      loopless := ⟨fun _ h => h rfl⟩ }
  let L (v : Fin (2 * H.card)) : Finset ℕ := (e v).2.val.map Fin.valEmbedding
  have hL (v : Fin (2 * H.card)) : (L v).card = k := by
    rw [show L v = (e v).2.val.map Fin.valEmbedding from rfl, Finset.card_map]
    exact hU _ (e v).2.property
  have hBad : ¬ G.IsKChoosable k := by
    intro h
    obtain ⟨C, hC⟩ := h L hL
    let color (x : Fin m) : Fin 2 :=
      if ∃ ed : ↥H, C (e.symm (0, ed)) = x.val then 0 else 1
    apply hNot
    refine ⟨color, ?_⟩
    intro edge he
    let E : ↥H := ⟨edge, he⟩
    have hleft : C (e.symm (0, E)) ∈ edge.map Fin.valEmbedding := by
      simpa only [L, e.apply_symm_apply] using hC (e.symm (0, E))
    have hright : C (e.symm (1, E)) ∈ edge.map Fin.valEmbedding := by
      simpa only [L, e.apply_symm_apply] using hC (e.symm (1, E))
    obtain ⟨x, hx, hx_eq⟩ := Finset.mem_map.mp hleft
    obtain ⟨y, hy, hy_eq⟩ := Finset.mem_map.mp hright
    have h0 : color x = 0 := if_pos ⟨E, hx_eq.symm⟩
    have h1 : color y = 1 := by
      apply if_neg
      rintro ⟨F, hF⟩
      have hAdj : G.Adj (e.symm (0, F)) (e.symm (1, E)) := by
        change (e (e.symm (0, F))).1 ≠ (e (e.symm (1, E))).1
        simp
      exact C.valid hAdj (hF.trans hy_eq)
    exact ⟨x, hx, y, hy, by rw [h0, h1]; decide⟩
  have hs : {j : ℕ | G.IsKChoosable j}.Nonempty :=
    ⟨Fintype.card (Fin (2 * H.card)), OMA.property_b_finite_choosable G⟩
  have hmin : G.IsKChoosable G.listChromaticNumber := Nat.sInf_mem hs
  refine ⟨G, ⟨Coloring.mk (fun v => (e v).1) (fun h => h)⟩, ?_⟩
  by_contra! hle
  exact hBad (OMA.property_b_choosable_mono hle hmin)

lemma OMA.ert_uncolorable_of_no_split {m : ℕ} (H : Finset (Finset (Fin m)))
    (hNoSplit : ∀ S : Finset (Fin m), ∃ E ∈ H, E ⊆ S ∨ Disjoint E S) :
    ¬ H.HypergraphColorable 2 := by
  rintro ⟨c, hc⟩
  let S : Finset (Fin m) := Finset.univ.filter fun x => c x = 0
  obtain ⟨E, hE, hMono⟩ := hNoSplit S
  obtain ⟨x, hx, y, hy, hxy⟩ := hc E hE
  apply hxy
  rcases hMono with hSub | hDisj
  · exact ((Finset.mem_filter.mp (hSub hx)).2).trans ((Finset.mem_filter.mp (hSub hy)).2).symm
  · have hcases : ∀ t : Fin 2, t ≠ 0 → t = 1 := by decide
    have h1 (z : Fin m) (hz : z ∈ E) : c z = 1 := by
      apply hcases
      intro hz0
      exact Finset.disjoint_left.mp hDisj hz
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz0⟩)
    exact (h1 x hx).trans (h1 y hy).symm

lemma OMA.ert_n_one : Erdos629.n 1 = 2 := by
  let H : Finset (Finset (Fin 1)) := {{0}}
  have hU : H.IsUniform 1 := by simp [H, Finset.IsUniform]
  have hNot : ¬ H.HypergraphColorable 2 := by
    rintro ⟨c, hc⟩
    obtain ⟨x, _, y, _, hxy⟩ := hc {0} (by simp [H])
    exact hxy (congrArg c (Subsingleton.elim x y))
  obtain ⟨G, hG, hList⟩ := OMA.property_b_to_bipartite H hU hNot
  have hUp := Erdos629.n_le G hG hList
  have hs : {m : ℕ | ∃ G : SimpleGraph (Fin m),
      G.Colorable 2 ∧ 1 < G.listChromaticNumber}.Nonempty := ⟨_, G, hG, hList⟩
  obtain ⟨J, _, hJList⟩ : ∃ J : SimpleGraph (Fin (Erdos629.n 1)),
      J.Colorable 2 ∧ 1 < J.listChromaticNumber := Nat.sInf_mem hs
  have hLo : J.listChromaticNumber ≤ Erdos629.n 1 := by
    have hChoosable : J.IsKChoosable (Erdos629.n 1) := by
      simpa only [Fintype.card_fin] using OMA.property_b_finite_choosable J
    exact Nat.sInf_le hChoosable
  have hH : H.card = 1 := by decide
  omega

/- A counting proof of the lower bound on the order of a bipartite obstruction. -/

open SimpleGraph

-- A fixed list forbids just one assignment on its colors. A bad assignment
-- is therefore determined by its restriction to the remaining palette.
private lemma erdos629_card_bad {α : Type} [Fintype α] [DecidableEq α] (s : Finset α) (b : Fin 2) :
    ((Finset.univ : Finset (α → Fin 2)).filter (fun f => ∀ c ∈ s, f c ≠ b)).card
      ≤ 2 ^ (Fintype.card α - s.card) := by
  classical
  let bad := (Finset.univ : Finset (α → Fin 2)).filter (fun f => ∀ c ∈ s, f c ≠ b)
  let restrict : ↥bad → {c : α // c ∉ s} → Fin 2 := fun f c => f.val c.val
  have hinj : Function.Injective restrict := by
    intro f g hfg
    apply Subtype.ext
    funext c
    by_cases hc : c ∈ s
    · have hf := (Finset.mem_filter.mp f.property).2 c hc
      have hg := (Finset.mem_filter.mp g.property).2 c hc
      apply Fin.ext
      have hfv : (f.val c).val ≠ b.val := fun h => hf (Fin.ext h)
      have hgv : (g.val c).val ≠ b.val := fun h => hg (Fin.ext h)
      have hf_lt := (f.val c).isLt
      have hg_lt := (g.val c).isLt
      have hb_lt := b.isLt
      omega
    · exact congrFun hfg ⟨c, hc⟩
  have hcount := Fintype.card_le_of_injective restrict hinj
  have hd : Fintype.card {c : α // c ∉ s} = Fintype.card α - s.card := by
    rw [Fintype.card_subtype_compl (· ∈ s), Fintype.card_coe]
  rw [Fintype.card_coe, Fintype.card_fun, Fintype.card_fin, hd] at hcount
  exact hcount

private lemma erdos629_choosable {m k : ℕ} {G : SimpleGraph (Fin m)}
    (hb : G.Colorable 2) (hm : m < 2 ^ k) : G.IsKChoosable k := by
  classical
  obtain ⟨B⟩ := hb
  intro L hL
  let palette : Finset ℕ := Finset.univ.biUnion L
  have hsub (v : Fin m) : L v ⊆ palette := by
    intro c hc
    exact Finset.mem_biUnion.mpr ⟨v, Finset.mem_univ _, hc⟩
  let S (v : Fin m) : Finset ↥palette := (L v).subtype (· ∈ palette)
  have hS (v : Fin m) : (S v).card = k := by
    dsimp only [S]
    rw [Finset.card_subtype, Finset.filter_true_of_mem (fun c hc => hsub v hc), hL]
  let bad (v : Fin m) : Finset (↥palette → Fin 2) :=
    Finset.univ.filter (fun f => ∀ c ∈ S v, f c ≠ B v)
  have hbad (v : Fin m) : (bad v).card ≤ 2 ^ (Fintype.card ↥palette - k) := by
    simpa only [hS v] using erdos629_card_bad (S v) (B v)
  let allBad := Finset.univ.biUnion bad
  have hbound : allBad.card ≤ m * 2 ^ (Fintype.card ↥palette - k) := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      Finset.card_biUnion_le_card_mul Finset.univ bad _ (fun v _ => hbad v)
  have hstrict : m * 2 ^ (Fintype.card ↥palette - k) < 2 ^ Fintype.card ↥palette := by
    by_cases hm0 : m = 0
    · simp [hm0]
    · let v : Fin m := ⟨0, Nat.pos_of_ne_zero hm0⟩
      have hk : k ≤ Fintype.card ↥palette := (hS v) ▸ (S v).card_le_univ
      calc
        _ < 2 ^ k * 2 ^ (Fintype.card ↥palette - k) :=
          Nat.mul_lt_mul_of_pos_right hm (by positivity)
        _ = _ := by rw [← Nat.pow_add, Nat.add_sub_of_le hk]
  have hcard : allBad.card < (Finset.univ : Finset (↥palette → Fin 2)).card := by
    simpa only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin] using hbound.trans_lt hstrict
  obtain ⟨f, -, hf⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  have hgood (v : Fin m) : ∃ c ∈ S v, f c = B v := by
    by_contra! h
    exact hf (Finset.mem_biUnion.mpr
      ⟨v, Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩)
  choose c hc hfB using hgood
  refine ⟨Coloring.mk (fun v => (c v).val) ?_, fun v => Finset.mem_subtype.mp (hc v)⟩
  intro v w hvw heq
  exact B.valid hvw (by rw [← hfB v, ← hfB w, Subtype.ext heq])

lemma erdos629_lower (k : ℕ) (hk : 1 ≤ k)
    (hne : {m : ℕ | ∃ G : SimpleGraph (Fin m), G.Colorable 2 ∧ k < G.listChromaticNumber}.Nonempty) :
    2 ^ (k - 1) < Erdos629.n k := by
  obtain ⟨G, hb, hG⟩ := Nat.sInf_mem hne
  change k < G.listChromaticNumber at hG
  by_contra! hn
  have hm : Erdos629.n k < 2 ^ k := hn.trans_lt
    (Nat.pow_lt_pow_right (by decide : 1 < (2 : ℕ)) (by omega))
  have hc := erdos629_choosable hb hm
  exact (not_le_of_gt hG) (Nat.sInf_le hc)

/- The number of monochromatic lists is minimized by a balanced split. -/

private lemma ert_choose_balanced_aux (m r : ℕ) :
    ∀ d ≤ m, 2 * m.choose (r + 1) ≤
      (m - d).choose (r + 1) + (m + d).choose (r + 1) := by
  intro d
  induction d with
  | zero => simp [two_mul]
  | succ d ih =>
    intro hd
    have hsmall : m - (d + 1) + 1 = m - d := by omega
    have hleft := Nat.choose_succ_succ' (m - (d + 1)) r
    have hright := Nat.choose_succ_succ' (m + d) r
    rw [hsmall] at hleft
    have hinc := Nat.choose_le_choose r (show m - (d + 1) ≤ m + d by omega)
    have hprev := ih (by omega)
    change 2 * m.choose (r + 1) ≤
      (m - (d + 1)).choose (r + 1) + (m + d + 1).choose (r + 1)
    omega

private lemma ert_choose_balanced (m k b : ℕ) (hb : b ≤ 2 * m) :
    2 * m.choose k ≤ b.choose k + (2 * m - b).choose k := by
  cases k with
  | zero => simp
  | succ r =>
    by_cases h : b ≤ m
    · have hi := ert_choose_balanced_aux m r (m - b) (by omega)
      have hl : m - (m - b) = b := by omega
      have hr : m + (m - b) = 2 * m - b := by omega
      simpa only [hl, hr] using hi
    · have hi := ert_choose_balanced_aux m r (b - m) (by omega)
      have hl : m - (b - m) = 2 * m - b := by omega
      have hr : m + (b - m) = b := by omega
      simpa only [hl, hr, add_comm] using hi

private lemma ert_one_sub_sum_le_prod (a : ℕ → ℚ) (r : ℕ)
    (ha : ∀ i < r, 0 ≤ a i ∧ a i ≤ 1) :
    1 - ∑ i ∈ Finset.range r, a i ≤ ∏ i ∈ Finset.range r, (1 - a i) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Finset.sum_range_succ, Finset.prod_range_succ]
    have har := ha r (Nat.lt_succ_self r)
    have hsum : 0 ≤ ∑ i ∈ Finset.range r, a i :=
      Finset.sum_nonneg fun i hi => (ha i (by have := Finset.mem_range.mp hi; omega)).1
    have hmul := mul_le_mul_of_nonneg_right
      (ih fun i hi => ha i (by omega)) (sub_nonneg.mpr har.2)
    nlinarith [mul_nonneg hsum har.1]

private lemma ert_sum_range_cast (k : ℕ) :
    (∑ i ∈ Finset.range k, (i : ℚ)) = (k : ℚ) * ((k : ℚ) - 1) / 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih, Nat.cast_succ]
    ring

private lemma ert_desc_factorial_cast (m k : ℕ) (h : k ≤ m) :
    (m.descFactorial k : ℚ) = ∏ i ∈ Finset.range k, ((m : ℚ) - (i : ℚ)) := by
  rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
  refine Finset.prod_congr rfl fun i hi => Nat.cast_sub ?_
  have := Finset.mem_range.mp hi
  omega

private lemma ert_choose_half (m k : ℕ) (hk : 2 ≤ k) (hs : k ^ 2 ≤ 2 * m) :
    (2 * m).choose k ≤ 2 ^ (k + 1) * m.choose k := by
  let s : ℚ := 2 * (m : ℚ)
  let q : ℚ := s - (k : ℚ) + 1
  let a (i : ℕ) : ℚ := (i : ℚ) / (s - i)
  have hkm : k ≤ m := by
    have hkk := Nat.mul_le_mul_right k hk
    rw [pow_two] at hs
    omega
  have hkmQ : (k : ℚ) ≤ m := by exact_mod_cast hkm
  have hsQ : (k : ℚ) ^ 2 ≤ s := by
    dsimp [s]
    exact_mod_cast hs
  have hqpos : 0 < q := by
    dsimp [q, s]
    linarith
  have hden : ∀ i < k, q ≤ s - (i : ℚ) := by
    intro i hi
    have hiQ : (i : ℚ) + 1 ≤ k := by exact_mod_cast (Nat.succ_le_iff.mpr hi)
    dsimp [q]
    linarith
  have ha : ∀ i < k, 0 ≤ a i ∧ a i ≤ 1 := by
    intro i hi
    have hp : 0 < s - (i : ℚ) := hqpos.trans_le (hden i hi)
    have hiQ : (i : ℚ) ≤ k := by exact_mod_cast hi.le
    refine ⟨div_nonneg (by positivity) hp.le, (div_le_iff₀ hp).mpr ?_⟩
    dsimp [s]
    linarith
  have hsum : (∑ i ∈ Finset.range k, a i) ≤ 1 / 2 := by
    calc
      (∑ i ∈ Finset.range k, a i) ≤ ∑ i ∈ Finset.range k, (i : ℚ) / q := by
        refine Finset.sum_le_sum fun i hi => ?_
        exact div_le_div_of_nonneg_left (by positivity) hqpos (hden i (Finset.mem_range.mp hi))
      _ = (∑ i ∈ Finset.range k, (i : ℚ)) / q := by rw [Finset.sum_div]
      _ ≤ 1 / 2 := by
        apply (div_le_iff₀ hqpos).mpr
        rw [ert_sum_range_cast]
        dsimp [q]
        nlinarith
  have hprod : (1 / 2 : ℚ) ≤ ∏ i ∈ Finset.range k, (1 - a i) := by
    have h := ert_one_sub_sum_le_prod a k ha
    linarith
  let D : ℚ := ∏ i ∈ Finset.range k, (s - (i : ℚ))
  have hD : 0 ≤ D := by
    dsimp [D]
    exact Finset.prod_nonneg fun i hi => hqpos.le.trans (hden i (Finset.mem_range.mp hi))
  have hratio :
      (2 : ℚ) ^ k * (∏ i ∈ Finset.range k, ((m : ℚ) - (i : ℚ))) =
        (∏ i ∈ Finset.range k, (1 - a i)) * D := by
    calc
      _ = ∏ i ∈ Finset.range k, (2 : ℚ) * ((m : ℚ) - (i : ℚ)) := by
        simp [Finset.prod_mul_distrib]
      _ = ∏ i ∈ Finset.range k, (1 - a i) * (s - (i : ℚ)) := by
        refine Finset.prod_congr rfl fun i hi => ?_
        have hp : s - (i : ℚ) ≠ 0 :=
          (hqpos.trans_le (hden i (Finset.mem_range.mp hi))).ne'
        dsimp [a]
        rw [sub_mul, one_mul, div_mul_cancel₀ _ hp]
        dsimp [s]
        ring
      _ = _ := Finset.prod_mul_distrib
  have hbound : D ≤ (2 : ℚ) ^ (k + 1) *
      (∏ i ∈ Finset.range k, ((m : ℚ) - (i : ℚ))) := by
    have h := mul_le_mul_of_nonneg_right hprod hD
    rw [← hratio] at h
    rw [pow_succ]
    linarith
  have hdescQ : ((2 * m).descFactorial k : ℚ) ≤
      (2 : ℚ) ^ (k + 1) * (m.descFactorial k : ℚ) := by
    rw [ert_desc_factorial_cast _ _ (by omega : k ≤ 2 * m), ert_desc_factorial_cast _ _ hkm]
    simpa [D, s, Nat.cast_mul] using hbound
  have hdesc : (2 * m).descFactorial k ≤ 2 ^ (k + 1) * m.descFactorial k := by
    exact_mod_cast hdescQ
  have hfac : k.factorial * (2 * m).choose k ≤
      k.factorial * (2 ^ (k + 1) * m.choose k) := by
    simpa [Nat.descFactorial_eq_factorial_mul_choose, Nat.mul_left_comm] using hdesc
  exact Nat.le_of_mul_le_mul_left hfac (Nat.factorial_pos k)

private lemma ert_monochromatic_choose (m k b : ℕ) (hk : 2 ≤ k) (hs : k ^ 2 ≤ 2 * m)
    (hb : b ≤ 2 * m) : (2 * m).choose k ≤ 2 ^ k * (b.choose k + (2 * m - b).choose k) := by
  calc
    _ ≤ 2 ^ (k + 1) * m.choose k := ert_choose_half m k hk hs
    _ = 2 ^ k * (2 * m.choose k) := by rw [pow_succ, Nat.mul_assoc]
    _ ≤ _ := Nat.mul_le_mul_left _ (ert_choose_balanced m k b hb)

/- Counting monochromatic lists for a partition of the palette. -/

lemma erdos629_mono_count (s k : ℕ) (hk : 0 < k) (B : Finset (Fin s)) :
    (((Finset.univ : Finset (Fin s)).powersetCard k).filter
        (fun A => A ⊆ B ∨ Disjoint A B)).card =
      B.card.choose k + (s - B.card).choose k := by
  classical
  have hunion : ((Finset.univ : Finset (Fin s)).powersetCard k).filter
        (fun A => A ⊆ B ∨ Disjoint A B) = B.powersetCard k ∪ Bᶜ.powersetCard k := by
    ext A
    have hiff : Disjoint A B ↔ A ⊆ Bᶜ := by
      simp only [Finset.disjoint_left, Finset.subset_iff, Finset.mem_compl]
    simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and,
      Finset.mem_union, hiff]
    tauto
  have hdis : Disjoint (B.powersetCard k) (Bᶜ.powersetCard k) := by
    rw [Finset.disjoint_left]
    intro A hA hAc
    obtain ⟨hAB, hcard⟩ := Finset.mem_powersetCard.mp hA
    have hABc := (Finset.mem_powersetCard.mp hAc).1
    obtain ⟨a, ha⟩ := Finset.card_pos.mp (hcard ▸ hk)
    exact Finset.mem_compl.mp (hABc ha) (hAB ha)
  rw [hunion, Finset.card_union_of_disjoint hdis]
  simp only [Finset.card_powersetCard, Finset.card_compl, Fintype.card_fin]

lemma erdos629_palette_partitions (s : ℕ) : (Finset.univ : Finset (Finset (Fin s))).card = 2 ^ s := by
  simp only [Finset.card_univ, Fintype.card_finset, Fintype.card_fin]

namespace OMA.ERTBounds

open Finset

section Covering

variable {α β : Type*}
variable (hits : α → β → Prop) [DecidableRel hits]

def uncovered (A : Finset α) (Y : Finset β) : Finset β :=
  Y.filter fun b => ∀ a ∈ A, ¬ hits a b

lemma uncovered_insert [DecidableEq α] (a : α) (A : Finset α) (Y : Finset β) :
    uncovered hits (insert a A) Y = (uncovered hits A Y).filter fun b => ¬ hits a b := by
  ext b
  simp [uncovered, and_left_comm, and_comm]

lemma uncovered_union [DecidableEq α] (A B : Finset α) (Y : Finset β) :
    uncovered hits (A ∪ B) Y = uncovered hits B (uncovered hits A Y) := by
  ext b
  simp [uncovered, or_imp, forall_and, and_assoc]

lemma exists_large_cover {X : Finset α} (hX : X.Nonempty) (Y : Finset β) (D : ℕ)
    (hD : ∀ b ∈ Y, X.card ≤ D * (X.filter fun a => hits a b).card) :
    ∃ a ∈ X, Y.card ≤ D * (Y.filter (hits a)).card := by
  by_contra! h
  have hrows := sum_lt_sum_of_nonempty hX h
  have hcols := sum_le_sum (s := Y) hD
  simp only [sum_const, nsmul_eq_mul] at hrows hcols
  rw [← mul_sum] at hrows hcols
  have hcount := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (r := hits) (s := X) (t := Y)
  change (∑ a ∈ X, (Y.filter (hits a)).card) =
    ∑ b ∈ Y, (X.filter fun a => hits a b).card at hcount
  rw [hcount] at hrows
  exact (not_lt_of_ge hcols) (by simpa [Nat.mul_comm] using hrows)

-- Repeat the averaging step until the uncovered set has at most half its initial size.
lemma cover_half [DecidableEq α] {X : Finset α} (hX : X.Nonempty) (Y : Finset β) (D : ℕ) (hDpos : 0 < D)
    (hD : ∀ b ∈ Y, X.card ≤ D * (X.filter fun a => hits a b).card) :
    ∃ A ⊆ X, A.card ≤ D ∧ 2 * (uncovered hits A Y).card ≤ Y.card := by
  have hgreedy (i : ℕ) : ∃ A ⊆ X, A.card ≤ i ∧
      (2 * (uncovered hits A Y).card ≤ Y.card ∨
        (2 * D) * (uncovered hits A Y).card + i * Y.card ≤ (2 * D) * Y.card) := by
    induction i with
    | zero => exact ⟨∅, empty_subset _, by simp, Or.inr (by simp [uncovered])⟩
    | succ i ih =>
        obtain ⟨A, hAX, hAi, hcases⟩ := ih
        by_cases hhalf : 2 * (uncovered hits A Y).card ≤ Y.card
        · exact ⟨A, hAX, hAi.trans (Nat.le_succ _), Or.inl hhalf⟩
        have hbudget := hcases.resolve_left hhalf
        let Z := uncovered hits A Y
        have hZY : Z ⊆ Y := filter_subset _ _
        obtain ⟨a, ha, hcov⟩ := exists_large_cover hits hX Z D fun b hb => hD b (hZY hb)
        refine ⟨insert a A, insert_subset_iff.mpr ⟨ha, hAX⟩,
          (card_insert_le _ _).trans (Nat.succ_le_succ hAi), Or.inr ?_⟩
        have hscaled : Y.card ≤ (2 * D) * (Z.filter (hits a)).card :=
          calc
            Y.card ≤ 2 * Z.card := le_of_lt (lt_of_not_ge hhalf)
            _ ≤ 2 * (D * (Z.filter (hits a)).card) := Nat.mul_le_mul_left 2 hcov
            _ = _ := by rw [Nat.mul_assoc]
        have hpart : (Z.filter (hits a)).card + (Z.filter fun b => ¬ hits a b).card = Z.card :=
          card_filter_add_card_filter_not _
        have hpart' := congrArg (fun c => (2 * D) * c) hpart
        change (2 * D) * ((Z.filter (hits a)).card + (Z.filter fun b => ¬ hits a b).card) =
          (2 * D) * Z.card at hpart'
        rw [Nat.mul_add] at hpart'
        rw [uncovered_insert]
        change (2 * D) * (Z.filter fun b => ¬ hits a b).card +
          (i + 1) * Y.card ≤ (2 * D) * Y.card
        rw [Nat.add_mul, Nat.one_mul]
        change (2 * D) * Z.card + i * Y.card ≤ (2 * D) * Y.card at hbudget
        omega
  obtain ⟨A, hAX, hAD, hhalf | hbudget⟩ := hgreedy D
  · exact ⟨A, hAX, hAD, hhalf⟩
  refine ⟨A, hAX, hAD, Nat.le_of_mul_le_mul_left ?_ hDpos⟩
  have hleft : D * (2 * (uncovered hits A Y).card) = (2 * D) * (uncovered hits A Y).card := by ring
  have hright : (2 * D) * Y.card = D * Y.card + D * Y.card := by ring
  rw [hleft]
  rw [hright] at hbudget
  omega

lemma cover_in_blocks [DecidableEq α] {X : Finset α} (hX : X.Nonempty) (Y : Finset β) (D : ℕ) (hDpos : 0 < D)
    (hD : ∀ b ∈ Y, X.card ≤ D * (X.filter fun a => hits a b).card) (j : ℕ) :
    ∃ A ⊆ X, A.card ≤ j * D ∧ 2 ^ j * (uncovered hits A Y).card ≤ Y.card := by
  induction j with
  | zero => exact ⟨∅, empty_subset _, by simp, by simp [uncovered]⟩
  | succ j ih =>
      obtain ⟨A, hAX, hAj, hAcard⟩ := ih
      let Z := uncovered hits A Y
      have hZY : Z ⊆ Y := filter_subset _ _
      obtain ⟨B, hBX, hBD, hBcard⟩ := cover_half hits hX Z D hDpos fun b hb => hD b (hZY hb)
      refine ⟨A ∪ B, union_subset hAX hBX, ?_, ?_⟩
      · rw [Nat.succ_mul]
        exact (card_union_le _ _).trans (Nat.add_le_add hAj hBD)
      · rw [uncovered_union, pow_succ, Nat.mul_assoc]
        exact (Nat.mul_le_mul_left (2 ^ j) hBcard).trans hAcard

end Covering

end OMA.ERTBounds

private lemma ert_palette_bound (k : ℕ) (hk : 2 ≤ k) :
    let m := (k ^ 2 + 1) / 2
    k ^ 2 ≤ 2 * m ∧ 0 < m ∧
      2 * (2 ^ k * (2 * m + 1)) < k ^ 2 * 2 ^ (k + 2) := by
  dsimp
  have hkk : 4 ≤ k ^ 2 := by
    calc
      4 = 2 ^ 2 := rfl
      _ ≤ k ^ 2 := Nat.pow_le_pow_left hk _
  have hsmall : 2 * (2 * ((k ^ 2 + 1) / 2) + 1) < 4 * k ^ 2 := by omega
  refine ⟨by omega, by omega, ?_⟩
  calc
    _ = (2 * (2 * ((k ^ 2 + 1) / 2) + 1)) * 2 ^ k := by ring
    _ < (4 * k ^ 2) * 2 ^ k := Nat.mul_lt_mul_of_pos_right hsmall (by positivity)
    _ = _ := by rw [pow_add]; ring

private lemma ert_has_small_obstruction (k : ℕ) (hk : 2 ≤ k) :
    ∃ (v : ℕ) (G : SimpleGraph (Fin v)), G.Colorable 2 ∧
      k < G.listChromaticNumber ∧ v < k ^ 2 * 2 ^ (k + 2) := by
  classical
  let m := (k ^ 2 + 1) / 2
  have ⟨hsize, _, hbound⟩ := ert_palette_bound k hk
  change k ^ 2 ≤ 2 * m at hsize
  change 2 * (2 ^ k * (2 * m + 1)) < k ^ 2 * 2 ^ (k + 2) at hbound
  let X := (Finset.univ : Finset (Fin (2 * m))).powersetCard k
  let Y : Finset (Finset (Fin (2 * m))) := Finset.univ
  let hits (E S : Finset (Fin (2 * m))) : Prop := E ⊆ S ∨ Disjoint E S
  have hXcard : X.card = (2 * m).choose k := by
    simp [X, Finset.card_powersetCard]
  have hX : X.Nonempty := by
    apply Finset.card_pos.mp
    rw [hXcard]
    exact Nat.choose_pos ((by nlinarith : k ≤ k ^ 2).trans hsize)
  have hD : ∀ S ∈ Y, X.card ≤ 2 ^ k * (X.filter fun E => hits E S).card := by
    intro S _
    rw [hXcard, show (X.filter fun E => hits E S).card =
      S.card.choose k + (2 * m - S.card).choose k from
      erdos629_mono_count (2 * m) k (by omega) S]
    apply ert_monochromatic_choose m k S.card hk hsize
    simpa using Finset.card_le_univ S
  obtain ⟨H, hHX, hHcard, hRem⟩ :=
    OMA.ERTBounds.cover_in_blocks hits hX Y (2 ^ k) (by positivity) hD (2 * m + 1)
  have hYcard : Y.card = 2 ^ (2 * m) := erdos629_palette_partitions (2 * m)
  have hEmpty : OMA.ERTBounds.uncovered hits H Y = ∅ := by
    apply Finset.card_eq_zero.mp
    by_contra! hne
    have hpos : 1 ≤ (OMA.ERTBounds.uncovered hits H Y).card := by omega
    have hle := Nat.mul_le_mul_left (2 ^ (2 * m + 1)) hpos
    rw [mul_one] at hle
    have hlt : 2 ^ (2 * m) < 2 ^ (2 * m + 1) :=
      Nat.pow_lt_pow_right (by decide) (by omega)
    omega
  have hNoSplit : ∀ S : Finset (Fin (2 * m)), ∃ E ∈ H, E ⊆ S ∨ Disjoint E S := by
    intro S
    by_contra! h
    have hmem : S ∈ OMA.ERTBounds.uncovered hits H Y := by
      simp only [OMA.ERTBounds.uncovered, Finset.mem_filter, Y, Finset.mem_univ, true_and]
      intro E hE hmono
      rcases hmono with hsub | hdisj
      · exact (h E hE).1 hsub
      · exact (h E hE).2 hdisj
    simp [hEmpty] at hmem
  have hU : H.IsUniform k := fun E hE => (Finset.mem_powersetCard.mp (hHX hE)).2
  obtain ⟨G, hG, hList⟩ := OMA.property_b_to_bipartite H hU
    (OMA.ert_uncolorable_of_no_split H hNoSplit)
  refine ⟨2 * H.card, G, hG, hList, ?_⟩
  have htarget := (Nat.mul_le_mul_left 2 hHcard).trans_lt
    (show 2 * ((2 * m + 1) * 2 ^ k) < _ by simpa only [Nat.mul_comm (2 * m + 1)] using hbound)
  exact htarget

theorem OMA.solution : type_of% @Erdos629.erdos_629.variants.ert_bounds := by
  intro k hk
  by_cases h : k = 1
  · subst k
    norm_num [OMA.ert_n_one]
  obtain ⟨v, G, hG, hList, hbound⟩ := ert_has_small_obstruction k (by omega)
  exact ⟨erdos629_lower k hk ⟨v, G, hG, hList⟩, (Erdos629.n_le G hG hList).trans_lt hbound⟩
