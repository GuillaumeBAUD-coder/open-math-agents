import OMAReductions.R_Green19_green_19_R1

/-!
Probabilistic construction (Fox–Sah–Sawhney–Stoner–Zhao 2020) proving `Green19.green_19.R1.H2`:
for any locally linear graph `G` on `q > 1` vertices and any sufficiently large `n`, random
function triples `(f, g, h) : 𝔽₂ n → Fin q` yield a subset `A ⊆ 𝔽₂ n × 𝔽₂ n` with
`|A| ≥ |T(G)| / q^3 * N^2` and `|S_d(A)| ≤ 2 / q^4 * N^2` simultaneously for all `d ≠ 0`,
proved via elementary finite-sum second and fourth moment bounds.
-/

-- Step Green19.green_19.R1.H2: hypothesis H2 of reduction Green19.green_19.R1
-- Credit: @luciusacarr
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace Helpers

open Finset

private lemma f2_add_self {n : ℕ} (x : 𝔽₂ n) : x + x = 0 := by
  ext i
  exact CharTwo.add_self_eq_zero (x i)

private lemma f2_eq_add_iff {n : ℕ} (a b d : 𝔽₂ n) : a + d = b ↔ a = b + d := by
  constructor <;> rintro rfl <;> simp [add_assoc, f2_add_self]

/-- Ordered triples forming a triangle in `G`. -/
private def Tri {q : ℕ} (G : SimpleGraph (Fin q)) (a b c : Fin q) : Prop :=
  G.Adj a b ∧ G.Adj a c ∧ G.Adj b c

private instance {q : ℕ} (G : SimpleGraph (Fin q)) [DecidableRel G.Adj] (a b c : Fin q) :
    Decidable (Tri G a b c) :=
  inferInstanceAs (Decidable (G.Adj a b ∧ G.Adj a c ∧ G.Adj b c))

private def triSet {q : ℕ} (G : SimpleGraph (Fin q)) [DecidableRel G.Adj] :
    Finset (Fin q × Fin q × Fin q) :=
  univ.filter fun p => Tri G p.1 p.2.1 p.2.2

private lemma tri_edge_unique {q : ℕ} {G : SimpleGraph (Fin q)} (hG : G.LocallyLinear)
    {a b c₁ c₂ : Fin q} (h1 : Tri G a b c₁) (h2 : Tri G a b c₂) : c₁ = c₂ := by
  have hab : a ≠ b := h1.1.ne
  have hs1 : ({a, b, c₁} : Finset (Fin q)) ∈ G.cliqueSet 3 := by
    rw [SimpleGraph.mem_cliqueSet_iff, SimpleGraph.is3Clique_iff]
    exact ⟨a, b, c₁, h1.1, h1.2.1, h1.2.2, rfl⟩
  have hs2 : ({a, b, c₂} : Finset (Fin q)) ∈ G.cliqueSet 3 := by
    rw [SimpleGraph.mem_cliqueSet_iff, SimpleGraph.is3Clique_iff]
    exact ⟨a, b, c₂, h2.1, h2.2.1, h2.2.2, rfl⟩
  have heq : ({a, b, c₁} : Finset (Fin q)) = {a, b, c₂} := by
    by_contra hne
    have hsub := hG.1 hs1 hs2 hne
    have ha : a ∈ (({a, b, c₁} : Finset (Fin q)) : Set (Fin q)) ∩ ({a, b, c₂} : Finset (Fin q)) := by
      simp
    have hb : b ∈ (({a, b, c₁} : Finset (Fin q)) : Set (Fin q)) ∩ ({a, b, c₂} : Finset (Fin q)) := by
      simp
    exact hab (hsub ha hb)
  have hc1 : c₁ ∈ ({a, b, c₂} : Finset (Fin q)) := by
    rw [← heq]
    simp
  simp only [mem_insert, mem_singleton] at hc1
  rcases hc1 with rfl | rfl | rfl
  · exact absurd h1.2.1 (G.loopless.irrefl _)
  · exact absurd h1.2.2 (G.loopless.irrefl _)
  · rfl

private lemma triSet_card_le {q : ℕ} (_hq : 1 < q) (G : SimpleGraph (Fin q)) [DecidableRel G.Adj]
    (hG : G.LocallyLinear) : (triSet G).card ≤ q * q := by
  have hle : (triSet G).card ≤ (univ : Finset (Fin q × Fin q)).card := by
    refine Finset.card_le_card_of_injOn (fun p => (p.1, p.2.1)) (fun _ _ => mem_univ _) ?_
    intro p hp q' hq' hpq
    simp only [mem_coe, triSet, mem_filter, mem_univ, true_and] at hp hq'
    rcases p with ⟨a₁, b₁, c₁⟩
    rcases q' with ⟨a₂, b₂, c₂⟩
    have ha : a₁ = a₂ := congrArg Prod.fst hpq
    have hb : b₁ = b₂ := congrArg Prod.snd hpq
    subst ha hb
    have hc : c₁ = c₂ := tri_edge_unique hG hp hq'
    subst hc
    rfl
  simpa [Fintype.card_prod, Fintype.card_fin] using hle

private lemma six_mul_clique_le_triSet {q : ℕ} (hq : 0 < q) (G : SimpleGraph (Fin q)) [DecidableRel G.Adj] :
    6 * (G.cliqueFinset 3).card ≤ (triSet G).card := by
  classical
  have : NeZero q := ⟨hq.ne'⟩
  let L (s : Finset (Fin q)) := s.sort (· ≤ ·)
  have hL_len : ∀ s ∈ G.cliqueFinset 3, (L s).length = 3 := by
    intro s hs
    rw [SimpleGraph.mem_cliqueFinset_iff] at hs
    rw [Finset.length_sort, hs.card_eq]
  have hL_mem : ∀ (s : Finset (Fin q)) (hs : s ∈ G.cliqueFinset 3) (i : Fin 3),
      (L s)[i.val]'(by rw [hL_len s hs]; exact i.isLt) ∈ s := by
    intro s hs i
    rw [← Finset.mem_sort (r := (· ≤ ·))]
    exact List.getElem_mem _
  have hL_inj : ∀ (s : Finset (Fin q)) (hs : s ∈ G.cliqueFinset 3),
      Function.Injective (fun i : Fin 3 => (L s)[i.val]'(by rw [hL_len s hs]; exact i.isLt)) := by
    intro s hs i j hij
    have hnd : (L s).Nodup := Finset.sort_nodup _ _
    exact Fin.ext (hnd.getElem_inj_iff.mp hij)
  have hL_surj : ∀ (s : Finset (Fin q)) (hs : s ∈ G.cliqueFinset 3) (x : Fin q),
      x ∈ s → ∃ i : Fin 3, (L s)[i.val]'(by rw [hL_len s hs]; exact i.isLt) = x := by
    intro s hs x hx
    rw [← Finset.mem_sort (r := (· ≤ ·))] at hx
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hx
    exact ⟨⟨k, by rw [hL_len s hs] at hk; exact hk⟩, rfl⟩
  let dom := (G.cliqueFinset 3) ×ˢ (univ : Finset (Equiv.Perm (Fin 3)))
  have hcard : dom.card = (G.cliqueFinset 3).card * 6 := by
    rw [card_product, card_univ, Fintype.card_perm, Fintype.card_fin]
    rfl
  rw [mul_comm, ← hcard]
  refine Finset.card_le_card_of_injOn
    (fun p => if h : p.1 ∈ G.cliqueFinset 3 then
      let v : Fin 3 → Fin q := fun i => (L p.1)[i.val]'(by rw [hL_len p.1 h]; exact i.isLt)
      (v (p.2 0), v (p.2 1), v (p.2 2))
    else (0, 0, 0)) ?_ ?_
  · intro p hp
    rcases p with ⟨s, σ⟩
    have hs : s ∈ G.cliqueFinset 3 := (mem_product.mp hp).1
    simp only [hs, ↓reduceDIte, mem_coe]
    rw [triSet, mem_filter]
    have hcl : G.IsNClique 3 s := (SimpleGraph.mem_cliqueFinset_iff.mp hs)
    have hne : ∀ i j : Fin 3, i ≠ j → σ i ≠ σ j := fun i j hij => σ.injective.ne hij
    have hinj := hL_inj s hs
    exact ⟨mem_univ _,
           ⟨hcl.1 (hL_mem s hs _) (hL_mem s hs _) (hinj.ne (hne 0 1 (by decide))),
            hcl.1 (hL_mem s hs _) (hL_mem s hs _) (hinj.ne (hne 0 2 (by decide))),
            hcl.1 (hL_mem s hs _) (hL_mem s hs _) (hinj.ne (hne 1 2 (by decide)))⟩⟩
  · intro p₁ hp₁ p₂ hp₂ heq
    rcases p₁ with ⟨s₁, σ₁⟩
    rcases p₂ with ⟨s₂, σ₂⟩
    have hs₁ : s₁ ∈ G.cliqueFinset 3 := (mem_product.mp hp₁).1
    have hs₂ : s₂ ∈ G.cliqueFinset 3 := (mem_product.mp hp₂).1
    simp only [hs₁, hs₂, ↓reduceDIte] at heq
    have h0 : (L s₁)[(σ₁ 0).val]'(by rw [hL_len s₁ hs₁]; exact (σ₁ 0).isLt) =
              (L s₂)[(σ₂ 0).val]'(by rw [hL_len s₂ hs₂]; exact (σ₂ 0).isLt) :=
      congrArg Prod.fst heq
    have h1 : (L s₁)[(σ₁ 1).val]'(by rw [hL_len s₁ hs₁]; exact (σ₁ 1).isLt) =
              (L s₂)[(σ₂ 1).val]'(by rw [hL_len s₂ hs₂]; exact (σ₂ 1).isLt) :=
      congrArg (fun x => x.2.1) heq
    have h2 : (L s₁)[(σ₁ 2).val]'(by rw [hL_len s₁ hs₁]; exact (σ₁ 2).isLt) =
              (L s₂)[(σ₂ 2).val]'(by rw [hL_len s₂ hs₂]; exact (σ₂ 2).isLt) :=
      congrArg (fun x => x.2.2) heq
    have hvals : ∀ i : Fin 3,
        (L s₁)[(σ₁ i).val]'(by rw [hL_len s₁ hs₁]; exact (σ₁ i).isLt) =
        (L s₂)[(σ₂ i).val]'(by rw [hL_len s₂ hs₂]; exact (σ₂ i).isLt) := by
      intro i
      fin_cases i <;> assumption
    have hs_eq : s₁ = s₂ := by
      ext x
      constructor <;> intro hx
      · obtain ⟨j, hj⟩ := hL_surj s₁ hs₁ x hx
        obtain ⟨i, hi⟩ := σ₁.surjective j
        rw [← hj, ← hi, hvals i]
        exact hL_mem s₂ hs₂ _
      · obtain ⟨j, hj⟩ := hL_surj s₂ hs₂ x hx
        obtain ⟨i, hi⟩ := σ₂.surjective j
        rw [← hj, ← hi, ← hvals i]
        exact hL_mem s₁ hs₁ _
    subst hs_eq
    have hσ : σ₁ = σ₂ := Equiv.Perm.ext fun i => hL_inj s₁ hs₁ (hvals i)
    rw [hσ]

private lemma corner_tri_iff {q : ℕ} {G : SimpleGraph (Fin q)} (hG : G.LocallyLinear)
    {a₁ a₂ b₁ b₂ c₁ c₂ : Fin q} :
    (Tri G a₁ b₁ c₁ ∧ Tri G a₂ b₁ c₂ ∧ Tri G a₁ b₂ c₂) ↔
      (Tri G a₁ b₁ c₁ ∧ a₁ = a₂ ∧ b₁ = b₂ ∧ c₁ = c₂) := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    have htri : Tri G a₁ b₁ c₂ := ⟨h1.1, h3.2.1, h2.2.2⟩
    have hc : c₁ = c₂ := tri_edge_unique hG h1 htri
    have h2' : Tri G b₁ c₂ a₂ := ⟨h2.2.2, h2.1.symm, h2.2.1.symm⟩
    have htri' : Tri G b₁ c₂ a₁ := ⟨htri.2.2, htri.1.symm, htri.2.1.symm⟩
    have ha : a₂ = a₁ := tri_edge_unique hG h2' htri'
    have h3' : Tri G a₁ c₂ b₂ := ⟨h3.2.1, h3.1, h3.2.2.symm⟩
    have htri'' : Tri G a₁ c₂ b₁ := ⟨htri.2.1, htri.1, htri.2.2.symm⟩
    have hb : b₂ = b₁ := tri_edge_unique hG h3' htri''
    exact ⟨h1, ha.symm, hb.symm, hc⟩
  · rintro ⟨h1, rfl, rfl, rfl⟩
    exact ⟨h1, h1, h1⟩

private def setA {n q : ℕ} (G : SimpleGraph (Fin q)) [DecidableRel G.Adj]
    (ω : (𝔽₂ n → Fin q) × (𝔽₂ n → Fin q) × (𝔽₂ n → Fin q)) : Finset (𝔽₂ n × 𝔽₂ n) :=
  univ.filter fun p => Tri G (ω.1 p.1) (ω.2.1 p.2) (ω.2.2 (p.1 + p.2))

private lemma mem_S_iff {n q : ℕ} (G : SimpleGraph (Fin q)) [DecidableRel G.Adj]
    (hG : G.LocallyLinear) (ω : (𝔽₂ n → Fin q) × (𝔽₂ n → Fin q) × (𝔽₂ n → Fin q))
    (d x y : 𝔽₂ n) :
    (x, y) ∈ Green19.S d (setA G ω) ↔
      Tri G (ω.1 x) (ω.2.1 y) (ω.2.2 (x + y)) ∧
      ω.1 x = ω.1 (x + d) ∧ ω.2.1 y = ω.2.1 (y + d) ∧ ω.2.2 (x + y) = ω.2.2 (x + y + d) := by
  classical
  simp only [Green19.S, mem_filter, mem_univ, true_and, Green19.IsCorner, setA]
  have hxy1 : (x + d) + y = x + y + d := by abel
  have hxy2 : x + (y + d) = x + y + d := by abel
  rw [hxy1, hxy2]
  exact corner_tri_iff hG

/-- Split a function `V → Fin q` into its restriction on `S` and on `Sᶜ`. -/
private def splitFun {V : Type*} [Fintype V] [DecidableEq V] {q : ℕ} (S : Finset V) :
    (V → Fin q) ≃ (↥S → Fin q) × ({x : V // x ∉ S} → Fin q) where
  toFun f := (fun x => f x.1, fun x => f x.1)
  invFun p x := if h : x ∈ S then p.1 ⟨x, h⟩ else p.2 ⟨x, h⟩
  left_inv f := by funext x; dsimp; split_ifs <;> rfl
  right_inv p := by
    rcases p with ⟨p1, p2⟩
    refine Prod.ext (funext fun x => ?_) (funext fun x => ?_) <;> simp [x.2]

private lemma sum_split_prod {V : Type*} [Fintype V] [DecidableEq V] {q : ℕ}
    (S₁ S₂ S₃ : Finset V) (F : (↥S₁ → Fin q) × (↥S₂ → Fin q) × (↥S₃ → Fin q) → ℝ)
    (H : ({x : V // x ∉ S₁} → Fin q) × ({x : V // x ∉ S₂} → Fin q) × ({x : V // x ∉ S₃} → Fin q) → ℝ) :
    (∑ ω : (V → Fin q) × (V → Fin q) × (V → Fin q),
      F (fun x => ω.1 x.1, fun y => ω.2.1 y.1, fun z => ω.2.2 z.1) *
      H (fun x => ω.1 x.1, fun y => ω.2.1 y.1, fun z => ω.2.2 z.1)) =
    (∑ a : (↥S₁ → Fin q) × (↥S₂ → Fin q) × (↥S₃ → Fin q), F a) *
    (∑ b : ({x : V // x ∉ S₁} → Fin q) × ({x : V // x ∉ S₂} → Fin q) × ({x : V // x ∉ S₃} → Fin q), H b) := by
  let e : ((V → Fin q) × (V → Fin q) × (V → Fin q)) ≃
      ((↥S₁ → Fin q) × (↥S₂ → Fin q) × (↥S₃ → Fin q)) ×
      (({x : V // x ∉ S₁} → Fin q) × ({x : V // x ∉ S₂} → Fin q) × ({x : V // x ∉ S₃} → Fin q)) :=
    { toFun := fun ω =>
        ((fun x => ω.1 x.1, fun y => ω.2.1 y.1, fun z => ω.2.2 z.1),
         (fun x => ω.1 x.1, fun y => ω.2.1 y.1, fun z => ω.2.2 z.1))
      invFun := fun p =>
        ((splitFun S₁).symm (p.1.1, p.2.1),
         (splitFun S₂).symm (p.1.2.1, p.2.2.1),
         (splitFun S₃).symm (p.1.2.2, p.2.2.2))
      left_inv := fun ω => by
        rcases ω with ⟨f, g, h⟩
        refine Prod.ext (funext fun x => ?_) (Prod.ext (funext fun y => ?_) (funext fun z => ?_)) <;>
          dsimp [splitFun] <;> split_ifs <;> rfl
      right_inv := fun p => by
        rcases p with ⟨⟨f1, g1, h1⟩, ⟨f2, g2, h2⟩⟩
        refine Prod.ext
          (Prod.ext (funext fun x => ?_) (Prod.ext (funext fun y => ?_) (funext fun z => ?_)))
          (Prod.ext (funext fun x => ?_) (Prod.ext (funext fun y => ?_) (funext fun z => ?_)))
        · exact congrFun (congrArg Prod.fst ((splitFun S₁).right_inv (f1, f2))) x
        · exact congrFun (congrArg Prod.fst ((splitFun S₂).right_inv (g1, g2))) y
        · exact congrFun (congrArg Prod.fst ((splitFun S₃).right_inv (h1, h2))) z
        · exact congrFun (congrArg Prod.snd ((splitFun S₁).right_inv (f1, f2))) x
        · exact congrFun (congrArg Prod.snd ((splitFun S₂).right_inv (g1, g2))) y
        · exact congrFun (congrArg Prod.snd ((splitFun S₃).right_inv (h1, h2))) z }
  change (∑ ω : (V → Fin q) × (V → Fin q) × (V → Fin q), F (e ω).1 * H (e ω).2) = _
  rw [Equiv.sum_comp e (fun p => F p.1 * H p.2), Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]

private lemma singleton_inner_sum_A {n q : ℕ} (hq : 0 < q) (G : SimpleGraph (Fin q))
    [DecidableRel G.Adj] (x y : 𝔽₂ n) :
    (∑ a : (↥({x} : Finset (𝔽₂ n)) → Fin q) × (↥({y} : Finset (𝔽₂ n)) → Fin q) ×
        (↥({x + y} : Finset (𝔽₂ n)) → Fin q),
      ((if Tri G (a.1 ⟨x, mem_singleton_self x⟩) (a.2.1 ⟨y, mem_singleton_self y⟩)
          (a.2.2 ⟨x + y, mem_singleton_self (x + y)⟩) then (1 : ℝ) else 0) -
        ((triSet G).card : ℝ) / (q : ℝ) ^ 3)) = 0 := by
  let e : ((↥({x} : Finset (𝔽₂ n)) → Fin q) × (↥({y} : Finset (𝔽₂ n)) → Fin q) ×
      (↥({x + y} : Finset (𝔽₂ n)) → Fin q)) ≃ Fin q × Fin q × Fin q :=
    { toFun := fun a =>
        (a.1 ⟨x, mem_singleton_self x⟩, a.2.1 ⟨y, mem_singleton_self y⟩,
          a.2.2 ⟨x + y, mem_singleton_self (x + y)⟩)
      invFun := fun t => (fun _ => t.1, fun _ => t.2.1, fun _ => t.2.2)
      left_inv := fun a => by
        rcases a with ⟨a1, a2, a3⟩
        ext ⟨z, hz⟩ <;> simp only [mem_singleton] at hz <;> subst hz <;> rfl
      right_inv := fun t => by rcases t with ⟨a, b, c⟩; rfl }
  rw [← Equiv.sum_comp e.symm]
  simp only [e, Equiv.coe_fn_symm_mk, sum_sub_distrib, sum_const, card_univ, Fintype.card_prod,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul]
  have h1 : (∑ t : Fin q × Fin q × Fin q, if Tri G t.1 t.2.1 t.2.2 then (1 : ℝ) else 0) =
      ((triSet G).card : ℝ) := by
    have hcard : ((triSet G).card : ℝ) =
        ∑ t : Fin q × Fin q × Fin q, if Tri G t.1 t.2.1 t.2.2 then (1 : ℝ) else 0 := by
      unfold triSet
      rw [Finset.card_filter, Nat.cast_sum]
      simp
    exact hcard.symm
  rw [h1]
  have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  field_simp [hq0]
  ring

private lemma pair_inner_sum_S {n q : ℕ} (hq : 0 < q) (G : SimpleGraph (Fin q))
    [DecidableRel G.Adj] {d : 𝔽₂ n} (hd : d ≠ 0) (x y : 𝔽₂ n) :
    (∑ a : (↥({x, x + d} : Finset (𝔽₂ n)) → Fin q) ×
        (↥({y, y + d} : Finset (𝔽₂ n)) → Fin q) ×
        (↥({x + y, x + y + d} : Finset (𝔽₂ n)) → Fin q),
      ((if Tri G (a.1 ⟨x, by simp⟩) (a.2.1 ⟨y, by simp⟩) (a.2.2 ⟨x + y, by simp⟩) ∧
            a.1 ⟨x, by simp⟩ = a.1 ⟨x + d, by simp⟩ ∧
            a.2.1 ⟨y, by simp⟩ = a.2.1 ⟨y + d, by simp⟩ ∧
            a.2.2 ⟨x + y, by simp⟩ = a.2.2 ⟨x + y + d, by simp⟩
          then (1 : ℝ) else 0) -
        ((triSet G).card : ℝ) / (q : ℝ) ^ 6)) = 0 := by
  have hx : x ≠ x + d := fun h => hd (by simpa [← add_assoc, f2_add_self] using congrArg (x + ·) h.symm)
  have hy : y ≠ y + d := fun h => hd (by simpa [← add_assoc, f2_add_self] using congrArg (y + ·) h.symm)
  have hxy : x + y ≠ x + y + d := fun h =>
    hd (by simpa [← add_assoc, f2_add_self] using congrArg ((x + y) + ·) h.symm)
  let e : ((↥({x, x + d} : Finset (𝔽₂ n)) → Fin q) ×
      (↥({y, y + d} : Finset (𝔽₂ n)) → Fin q) ×
      (↥({x + y, x + y + d} : Finset (𝔽₂ n)) → Fin q)) ≃
      (Fin q × Fin q) × ((Fin q × Fin q) × (Fin q × Fin q)) :=
    { toFun := fun a =>
        ((a.1 ⟨x, by simp⟩, a.1 ⟨x + d, by simp⟩),
         ((a.2.1 ⟨y, by simp⟩, a.2.1 ⟨y + d, by simp⟩),
          (a.2.2 ⟨x + y, by simp⟩, a.2.2 ⟨x + y + d, by simp⟩)))
      invFun := fun p =>
        (fun z => if z.1 = x then p.1.1 else p.1.2,
         fun z => if z.1 = y then p.2.1.1 else p.2.1.2,
         fun z => if z.1 = x + y then p.2.2.1 else p.2.2.2)
      left_inv := fun a => by
        rcases a with ⟨a1, a2, a3⟩
        ext ⟨z, hz⟩ <;> simp only [mem_insert, mem_singleton] at hz <;>
          rcases hz with rfl | rfl <;> simp [hx.symm, hy.symm, hxy.symm]
      right_inv := fun p => by
        rcases p with ⟨⟨a1, a2⟩, ⟨b1, b2⟩, ⟨c1, c2⟩⟩
        ext <;> simp [hx.symm, hy.symm, hxy.symm] }
  rw [← Equiv.sum_comp e.symm]
  simp only [e, Equiv.coe_fn_symm_mk, ↓reduceIte, hx.symm, hy.symm, hxy.symm,
    sum_sub_distrib, sum_const, card_univ, Fintype.card_prod, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_mul]
  have h1 : (∑ p : (Fin q × Fin q) × ((Fin q × Fin q) × (Fin q × Fin q)),
      if Tri G p.1.1 p.2.1.1 p.2.2.1 ∧ p.1.1 = p.1.2 ∧ p.2.1.1 = p.2.1.2 ∧ p.2.2.1 = p.2.2.2
      then (1 : ℝ) else 0) = ((triSet G).card : ℝ) := by
    have hcard : (((univ.filter fun p : (Fin q × Fin q) × ((Fin q × Fin q) × (Fin q × Fin q)) =>
        Tri G p.1.1 p.2.1.1 p.2.2.1 ∧ p.1.1 = p.1.2 ∧ p.2.1.1 = p.2.1.2 ∧
        p.2.2.1 = p.2.2.2).card : ℕ) : ℝ) =
        ∑ p : (Fin q × Fin q) × ((Fin q × Fin q) × (Fin q × Fin q)),
          if Tri G p.1.1 p.2.1.1 p.2.2.1 ∧ p.1.1 = p.1.2 ∧ p.2.1.1 = p.2.1.2 ∧ p.2.2.1 = p.2.2.2
          then (1 : ℝ) else 0 := by
      rw [Finset.card_filter, Nat.cast_sum]
      simp
    rw [← hcard]
    congr 1
    refine Finset.card_bij (fun p _ => (p.1.1, p.2.1.1, p.2.2.1)) ?_ ?_ ?_
    · intro p hp
      simp only [mem_filter, mem_univ, true_and] at hp
      simp [triSet, hp.1]
    · intro p₁ hp₁ p₂ hp₂ heq
      simp only [mem_filter, mem_univ, true_and] at hp₁ hp₂
      rcases p₁ with ⟨⟨a₁, a₁'⟩, ⟨⟨b₁, b₁'⟩, ⟨c₁, c₁'⟩⟩⟩
      rcases p₂ with ⟨⟨a₂, a₂'⟩, ⟨⟨b₂, b₂'⟩, ⟨c₂, c₂'⟩⟩⟩
      dsimp at hp₁ hp₂ heq
      obtain ⟨rfl, rfl, rfl⟩ := hp₁.2
      obtain ⟨rfl, rfl, rfl⟩ := hp₂.2
      have ha : a₁ = a₂ := congrArg Prod.fst heq
      have hb : b₁ = b₂ := congrArg (fun x => x.2.1) heq
      have hc : c₁ = c₂ := congrArg (fun x => x.2.2) heq
      subst ha hb hc
      rfl
    · intro t ht
      simp only [triSet, mem_filter, mem_univ, true_and] at ht
      exact ⟨((t.1, t.1), ((t.2.1, t.2.1), (t.2.2, t.2.2))),
        by simp [mem_filter, ht], rfl⟩
  rw [h1]
  have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  field_simp [hq0]
  ring

private def ClashA {n : ℕ} (u v : 𝔽₂ n × 𝔽₂ n) : Prop :=
  u.1 = v.1 ∨ u.2 = v.2 ∨ u.1 + u.2 = v.1 + v.2

private instance {n : ℕ} (u v : 𝔽₂ n × 𝔽₂ n) : Decidable (ClashA u v) :=
  inferInstanceAs (Decidable (u.1 = v.1 ∨ u.2 = v.2 ∨ u.1 + u.2 = v.1 + v.2))

private def ClashS {n : ℕ} (d : 𝔽₂ n) (u v : 𝔽₂ n × 𝔽₂ n) : Prop :=
  u.1 = v.1 ∨ u.1 = v.1 + d ∨ u.2 = v.2 ∨ u.2 = v.2 + d ∨
    u.1 + u.2 = v.1 + v.2 ∨ u.1 + u.2 = v.1 + v.2 + d

private instance {n : ℕ} (d : 𝔽₂ n) (u v : 𝔽₂ n × 𝔽₂ n) : Decidable (ClashS d u v) :=
  inferInstanceAs (Decidable (u.1 = v.1 ∨ u.1 = v.1 + d ∨ u.2 = v.2 ∨ u.2 = v.2 + d ∨
    u.1 + u.2 = v.1 + v.2 ∨ u.1 + u.2 = v.1 + v.2 + d))

private lemma clashA_symm {n : ℕ} {u v : 𝔽₂ n × 𝔽₂ n} (h : ClashA u v) : ClashA v u := by
  rcases h with h | h | h <;> [exact Or.inl h.symm; exact Or.inr (Or.inl h.symm); exact Or.inr (Or.inr h.symm)]

private lemma clashS_symm {n : ℕ} {d : 𝔽₂ n} {u v : 𝔽₂ n × 𝔽₂ n} (h : ClashS d u v) :
    ClashS d v u := by
  rcases h with h | h | h | h | h | h
  · exact Or.inl h.symm
  · exact Or.inr (Or.inl ((f2_eq_add_iff _ _ _).mp h.symm))
  · exact Or.inr (Or.inr (Or.inl h.symm))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ((f2_eq_add_iff _ _ _).mp h.symm))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h.symm))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ((f2_eq_add_iff _ _ _).mp h.symm)))))

private lemma card_fiber_fst {n : ℕ} (a : 𝔽₂ n) :
    (univ.filter fun v : 𝔽₂ n × 𝔽₂ n => v.1 = a).card = Fintype.card (𝔽₂ n) := by
  rw [← Fintype.card_coe]
  refine Fintype.card_congr
    { toFun := fun ⟨v, _⟩ => v.2
      invFun := fun y => ⟨(a, y), by simp⟩
      left_inv := fun ⟨⟨x, y⟩, h⟩ => by
        simp only [mem_filter, mem_univ, true_and] at h
        subst h
        rfl
      right_inv := fun y => rfl }

private lemma card_fiber_snd {n : ℕ} (b : 𝔽₂ n) :
    (univ.filter fun v : 𝔽₂ n × 𝔽₂ n => v.2 = b).card = Fintype.card (𝔽₂ n) := by
  rw [← Fintype.card_coe]
  refine Fintype.card_congr
    { toFun := fun ⟨v, _⟩ => v.1
      invFun := fun x => ⟨(x, b), by simp⟩
      left_inv := fun ⟨⟨x, y⟩, h⟩ => by
        simp only [mem_filter, mem_univ, true_and] at h
        subst h
        rfl
      right_inv := fun x => rfl }

private lemma card_fiber_sum {n : ℕ} (c : 𝔽₂ n) :
    (univ.filter fun v : 𝔽₂ n × 𝔽₂ n => v.1 + v.2 = c).card = Fintype.card (𝔽₂ n) := by
  rw [← Fintype.card_coe]
  refine Fintype.card_congr
    { toFun := fun ⟨v, _⟩ => v.1
      invFun := fun x => ⟨(x, x + c), by simp [← add_assoc, f2_add_self]⟩
      left_inv := fun ⟨⟨x, y⟩, h⟩ => by
        simp only [mem_filter, mem_univ, true_and] at h
        have hy : y = x + c := by
          rw [← h, ← add_assoc, f2_add_self, zero_add]
        subst hy
        rfl
      right_inv := fun x => rfl }

private lemma card_clashA_le {n : ℕ} (u : 𝔽₂ n × 𝔽₂ n) :
    (univ.filter fun v => ClashA u v).card ≤ 3 * Fintype.card (𝔽₂ n) := by
  have hsub : (univ.filter fun v => ClashA u v) ⊆
      (univ.filter fun v : 𝔽₂ n × 𝔽₂ n => v.1 = u.1) ∪
      ((univ.filter fun v : 𝔽₂ n × 𝔽₂ n => v.2 = u.2) ∪
       (univ.filter fun v : 𝔽₂ n × 𝔽₂ n => v.1 + v.2 = u.1 + u.2)) := by
    intro v hv
    have hv' : ClashA u v := (mem_filter.mp hv).2
    simp only [mem_union, mem_filter, mem_univ, true_and]
    rcases hv' with h | h | h <;> [exact Or.inl h.symm; exact Or.inr (Or.inl h.symm); exact Or.inr (Or.inr h.symm)]
  calc (univ.filter fun v => ClashA u v).card
      ≤ ((univ.filter fun v : 𝔽₂ n × 𝔽₂ n => v.1 = u.1) ∪
          ((univ.filter fun v : 𝔽₂ n × 𝔽₂ n => v.2 = u.2) ∪
           (univ.filter fun v : 𝔽₂ n × 𝔽₂ n => v.1 + v.2 = u.1 + u.2))).card :=
        Finset.card_le_card hsub
    _ ≤ (univ.filter fun v : 𝔽₂ n × 𝔽₂ n => v.1 = u.1).card +
          ((univ.filter fun v : 𝔽₂ n × 𝔽₂ n => v.2 = u.2).card +
           (univ.filter fun v : 𝔽₂ n × 𝔽₂ n => v.1 + v.2 = u.1 + u.2).card) :=
        (card_union_le _ _).trans (Nat.add_le_add_left (card_union_le _ _) _)
    _ = 3 * Fintype.card (𝔽₂ n) := by
        rw [card_fiber_fst, card_fiber_snd, card_fiber_sum]; omega

private lemma card_clashS_le {n : ℕ} (d : 𝔽₂ n) (u : 𝔽₂ n × 𝔽₂ n) :
    (univ.filter fun v => ClashS d u v).card ≤ 6 * Fintype.card (𝔽₂ n) := by
  let A1 := univ.filter fun v : 𝔽₂ n × 𝔽₂ n => v.1 = u.1
  let A2 := univ.filter fun v : 𝔽₂ n × 𝔽₂ n => v.1 = u.1 + d
  let A3 := univ.filter fun v : 𝔽₂ n × 𝔽₂ n => v.2 = u.2
  let A4 := univ.filter fun v : 𝔽₂ n × 𝔽₂ n => v.2 = u.2 + d
  let A5 := univ.filter fun v : 𝔽₂ n × 𝔽₂ n => v.1 + v.2 = u.1 + u.2
  let A6 := univ.filter fun v : 𝔽₂ n × 𝔽₂ n => v.1 + v.2 = u.1 + u.2 + d
  have hsub : (univ.filter fun v => ClashS d u v) ⊆
      A1 ∪ (A2 ∪ (A3 ∪ (A4 ∪ (A5 ∪ A6)))) := by
    intro v hv
    have hv' : ClashS d u v := (mem_filter.mp hv).2
    simp only [mem_union, A1, A2, A3, A4, A5, A6, mem_filter, mem_univ, true_and]
    rcases hv' with h | h | h | h | h | h
    · exact Or.inl h.symm
    · exact Or.inr (Or.inl ((f2_eq_add_iff _ _ _).mp h.symm))
    · exact Or.inr (Or.inr (Or.inl h.symm))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ((f2_eq_add_iff _ _ _).mp h.symm))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h.symm))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ((f2_eq_add_iff _ _ _).mp h.symm)))))
  have hb : (A1 ∪ (A2 ∪ (A3 ∪ (A4 ∪ (A5 ∪ A6))))).card ≤
      A1.card + A2.card + A3.card + A4.card + A5.card + A6.card := by
    have c1 := card_union_le A1 (A2 ∪ (A3 ∪ (A4 ∪ (A5 ∪ A6))))
    have c2 := card_union_le A2 (A3 ∪ (A4 ∪ (A5 ∪ A6)))
    have c3 := card_union_le A3 (A4 ∪ (A5 ∪ A6))
    have c4 := card_union_le A4 (A5 ∪ A6)
    have c5 := card_union_le A5 A6
    omega
  refine (Finset.card_le_card hsub).trans (hb.trans ?_)
  dsimp [A1, A2, A3, A4, A5, A6]
  rw [card_fiber_fst, card_fiber_fst, card_fiber_snd, card_fiber_snd, card_fiber_sum, card_fiber_sum]
  omega

private lemma graph4_cover {R : Fin 4 → Fin 4 → Prop} (hsym : ∀ i j, R i j → R j i)
    (hdeg : ∀ i : Fin 4, ∃ j : Fin 4, j ≠ i ∧ R i j) :
    (R 0 1 ∧ R 2 3) ∨ (R 0 2 ∧ R 1 3) ∨ (R 0 3 ∧ R 1 2) ∨
    (∃ i : Fin 4, ∀ j : Fin 4, j ≠ i → R i j) := by
  have edge_cases : ∀ i : Fin 4,
      (i = 0 → R 0 1 ∨ R 0 2 ∨ R 0 3) ∧
      (i = 1 → R 1 0 ∨ R 1 2 ∨ R 1 3) ∧
      (i = 2 → R 2 0 ∨ R 2 1 ∨ R 2 3) ∧
      (i = 3 → R 3 0 ∨ R 3 1 ∨ R 3 2) := by
    intro i
    obtain ⟨j, hj, hr⟩ := hdeg i
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rintro rfl <;> fin_cases j <;> simp_all
  have d0 := (edge_cases 0).1 rfl
  have d1 := (edge_cases 1).2.1 rfl
  have d2 := (edge_cases 2).2.2.1 rfl
  have d3 := (edge_cases 3).2.2.2 rfl
  by_cases m1 : R 0 1 ∧ R 2 3
  · exact Or.inl m1
  by_cases m2 : R 0 2 ∧ R 1 3
  · exact Or.inr (Or.inl m2)
  by_cases m3 : R 0 3 ∧ R 1 2
  · exact Or.inr (Or.inr (Or.inl m3))
  refine Or.inr (Or.inr (Or.inr ?_))
  by_cases h01 : R 0 1
  · have hn23 : ¬ R 2 3 := fun h => m1 ⟨h01, h⟩
    rcases d2 with h20 | h21 | h23
    · have h02 : R 0 2 := hsym _ _ h20
      have hn13 : ¬ R 1 3 := fun h => m2 ⟨h02, h⟩
      have hn31 : ¬ R 3 1 := fun h => hn13 (hsym _ _ h)
      have hn32 : ¬ R 3 2 := fun h => hn23 (hsym _ _ h)
      have h30 : R 3 0 := by rcases d3 with h | h | h; exact h; exact absurd h hn31; exact absurd h hn32
      refine ⟨0, fun j hj => ?_⟩
      fin_cases j
      · exact absurd rfl hj
      · exact h01
      · exact h02
      · exact hsym _ _ h30
    · have h12 : R 1 2 := hsym _ _ h21
      have hn03 : ¬ R 0 3 := fun h => m3 ⟨h, h12⟩
      have hn30 : ¬ R 3 0 := fun h => hn03 (hsym _ _ h)
      have hn32 : ¬ R 3 2 := fun h => hn23 (hsym _ _ h)
      have h31 : R 3 1 := by rcases d3 with h | h | h; exact absurd h hn30; exact h; exact absurd h hn32
      refine ⟨1, fun j hj => ?_⟩
      fin_cases j
      · exact hsym _ _ h01
      · exact absurd rfl hj
      · exact h12
      · exact hsym _ _ h31
    · exact absurd h23 hn23
  · have hn10 : ¬ R 1 0 := fun h => h01 (hsym _ _ h)
    by_cases h02 : R 0 2
    · have hn13 : ¬ R 1 3 := fun h => m2 ⟨h02, h⟩
      have h12 : R 1 2 := by rcases d1 with h | h | h; exact absurd h hn10; exact h; exact absurd h hn13
      have hn03 : ¬ R 0 3 := fun h => m3 ⟨h, h12⟩
      have hn30 : ¬ R 3 0 := fun h => hn03 (hsym _ _ h)
      have hn31 : ¬ R 3 1 := fun h => hn13 (hsym _ _ h)
      have h32 : R 3 2 := by rcases d3 with h | h | h; exact absurd h hn30; exact absurd h hn31; exact h
      refine ⟨2, fun j hj => ?_⟩
      fin_cases j
      · exact hsym _ _ h02
      · exact hsym _ _ h12
      · exact absurd rfl hj
      · exact hsym _ _ h32
    · have h03 : R 0 3 := by rcases d0 with h | h | h; exact absurd h h01; exact absurd h h02; exact h
      have hn12 : ¬ R 1 2 := fun h => m3 ⟨h03, h⟩
      have h13 : R 1 3 := by rcases d1 with h | h | h; exact absurd h hn10; exact absurd h hn12; exact h
      have hn20 : ¬ R 2 0 := fun h => h02 (hsym _ _ h)
      have hn21 : ¬ R 2 1 := fun h => hn12 (hsym _ _ h)
      have h23 : R 2 3 := by rcases d2 with h | h | h; exact absurd h hn20; exact absurd h hn21; exact h
      refine ⟨3, fun j hj => ?_⟩
      fin_cases j
      · exact hsym _ _ h03
      · exact hsym _ _ h13
      · exact hsym _ _ h23
      · exact absurd rfl hj

private lemma sum_YA_zero_if_disjoint {n q : ℕ} (hq : 0 < q) (G : SimpleGraph (Fin q))
    [DecidableRel G.Adj] (u₁ u₂ : 𝔽₂ n × 𝔽₂ n) (hdisj : ¬ ClashA u₁ u₂) :
    let pA : ℝ := ((triSet G).card : ℝ) / (q : ℝ) ^ 3
    let YA := fun (u : 𝔽₂ n × 𝔽₂ n) (ω : (𝔽₂ n → Fin q) × (𝔽₂ n → Fin q) × (𝔽₂ n → Fin q)) =>
      (if Tri G (ω.1 u.1) (ω.2.1 u.2) (ω.2.2 (u.1 + u.2)) then (1 : ℝ) else 0) - pA
    (∑ ω : (𝔽₂ n → Fin q) × (𝔽₂ n → Fin q) × (𝔽₂ n → Fin q), YA u₁ ω * YA u₂ ω) = 0 := by
  intro pA YA
  simp only [ClashA, not_or] at hdisj
  let S₁ : Finset (𝔽₂ n) := {u₁.1}
  let S₂ : Finset (𝔽₂ n) := {u₁.2}
  let S₃ : Finset (𝔽₂ n) := {u₁.1 + u₁.2}
  have hu2_1 : u₂.1 ∉ S₁ := by simp [S₁, Ne.symm hdisj.1]
  have hu2_2 : u₂.2 ∉ S₂ := by simp [S₂, Ne.symm hdisj.2.1]
  have hu2_3 : u₂.1 + u₂.2 ∉ S₃ := by simp [S₃, Ne.symm hdisj.2.2]
  let F : (↥S₁ → Fin q) × (↥S₂ → Fin q) × (↥S₃ → Fin q) → ℝ := fun a =>
    (if Tri G (a.1 ⟨u₁.1, mem_singleton_self u₁.1⟩)
        (a.2.1 ⟨u₁.2, mem_singleton_self u₁.2⟩)
        (a.2.2 ⟨u₁.1 + u₁.2, mem_singleton_self (u₁.1 + u₁.2)⟩) then (1 : ℝ) else 0) - pA
  let H : ({x : 𝔽₂ n // x ∉ S₁} → Fin q) × ({x : 𝔽₂ n // x ∉ S₂} → Fin q) ×
      ({x : 𝔽₂ n // x ∉ S₃} → Fin q) → ℝ := fun b =>
    (if Tri G (b.1 ⟨u₂.1, hu2_1⟩) (b.2.1 ⟨u₂.2, hu2_2⟩)
        (b.2.2 ⟨u₂.1 + u₂.2, hu2_3⟩) then (1 : ℝ) else 0) - pA
  have hfac := sum_split_prod S₁ S₂ S₃ F H
  have heq : (∑ ω : (𝔽₂ n → Fin q) × (𝔽₂ n → Fin q) × (𝔽₂ n → Fin q), YA u₁ ω * YA u₂ ω) =
      (∑ a, F a) * (∑ b, H b) := hfac
  rw [heq, singleton_inner_sum_A hq G u₁.1 u₁.2, zero_mul]

private lemma not_mem_pair {n : ℕ} {a b d : 𝔽₂ n} (h1 : a ≠ b) (h2 : a ≠ b + d) :
    b ∉ ({a, a + d} : Finset (𝔽₂ n)) ∧ b + d ∉ ({a, a + d} : Finset (𝔽₂ n)) := by
  simp only [mem_insert, mem_singleton, not_or]
  refine ⟨⟨h1.symm, fun h => h2 ((f2_eq_add_iff _ _ _).mp h.symm)⟩,
          ⟨fun h => h2 h.symm, fun h => h1 (by simpa [add_assoc, f2_add_self] using congrArg (· + d) h.symm)⟩⟩

private lemma sum_YS_zero_if_isolated {n q : ℕ} (hq : 0 < q) (G : SimpleGraph (Fin q))
    [DecidableRel G.Adj] {d : 𝔽₂ n} (hd : d ≠ 0) (u : Fin 4 → 𝔽₂ n × 𝔽₂ n)
    (i : Fin 4) (hiso : ∀ j : Fin 4, j ≠ i → ¬ ClashS d (u i) (u j)) :
    let pS : ℝ := ((triSet G).card : ℝ) / (q : ℝ) ^ 6
    let YS := fun (v : 𝔽₂ n × 𝔽₂ n) (ω : (𝔽₂ n → Fin q) × (𝔽₂ n → Fin q) × (𝔽₂ n → Fin q)) =>
      (if Tri G (ω.1 v.1) (ω.2.1 v.2) (ω.2.2 (v.1 + v.2)) ∧
            ω.1 v.1 = ω.1 (v.1 + d) ∧ ω.2.1 v.2 = ω.2.1 (v.2 + d) ∧
            ω.2.2 (v.1 + v.2) = ω.2.2 (v.1 + v.2 + d)
          then (1 : ℝ) else 0) - pS
    (∑ ω : (𝔽₂ n → Fin q) × (𝔽₂ n → Fin q) × (𝔽₂ n → Fin q),
      YS (u 0) ω * YS (u 1) ω * YS (u 2) ω * YS (u 3) ω) = 0 := by
  intro pS YS
  let S₁ : Finset (𝔽₂ n) := {(u i).1, (u i).1 + d}
  let S₂ : Finset (𝔽₂ n) := {(u i).2, (u i).2 + d}
  let S₃ : Finset (𝔽₂ n) := {(u i).1 + (u i).2, (u i).1 + (u i).2 + d}
  have hout : ∀ j : Fin 4, j ≠ i →
      (u j).1 ∉ S₁ ∧ (u j).1 + d ∉ S₁ ∧
      (u j).2 ∉ S₂ ∧ (u j).2 + d ∉ S₂ ∧
      (u j).1 + (u j).2 ∉ S₃ ∧ (u j).1 + (u j).2 + d ∉ S₃ := by
    intro j hj
    have hc := hiso j hj
    simp only [ClashS, not_or] at hc
    have p1 := not_mem_pair hc.1 hc.2.1
    have p2 := not_mem_pair hc.2.2.1 hc.2.2.2.1
    have p3 := not_mem_pair hc.2.2.2.2.1 hc.2.2.2.2.2
    exact ⟨p1.1, p1.2, p2.1, p2.2, p3.1, p3.2⟩
  let F : (↥S₁ → Fin q) × (↥S₂ → Fin q) × (↥S₃ → Fin q) → ℝ := fun a =>
    (if Tri G (a.1 ⟨(u i).1, by simp [S₁]⟩)
          (a.2.1 ⟨(u i).2, by simp [S₂]⟩)
          (a.2.2 ⟨(u i).1 + (u i).2, by simp [S₃]⟩) ∧
        a.1 ⟨(u i).1, by simp [S₁]⟩ = a.1 ⟨(u i).1 + d, by simp [S₁]⟩ ∧
        a.2.1 ⟨(u i).2, by simp [S₂]⟩ = a.2.1 ⟨(u i).2 + d, by simp [S₂]⟩ ∧
        a.2.2 ⟨(u i).1 + (u i).2, by simp [S₃]⟩ = a.2.2 ⟨(u i).1 + (u i).2 + d, by simp [S₃]⟩
      then (1 : ℝ) else 0) - pS
  let term_out (j : Fin 4) (hj : j ≠ i)
      (b : ({x : 𝔽₂ n // x ∉ S₁} → Fin q) × ({x : 𝔽₂ n // x ∉ S₂} → Fin q) ×
        ({x : 𝔽₂ n // x ∉ S₃} → Fin q)) : ℝ :=
    let o := hout j hj
    (if Tri G (b.1 ⟨(u j).1, o.1⟩) (b.2.1 ⟨(u j).2, o.2.2.1⟩)
          (b.2.2 ⟨(u j).1 + (u j).2, o.2.2.2.2.1⟩) ∧
        b.1 ⟨(u j).1, o.1⟩ = b.1 ⟨(u j).1 + d, o.2.1⟩ ∧
        b.2.1 ⟨(u j).2, o.2.2.1⟩ = b.2.1 ⟨(u j).2 + d, o.2.2.2.1⟩ ∧
        b.2.2 ⟨(u j).1 + (u j).2, o.2.2.2.2.1⟩ =
          b.2.2 ⟨(u j).1 + (u j).2 + d, o.2.2.2.2.2⟩
      then (1 : ℝ) else 0) - pS
  let H : ({x : 𝔽₂ n // x ∉ S₁} → Fin q) × ({x : 𝔽₂ n // x ∉ S₂} → Fin q) ×
      ({x : 𝔽₂ n // x ∉ S₃} → Fin q) → ℝ := fun b =>
    ∏ j ∈ univ.erase i, if h : j = i then 1 else term_out j h b
  have heq : (∑ ω : (𝔽₂ n → Fin q) × (𝔽₂ n → Fin q) × (𝔽₂ n → Fin q),
      YS (u 0) ω * YS (u 1) ω * YS (u 2) ω * YS (u 3) ω) =
      (∑ ω : (𝔽₂ n → Fin q) × (𝔽₂ n → Fin q) × (𝔽₂ n → Fin q),
        F (fun x => ω.1 x.1, fun y => ω.2.1 y.1, fun z => ω.2.2 z.1) *
        H (fun x => ω.1 x.1, fun y => ω.2.1 y.1, fun z => ω.2.2 z.1)) := by
    refine sum_congr rfl fun ω _ => ?_
    have h4 : YS (u 0) ω * YS (u 1) ω * YS (u 2) ω * YS (u 3) ω =
        ∏ j : Fin 4, YS (u j) ω := by
      simp [Fin.prod_univ_four, mul_assoc]
    rw [h4, ← Finset.mul_prod_erase univ (fun j => YS (u j) ω) (mem_univ i)]
    congr 1
    refine Finset.prod_congr rfl fun j hj => ?_
    have hjne : j ≠ i := (mem_erase.mp hj).1
    simp [hjne, term_out, YS]
  rw [heq, sum_split_prod S₁ S₂ S₃ F H, pair_inner_sum_S hq G hd (u i).1 (u i).2, zero_mul]

private lemma abs_sub_prob_le_one (b : Bool) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    |(if b then (1 : ℝ) else 0) - p| ≤ 1 := by
  cases b <;> dsimp <;> rw [abs_le] <;> constructor <;> linarith

private lemma sum_pow_four_fin4 {α : Type*} [Fintype α] (f : α → ℝ) :
    (∑ x : α, f x) ^ 4 = ∑ u : Fin 4 → α, f (u 0) * f (u 1) * f (u 2) * f (u 3) := by
  have h1 : (∑ x : α, f x) ^ 4 =
      (∑ x : α, f x) * ((∑ y : α, f y) * ((∑ z : α, f z) * (∑ w : α, f w))) := by ring
  let e : (Fin 4 → α) ≃ α × α × α × α :=
    { toFun := fun u => (u 0, u 1, u 2, u 3)
      invFun := fun p i => match i with | 0 => p.1 | 1 => p.2.1 | 2 => p.2.2.1 | 3 => p.2.2.2
      left_inv := fun u => by funext i; fin_cases i <;> rfl
      right_inv := fun p => by rcases p with ⟨a, b, c, d⟩; rfl }
  have h4sum : ∑ p : α × α × α × α, f p.1 * (f p.2.1 * (f p.2.2.1 * f p.2.2.2)) =
      (∑ x : α, f x) ^ 4 := by
    rw [Fintype.sum_prod_type]
    simp_rw [Fintype.sum_prod_type]
    rw [h1]
    simp_rw [Finset.sum_mul_sum, Finset.mul_sum]
  rw [← h4sum, ← Equiv.sum_comp e]
  refine Finset.sum_congr rfl fun u _ => ?_
  simp only [e, Equiv.coe_fn_mk, mul_assoc]

private lemma badA_bound {n q : ℕ} (hq : 1 < q) (G : SimpleGraph (Fin q)) [DecidableRel G.Adj]
    (hG : G.LocallyLinear) (hTpos : 1 ≤ (G.cliqueFinset 3).card) :
    let N : ℝ := Fintype.card (𝔽₂ n)
    let Ω := (𝔽₂ n → Fin q) × (𝔽₂ n → Fin q) × (𝔽₂ n → Fin q)
    let badA : Finset Ω := univ.filter fun ω =>
      ((setA G ω).card : ℝ) < ((G.cliqueFinset 3).card : ℝ) / (q : ℝ) ^ 3 * N ^ 2
    (badA.card : ℝ) ≤ (3 * (q : ℝ) ^ 6 / (25 * N)) * (Fintype.card Ω : ℝ) := by
  classical
  intro N Ω badA
  have : NeZero q := ⟨by omega⟩
  let Nnat : ℕ := Fintype.card (𝔽₂ n)
  have hNpos_nat : 0 < Nnat := Fintype.card_pos
  have hNpos : 0 < N := Nat.cast_pos.mpr hNpos_nat
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (by omega)
  let cardΩ : ℝ := (Fintype.card Ω : ℝ)
  have hcardΩ : 0 < cardΩ := Nat.cast_pos.mpr Fintype.card_pos
  have htri_up : (triSet G).card ≤ q * q := triSet_card_le hq G hG
  have htri_low : 6 * (G.cliqueFinset 3).card ≤ (triSet G).card := six_mul_clique_le_triSet (by omega) G
  let pA : ℝ := ((triSet G).card : ℝ) / (q : ℝ) ^ 3
  have hpA0 : 0 ≤ pA := by positivity
  have hpA1 : pA ≤ 1 := by
    dsimp [pA]
    rw [div_le_one (by positivity)]
    have hq3 : q * q ≤ q ^ 3 := by
      have : q * q * 1 ≤ q * q * q := Nat.mul_le_mul_left _ (by omega)
      simpa [pow_three, mul_assoc] using this
    exact_mod_cast htri_up.trans hq3
  let YA (u : 𝔽₂ n × 𝔽₂ n) (ω : Ω) : ℝ :=
    (if Tri G (ω.1 u.1) (ω.2.1 u.2) (ω.2.2 (u.1 + u.2)) then (1 : ℝ) else 0) - pA
  have hsum_A : ∀ ω : Ω, ((setA G ω).card : ℝ) - pA * N ^ 2 = ∑ u : 𝔽₂ n × 𝔽₂ n, YA u ω := by
    intro ω
    have hcard_u : (univ : Finset (𝔽₂ n × 𝔽₂ n)).card = Nnat ^ 2 := by
      simp [Nnat, Fintype.card_prod, sq]
    have hA_eq : setA G ω = univ.filter (fun u : 𝔽₂ n × 𝔽₂ n =>
        Tri G (ω.1 u.1) (ω.2.1 u.2) (ω.2.2 (u.1 + u.2))) := by
      ext ⟨x, y⟩; rfl
    have hA_sum : ((setA G ω).card : ℝ) =
        ∑ u : 𝔽₂ n × 𝔽₂ n, if Tri G (ω.1 u.1) (ω.2.1 u.2) (ω.2.2 (u.1 + u.2)) then (1 : ℝ) else 0 := by
      rw [hA_eq, Finset.card_filter, Nat.cast_sum]
      simp
    simp only [YA, sum_sub_distrib, sum_const, hcard_u, nsmul_eq_mul, Nat.cast_pow, N, Nnat]
    rw [hA_sum, mul_comm pA]
  have hvar : (∑ ω : Ω, (((setA G ω).card : ℝ) - pA * N ^ 2) ^ 2) ≤ 3 * N ^ 3 * cardΩ := by
    simp_rw [hsum_A, sq, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    have hswap : (∑ x : 𝔽₂ n × 𝔽₂ n, ∑ ω : Ω, ∑ y : 𝔽₂ n × 𝔽₂ n, YA x ω * YA y ω) =
        ∑ x : 𝔽₂ n × 𝔽₂ n, ∑ y : 𝔽₂ n × 𝔽₂ n, ∑ ω : Ω, YA x ω * YA y ω :=
      Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    rw [hswap]
    calc (∑ x : 𝔽₂ n × 𝔽₂ n, ∑ y : 𝔽₂ n × 𝔽₂ n, ∑ ω : Ω, YA x ω * YA y ω)
        = ∑ x : 𝔽₂ n × 𝔽₂ n, ∑ y ∈ univ.filter (ClashA x), ∑ ω : Ω, YA x ω * YA y ω := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [← Finset.sum_filter_add_sum_filter_not univ (ClashA x)]
          have hzero : ∑ y ∈ univ.filter (fun v => ¬ ClashA x v), ∑ ω : Ω, YA x ω * YA y ω = 0 :=
            Finset.sum_eq_zero fun y hy =>
              sum_YA_zero_if_disjoint (by omega) G x y (mem_filter.mp hy).2
          rw [hzero, add_zero]
      _ ≤ ∑ x : 𝔽₂ n × 𝔽₂ n, ∑ _y ∈ univ.filter (ClashA x), cardΩ := by
          refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => ?_
          calc (∑ ω : Ω, YA x ω * YA y ω)
              ≤ ∑ _ω : Ω, (1 : ℝ) := Finset.sum_le_sum fun ω _ => by
                have hx1 : |YA x ω| ≤ 1 := by
                  simpa [YA] using abs_sub_prob_le_one
                    (decide (Tri G (ω.1 x.1) (ω.2.1 x.2) (ω.2.2 (x.1 + x.2)))) hpA0 hpA1
                have hy1 : |YA y ω| ≤ 1 := by
                  simpa [YA] using abs_sub_prob_le_one
                    (decide (Tri G (ω.1 y.1) (ω.2.1 y.2) (ω.2.2 (y.1 + y.2)))) hpA0 hpA1
                exact (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_one₀ hx1 (abs_nonneg _) hy1)
            _ = cardΩ := by simp [cardΩ]
      _ ≤ ∑ _x : 𝔽₂ n × 𝔽₂ n, (3 * N) * cardΩ := by
          refine Finset.sum_le_sum fun x _ => ?_
          simp only [sum_const, nsmul_eq_mul]
          refine mul_le_mul_of_nonneg_right ?_ hcardΩ.le
          dsimp [N]
          exact_mod_cast card_clashA_le x
      _ = 3 * N ^ 3 * cardΩ := by
          simp only [sum_const, card_univ, Fintype.card_prod, nsmul_eq_mul, Nat.cast_mul, N]
          ring
  have hbad_sq : (badA.card : ℝ) * (25 / (q : ℝ) ^ 6 * N ^ 4) ≤ 3 * N ^ 3 * cardΩ := by
    let T := (G.cliqueFinset 3).card
    calc (badA.card : ℝ) * (25 / (q : ℝ) ^ 6 * N ^ 4)
        = ∑ _ω ∈ badA, (5 / (q : ℝ) ^ 3 * N ^ 2) ^ 2 := by
          simp only [sum_const, nsmul_eq_mul]; ring
      _ ≤ ∑ ω ∈ badA, (((setA G ω).card : ℝ) - pA * N ^ 2) ^ 2 := by
          refine Finset.sum_le_sum fun ω hω => ?_
          have hlt : ((setA G ω).card : ℝ) < (T : ℝ) / (q : ℝ) ^ 3 * N ^ 2 := (mem_filter.mp hω).2
          have hpA_min : 6 * (T : ℝ) / (q : ℝ) ^ 3 ≤ pA := by
            dsimp [pA, T]
            refine div_le_div_of_nonneg_right ?_ (by positivity)
            exact_mod_cast htri_low
          have hT1 : (1 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hTpos
          have hgap : 5 / (q : ℝ) ^ 3 * N ^ 2 ≤ pA * N ^ 2 - ((setA G ω).card : ℝ) := by
            have h1 : (T : ℝ) / (q : ℝ) ^ 3 * N ^ 2 + 5 * (T : ℝ) / (q : ℝ) ^ 3 * N ^ 2 ≤ pA * N ^ 2 := by
              have h2 : (T : ℝ) / (q : ℝ) ^ 3 + 5 * (T : ℝ) / (q : ℝ) ^ 3 = 6 * (T : ℝ) / (q : ℝ) ^ 3 := by ring
              nlinarith [sq_nonneg N]
            have h3 : 5 / (q : ℝ) ^ 3 * N ^ 2 ≤ 5 * (T : ℝ) / (q : ℝ) ^ 3 * N ^ 2 := by
              have hle1 : 5 / (q : ℝ) ^ 3 * 1 * N ^ 2 ≤ 5 / (q : ℝ) ^ 3 * (T : ℝ) * N ^ 2 := by gcongr
              have heq1 : 5 / (q : ℝ) ^ 3 * 1 * N ^ 2 = 5 / (q : ℝ) ^ 3 * N ^ 2 := by ring
              have heq2 : 5 / (q : ℝ) ^ 3 * (T : ℝ) * N ^ 2 = 5 * (T : ℝ) / (q : ℝ) ^ 3 * N ^ 2 := by ring
              linarith
            linarith
          rw [← sq_abs (((setA G ω).card : ℝ) - pA * N ^ 2)]
          have habs : 5 / (q : ℝ) ^ 3 * N ^ 2 ≤ |((setA G ω).card : ℝ) - pA * N ^ 2| := by
            rw [abs_sub_comm]
            exact hgap.trans (le_abs_self _)
          exact pow_le_pow_left₀ (by positivity) habs 2
      _ ≤ ∑ ω : Ω, (((setA G ω).card : ℝ) - pA * N ^ 2) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => sq_nonneg _)
      _ ≤ 3 * N ^ 3 * cardΩ := hvar
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  calc (badA.card : ℝ) * (25 * N)
      = ((badA.card : ℝ) * (25 / (q : ℝ) ^ 6 * N ^ 4)) * ((q : ℝ) ^ 6 / N ^ 3) := by
        field_simp [hq0.ne', hNpos.ne']
    _ ≤ (3 * N ^ 3 * cardΩ) * ((q : ℝ) ^ 6 / N ^ 3) :=
        mul_le_mul_of_nonneg_right hbad_sq (by positivity)
    _ = 3 * (q : ℝ) ^ 6 * cardΩ := by field_simp [hNpos.ne']

private lemma good4_card_bound {n : ℕ} (d : 𝔽₂ n) :
    let Nnat : ℕ := Fintype.card (𝔽₂ n)
    let V2 := 𝔽₂ n × 𝔽₂ n
    let good4 : Finset (Fin 4 → V2) := univ.filter fun u =>
      ∀ i : Fin 4, ∃ j : Fin 4, j ≠ i ∧ ClashS d (u i) (u j)
    good4.card ≤ 1000 * Nnat ^ 6 := by
  classical
  intro Nnat V2 good4
  have hNpos_nat : 0 < Nnat := Fintype.card_pos
  let M01 := univ.filter fun u : Fin 4 → V2 => ClashS d (u 0) (u 1) ∧ ClashS d (u 2) (u 3)
  let M02 := univ.filter fun u : Fin 4 → V2 => ClashS d (u 0) (u 2) ∧ ClashS d (u 1) (u 3)
  let M03 := univ.filter fun u : Fin 4 → V2 => ClashS d (u 0) (u 3) ∧ ClashS d (u 1) (u 2)
  let S_star (i : Fin 4) := univ.filter fun u : Fin 4 → V2 => ∀ j : Fin 4, j ≠ i → ClashS d (u i) (u j)
  have hsub : good4 ⊆ M01 ∪ M02 ∪ M03 ∪ S_star 0 ∪ S_star 1 ∪ S_star 2 ∪ S_star 3 := by
    intro u hu
    have hdeg := (mem_filter.mp hu).2
    rcases graph4_cover (fun _ _ h => clashS_symm h) hdeg with
      ⟨h01, h23⟩ | ⟨h02, h13⟩ | ⟨h03, h12⟩ | ⟨i, hi⟩
    · simp only [mem_union, M01, mem_filter, mem_univ, true_and]; exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨h01, h23⟩)))))
    · simp only [mem_union, M02, mem_filter, mem_univ, true_and]; exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨h02, h13⟩)))))
    · simp only [mem_union, M03, mem_filter, mem_univ, true_and]; exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨h03, h12⟩))))
    · fin_cases i
      · simp only [mem_union, S_star, mem_filter, mem_univ, true_and]; exact Or.inl (Or.inl (Or.inl (Or.inr hi)))
      · simp only [mem_union, S_star, mem_filter, mem_univ, true_and]; exact Or.inl (Or.inl (Or.inr hi))
      · simp only [mem_union, S_star, mem_filter, mem_univ, true_and]; exact Or.inl (Or.inr hi)
      · simp only [mem_union, S_star, mem_filter, mem_univ, true_and]; exact Or.inr hi
  have hcard_matching : ∀ (a b c e : Fin 4), a ≠ b → a ≠ c → a ≠ e → b ≠ c → b ≠ e → c ≠ e →
      (univ.filter fun u : Fin 4 → V2 => ClashS d (u a) (u b) ∧ ClashS d (u c) (u e)).card ≤
        (Nnat ^ 2 * (6 * Nnat)) ^ 2 := by
    intro a b c e hab hac hae hbc hbe hce
    let target := (univ.sigma fun x : V2 => univ.filter (ClashS d x)) ×ˢ
                  (univ.sigma fun y : V2 => univ.filter (ClashS d y))
    have hle_t : (univ.filter fun u : Fin 4 → V2 => ClashS d (u a) (u b) ∧ ClashS d (u c) (u e)).card ≤
        target.card := by
      refine Finset.card_le_card_of_injOn (fun u => (⟨u a, u b⟩, ⟨u c, u e⟩)) ?_ ?_
      · intro u hu
        have h := (mem_filter.mp hu).2
        simp [target, h.1, h.2]
      · intro u₁ _ u₂ _ heq
        have ha' : u₁ a = u₂ a := congrArg (fun p => p.1.1) heq
        have hb' : u₁ b = u₂ b := congrArg (fun p => p.1.2) heq
        have hc' : u₁ c = u₂ c := congrArg (fun p => p.2.1) heq
        have he' : u₁ e = u₂ e := congrArg (fun p => p.2.2) heq
        funext k
        have hmem : k ∈ ({a, b, c, e} : Finset (Fin 4)) := by
          have h4 : ({a, b, c, e} : Finset (Fin 4)).card = 4 := by
            rw [card_insert_of_notMem, card_insert_of_notMem, card_insert_of_notMem, card_singleton]
            · simp [hce]
            · simp [hbc, hbe]
            · simp [hab, hac, hae]
          exact eq_univ_of_card _ (by rw [h4, Fintype.card_fin]) ▸ mem_univ k
        simp only [mem_insert, mem_singleton] at hmem
        rcases hmem with rfl | rfl | rfl | rfl <;> assumption
    have htarget_card : target.card ≤ (Nnat ^ 2 * (6 * Nnat)) ^ 2 := by
      have hs : ∀ p : V2 → Finset V2, (∀ x, (p x).card ≤ 6 * Nnat) →
          (univ.sigma p).card ≤ Nnat ^ 2 * (6 * Nnat) := by
        intro p hp
        rw [card_sigma]
        calc ∑ x : V2, (p x).card ≤ ∑ _x : V2, 6 * Nnat := sum_le_sum fun x _ => hp x
          _ = Nnat ^ 2 * (6 * Nnat) := by
            rw [sum_const, card_univ, smul_eq_mul]
            have hV2 : Fintype.card V2 = Nnat ^ 2 := by simp [V2, Nnat, Fintype.card_prod, sq]
            rw [hV2]
      rw [card_product, sq]
      exact Nat.mul_le_mul (hs _ (fun x => card_clashS_le d x)) (hs _ (fun y => card_clashS_le d y))
    exact hle_t.trans htarget_card
  have hcard_star : ∀ i : Fin 4, (S_star i).card ≤ Nnat ^ 2 * (6 * Nnat) ^ 3 := by
    intro i
    let j0 := i.succAbove 0
    let j1 := i.succAbove 1
    let j2 := i.succAbove 2
    have hne0 : j0 ≠ i := Fin.succAbove_ne i 0
    have hne1 : j1 ≠ i := Fin.succAbove_ne i 1
    have hne2 : j2 ≠ i := Fin.succAbove_ne i 2
    let target := univ.sigma fun x : V2 =>
      (univ.filter (ClashS d x)) ×ˢ (univ.filter (ClashS d x)) ×ˢ (univ.filter (ClashS d x))
    have hle_t : (S_star i).card ≤ target.card := by
      refine Finset.card_le_card_of_injOn (fun u => ⟨u i, (u j0, u j1, u j2)⟩) ?_ ?_
      · intro u hu
        have hi := (mem_filter.mp hu).2
        simp [target, hi j0 hne0, hi j1 hne1, hi j2 hne2]
      · intro u₁ _ u₂ _ heq
        have hi' : u₁ i = u₂ i := congrArg Sigma.fst heq
        have hsnd := congrArg Sigma.snd heq
        have h0' : u₁ j0 = u₂ j0 := congrArg Prod.fst hsnd
        have h1' : u₁ j1 = u₂ j1 := congrArg (fun p => p.2.1) hsnd
        have h2' : u₁ j2 = u₂ j2 := congrArg (fun p => p.2.2) hsnd
        funext k
        by_cases hk : k = i
        · rw [hk, hi']
        · obtain ⟨m, hm⟩ := Fin.exists_succAbove_eq hk
          rw [← hm]
          fin_cases m
          · exact h0'
          · exact h1'
          · exact h2'
    have htarget_card : target.card ≤ Nnat ^ 2 * (6 * Nnat) ^ 3 := by
      rw [card_sigma]
      calc ∑ x : V2, ((univ.filter (ClashS d x)) ×ˢ (univ.filter (ClashS d x)) ×ˢ
            (univ.filter (ClashS d x))).card
          ≤ ∑ _x : V2, (6 * Nnat) ^ 3 := by
            refine sum_le_sum fun x _ => ?_
            rw [card_product, card_product]
            have hx := card_clashS_le d x
            have : (6 * Nnat) ^ 3 = (6 * Nnat) * ((6 * Nnat) * (6 * Nnat)) := by ring
            rw [this]
            exact Nat.mul_le_mul hx (Nat.mul_le_mul hx hx)
        _ = Nnat ^ 2 * (6 * Nnat) ^ 3 := by
            rw [sum_const, card_univ, smul_eq_mul]
            have hV2 : Fintype.card V2 = Nnat ^ 2 := by simp [V2, Nnat, Fintype.card_prod, sq]
            rw [hV2]
    exact hle_t.trans htarget_card
  have hM01 := hcard_matching 0 1 2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hM02 := hcard_matching 0 2 1 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hM03 := hcard_matching 0 3 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hS0 := hcard_star 0
  have hS1 := hcard_star 1
  have hS2 := hcard_star 2
  have hS3 := hcard_star 3
  have hcu : good4.card ≤ M01.card + M02.card + M03.card +
      (S_star 0).card + (S_star 1).card + (S_star 2).card + (S_star 3).card := by
    have c1 := Finset.card_le_card hsub
    have c2 := card_union_le (M01 ∪ M02 ∪ M03 ∪ S_star 0 ∪ S_star 1 ∪ S_star 2) (S_star 3)
    have c3 := card_union_le (M01 ∪ M02 ∪ M03 ∪ S_star 0 ∪ S_star 1) (S_star 2)
    have c4 := card_union_le (M01 ∪ M02 ∪ M03 ∪ S_star 0) (S_star 1)
    have c5 := card_union_le (M01 ∪ M02 ∪ M03) (S_star 0)
    have c6 := card_union_le (M01 ∪ M02) M03
    have c7 := card_union_le M01 M02
    omega
  have hM_eq : (Nnat ^ 2 * (6 * Nnat)) ^ 2 = 36 * Nnat ^ 6 := by ring
  have hS_le : Nnat ^ 2 * (6 * Nnat) ^ 3 ≤ 216 * Nnat ^ 6 := by
    have h1 : Nnat ^ 5 ≤ Nnat ^ 6 := Nat.pow_le_pow_right hNpos_nat (by decide)
    calc Nnat ^ 2 * (6 * Nnat) ^ 3 = 216 * Nnat ^ 5 := by ring
      _ ≤ 216 * Nnat ^ 6 := Nat.mul_le_mul_left 216 h1
  dsimp [M01, M02, M03, S_star] at hcu
  linarith

private lemma badS_bound {n q : ℕ} (hq : 1 < q) (G : SimpleGraph (Fin q)) [DecidableRel G.Adj]
    (hG : G.LocallyLinear) (d : 𝔽₂ n) (hd : d ≠ 0) :
    let N : ℝ := Fintype.card (𝔽₂ n)
    let Ω := (𝔽₂ n → Fin q) × (𝔽₂ n → Fin q) × (𝔽₂ n → Fin q)
    let badS : Finset Ω := univ.filter fun ω =>
      (2 / (q : ℝ) ^ 4) * N ^ 2 < ((Green19.S d (setA G ω)).card : ℝ)
    (badS.card : ℝ) ≤ (1000 * (q : ℝ) ^ 16 / N ^ 2) * (Fintype.card Ω : ℝ) := by
  classical
  intro N Ω badS
  have : NeZero q := ⟨by omega⟩
  let Nnat : ℕ := Fintype.card (𝔽₂ n)
  have hNpos_nat : 0 < Nnat := Fintype.card_pos
  have hNpos : 0 < N := Nat.cast_pos.mpr hNpos_nat
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (by omega)
  let cardΩ : ℝ := (Fintype.card Ω : ℝ)
  have hcardΩ : 0 < cardΩ := Nat.cast_pos.mpr Fintype.card_pos
  have htri_up : (triSet G).card ≤ q * q := triSet_card_le hq G hG
  let pS : ℝ := ((triSet G).card : ℝ) / (q : ℝ) ^ 6
  have hpS0 : 0 ≤ pS := by positivity
  have hpS_bound : pS ≤ 1 / (q : ℝ) ^ 4 := by
    dsimp [pS]
    rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul]
    have htriR : ((triSet G).card : ℝ) ≤ (q : ℝ) ^ 2 := by
      have : (triSet G).card ≤ q ^ 2 := by simpa [sq] using htri_up
      exact_mod_cast this
    calc ((triSet G).card : ℝ) * (q : ℝ) ^ 4 ≤ (q : ℝ) ^ 2 * (q : ℝ) ^ 4 :=
          mul_le_mul_of_nonneg_right htriR (by positivity)
      _ = (q : ℝ) ^ 6 := by ring
  have hpS1 : pS ≤ 1 := hpS_bound.trans (by
    rw [div_le_one (by positivity)]
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
    exact one_le_pow₀ hq1)
  let YS (u : 𝔽₂ n × 𝔽₂ n) (ω : Ω) : ℝ :=
    (if Tri G (ω.1 u.1) (ω.2.1 u.2) (ω.2.2 (u.1 + u.2)) ∧
          ω.1 u.1 = ω.1 (u.1 + d) ∧ ω.2.1 u.2 = ω.2.1 (u.2 + d) ∧
          ω.2.2 (u.1 + u.2) = ω.2.2 (u.1 + u.2 + d)
        then (1 : ℝ) else 0) - pS
  have hsum_S : ∀ ω : Ω, ((Green19.S d (setA G ω)).card : ℝ) - pS * N ^ 2 =
      ∑ u : 𝔽₂ n × 𝔽₂ n, YS u ω := by
    intro ω
    have hcard_u : (univ : Finset (𝔽₂ n × 𝔽₂ n)).card = Nnat ^ 2 := by
      simp [Nnat, Fintype.card_prod, sq]
    have hS_eq : Green19.S d (setA G ω) = univ.filter (fun u : 𝔽₂ n × 𝔽₂ n =>
        Tri G (ω.1 u.1) (ω.2.1 u.2) (ω.2.2 (u.1 + u.2)) ∧
          ω.1 u.1 = ω.1 (u.1 + d) ∧ ω.2.1 u.2 = ω.2.1 (u.2 + d) ∧
          ω.2.2 (u.1 + u.2) = ω.2.2 (u.1 + u.2 + d)) := by
      ext ⟨x, y⟩
      simp only [mem_filter, mem_univ, true_and]
      exact mem_S_iff G hG ω d x y
    have hS_sum : ((Green19.S d (setA G ω)).card : ℝ) =
        ∑ u : 𝔽₂ n × 𝔽₂ n,
          if Tri G (ω.1 u.1) (ω.2.1 u.2) (ω.2.2 (u.1 + u.2)) ∧
              ω.1 u.1 = ω.1 (u.1 + d) ∧ ω.2.1 u.2 = ω.2.1 (u.2 + d) ∧
              ω.2.2 (u.1 + u.2) = ω.2.2 (u.1 + u.2 + d)
          then (1 : ℝ) else 0 := by
      rw [hS_eq, Finset.card_filter, Nat.cast_sum]
      simp
    simp only [YS, sum_sub_distrib, sum_const, hcard_u, nsmul_eq_mul, Nat.cast_pow, N, Nnat]
    rw [hS_sum, mul_comm pS]
  let V2 := 𝔽₂ n × 𝔽₂ n
  let good4 : Finset (Fin 4 → V2) := univ.filter fun u =>
    ∀ i : Fin 4, ∃ j : Fin 4, j ≠ i ∧ ClashS d (u i) (u j)
  have h4th_expand : (∑ ω : Ω, (((Green19.S d (setA G ω)).card : ℝ) - pS * N ^ 2) ^ 4) =
      ∑ u ∈ good4, ∑ ω : Ω, YS (u 0) ω * YS (u 1) ω * YS (u 2) ω * YS (u 3) ω := by
    have hpow4 : ∀ ω : Ω, (((Green19.S d (setA G ω)).card : ℝ) - pS * N ^ 2) ^ 4 =
        ∑ u : Fin 4 → V2, YS (u 0) ω * YS (u 1) ω * YS (u 2) ω * YS (u 3) ω := by
      intro ω
      rw [hsum_S ω]
      exact sum_pow_four_fin4 (fun u => YS u ω)
    simp_rw [hpow4]
    rw [Finset.sum_comm, ← Finset.sum_filter_add_sum_filter_not univ
      (fun u : Fin 4 → V2 => ∀ i : Fin 4, ∃ j : Fin 4, j ≠ i ∧ ClashS d (u i) (u j))]
    have hzero : ∑ u ∈ univ.filter (fun u : Fin 4 → V2 =>
          ¬ ∀ i : Fin 4, ∃ j : Fin 4, j ≠ i ∧ ClashS d (u i) (u j)),
        ∑ ω : Ω, YS (u 0) ω * YS (u 1) ω * YS (u 2) ω * YS (u 3) ω = 0 := by
      refine Finset.sum_eq_zero fun u hu => ?_
      have hnot := (mem_filter.mp hu).2
      push Not at hnot
      obtain ⟨i, hi⟩ := hnot
      exact sum_YS_zero_if_isolated (by omega) G hd u i hi
    rw [hzero, add_zero]
  have hgood4_card : (good4.card : ℝ) ≤ 1000 * N ^ 6 := by
    dsimp [N]
    exact_mod_cast good4_card_bound d
  have hvar4 : (∑ ω : Ω, (((Green19.S d (setA G ω)).card : ℝ) - pS * N ^ 2) ^ 4) ≤
      1000 * N ^ 6 * cardΩ := by
    rw [h4th_expand]
    calc (∑ u ∈ good4, ∑ ω : Ω, YS (u 0) ω * YS (u 1) ω * YS (u 2) ω * YS (u 3) ω)
        ≤ ∑ _u ∈ good4, cardΩ := by
          refine Finset.sum_le_sum fun u _ => ?_
          calc (∑ ω : Ω, YS (u 0) ω * YS (u 1) ω * YS (u 2) ω * YS (u 3) ω)
              ≤ ∑ _ω : Ω, (1 : ℝ) := Finset.sum_le_sum fun ω _ => by
                have hle1 : ∀ v : V2, |YS v ω| ≤ 1 := fun v => by
                  simpa [YS] using abs_sub_prob_le_one (decide (Tri G (ω.1 v.1) (ω.2.1 v.2) (ω.2.2 (v.1 + v.2)) ∧
                    ω.1 v.1 = ω.1 (v.1 + d) ∧ ω.2.1 v.2 = ω.2.1 (v.2 + d) ∧
                    ω.2.2 (v.1 + v.2) = ω.2.2 (v.1 + v.2 + d))) hpS0 hpS1
                have hm1 : |YS (u 0) ω * YS (u 1) ω| ≤ 1 := by
                  rw [abs_mul]; exact mul_le_one₀ (hle1 (u 0)) (abs_nonneg _) (hle1 (u 1))
                have hm2 : |YS (u 0) ω * YS (u 1) ω * YS (u 2) ω| ≤ 1 := by
                  rw [abs_mul]; exact mul_le_one₀ hm1 (abs_nonneg _) (hle1 (u 2))
                have hm3 : |YS (u 0) ω * YS (u 1) ω * YS (u 2) ω * YS (u 3) ω| ≤ 1 := by
                  rw [abs_mul]; exact mul_le_one₀ hm2 (abs_nonneg _) (hle1 (u 3))
                exact (le_abs_self _).trans hm3
            _ = cardΩ := by simp [cardΩ]
      _ = (good4.card : ℝ) * cardΩ := by simp [sum_const, nsmul_eq_mul]
      _ ≤ (1000 * N ^ 6) * cardΩ := mul_le_mul_of_nonneg_right hgood4_card hcardΩ.le
  have hbad_p4 : (badS.card : ℝ) * ((1 / (q : ℝ) ^ 16) * N ^ 8) ≤ 1000 * N ^ 6 * cardΩ := by
    calc (badS.card : ℝ) * ((1 / (q : ℝ) ^ 16) * N ^ 8)
        = ∑ _ω ∈ badS, ((1 / (q : ℝ) ^ 4) * N ^ 2) ^ 4 := by
          simp only [sum_const, nsmul_eq_mul]; ring
      _ ≤ ∑ ω ∈ badS, (((Green19.S d (setA G ω)).card : ℝ) - pS * N ^ 2) ^ 4 := by
          refine Finset.sum_le_sum fun ω hω => ?_
          have hlt : (2 / (q : ℝ) ^ 4) * N ^ 2 < ((Green19.S d (setA G ω)).card : ℝ) :=
            (mem_filter.mp hω).2
          have hgap : (1 / (q : ℝ) ^ 4) * N ^ 2 ≤ ((Green19.S d (setA G ω)).card : ℝ) - pS * N ^ 2 := by
            have hpSN : pS * N ^ 2 ≤ (1 / (q : ℝ) ^ 4) * N ^ 2 :=
              mul_le_mul_of_nonneg_right hpS_bound (sq_nonneg N)
            have h21 : (1 / (q : ℝ) ^ 4) * N ^ 2 + (1 / (q : ℝ) ^ 4) * N ^ 2 = (2 / (q : ℝ) ^ 4) * N ^ 2 := by ring
            linarith
          exact pow_le_pow_left₀ (by positivity) hgap 4
      _ ≤ ∑ ω : Ω, (((Green19.S d (setA G ω)).card : ℝ) - pS * N ^ 2) ^ 4 :=
          Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _) fun ω _ _ => by
            rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul]
            exact sq_nonneg _
      _ ≤ 1000 * N ^ 6 * cardΩ := hvar4
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  calc (badS.card : ℝ) * N ^ 2
      = ((badS.card : ℝ) * ((1 / (q : ℝ) ^ 16) * N ^ 8)) * ((q : ℝ) ^ 16 / N ^ 6) := by
        field_simp [hq0.ne', hNpos.ne']
    _ ≤ (1000 * N ^ 6 * cardΩ) * ((q : ℝ) ^ 16 / N ^ 6) :=
        mul_le_mul_of_nonneg_right hbad_p4 (by positivity)
    _ = 1000 * (q : ℝ) ^ 16 * cardΩ := by field_simp [hNpos.ne']

private lemma h2_main : ∀ q : ℕ, 1 < q → ∀ (G : SimpleGraph (Fin q)) [DecidableRel G.Adj],
    G.LocallyLinear →
    Filter.atTop.Frequently fun n => ∃ A : Finset (𝔽₂ n × 𝔽₂ n),
      let N : ℝ := Fintype.card (𝔽₂ n)
      ((G.cliqueFinset 3).card : ℝ) / (q : ℝ) ^ 3 * N ^ 2 ≤ A.card ∧
        ∀ d : 𝔽₂ n, d ≠ 0 → ((Green19.S d A).card : ℝ) ≤ (2 / (q : ℝ) ^ 4) * N ^ 2 := by
  intro q hq G _ hG
  classical
  rw [Filter.frequently_atTop]
  intro n₀
  let T : ℕ := (G.cliqueFinset 3).card
  by_cases hT : T = 0
  · refine ⟨n₀, le_rfl, ∅, ?_⟩
    have hT0 : (G.cliqueFinset 3).card = 0 := hT
    rw [hT0]
    simp only [Nat.cast_zero, zero_div, zero_mul, card_empty, le_refl, true_and]
    intro d _
    have hSe : Green19.S d ∅ = ∅ := by
      ext p
      simp [Green19.S, Green19.IsCorner]
    rw [hSe, card_empty, Nat.cast_zero]
    positivity
  have hTpos : 1 ≤ T := Nat.pos_of_ne_zero hT
  let m := 3 * q ^ 6 + 1000 * q ^ 16
  have hm : m < 2 ^ m := Nat.lt_two_pow_self
  let n := max n₀ m
  have hn0 : n₀ ≤ n := le_max_left _ _
  have hNm_nat : 3 * q ^ 6 + 1000 * q ^ 16 < 2 ^ n :=
    lt_of_lt_of_le hm (Nat.pow_le_pow_right (by decide : 0 < 2) (le_max_right _ _))
  refine ⟨n, hn0, ?_⟩
  let Nnat : ℕ := Fintype.card (𝔽₂ n)
  have hNnat : Nnat = 2 ^ n := by
    simp [Nnat, Fintype.card_fin, ZMod.card]
  have hNbig : 3 * q ^ 6 + 1000 * q ^ 16 < Nnat := by rw [hNnat]; exact hNm_nat
  have hNpos_nat : 0 < Nnat := by omega
  let N : ℝ := (Nnat : ℝ)
  have hNpos : 0 < N := Nat.cast_pos.mpr hNpos_nat
  let Ω := (𝔽₂ n → Fin q) × (𝔽₂ n → Fin q) × (𝔽₂ n → Fin q)
  have : NeZero q := ⟨by omega⟩
  let cardΩ : ℝ := (Fintype.card Ω : ℝ)
  have hcardΩ : 0 < cardΩ := Nat.cast_pos.mpr Fintype.card_pos
  let badA : Finset Ω := univ.filter fun ω =>
    ((setA G ω).card : ℝ) < (T : ℝ) / (q : ℝ) ^ 3 * N ^ 2
  let badS (d : 𝔽₂ n) : Finset Ω := univ.filter fun ω =>
    (2 / (q : ℝ) ^ 4) * N ^ 2 < ((Green19.S d (setA G ω)).card : ℝ)
  have hbadA : (badA.card : ℝ) ≤ (3 * (q : ℝ) ^ 6 / (25 * N)) * cardΩ :=
    badA_bound hq G hG hTpos
  have hbadS : ∀ d : 𝔽₂ n, d ≠ 0 → ((badS d).card : ℝ) ≤ (1000 * (q : ℝ) ^ 16 / N ^ 2) * cardΩ :=
    fun d hd => badS_bound hq G hG d hd
  let badAll : Finset Ω := badA ∪ (univ.erase (0 : 𝔽₂ n)).biUnion badS
  have hbadAll : (badAll.card : ℝ) < cardΩ := by
    have h1 : badAll.card ≤ badA.card + ((univ.erase (0 : 𝔽₂ n)).biUnion badS).card :=
      card_union_le _ _
    have h2 : ((univ.erase (0 : 𝔽₂ n)).biUnion badS).card ≤
        ∑ d ∈ univ.erase (0 : 𝔽₂ n), (badS d).card := card_biUnion_le
    have hsum_R : (badAll.card : ℝ) ≤
        (3 * (q : ℝ) ^ 6 / (25 * N)) * cardΩ +
          N * ((1000 * (q : ℝ) ^ 16 / N ^ 2) * cardΩ) := by
      have hcast : (badAll.card : ℝ) ≤ (badA.card : ℝ) + ∑ d ∈ univ.erase (0 : 𝔽₂ n), ((badS d).card : ℝ) := by
        exact_mod_cast h1.trans (Nat.add_le_add_left h2 _)
      refine hcast.trans (add_le_add hbadA ?_)
      calc ∑ d ∈ univ.erase (0 : 𝔽₂ n), ((badS d).card : ℝ)
          ≤ ∑ _d ∈ univ.erase (0 : 𝔽₂ n), (1000 * (q : ℝ) ^ 16 / N ^ 2) * cardΩ :=
            sum_le_sum fun d hd => hbadS d (mem_erase.mp hd).1
        _ = ((univ.erase (0 : 𝔽₂ n)).card : ℝ) * ((1000 * (q : ℝ) ^ 16 / N ^ 2) * cardΩ) := by
            simp [sum_const, nsmul_eq_mul]
        _ ≤ N * ((1000 * (q : ℝ) ^ 16 / N ^ 2) * cardΩ) := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            have hle_N : (univ.erase (0 : 𝔽₂ n)).card ≤ Nnat :=
              (card_le_card (erase_subset _ _)).trans (by simp [Nnat])
            dsimp [N]
            exact_mod_cast hle_N
    have hN_R : 3 * (q : ℝ) ^ 6 + 1000 * (q : ℝ) ^ 16 < N := by
      dsimp [N]
      exact_mod_cast hNbig
    have hfrac : (3 * (q : ℝ) ^ 6 / 25 + 1000 * (q : ℝ) ^ 16) / N < 1 := by
      rw [div_lt_one hNpos]
      linarith [show 0 ≤ (q : ℝ) ^ 6 by positivity]
    calc (badAll.card : ℝ)
        ≤ (3 * (q : ℝ) ^ 6 / (25 * N)) * cardΩ + N * ((1000 * (q : ℝ) ^ 16 / N ^ 2) * cardΩ) := hsum_R
      _ = ((3 * (q : ℝ) ^ 6 / 25 + 1000 * (q : ℝ) ^ 16) / N) * cardΩ := by
          field_simp [hNpos.ne']
      _ < 1 * cardΩ := mul_lt_mul_of_pos_right hfrac hcardΩ
      _ = cardΩ := one_mul cardΩ
  have hdiff : (univ \ badAll : Finset Ω).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    have hsub : (univ : Finset Ω) ⊆ badAll := Finset.sdiff_eq_empty_iff_subset.mp he
    have hle : cardΩ ≤ (badAll.card : ℝ) := by
      dsimp [cardΩ]
      rw [← Finset.card_univ]
      exact_mod_cast Finset.card_le_card hsub
    exact hbadAll.not_ge hle
  obtain ⟨ω, hω⟩ := hdiff
  have hωnot : ω ∉ badAll := (mem_sdiff.mp hω).2
  have hnotA : ω ∉ badA := fun h => hωnot (mem_union_left _ h)
  have hA_ge : (T : ℝ) / (q : ℝ) ^ 3 * N ^ 2 ≤ ((setA G ω).card : ℝ) := by
    by_contra hlt
    push Not at hlt
    exact hnotA (mem_filter.mpr ⟨mem_univ _, hlt⟩)
  refine ⟨setA G ω, hA_ge, fun d hd => ?_⟩
  have hnotS : ω ∉ badS d := fun h =>
    hωnot (mem_union_right _ (mem_biUnion.mpr ⟨d, mem_erase.mpr ⟨hd, mem_univ _⟩, h⟩))
  by_contra hgt
  push Not at hgt
  exact hnotS (mem_filter.mpr ⟨mem_univ _, hgt⟩)

end Helpers

theorem OMA.solution : OMA.R_Green19_green_19_R1.H2 :=
  Helpers.h2_main
