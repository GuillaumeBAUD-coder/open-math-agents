import OMAReductions.R_Erdos161_erdos_161_parts_ii_R1
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Reduction of Erdős Problem 161 (Part ii, Higher-Uniformity Core `R1.H2`)

We formalize the Ramsey supersaturation + Hypergraph Nikiforov reduction for the open `t ≥ 4`
core of Erdős Problem 161 (ii):

1. **Hypergraph Ramsey Supersaturation** (proved unconditionally): if every 2-coloring of the
   `t`-subsets of `Fin R` contains a monochromatic `d`-clique, then every 2-coloring of the
   `t`-subsets of `Fin n` (`n ≥ R`) contains at least `(1 / (2 * C(R, d))) * C(n, d)`
   monochromatic `d`-cliques in a single color.
2. **Multipartite Blowup Density** (proved unconditionally for all `t ≥ 4`): a monochromatic
   complete `d`-partite `t`-uniform hypergraph `K_d^t(s)` with `d > t^2 / α` has at least
   `C(d, t) * s^t > (1 - α) * C(d * s, t)` monochromatic `t`-subsets inside its `d * s`
   vertices, leaving strictly fewer than `α * C(d * s, t)` edges of the opposite color.

This reduces `Erdos161.erdos_161.parts.ii.R1.H2` to:
- `H1`: Ramsey's Theorem for 2-colored `t`-uniform hypergraphs (`t ≥ 4`, known).
- `H2`: The Hypergraph Nikiforov Conjecture for cliques (`t ≥ 4`, open).
-/

-- Credit: @skhakim

namespace OMA.R_Erdos161_erdos_161_parts_ii_R1_H2_R1

open Filter

/-- Hypergraph Ramsey's Theorem (Ramsey 1930) for 2-colorings of `t`-uniform hypergraphs (`t ≥ 4`):
for every `t ≥ 4` and `d ≥ t`, there exists `R ≥ d` such that every 2-coloring of the `t`-subsets
of `Fin R` contains a monochromatic `d`-element subset. -/
def H1 : Prop :=
  ∀ t d : ℕ, 4 ≤ t → t ≤ d →
    ∃ R : ℕ, d ≤ R ∧
      ∀ col : Finset (Fin R) → Bool,
        ∃ (b : Bool) (S : Finset (Fin R)),
          S.card = d ∧ ∀ e ⊆ S, e.card = t → col e = b

/-- Hypergraph Nikiforov Conjecture for cliques (`t ≥ 4`): for every `t ≥ 4`, `d ≥ t`, and
density `δ > 0`, there exists `c > 0` such that for all sufficiently large `n`, every `t`-uniform
hypergraph `G` on `Fin n` containing at least `δ * C(n, d)` cliques of size `d` contains a
complete `d`-partite `t`-uniform blowup `K_d^t(s)` with `s ≥ c * (log n)^(1/(t - 1))`. -/
def H2 : Prop :=
  ∀ t d : ℕ, 4 ≤ t → t ≤ d → ∀ δ : ℝ, 0 < δ →
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ n : ℕ in Filter.atTop,
        ∀ G : Finset (Fin n) → Bool,
          δ * (n.choose d : ℝ) ≤
            ((((Finset.univ : Finset (Fin n)).powersetCard d).filter
              (fun S ↦ ∀ e ⊆ S, e.card = t → G e = true)).card : ℝ) →
          ∃ (s : ℕ) (V : Fin d → Finset (Fin n)),
            1 ≤ s ∧
            c * (Real.log n) ^ (((t : ℝ) - 1)⁻¹) ≤ (s : ℝ) ∧
            (∀ i, (V i).card = s) ∧
            (∀ i j, i ≠ j → Disjoint (V i) (V j)) ∧
            ∀ e : Finset (Fin n), e.card = t →
              (∀ x ∈ e, ∃ i, x ∈ V i) →
              (∀ i, (e ∩ V i).card ≤ 1) →
              G e = true

/- ### Part 1: Hypergraph Ramsey supersaturation by double counting -/

lemma card_powersetCard_filter_superset {n d R : ℕ} {S : Finset (Fin n)}
    (hSd : S.card = d) (hdR : d ≤ R) :
    (((Finset.univ : Finset (Fin n)).powersetCard R).filter (fun U ↦ S ⊆ U)).card =
      (n - d).choose (R - d) := by
  have hbij : (((Finset.univ : Finset (Fin n)) \ S).powersetCard (R - d)).card =
      (((Finset.univ : Finset (Fin n)).powersetCard R).filter (fun U ↦ S ⊆ U)).card := by
    refine Finset.card_bij (fun A _ ↦ A ∪ S) ?_ ?_ ?_
    · intro A hA
      rw [Finset.mem_powersetCard] at hA
      rw [Finset.mem_filter, Finset.mem_powersetCard]
      have hdisj : Disjoint A S := Finset.disjoint_sdiff.symm.mono_left hA.1
      refine ⟨⟨Finset.subset_univ _, ?_⟩, Finset.subset_union_right⟩
      rw [Finset.card_union_of_disjoint hdisj, hA.2, hSd, Nat.sub_add_cancel hdR]
    · intro A₁ hA₁ A₂ hA₂ heq
      rw [Finset.mem_powersetCard] at hA₁ hA₂
      have hd₁ : Disjoint A₁ S := Finset.disjoint_sdiff.symm.mono_left hA₁.1
      have hd₂ : Disjoint A₂ S := Finset.disjoint_sdiff.symm.mono_left hA₂.1
      have h1 : (A₁ ∪ S) \ S = A₁ := Finset.union_sdiff_cancel_right hd₁
      have h2 : (A₂ ∪ S) \ S = A₂ := Finset.union_sdiff_cancel_right hd₂
      rw [← h1, ← h2, heq]
    · intro U hU
      rw [Finset.mem_filter, Finset.mem_powersetCard] at hU
      refine ⟨U \ S, ?_, Finset.sdiff_union_of_subset hU.2⟩
      rw [Finset.mem_powersetCard]
      refine ⟨Finset.sdiff_subset_sdiff (Finset.subset_univ U) (Finset.Subset.refl S), ?_⟩
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hU.2, hU.1.2, hSd]
  rw [← hbij, Finset.card_powersetCard, Finset.card_sdiff,
    Finset.inter_eq_left.mpr (Finset.subset_univ S), Finset.card_univ, Fintype.card_fin, hSd]

lemma ramsey_on_subset {n t d R : ℕ}
    (hRam : ∀ col : Finset (Fin R) → Bool,
      ∃ (b : Bool) (S : Finset (Fin R)),
        S.card = d ∧ ∀ e ⊆ S, e.card = t → col e = b)
    (col : Finset (Fin n) → Bool)
    {U : Finset (Fin n)} (hU : U.card = R) :
    ∃ (b : Bool) (S : Finset (Fin n)),
      S ⊆ U ∧ S.card = d ∧ ∀ e ⊆ S, e.card = t → col e = b := by
  let emb : Fin R ↪ Fin n := (U.orderEmbOfFin hU).toEmbedding
  let col' : Finset (Fin R) → Bool := fun A ↦ col (A.map emb)
  obtain ⟨b, S', hS'card, hS'mono⟩ := hRam col'
  refine ⟨b, S'.map emb, ?_, ?_, ?_⟩
  · intro x hx
    rw [Finset.mem_map] at hx
    obtain ⟨i, _, rfl⟩ := hx
    exact U.orderEmbOfFin_mem hU i
  · rw [Finset.card_map, hS'card]
  · intro e heS het
    let e' : Finset (Fin R) := S'.filter (fun i ↦ emb i ∈ e)
    have he_eq : e'.map emb = e := by
      ext x
      simp only [e', Finset.mem_map, Finset.mem_filter]
      constructor
      · rintro ⟨i, ⟨_, hi⟩, rfl⟩
        exact hi
      · intro hx
        have hxS : x ∈ S'.map emb := heS hx
        rw [Finset.mem_map] at hxS
        obtain ⟨i, hiS', rfl⟩ := hxS
        exact ⟨i, ⟨hiS', hx⟩, rfl⟩
    have he'_card : e'.card = t := by
      rw [← Finset.card_map emb, he_eq, het]
    have he'_sub : e' ⊆ S' := Finset.filter_subset _ _
    have hcol' : col' e' = b := hS'mono e' he'_sub he'_card
    simpa [col', he_eq] using hcol'

lemma supersaturation_monochromatic_cliques {n t d R : ℕ}
    (hdR : d ≤ R) (hRn : R ≤ n)
    (hRam : ∀ col : Finset (Fin R) → Bool,
      ∃ (b : Bool) (S : Finset (Fin R)),
        S.card = d ∧ ∀ e ⊆ S, e.card = t → col e = b)
    (col : Finset (Fin n) → Bool) :
    ∃ b : Bool,
      (1 / (2 * (R.choose d : ℝ))) * (n.choose d : ℝ) ≤
        ((((Finset.univ : Finset (Fin n)).powersetCard d).filter
          (fun S ↦ ∀ e ⊆ S, e.card = t → (col e == b) = true)).card : ℝ) := by
  let Mtrue : Finset (Finset (Fin n)) :=
    ((Finset.univ : Finset (Fin n)).powersetCard d).filter
      (fun S ↦ ∀ e ⊆ S, e.card = t → col e = true)
  let Mfalse : Finset (Finset (Fin n)) :=
    ((Finset.univ : Finset (Fin n)).powersetCard d).filter
      (fun S ↦ ∀ e ⊆ S, e.card = t → col e = false)
  let M : Finset (Finset (Fin n)) := Mtrue ∪ Mfalse
  have hU_has : ∀ U ∈ (Finset.univ : Finset (Fin n)).powersetCard R,
      1 ≤ (M.filter (fun S ↦ S ⊆ U)).card := by
    intro U hU
    have hUcard : U.card = R := (Finset.mem_powersetCard.mp hU).2
    obtain ⟨b, S, hSU, hScard, hSmono⟩ := ramsey_on_subset hRam col hUcard
    refine Finset.card_pos.mpr ⟨S, ?_⟩
    rw [Finset.mem_filter]
    refine ⟨?_, hSU⟩
    cases b
    · apply Finset.mem_union_right
      rw [Finset.mem_filter, Finset.mem_powersetCard]
      exact ⟨⟨Finset.subset_univ S, hScard⟩, hSmono⟩
    · apply Finset.mem_union_left
      rw [Finset.mem_filter, Finset.mem_powersetCard]
      exact ⟨⟨Finset.subset_univ S, hScard⟩, hSmono⟩
  have hsum_ge : n.choose R ≤
      ∑ U ∈ (Finset.univ : Finset (Fin n)).powersetCard R, (M.filter (fun S ↦ S ⊆ U)).card := by
    calc n.choose R
        = ∑ _U ∈ (Finset.univ : Finset (Fin n)).powersetCard R, 1 := by
            rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
              smul_eq_mul, mul_one]
      _ ≤ ∑ U ∈ (Finset.univ : Finset (Fin n)).powersetCard R, (M.filter (fun S ↦ S ⊆ U)).card :=
            Finset.sum_le_sum hU_has
  have hsum_eq :
      ∑ U ∈ (Finset.univ : Finset (Fin n)).powersetCard R, (M.filter (fun S ↦ S ⊆ U)).card =
        M.card * (n - d).choose (R - d) := by
    simp_rw [Finset.card_filter]
    rw [Finset.sum_comm]
    have hinner : ∀ S ∈ M,
        ∑ U ∈ (Finset.univ : Finset (Fin n)).powersetCard R, (if S ⊆ U then 1 else 0) =
          (n - d).choose (R - d) := by
      intro S hS
      rw [← Finset.card_filter]
      have hScard : S.card = d := by
        simp only [M, Mtrue, Mfalse, Finset.mem_union, Finset.mem_filter,
          Finset.mem_powersetCard] at hS
        rcases hS with ⟨⟨_, hc⟩, _⟩ | ⟨⟨_, hc⟩, _⟩ <;> exact hc
      exact card_powersetCard_filter_superset hScard hdR
    rw [Finset.sum_congr rfl hinner, Finset.sum_const, smul_eq_mul]
  rw [hsum_eq] at hsum_ge
  have hchoose_id : n.choose R * R.choose d = n.choose d * (n - d).choose (R - d) :=
    Nat.choose_mul (n := n) hdR
  have hpos_nd : 0 < (n - d).choose (R - d) := Nat.choose_pos (Nat.sub_le_sub_right hRn d)
  have hmul : n.choose d * (n - d).choose (R - d) ≤
      (M.card * R.choose d) * (n - d).choose (R - d) := by
    calc n.choose d * (n - d).choose (R - d)
        = n.choose R * R.choose d := hchoose_id.symm
      _ ≤ (M.card * (n - d).choose (R - d)) * R.choose d := Nat.mul_le_mul_right _ hsum_ge
      _ = (M.card * R.choose d) * (n - d).choose (R - d) := by ring
  have hM_ge : n.choose d ≤ M.card * R.choose d := Nat.le_of_mul_le_mul_right hmul hpos_nd
  have hM_le : M.card ≤ Mtrue.card + Mfalse.card := Finset.card_union_le Mtrue Mfalse
  have hsum_cards : n.choose d ≤ (Mtrue.card + Mfalse.card) * R.choose d :=
    hM_ge.trans (Nat.mul_le_mul_right _ hM_le)
  have hRd_pos : (0 : ℝ) < (R.choose d : ℝ) := by exact_mod_cast Nat.choose_pos hdR
  have hbranch : n.choose d ≤ 2 * Mtrue.card * R.choose d ∨
      n.choose d ≤ 2 * Mfalse.card * R.choose d := by
    by_cases hcmp : Mfalse.card ≤ Mtrue.card
    · left
      calc n.choose d ≤ (Mtrue.card + Mfalse.card) * R.choose d := hsum_cards
        _ ≤ (Mtrue.card + Mtrue.card) * R.choose d := by
              exact Nat.mul_le_mul_right _ (Nat.add_le_add_left hcmp _)
        _ = 2 * Mtrue.card * R.choose d := by ring
    · right
      have hlt : Mtrue.card ≤ Mfalse.card := by omega
      calc n.choose d ≤ (Mtrue.card + Mfalse.card) * R.choose d := hsum_cards
        _ ≤ (Mfalse.card + Mfalse.card) * R.choose d := by
              exact Nat.mul_le_mul_right _ (Nat.add_le_add_right hlt _)
        _ = 2 * Mfalse.card * R.choose d := by ring
  rcases hbranch with hT | hF
  · refine ⟨true, ?_⟩
    have hfilt : (((Finset.univ : Finset (Fin n)).powersetCard d).filter
        (fun S ↦ ∀ e ⊆ S, e.card = t → (col e == true) = true)) = Mtrue := by
      refine Finset.filter_congr fun S _ ↦ ?_
      simp
    rw [hfilt]
    have hT_r : (n.choose d : ℝ) ≤ 2 * (Mtrue.card : ℝ) * (R.choose d : ℝ) := by exact_mod_cast hT
    rw [one_div_mul_eq_div, div_le_iff₀ (by positivity)]
    linarith
  · refine ⟨false, ?_⟩
    have hfilt : (((Finset.univ : Finset (Fin n)).powersetCard d).filter
        (fun S ↦ ∀ e ⊆ S, e.card = t → (col e == false) = true)) = Mfalse := by
      refine Finset.filter_congr fun S _ ↦ ?_
      simp
    rw [hfilt]
    have hF_r : (n.choose d : ℝ) ≤ 2 * (Mfalse.card : ℝ) * (R.choose d : ℝ) := by exact_mod_cast hF
    rw [one_div_mul_eq_div, div_le_iff₀ (by positivity)]
    linarith

/- ### Part 2: Complete multipartite `t`-uniform blowup to discrepancy reduction -/

lemma transverse_subsets_card_ge {n t d s : ℕ} (V : Fin d → Finset (Fin n))
    (hcard : ∀ i, (V i).card = s)
    (hdisj : ∀ i j, i ≠ j → Disjoint (V i) (V j)) :
    d.choose t * s ^ t ≤
      (((Finset.univ.biUnion V).powersetCard t).filter
        (fun e ↦ ∀ i, (e ∩ V i).card ≤ 1)).card := by
  let X := Finset.univ.biUnion V
  let dom := ((Finset.univ : Finset (Fin d)).powersetCard t).sigma fun I ↦
    Finset.pi I (fun i ↦ V i)
  have hdom_card : dom.card = d.choose t * s ^ t := by
    rw [Finset.card_sigma]
    have hinner : ∀ I ∈ (Finset.univ : Finset (Fin d)).powersetCard t,
        (Finset.pi I (fun i ↦ V i)).card = s ^ t := by
      intro I hI
      rw [Finset.card_pi]
      have hIcard : I.card = t := (Finset.mem_powersetCard.mp hI).2
      calc ∏ i ∈ I, (V i).card = ∏ _i ∈ I, s := Finset.prod_congr rfl fun i _ ↦ hcard i
        _ = s ^ I.card := Finset.prod_const s
        _ = s ^ t := by rw [hIcard]
    rw [Finset.sum_congr rfl hinner, Finset.sum_const, Finset.card_powersetCard,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [← hdom_card]
  refine Finset.card_le_card_of_injOn
    (fun p ↦ p.1.attach.image (fun i ↦ p.2 i.1 i.2)) ?_ ?_
  · intro p hp
    rcases p with ⟨I, f⟩
    simp only [Finset.mem_coe, dom, Finset.mem_sigma, Finset.mem_powersetCard, Finset.mem_pi] at hp
    have hinj_f : Function.Injective (fun i : {x // x ∈ I} ↦ f i.1 i.2) := by
      intro a b hab
      dsimp at hab
      by_contra hne
      have hne' : a.1 ≠ b.1 := fun h ↦ hne (Subtype.ext h)
      have ha : f a.1 a.2 ∈ V a.1 := hp.2 a.1 a.2
      have hb : f a.1 a.2 ∈ V b.1 := hab ▸ hp.2 b.1 b.2
      exact Finset.disjoint_left.mp (hdisj a.1 b.1 hne') ha hb
    have hcard_img : (I.attach.image (fun i ↦ f i.1 i.2)).card = t := by
      rw [Finset.card_image_of_injective _ hinj_f, Finset.card_attach, hp.1.2]
    have hsub : I.attach.image (fun i ↦ f i.1 i.2) ⊆ X := by
      intro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨i, _, rfl⟩ := hx
      exact Finset.mem_biUnion.mpr ⟨i.1, Finset.mem_univ _, hp.2 i.1 i.2⟩
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_powersetCard]
    refine ⟨⟨hsub, hcard_img⟩, fun j ↦ ?_⟩
    by_cases hj : j ∈ I
    · have hinter : (I.attach.image (fun i ↦ f i.1 i.2)) ∩ V j = {f j hj} := by
        ext x
        simp only [Finset.mem_inter, Finset.mem_image, Finset.mem_attach, true_and,
          Finset.mem_singleton, Subtype.exists]
        constructor
        · rintro ⟨⟨k, hk, rfl⟩, hxj⟩
          by_cases hkj : k = j
          · subst hkj; rfl
          · exfalso
            exact Finset.disjoint_left.mp (hdisj k j hkj) (hp.2 k hk) hxj
        · rintro rfl
          exact ⟨⟨j, hj, rfl⟩, hp.2 j hj⟩
      rw [hinter, Finset.card_singleton]
    · have hinter : (I.attach.image (fun i ↦ f i.1 i.2)) ∩ V j = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro x hx
        rw [Finset.mem_inter, Finset.mem_image] at hx
        obtain ⟨⟨i, _, rfl⟩, hxj⟩ := hx
        have hij : i.1 ≠ j := fun h ↦ hj (h ▸ i.2)
        exact Finset.disjoint_left.mp (hdisj i.1 j hij) (hp.2 i.1 i.2) hxj
      rw [hinter, Finset.card_empty]
      exact Nat.zero_le 1
  · intro p₁ hp₁ p₂ hp₂ heq
    rcases p₁ with ⟨I₁, f₁⟩
    rcases p₂ with ⟨I₂, f₂⟩
    dsimp at heq
    simp only [Finset.mem_coe, dom, Finset.mem_sigma, Finset.mem_powersetCard,
      Finset.mem_pi] at hp₁ hp₂
    have hI_eq : I₁ = I₂ := by
      ext j
      constructor
      · intro hj
        have hmem : f₁ j hj ∈ I₁.attach.image (fun i ↦ f₁ i.1 i.2) :=
          Finset.mem_image.mpr ⟨⟨j, hj⟩, Finset.mem_attach _ _, rfl⟩
        rw [heq, Finset.mem_image] at hmem
        obtain ⟨k, _, hfk⟩ := hmem
        by_contra hj2
        have hkj : k.1 ≠ j := fun h ↦ hj2 (h ▸ k.2)
        exact Finset.disjoint_left.mp (hdisj k.1 j hkj) (hp₂.2 k.1 k.2) (hfk ▸ hp₁.2 j hj)
      · intro hj
        have hmem : f₂ j hj ∈ I₂.attach.image (fun i ↦ f₂ i.1 i.2) :=
          Finset.mem_image.mpr ⟨⟨j, hj⟩, Finset.mem_attach _ _, rfl⟩
        rw [← heq, Finset.mem_image] at hmem
        obtain ⟨k, _, hfk⟩ := hmem
        by_contra hj1
        have hkj : k.1 ≠ j := fun h ↦ hj1 (h ▸ k.2)
        exact Finset.disjoint_left.mp (hdisj k.1 j hkj) (hp₁.2 k.1 k.2) (hfk ▸ hp₂.2 j hj)
    subst hI_eq
    congr 1
    funext j hj
    have hmem : f₁ j hj ∈ I₁.attach.image (fun i ↦ f₁ i.1 i.2) :=
      Finset.mem_image.mpr ⟨⟨j, hj⟩, Finset.mem_attach _ _, rfl⟩
    rw [heq, Finset.mem_image] at hmem
    obtain ⟨k, _, hfk⟩ := hmem
    have hkj : k.1 = j := by
      by_contra hne
      exact Finset.disjoint_left.mp (hdisj k.1 j hne) (hp₂.2 k.1 k.2) (hfk ▸ hp₁.2 j hj)
    cases k with
    | mk kv hk =>
      dsimp at hkj hfk
      subst hkj
      exact hfk.symm

lemma multipartite_density_lt {t d s : ℕ} {α : ℝ}
    (htd : t ≤ d) (hs : 1 ≤ s) (hα0 : 0 < α) (hα1 : α < 1 / 2)
    (hdα : (t : ℝ) ^ 2 < α * (d : ℝ)) :
    (((d * s).choose t : ℕ) : ℝ) - ((d.choose t * s ^ t : ℕ) : ℝ) <
      α * (((d * s).choose t : ℕ) : ℝ) := by
  have hd_pos : (0 : ℝ) < (d : ℝ) := by
    have : 0 < d := by
      by_contra h0
      have hd0 : d = 0 := by omega
      rw [hd0] at hdα
      simp at hdα
      nlinarith
    exact_mod_cast this
  have hs_pos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast (show 0 < s by omega)
  have hfac_pos : (0 : ℝ) < (t.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos t
  have hdesc_ds : ((d * s).descFactorial t : ℝ) =
      (t.factorial : ℝ) * (((d * s).choose t : ℕ) : ℝ) := by
    exact_mod_cast Nat.descFactorial_eq_factorial_mul_choose (d * s) t
  have hdesc_d : (d.descFactorial t : ℝ) =
      (t.factorial : ℝ) * ((d.choose t : ℕ) : ℝ) := by
    exact_mod_cast Nat.descFactorial_eq_factorial_mul_choose d t
  have hdesc_ds_le : ((d * s).descFactorial t : ℝ) ≤ ((d : ℝ) * (s : ℝ)) ^ t := by
    have hnat : (d * s).descFactorial t ≤ (d * s) ^ t := Nat.descFactorial_le_pow (d * s) t
    have hcast : ((d * s).descFactorial t : ℝ) ≤ (((d * s) ^ t : ℕ) : ℝ) := by exact_mod_cast hnat
    simpa [Nat.cast_mul, Nat.cast_pow] using hcast
  have hdesc_d_ge : ((d : ℝ) - (t : ℝ)) ^ t ≤ (d.descFactorial t : ℝ) := by
    have hprod : ∀ k ≤ d, (d.descFactorial k : ℝ) = ∏ i ∈ Finset.range k, ((d : ℝ) - (i : ℝ)) := by
      intro k hk
      induction k with
      | zero => simp
      | succ k ih =>
        rw [Nat.descFactorial_succ, Finset.prod_range_succ, Nat.cast_mul, ih (by omega),
          Nat.cast_sub (by omega)]
        ring
    rw [hprod t htd]
    calc ((d : ℝ) - (t : ℝ)) ^ t
        = ∏ _i ∈ Finset.range t, ((d : ℝ) - (t : ℝ)) := by
            rw [Finset.prod_const, Finset.card_range]
      _ ≤ ∏ i ∈ Finset.range t, ((d : ℝ) - (i : ℝ)) := by
            have hdt_nonneg : 0 ≤ (d : ℝ) - (t : ℝ) := by
              have : (t : ℝ) ≤ (d : ℝ) := by exact_mod_cast htd
              linarith
            refine Finset.prod_le_prod (fun _ _ ↦ hdt_nonneg) fun i hi ↦ ?_
            rw [Finset.mem_range] at hi
            have : (i : ℝ) ≤ (t : ℝ) := by exact_mod_cast hi.le
            linarith
  have hbern : 1 - (t : ℝ) ^ 2 / (d : ℝ) ≤ (1 - (t : ℝ) / (d : ℝ)) ^ t := by
    have hge_neg2 : (-2 : ℝ) ≤ -((t : ℝ) / (d : ℝ)) := by
      have : (t : ℝ) / (d : ℝ) ≤ 1 := by
        rw [div_le_one hd_pos]
        exact_mod_cast htd
      linarith
    have h := one_add_mul_le_pow hge_neg2 t
    have hlhs : 1 + (t : ℝ) * -((t : ℝ) / (d : ℝ)) = 1 - (t : ℝ) ^ 2 / (d : ℝ) := by ring
    have hrhs : 1 + -((t : ℝ) / (d : ℝ)) = 1 - (t : ℝ) / (d : ℝ) := by ring
    rwa [hlhs, hrhs] at h
  have h1m_lt : 1 - α < 1 - (t : ℝ) ^ 2 / (d : ℝ) := by
    have hdiv : (t : ℝ) ^ 2 / (d : ℝ) < α := (div_lt_iff₀ hd_pos).mpr (by linarith)
    linarith
  have hds_pow_pos : 0 < ((d : ℝ) * (s : ℝ)) ^ t := by positivity
  have hmain_desc : (1 - α) * ((d * s).descFactorial t : ℝ) <
      (d.descFactorial t : ℝ) * (s : ℝ) ^ t := by
    calc (1 - α) * ((d * s).descFactorial t : ℝ)
        ≤ (1 - α) * ((d : ℝ) * (s : ℝ)) ^ t :=
            mul_le_mul_of_nonneg_left hdesc_ds_le (by linarith)
      _ < (1 - (t : ℝ) ^ 2 / (d : ℝ)) * ((d : ℝ) * (s : ℝ)) ^ t :=
            mul_lt_mul_of_pos_right h1m_lt hds_pow_pos
      _ ≤ (1 - (t : ℝ) / (d : ℝ)) ^ t * ((d : ℝ) * (s : ℝ)) ^ t :=
            mul_le_mul_of_nonneg_right hbern hds_pow_pos.le
      _ = ((d : ℝ) - (t : ℝ)) ^ t * (s : ℝ) ^ t := by
            rw [mul_pow, ← mul_assoc, ← mul_pow]
            congr 2
            field_simp
      _ ≤ (d.descFactorial t : ℝ) * (s : ℝ) ^ t :=
            mul_le_mul_of_nonneg_right hdesc_d_ge (by positivity)
  have hmain_choose : (1 - α) * (((d * s).choose t : ℕ) : ℝ) <
      ((d.choose t * s ^ t : ℕ) : ℝ) := by
    have h1 : (t.factorial : ℝ) * ((1 - α) * (((d * s).choose t : ℕ) : ℝ)) <
        (t.factorial : ℝ) * ((d.choose t * s ^ t : ℕ) : ℝ) := by
      calc (t.factorial : ℝ) * ((1 - α) * (((d * s).choose t : ℕ) : ℝ))
          = (1 - α) * ((t.factorial : ℝ) * (((d * s).choose t : ℕ) : ℝ)) := by ring
        _ = (1 - α) * ((d * s).descFactorial t : ℝ) := by rw [← hdesc_ds]
        _ < (d.descFactorial t : ℝ) * (s : ℝ) ^ t := hmain_desc
        _ = (t.factorial : ℝ) * ((d.choose t : ℕ) : ℝ) * (s : ℝ) ^ t := by rw [hdesc_d]
        _ = (t.factorial : ℝ) * ((d.choose t * s ^ t : ℕ) : ℝ) := by push_cast; ring
    exact lt_of_mul_lt_mul_left h1 hfac_pos.le
  linarith

/- ### Part 3: Assembly of `main` -/

theorem main : H1 → H2 → OMA.R_Erdos161_erdos_161_parts_ii_R1.H2 := by
  intro h1 h2 t ht α hα0 hα1
  let d : ℕ := max t (⌈(t : ℝ) ^ 2 / α⌉₊ + 1)
  have htd : t ≤ d := le_max_left _ _
  have hdα : (t : ℝ) ^ 2 < α * (d : ℝ) := by
    have h1' : ((⌈(t : ℝ) ^ 2 / α⌉₊ + 1 : ℕ) : ℝ) ≤ (d : ℝ) :=
      Nat.cast_le.mpr (le_max_right t (⌈(t : ℝ) ^ 2 / α⌉₊ + 1))
    rw [Nat.cast_add, Nat.cast_one] at h1'
    have h2' : (t : ℝ) ^ 2 / α ≤ (⌈(t : ℝ) ^ 2 / α⌉₊ : ℝ) := Nat.le_ceil _
    have h3' : (t : ℝ) ^ 2 / α < (d : ℝ) := by linarith
    have h4' := (div_lt_iff₀ hα0).mp h3'
    linarith
  obtain ⟨R, hdR, hRam⟩ := h1 t d ht htd
  have hRd_pos : (0 : ℝ) < (R.choose d : ℝ) := by exact_mod_cast Nat.choose_pos hdR
  let δ : ℝ := 1 / (2 * (R.choose d : ℝ))
  have hδ0 : 0 < δ := by positivity
  obtain ⟨c, hc0, hEv⟩ := h2 t d ht htd δ hδ0
  have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  refine ⟨(d : ℝ) * c, by positivity, ?_⟩
  filter_upwards [hEv, eventually_ge_atTop R] with n hn hRn col
  obtain ⟨b, hb_cliques⟩ := supersaturation_monochromatic_cliques hdR hRn hRam col
  obtain ⟨s, V, hs1, hs_size, hVcard, hVdisj, hVmono⟩ :=
    hn (fun e ↦ col e == b) hb_cliques
  let X : Finset (Fin n) := Finset.univ.biUnion V
  have hXcard : X.card = d * s := by
    rw [Finset.card_biUnion (fun i _ j _ hij ↦ hVdisj i j hij)]
    simp [hVcard]
  refine ⟨X, ?_, !b, ?_⟩
  · rw [hXcard, Nat.cast_mul]
    calc ((d : ℝ) * c) * (Real.log (n : ℝ)) ^ (((t : ℝ) - 1)⁻¹)
        = (d : ℝ) * (c * (Real.log (n : ℝ)) ^ (((t : ℝ) - 1)⁻¹)) := by ring
      _ ≤ (d : ℝ) * (s : ℝ) := mul_le_mul_of_nonneg_left hs_size hd_pos.le
  · have hT_sub : (X.powersetCard t).filter (fun e ↦ ∀ i, (e ∩ V i).card ≤ 1) ⊆
        (X.powersetCard t).filter (fun e ↦ col e = b) := by
      intro e he
      rw [Finset.mem_filter, Finset.mem_powersetCard] at he ⊢
      refine ⟨he.1, ?_⟩
      have hG : (col e == b) = true := hVmono e he.1.2 (fun x hx ↦ by
        have hxX : x ∈ X := he.1.1 hx
        rw [Finset.mem_biUnion] at hxX
        obtain ⟨i, _, hxi⟩ := hxX
        exact ⟨i, hxi⟩) he.2
      exact beq_iff_eq.mp hG
    have hmono_ge : d.choose t * s ^ t ≤ ((X.powersetCard t).filter (fun e ↦ col e = b)).card :=
      (transverse_subsets_card_ge V hVcard hVdisj).trans (Finset.card_le_card hT_sub)
    have hcomp_card :
        ((X.powersetCard t).filter (fun e ↦ col e = b)).card +
        ((X.powersetCard t).filter (fun e ↦ col e = !b)).card = X.card.choose t := by
      have hpart := Finset.card_filter_add_card_filter_not (s := X.powersetCard t)
        (p := fun e ↦ col e = b)
      rw [Finset.card_powersetCard] at hpart
      have hneg : (X.powersetCard t).filter (fun e ↦ ¬ col e = b) =
          (X.powersetCard t).filter (fun e ↦ col e = !b) := by
        refine Finset.filter_congr fun e _ ↦ ?_
        cases col e <;> cases b <;> decide
      rwa [hneg] at hpart
    have hle : (((X.powersetCard t).filter (fun e ↦ col e = !b)).card : ℝ) ≤
        ((X.card.choose t : ℕ) : ℝ) - ((d.choose t * s ^ t : ℕ) : ℝ) := by
      have hcast : (((X.powersetCard t).filter (fun e ↦ col e = b)).card : ℝ) +
          (((X.powersetCard t).filter (fun e ↦ col e = !b)).card : ℝ) =
          ((X.card.choose t : ℕ) : ℝ) := by exact_mod_cast hcomp_card
      have hge : ((d.choose t * s ^ t : ℕ) : ℝ) ≤
          (((X.powersetCard t).filter (fun e ↦ col e = b)).card : ℝ) := by
        exact_mod_cast hmono_ge
      linarith
    rw [hXcard] at hle ⊢
    exact lt_of_le_of_lt hle (multipartite_density_lt htd hs1 hα0 hα1 hdα)

end OMA.R_Erdos161_erdos_161_parts_ii_R1_H2_R1
