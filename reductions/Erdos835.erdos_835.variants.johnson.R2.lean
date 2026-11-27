import FormalConjectures.ErdosProblems.«835»

/-!
# Reduction R2 of Erdos Problem 835 to Large Sets of Steiner Systems on 2p - 3 Points

Reduces `Erdos835.erdos_835.variants.johnson` to the open prime frontier `p ≥ 17` (`k = p - 1 ≥ 16`)
in pure hypergraph / Steiner-design form on `2p - 3` points (`LS(p - 3, p - 2, 2p - 3)`), paired
with two true combinatorial lemmas (`H2` for `(p - 3)`-intersection separation via clique
bijectivity, and `H3` for disjoint-block separation at odd prime `p`).
-/

-- Credit: @nijv

open Finset SimpleGraph

namespace OMA.R_Erdos835_erdos_835_variants_johnson_R2

/-- Existence at some prime `p ≥ 17` of a `p`-coloring of the `(p - 2)`-subsets of `2p - 3`
points such that every `(p - 3)`-subset extends to all `p` colors (equivalently, a large set of
Steiner systems `LS(p - 3, p - 2, 2p - 3)` at the open prime frontier `k = p - 1 ≥ 16`). -/
def H1 : Prop :=
  ∃ (p : ℕ), Nat.Prime p ∧ 17 ≤ p ∧
    ∃ c : Finset (Fin (2 * p - 3)) → Fin p,
      ∀ T : Finset (Fin (2 * p - 3)), #T = p - 3 →
        ∀ γ : Fin p, ∃ y : Fin (2 * p - 3), y ∉ T ∧ c (insert y T) = γ

/-- Surjective color coverage on `(p - 3)`-subsets of `2p - 3` points forces any two `(p - 2)`-sets
sharing `p - 3` points to receive distinct colors. -/
def H2 : Prop :=
  ∀ (p : ℕ), Nat.Prime p → 5 ≤ p →
    ∀ c : Finset (Fin (2 * p - 3)) → Fin p,
      (∀ T : Finset (Fin (2 * p - 3)), #T = p - 3 →
        ∀ γ : Fin p, ∃ y : Fin (2 * p - 3), y ∉ T ∧ c (insert y T) = γ) →
      ∀ A B : Finset (Fin (2 * p - 3)),
        #A = p - 2 → #B = p - 2 → #(A ∩ B) = p - 3 → c A ≠ c B

/-- For prime `p ≥ 5`, any `p`-coloring of `(p - 2)`-subsets of `2p - 3` points that separates
pairs meeting in `p - 3` points also separates disjoint `(p - 2)`-subsets. -/
def H3 : Prop :=
  ∀ (p : ℕ), Nat.Prime p → 5 ≤ p →
    ∀ c : Finset (Fin (2 * p - 3)) → Fin p,
      (∀ A B : Finset (Fin (2 * p - 3)),
        #A = p - 2 → #B = p - 2 → #(A ∩ B) = p - 3 → c A ≠ c B) →
      ∀ A B : Finset (Fin (2 * p - 3)),
        #A = p - 2 → #B = p - 2 → Disjoint A B → c A ≠ c B

lemma clique_lower_bound (k : ℕ) (hk : 3 ≤ k) :
    ((k + 1 : ℕ) : ℕ∞) ≤ J(2 * k, k).chromaticNumber := by
  classical
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset (Fin (2 * k)))) (n := k - 1) (by simp; omega)
  let f (i : (sᶜ : Finset (Fin (2 * k)))) :
      {v : Finset (Fin (2 * k)) // v.card = k} :=
    ⟨insert i.val s, by
      rw [Finset.card_insert_of_notMem (Finset.mem_compl.mp i.property), hs]
      omega⟩
  apply SimpleGraph.le_chromaticNumber_of_pairwise_adj (ι := ↑(sᶜ : Finset (Fin (2 * k))))
    (f := f)
  · rw [Nat.card_eq_fintype_card, Fintype.card_coe, Finset.card_compl, Fintype.card_fin, hs]
    omega
  · intro i j hij
    have hne : i.val ≠ j.val := fun h => hij (Subtype.ext h)
    have h : insert i.val s ∩ insert j.val s = s := by
      ext z
      simp only [Finset.mem_inter, Finset.mem_insert]
      by_cases hz : z ∈ s
      · simp [hz]
      · simp only [hz, or_false, iff_false, not_and]
        exact fun he hf => hne (he.symm.trans hf)
    change (insert i.val s ∩ insert j.val s).card + 1 = k
    rw [h, hs]
    omega

theorem main : H1 → H2 → H3 → type_of% @Erdos835.erdos_835.variants.johnson := by
  classical
  rintro ⟨p, hp, hp17, c, hcov⟩ h₂ h₃
  have hp5 : 5 ≤ p := by omega
  have hadj_ne := h₂ p hp hp5 c hcov
  have hdisj_ne := h₃ p hp hp5 c hadj_ne
  let l : ℕ := p - 4
  let k : ℕ := l + 3
  have hk_eq : k = p - 1 := by omega
  have hk3 : 3 ≤ k := by omega
  have hp_eq : p = k + 1 := by omega
  let x₀ : Fin (2 * k) := ⟨2 * p - 3, by omega⟩
  let emb : Fin (2 * p - 3) ↪ Fin (2 * k) :=
    ⟨fun u => ⟨u.1, by omega⟩, fun u₁ u₂ h => Fin.ext (Fin.mk.inj h)⟩
  let proj (S : Finset (Fin (2 * k))) : Finset (Fin (2 * p - 3)) :=
    Finset.univ.filter (fun u => emb u ∈ S)
  have hmap_proj : ∀ S : Finset (Fin (2 * k)), (proj S).map emb = S.erase x₀ := by
    intro S
    ext z
    simp only [proj, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
    constructor
    · rintro ⟨u, huS, rfl⟩
      refine ⟨?_, huS⟩
      intro hzx
      have hval : u.1 = 2 * p - 3 := Fin.mk.inj hzx
      omega
    · rintro ⟨hzx, hzS⟩
      have hne : z.1 ≠ 2 * p - 3 := fun hv => hzx (Fin.ext hv)
      have hlt : z.1 < 2 * p - 3 := by omega
      exact ⟨⟨z.1, hlt⟩, hzS, Fin.ext rfl⟩
  have hcard_proj : ∀ S : Finset (Fin (2 * k)), #(proj S) = #(S.erase x₀) := by
    intro S
    rw [← hmap_proj S, Finset.card_map]
  have hinter_proj : ∀ S₁ S₂ : Finset (Fin (2 * k)),
      proj S₁ ∩ proj S₂ = proj (S₁ ∩ S₂) := by
    intro S₁ S₂
    ext u
    simp [proj]
  have hdisj_proj : ∀ S₁ S₂ : Finset (Fin (2 * k)),
      (S₁ ∩ S₂).erase x₀ = ∅ → Disjoint (proj S₁) (proj S₂) := by
    intro S₁ S₂ hEmpty
    rw [Finset.disjoint_iff_inter_eq_empty, hinter_proj]
    have hcard0 : #(proj (S₁ ∩ S₂)) = 0 := by
      rw [hcard_proj, hEmpty, Finset.card_empty]
    exact Finset.card_eq_zero.mp hcard0
  let fold (v : {s : Finset (Fin (2 * k)) // s.card = k}) : Finset (Fin (2 * k)) :=
    if x₀ ∈ v.val then v.val else v.valᶜ
  have hx₀_fold : ∀ v : {s : Finset (Fin (2 * k)) // s.card = k}, x₀ ∈ fold v := by
    intro v
    by_cases hx : x₀ ∈ v.val
    · simp [fold, hx]
    · simp [fold, hx]
  have hcard_fold : ∀ v : {s : Finset (Fin (2 * k)) // s.card = k}, #(fold v) = k := by
    intro v
    by_cases hx : x₀ ∈ v.val
    · simp [fold, hx, v.property]
    · simp only [fold, if_neg hx, Finset.card_compl, Fintype.card_fin, v.property]
      omega
  have hcard_proj_fold : ∀ v : {s : Finset (Fin (2 * k)) // s.card = k},
      #(proj (fold v)) = p - 2 := by
    intro v
    rw [hcard_proj, Finset.card_erase_of_mem (hx₀_fold v), hcard_fold v]
    omega
  have hcross : ∀ (a b : {s : Finset (Fin (2 * k)) // s.card = k}),
      x₀ ∈ a.val → x₀ ∉ b.val → (a.val ∩ b.val).card + 1 = k →
      (a.val ∩ b.valᶜ).erase x₀ = ∅ := by
    intro a b ha hb hab
    have hcount := Finset.card_sdiff_of_subset (Finset.inter_subset_left : a.val ∩ b.val ⊆ a.val)
    rw [a.property] at hcount
    have hset : a.val \ (a.val ∩ b.val) = a.val ∩ b.valᶜ := by
      ext z
      simp only [Finset.mem_sdiff, Finset.mem_inter, Finset.mem_compl]
      tauto
    rw [hset] at hcount
    have hsingle : (a.val ∩ b.valᶜ).card = 1 := by omega
    have hx_mem : x₀ ∈ a.val ∩ b.valᶜ := Finset.mem_inter.mpr ⟨ha, Finset.mem_compl.mpr hb⟩
    have heq_sing : a.val ∩ b.valᶜ = {x₀} :=
      (Finset.eq_of_subset_of_card_le (Finset.singleton_subset_iff.mpr hx_mem)
        (by simp [hsingle])).symm
    rw [heq_sing, Finset.erase_singleton]
  let col (v : {s : Finset (Fin (2 * k)) // s.card = k}) : Fin (k + 1) :=
    Fin.cast hp_eq (c (proj (fold v)))
  have hc_colorable : J(2 * k, k).Colorable (k + 1) := by
    refine ⟨SimpleGraph.Coloring.mk col ?_⟩
    intro v w hadj
    have hcard : (v.val ∩ w.val).card + 1 = k := hadj
    intro hcol_eq
    have hc_eq : c (proj (fold v)) = c (proj (fold w)) := Fin.cast_injective hp_eq hcol_eq
    have hcv_card := hcard_proj_fold v
    have hcw_card := hcard_proj_fold w
    by_cases hv : x₀ ∈ v.val <;> by_cases hw : x₀ ∈ w.val
    · have hfv : fold v = v.val := if_pos hv
      have hfw : fold w = w.val := if_pos hw
      have hx_inter : x₀ ∈ v.val ∩ w.val := Finset.mem_inter.mpr ⟨hv, hw⟩
      have hinter_card : #(proj (fold v) ∩ proj (fold w)) = p - 3 := by
        rw [hfv, hfw, hinter_proj, hcard_proj, Finset.card_erase_of_mem hx_inter]
        omega
      exact hadj_ne (proj (fold v)) (proj (fold w)) hcv_card hcw_card hinter_card hc_eq
    · have hfv : fold v = v.val := if_pos hv
      have hfw : fold w = w.valᶜ := if_neg hw
      have hdisj : Disjoint (proj (fold v)) (proj (fold w)) := by
        rw [hfv, hfw]
        exact hdisj_proj v.val w.valᶜ (hcross v w hv hw hcard)
      exact hdisj_ne (proj (fold v)) (proj (fold w)) hcv_card hcw_card hdisj hc_eq
    · have hfv : fold v = v.valᶜ := if_neg hv
      have hfw : fold w = w.val := if_pos hw
      have hwv : (w.val ∩ v.val).card + 1 = k := by simpa only [Finset.inter_comm] using hcard
      have hdisj : Disjoint (proj (fold w)) (proj (fold v)) := by
        rw [hfw, hfv]
        exact hdisj_proj w.val v.valᶜ (hcross w v hw hv hwv)
      exact hdisj_ne (proj (fold w)) (proj (fold v)) hcw_card hcv_card hdisj hc_eq.symm
    · have hfv : fold v = v.valᶜ := if_neg hv
      have hfw : fold w = w.valᶜ := if_neg hw
      have hx_inter : x₀ ∈ v.valᶜ ∩ w.valᶜ :=
        Finset.mem_inter.mpr ⟨Finset.mem_compl.mpr hv, Finset.mem_compl.mpr hw⟩
      have hunion := Finset.card_union_add_card_inter v.val w.val
      rw [v.property, w.property] at hunion
      have hcompl_card : #(v.valᶜ ∩ w.valᶜ) = p - 2 := by
        rw [← Finset.compl_union, Finset.card_compl, Fintype.card_fin]
        omega
      have hinter_card : #(proj (fold v) ∩ proj (fold w)) = p - 3 := by
        rw [hfv, hfw, hinter_proj, hcard_proj, Finset.card_erase_of_mem hx_inter, hcompl_card]
        omega
      exact hadj_ne (proj (fold v)) (proj (fold w)) hcv_card hcw_card hinter_card hc_eq
  refine ⟨l, ?_⟩
  change J(2 * k, k).chromaticNumber = ((k : ℕ) : ℕ∞) + 1
  rw [← Nat.cast_add_one]
  exact le_antisymm hc_colorable.chromaticNumber_le (clique_lower_bound k hk3)

end OMA.R_Erdos835_erdos_835_variants_johnson_R2
