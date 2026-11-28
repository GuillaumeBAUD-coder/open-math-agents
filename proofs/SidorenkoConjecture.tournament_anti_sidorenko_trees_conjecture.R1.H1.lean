import OMAReductions.R_SidorenkoConjecture_tournament_anti_sidorenko_trees_conjecture_R1
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Proof of `SidorenkoConjecture.tournament_anti_sidorenko_trees_conjecture.R1.H1`

Every star `T` admits a balanced orientation `D` (`⌈k/2⌉` out-leaves and `⌊k/2⌋` in-leaves from
the star centre) whose homomorphism density in every finite tournament `G` is at most `(1 / 2) ^ k`.
-/

-- Step SidorenkoConjecture.tournament_anti_sidorenko_trees_conjecture.R1.H1: hypothesis H1 of reduction SidorenkoConjecture.tournament_anti_sidorenko_trees_conjecture.R1
-- Credit: @LiJiaHua1024

namespace OMA.Step_Sidorenko_TAS_Stars

open Finset SimpleGraph

/-- In a tree where every edge contains `c`, every vertex `v ≠ c` is adjacent to `c`. -/
lemma star_adj_of_ne {V : Type*} (T : SimpleGraph V) (hT : T.IsTree) (c : V)
    (hc : ∀ u v : V, T.Adj u v → u = c ∨ v = c) {v : V} (hv : v ≠ c) :
    T.Adj c v := by
  obtain ⟨p, hp⟩ := (hT.connected c v).exists_isPath
  cases p with
  | nil => exact absurd rfl hv.symm
  | @cons _ u _ h1 q =>
    cases q with
    | nil => exact h1
    | @cons _ w _ h2 r =>
      rcases hc u w h2 with rfl | rfl
      · exact absurd rfl (T.ne_of_adj h1)
      · have hnodup := hp.support_nodup
        simp at hnodup

lemma star_adj_iff {V : Type*} (T : SimpleGraph V) (hT : T.IsTree) (c : V)
    (hc : ∀ u v : V, T.Adj u v → u = c ∨ v = c) (u v : V) :
    T.Adj u v ↔ (u = c ∧ v ≠ c) ∨ (v = c ∧ u ≠ c) := by
  constructor
  · intro huv
    have hne := T.ne_of_adj huv
    rcases hc u v huv with rfl | rfl
    · exact Or.inl ⟨rfl, hne.symm⟩
    · exact Or.inr ⟨rfl, hne⟩
  · rintro (⟨rfl, hv⟩ | ⟨rfl, hu⟩)
    · exact star_adj_of_ne T hT u hc hv
    · exact (star_adj_of_ne T hT v hc hu).symm

/-- Canonical model of an oriented star with out-leaf type `A` and in-leaf type `B`. -/
def modelStar (A B : Type*) : Digraph (Option (A ⊕ B)) where
  Adj o₁ o₂ :=
    (o₁ = none ∧ ∃ a : A, o₂ = some (Sum.inl a)) ∨
    (∃ b : B, o₁ = some (Sum.inr b) ∧ o₂ = none)

lemma homCount_modelStar {A B W : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] [Fintype W] [DecidableEq W]
    [DecidableRel (modelStar A B).Adj]
    (G : Digraph W) [DecidableRel G.Adj] :
    Digraph.homCount (modelStar A B) G =
      ∑ x : W,
        (Finset.univ.filter (fun y => G.Adj x y)).card ^ Fintype.card A *
        (Finset.univ.filter (fun y => G.Adj y x)).card ^ Fintype.card B := by
  unfold Digraph.homCount
  let Nout (x : W) : Finset W := Finset.univ.filter (fun y => G.Adj x y)
  let Nin (x : W) : Finset W := Finset.univ.filter (fun y => G.Adj y x)
  have hEquiv : (modelStar A B →g G) ≃
      Σ x : W, (A → ↥(Nout x)) × (B → ↥(Nin x)) :=
    { toFun := fun f =>
        ⟨f none,
          (fun a => ⟨f (some (Sum.inl a)), Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            f.map_adj' (Or.inl ⟨rfl, a, rfl⟩)⟩⟩,
           fun b => ⟨f (some (Sum.inr b)), Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            f.map_adj' (Or.inr ⟨b, rfl, rfl⟩)⟩⟩)⟩
      invFun := fun ⟨x, g1, g2⟩ =>
        { toFun := fun o => match o with
            | none => x
            | some (Sum.inl a) => (g1 a).1
            | some (Sum.inr b) => (g2 b).1
          map_adj' := by
            rintro o₁ o₂ (⟨rfl, a, rfl⟩ | ⟨b, rfl, rfl⟩)
            · exact (Finset.mem_filter.mp (g1 a).2).2
            · exact (Finset.mem_filter.mp (g2 b).2).2 }
      left_inv := fun f => by
        apply OMA.R_SidorenkoConjecture_tournament_anti_sidorenko_trees_conjecture_R1.hom_ext
        funext o
        rcases o with _ | (a | b) <;> rfl
      right_inv := fun ⟨x, g1, g2⟩ => rfl }
  rw [Fintype.card_congr hEquiv, Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro x _
  rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fun, Fintype.card_coe, Fintype.card_coe]

/-- In a tournament on `W`, out-degree + in-degree equals `|W| - 1` at every vertex. -/
lemma tournament_deg_sum {W : Type*} [Fintype W] [DecidableEq W]
    (G : Digraph W) [DecidableRel G.Adj] (hG : G.IsTournament) (x : W) :
    (Finset.univ.filter (fun y => G.Adj x y)).card +
      (Finset.univ.filter (fun y => G.Adj y x)).card = Fintype.card W - 1 := by
  let Nout : Finset W := Finset.univ.filter (fun y => G.Adj x y)
  let Nin : Finset W := Finset.univ.filter (fun y => G.Adj y x)
  have hdisj : Disjoint Nout Nin := by
    rw [Finset.disjoint_left]
    intro y h1 h2
    have hadj1 : G.Adj x y := (Finset.mem_filter.mp h1).2
    have hadj2 : G.Adj y x := (Finset.mem_filter.mp h2).2
    have hne : x ≠ y := fun h => hG.1 x (h ▸ hadj1)
    exact ((hG.2 x y hne).mp hadj1) hadj2
  have hunion : Nout ∪ Nin = (Finset.univ : Finset W).erase x := by
    ext y
    simp only [Nout, Nin, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_erase, and_true, ne_eq]
    constructor
    · rintro (h1 | h2)
      · exact fun hy => hG.1 x (hy ▸ h1)
      · exact fun hy => hG.1 x (hy ▸ h2)
    · intro hyx
      by_cases hxy : G.Adj x y
      · exact Or.inl hxy
      · refine Or.inr ?_
        by_contra hnyx
        exact hxy ((hG.2 x y (fun h => hyx h.symm)).mpr hnyx)
  rw [← Finset.card_union_of_disjoint hdisj, hunion,
    Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ]

lemma tournament_sum_out_eq_sum_in {W : Type*} [Fintype W] [DecidableEq W]
    (G : Digraph W) [DecidableRel G.Adj] :
    ∑ x : W, (Finset.univ.filter (fun y => G.Adj x y)).card =
      ∑ x : W, (Finset.univ.filter (fun y => G.Adj y x)).card := by
  simp only [Finset.card_filter]
  exact Finset.sum_comm

lemma tournament_two_mul_sum_out_le {W : Type*} [Fintype W] [DecidableEq W]
    (G : Digraph W) [DecidableRel G.Adj] (hG : G.IsTournament) :
    2 * (∑ x : W, (Finset.univ.filter (fun y => G.Adj x y)).card) ≤ Fintype.card W ^ 2 := by
  have h1 : 2 * (∑ x : W, (Finset.univ.filter (fun y => G.Adj x y)).card) =
      ∑ x : W, ((Finset.univ.filter (fun y => G.Adj x y)).card +
        (Finset.univ.filter (fun y => G.Adj y x)).card) := by
    rw [two_mul, Finset.sum_add_distrib, ← tournament_sum_out_eq_sum_in G]
  rw [h1]
  have h2 : ∀ x ∈ (Finset.univ : Finset W),
      (Finset.univ.filter (fun y => G.Adj x y)).card +
        (Finset.univ.filter (fun y => G.Adj y x)).card ≤ Fintype.card W := by
    intro x _
    rw [tournament_deg_sum G hG x]
    exact Nat.sub_le _ _
  calc ∑ x : W, ((Finset.univ.filter (fun y => G.Adj x y)).card +
          (Finset.univ.filter (fun y => G.Adj y x)).card)
      ≤ ∑ _x : W, Fintype.card W := Finset.sum_le_sum h2
    _ = Fintype.card W ^ 2 := by simp [sq]

lemma prod_pow_bound {u v m b : ℕ} (huv : u + v ≤ m) :
    2 ^ (2 * b) * (u ^ b * v ^ b) ≤ m ^ (2 * b) := by
  have h4 : 4 * (u * v) ≤ m ^ 2 := by
    have hsq : 4 * (u * v) ≤ (u + v) ^ 2 := by
      zify
      nlinarith [sq_nonneg ((u : ℤ) - (v : ℤ))]
    exact hsq.trans (Nat.pow_le_pow_left huv 2)
  have hpow := Nat.pow_le_pow_left h4 b
  calc 2 ^ (2 * b) * (u ^ b * v ^ b)
      = (4 * (u * v)) ^ b := by
        rw [pow_mul, show 2 ^ 2 = 4 by norm_num, mul_pow, mul_pow]
    _ ≤ (m ^ 2) ^ b := hpow
    _ = m ^ (2 * b) := (pow_mul m 2 b).symm

lemma nat_tas_star_bound {W : Type*} [Fintype W] [DecidableEq W]
    (G : Digraph W) [DecidableRel G.Adj] (hG : G.IsTournament) (k : ℕ) :
    2 ^ k *
      (∑ x : W,
        (Finset.univ.filter (fun y => G.Adj x y)).card ^ ((k + 1) / 2) *
        (Finset.univ.filter (fun y => G.Adj y x)).card ^ (k / 2)) ≤
      Fintype.card W ^ (k + 1) := by
  let m := Fintype.card W
  let u (x : W) := (Finset.univ.filter (fun y => G.Adj x y)).card
  let v (x : W) := (Finset.univ.filter (fun y => G.Adj y x)).card
  have huv : ∀ x : W, u x + v x ≤ m := by
    intro x
    dsimp [u, v, m]
    rw [tournament_deg_sum G hG x]
    exact Nat.sub_le _ _
  let b := k / 2
  have hb_eq : k / 2 = b := rfl
  by_cases heven : k % 2 = 0
  · have hk : k = 2 * b := by omega
    have ha : (k + 1) / 2 = b := by omega
    change 2 ^ k * (∑ x : W, u x ^ ((k + 1) / 2) * v x ^ (k / 2)) ≤ m ^ (k + 1)
    rw [ha, hb_eq, hk, Finset.mul_sum]
    calc ∑ x : W, 2 ^ (2 * b) * (u x ^ b * v x ^ b)
        ≤ ∑ _x : W, m ^ (2 * b) := Finset.sum_le_sum fun x _ => prod_pow_bound (huv x)
      _ = m * m ^ (2 * b) := by simp [m]
      _ = m ^ (2 * b + 1) := by rw [← pow_succ']
  · have hk : k = 2 * b + 1 := by omega
    have ha : (k + 1) / 2 = b + 1 := by omega
    change 2 ^ k * (∑ x : W, u x ^ ((k + 1) / 2) * v x ^ (k / 2)) ≤ m ^ (k + 1)
    rw [ha, hb_eq, hk]
    have hstep : ∑ x : W, 2 ^ (2 * b) * (u x ^ (b + 1) * v x ^ b) ≤
        m ^ (2 * b) * ∑ x : W, u x := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun x _ => ?_
      calc 2 ^ (2 * b) * (u x ^ (b + 1) * v x ^ b)
          = (2 ^ (2 * b) * (u x ^ b * v x ^ b)) * u x := by ring
        _ ≤ m ^ (2 * b) * u x := Nat.mul_le_mul_right (u x) (prod_pow_bound (huv x))
    calc 2 ^ (2 * b + 1) * ∑ x : W, u x ^ (b + 1) * v x ^ b
        = 2 * (∑ x : W, 2 ^ (2 * b) * (u x ^ (b + 1) * v x ^ b)) := by
          rw [pow_succ, mul_comm (2 ^ (2 * b)) 2, mul_assoc, Finset.mul_sum]
      _ ≤ 2 * (m ^ (2 * b) * ∑ x : W, u x) := Nat.mul_le_mul_left 2 hstep
      _ = m ^ (2 * b) * (2 * ∑ x : W, u x) := by ring
      _ ≤ m ^ (2 * b) * m ^ 2 := Nat.mul_le_mul_left _ (tournament_two_mul_sum_out_le G hG)
      _ = m ^ (2 * b + 2) := by rw [← pow_add]

end OMA.Step_Sidorenko_TAS_Stars

theorem OMA.solution :
    OMA.R_SidorenkoConjecture_tournament_anti_sidorenko_trees_conjecture_R1.H1 := by
  intro V _ _ T _ hT ⟨c, hc⟩
  classical
  let L : Finset V := (Finset.univ : Finset V).erase c
  let k : ℕ := L.card
  obtain ⟨L_out, hLout_sub, hLout_card⟩ :=
    Finset.exists_subset_card_eq (s := L) (n := (k + 1) / 2) (by dsimp [k]; omega)
  let L_in : Finset V := L \ L_out
  have hLin_sub : L_in ⊆ L := Finset.sdiff_subset
  have hLin_card : L_in.card = k / 2 := by
    dsimp [L_in]
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hLout_sub, hLout_card]
    dsimp [k]
    omega
  have hout_c : c ∉ L_out := fun h => (Finset.mem_erase.mp (hLout_sub h)).1 rfl
  have hin_c : c ∉ L_in := fun h => (Finset.mem_erase.mp (hLin_sub h)).1 rfl
  have hdisj : Disjoint L_out L_in := disjoint_sdiff_self_right
  have hcov : ∀ v : V, v ≠ c → v ∈ L_out ∨ v ∈ L_in := by
    intro v hv
    have hvL : v ∈ L := Finset.mem_erase.mpr ⟨hv, Finset.mem_univ v⟩
    by_cases h1 : v ∈ L_out
    · exact Or.inl h1
    · exact Or.inr (Finset.mem_sdiff.mpr ⟨hvL, h1⟩)
  let D : Digraph V :=
    { Adj := fun u v => (u = c ∧ v ∈ L_out) ∨ (u ∈ L_in ∧ v = c) }
  have hTreeCard : T.edgeFinset.card + 1 = Fintype.card V := hT.card_edgeFinset
  have hLcard : L.card + 1 = Fintype.card V := by
    dsimp [L]
    have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨c⟩
    rw [Finset.card_erase_of_mem (Finset.mem_univ c), Finset.card_univ]
    omega
  have hk_edges : T.edgeFinset.card = k := by
    dsimp [k]
    omega
  refine ⟨D, ⟨?_, ?_⟩, ?_⟩
  · intro u v huv
    rcases huv with ⟨rfl, hv⟩ | ⟨hu, rfl⟩
    · exact OMA.Step_Sidorenko_TAS_Stars.star_adj_of_ne T hT u hc
        (Finset.mem_erase.mp (hLout_sub hv)).1
    · exact (OMA.Step_Sidorenko_TAS_Stars.star_adj_of_ne T hT v hc
        (Finset.mem_erase.mp (hLin_sub hu)).1).symm
  · intro u v huv
    rcases (OMA.Step_Sidorenko_TAS_Stars.star_adj_iff T hT c hc u v).mp huv with
      ⟨rfl, hv⟩ | ⟨rfl, hu⟩
    · constructor
      · rintro (⟨-, hv1⟩ | ⟨hc2, -⟩) (⟨hvc, -⟩ | ⟨hv2, -⟩)
        · exact hv hvc
        · exact Finset.disjoint_left.mp hdisj hv1 hv2
        · exact hin_c hc2
        · exact hin_c hc2
      · intro hnot
        rcases hcov v hv with hv1 | hv2
        · exact Or.inl ⟨rfl, hv1⟩
        · exact absurd (Or.inr ⟨hv2, rfl⟩) hnot
    · constructor
      · rintro (⟨huc, -⟩ | ⟨hu2, -⟩)
        · exact absurd huc hu
        · rintro (⟨-, hu1⟩ | ⟨hc2, -⟩)
          · exact Finset.disjoint_right.mp hdisj hu2 hu1
          · exact hin_c hc2
      · intro hnot
        rcases hcov u hu with hu1 | hu2
        · exact absurd (Or.inl ⟨rfl, hu1⟩) hnot
        · exact Or.inr ⟨hu2, rfl⟩
  · intro W _ _ instNonempty G instDecG hG
    let e : V ≃ Option (↥L_out ⊕ ↥L_in) :=
      { toFun := fun v =>
          if h1 : v ∈ L_out then some (Sum.inl ⟨v, h1⟩)
          else if h2 : v ∈ L_in then some (Sum.inr ⟨v, h2⟩)
          else none
        invFun := fun o => match o with
          | none => c
          | some (Sum.inl u) => u.1
          | some (Sum.inr u) => u.1
        left_inv := fun v => by
          by_cases h1 : v ∈ L_out
          · simp [h1]
          · by_cases h2 : v ∈ L_in
            · simp [h1, h2]
            · have hvc : v = c := by
                by_contra hne
                rcases hcov v hne with h | h
                · exact h1 h
                · exact h2 h
              subst hvc
              simp [hout_c, hin_c]
        right_inv := fun o => by
          rcases o with _ | (⟨u, hu⟩ | ⟨u, hu⟩)
          · simp [hout_c, hin_c]
          · simp [hu]
          · have hnot : u ∉ L_out := Finset.disjoint_right.mp hdisj hu
            simp [hnot, hu] }
    have hD_iff : ∀ u v, D.Adj u v ↔
        (OMA.Step_Sidorenko_TAS_Stars.modelStar ↥L_out ↥L_in).Adj (e u) (e v) := by
      intro u v
      constructor
      · rintro (⟨rfl, hv⟩ | ⟨hu, rfl⟩)
        · left
          refine ⟨by simp [e, hout_c, hin_c], ⟨v, hv⟩, by simp [e, hv]⟩
        · right
          have hnot : u ∉ L_out := Finset.disjoint_right.mp hdisj hu
          exact ⟨⟨u, hu⟩, by simp [e, hnot, hu], by simp [e, hout_c, hin_c]⟩
      · rintro (⟨hu0, ⟨a, ha⟩, hv0⟩ | ⟨⟨b, hb⟩, hu0, hv0⟩)
        · have huc : u = c := (e.symm_apply_apply u).symm.trans (by rw [hu0]; rfl)
          have hva : v = a := (e.symm_apply_apply v).symm.trans (by rw [hv0]; rfl)
          subst huc hva
          exact Or.inl ⟨rfl, ha⟩
        · have hub : u = b := (e.symm_apply_apply u).symm.trans (by rw [hu0]; rfl)
          have hvc : v = c := (e.symm_apply_apply v).symm.trans (by rw [hv0]; rfl)
          subst hub hvc
          exact Or.inr ⟨hb, rfl⟩
    unfold Digraph.homDensity Digraph.homCount
    have hcard_hom : Fintype.card (D →g G) =
        ∑ x : W,
          (Finset.univ.filter (fun y => G.Adj x y)).card ^ ((k + 1) / 2) *
          (Finset.univ.filter (fun y => G.Adj y x)).card ^ (k / 2) := by
      have : DecidableRel (OMA.Step_Sidorenko_TAS_Stars.modelStar ↥L_out ↥L_in).Adj :=
        Classical.decRel _
      have hc1 : Fintype.card (D →g G) =
          Digraph.homCount (OMA.Step_Sidorenko_TAS_Stars.modelStar ↥L_out ↥L_in) G := by
        unfold Digraph.homCount
        refine Fintype.card_congr
          { toFun := fun f => ⟨fun o => f.toFun (e.symm o),
              fun {o₁ o₂} h => f.map_adj' ((hD_iff _ _).mpr (by simpa using h))⟩
            invFun := fun g => ⟨fun v => g.toFun (e v),
              fun {u v} h => g.map_adj' ((hD_iff u v).mp h)⟩
            left_inv := fun f =>
              OMA.R_SidorenkoConjecture_tournament_anti_sidorenko_trees_conjecture_R1.hom_ext
                (by funext v; simp)
            right_inv := fun g =>
              OMA.R_SidorenkoConjecture_tournament_anti_sidorenko_trees_conjecture_R1.hom_ext
                (by funext o; simp) }
      rw [hc1, OMA.Step_Sidorenko_TAS_Stars.homCount_modelStar G]
      simp only [Fintype.card_coe, hLout_card, hLin_card]
    have hcard_V : Fintype.card V = k + 1 := by omega
    rw [hcard_hom, hcard_V, hk_edges]
    let SNat : ℕ := ∑ x : W,
      (Finset.univ.filter (fun y => G.Adj x y)).card ^ ((k + 1) / 2) *
      (Finset.univ.filter (fun y => G.Adj y x)).card ^ (k / 2)
    change (SNat : ℝ) / (Fintype.card W : ℝ) ^ (k + 1) ≤ (1 / 2 : ℝ) ^ k
    have hnat : 2 ^ k * SNat ≤ Fintype.card W ^ (k + 1) :=
      OMA.Step_Sidorenko_TAS_Stars.nat_tas_star_bound G hG k
    have hreal : (2 : ℝ) ^ k * (SNat : ℝ) ≤ (Fintype.card W : ℝ) ^ (k + 1) := by
      exact_mod_cast hnat
    have hm_pos : (0 : ℝ) < (Fintype.card W : ℝ) ^ (k + 1) :=
      pow_pos (by exact_mod_cast Fintype.card_pos) (k + 1)
    have h2_pos : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
    rw [div_le_iff₀ hm_pos, one_div_pow]
    calc (SNat : ℝ)
        = ((2 : ℝ) ^ k * (SNat : ℝ)) / (2 : ℝ) ^ k :=
          (mul_div_cancel_left₀ (SNat : ℝ) h2_pos.ne').symm
      _ ≤ (Fintype.card W : ℝ) ^ (k + 1) / (2 : ℝ) ^ k :=
          div_le_div_of_nonneg_right hreal h2_pos.le
      _ = 1 / (2 : ℝ) ^ k * (Fintype.card W : ℝ) ^ (k + 1) := by ring
