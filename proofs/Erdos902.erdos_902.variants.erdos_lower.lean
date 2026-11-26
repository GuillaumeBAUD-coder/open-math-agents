import FormalConjectures.ErdosProblems.«902»
import Mathlib.Tactic

/-!
# Proof of Erdos 902 lower bound: 2^(n+1) - 1 <= f(n)
-/

section OMA902Lower

open Erdos902

abbrev omaUpperPairs (m : ℕ) := { p : Fin m × Fin m // p.1 < p.2 }

def omaTourOf {m : ℕ} (ω : omaUpperPairs m → Bool) : Digraph (Fin m) where
  Adj u v :=
    if h : u < v then ω ⟨(u, v), h⟩ = true
    else if h' : v < u then ω ⟨(v, u), h'⟩ = false
    else False

lemma omaTourOf_isTournament {m : ℕ} (ω : omaUpperPairs m → Bool) :
    (omaTourOf ω).IsTournament := by
  refine ⟨fun v => by simp [omaTourOf], fun u v huv => ?_⟩
  rcases lt_or_gt_of_ne huv with hlt | hgt
  · have hnot : ¬ v < u := asymm hlt
    simp [omaTourOf, hlt, hnot]
  · have hnot : ¬ u < v := asymm hgt
    simp [omaTourOf, hgt, hnot]

def omaEdgeOf {m : ℕ} {u v : Fin m} (huv : u ≠ v) : omaUpperPairs m :=
  if h : u < v then ⟨(u, v), h⟩
  else ⟨(v, u), lt_of_le_of_ne (le_of_not_gt h) huv.symm⟩

def omaWinBit {m : ℕ} (u v : Fin m) : Bool := decide (u < v)

lemma omaEdgeOf_eq_or {m : ℕ} {u₁ v₁ u₂ v₂ : Fin m} (h1 : u₁ ≠ v₁) (h2 : u₂ ≠ v₂)
    (heq : omaEdgeOf h1 = omaEdgeOf h2) :
    (u₁ = u₂ ∧ v₁ = v₂) ∨ (u₁ = v₂ ∧ v₁ = u₂) := by
  dsimp [omaEdgeOf] at heq
  by_cases c1 : u₁ < v₁ <;> by_cases c2 : u₂ < v₂
  · rw [dif_pos c1, dif_pos c2] at heq
    have hv := congrArg Subtype.val heq
    exact Or.inl ⟨congrArg Prod.fst hv, congrArg Prod.snd hv⟩
  · rw [dif_pos c1, dif_neg c2] at heq
    have hv := congrArg Subtype.val heq
    exact Or.inr ⟨congrArg Prod.fst hv, congrArg Prod.snd hv⟩
  · rw [dif_neg c1, dif_pos c2] at heq
    have hv := congrArg Subtype.val heq
    exact Or.inr ⟨congrArg Prod.snd hv, congrArg Prod.fst hv⟩
  · rw [dif_neg c1, dif_neg c2] at heq
    have hv := congrArg Subtype.val heq
    exact Or.inl ⟨congrArg Prod.snd hv, congrArg Prod.fst hv⟩

lemma omaTourOf_adj_iff {m : ℕ} (ω : omaUpperPairs m → Bool) {u v : Fin m} (huv : u ≠ v) :
    (omaTourOf ω).Adj u v ↔ ω (omaEdgeOf huv) = omaWinBit u v := by
  rcases lt_or_gt_of_ne huv with hlt | hgt
  · simp [omaTourOf, omaEdgeOf, omaWinBit, hlt]
  · have hnot : ¬ u < v := asymm hgt
    simp [omaTourOf, omaEdgeOf, omaWinBit, hgt, hnot]

lemma oma_exists_tournament_of_ineq {m n : ℕ}
    (hineq : m.choose n * (2 ^ n - 1) ^ (m - n) < (2 ^ n) ^ (m - n)) :
    ∃ G : Digraph (Fin m), G.IsTournament ∧ HasPropertyS G n := by
  classical
  let AllSub := (Finset.univ : Finset (Fin m)).powersetCard n
  let BadFor (E : Finset (Fin m)) : Finset (omaUpperPairs m → Bool) :=
    Finset.univ.filter (fun ω => ∀ x ∈ Finset.univ \ E, ¬ (∀ e ∈ E, (omaTourOf ω).Adj x e))
  have hBad_card : ∀ E ∈ AllSub,
      (BadFor E).card * (2 ^ n) ^ (m - n) =
        (2 ^ n - 1) ^ (m - n) * Fintype.card (omaUpperPairs m → Bool) := by
    intro E hE
    have hE_card : E.card = n := (Finset.mem_powersetCard.1 hE).2
    have hEc_card : (Finset.univ \ E).card = m - n := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.2 (Finset.subset_univ E),
        Finset.card_univ, Fintype.card_fin, hE_card]
    let XE := ↥(Finset.univ \ E)
    let EE := ↥E
    have hXE_card : Fintype.card XE = m - n := by
      rw [Fintype.card_coe, hEc_card]
    have hEE_card : Fintype.card EE = n := by
      rw [Fintype.card_coe, hE_card]
    let crossEmb : XE × EE ↪ omaUpperPairs m :=
      ⟨fun p => omaEdgeOf (u := p.1.1) (v := p.2.1)
          (fun heq => (Finset.mem_sdiff.1 p.1.2).2 (by rw [heq]; exact p.2.2)),
       fun p₁ p₂ heq => by
        rcases omaEdgeOf_eq_or _ _ heq with ⟨h1, h2⟩ | ⟨h1, _⟩
        · exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)
        · exact ((Finset.mem_sdiff.1 p₁.1.2).2 (by rw [h1]; exact p₂.2.2)).elim⟩
    let CrossSet : Finset (omaUpperPairs m) := Finset.univ.map crossEmb
    let Rest := { q : omaUpperPairs m // q ∉ CrossSet }
    let splitEquiv : (omaUpperPairs m → Bool) ≃ ((XE → (EE → Bool)) × (Rest → Bool)) :=
      { toFun := fun ω => (fun x e => ω (crossEmb (x, e)), fun q => ω q.1)
        invFun := fun fg p =>
          if hp : p ∈ CrossSet then
            let xe := Classical.choose (Finset.mem_map.1 hp)
            fg.1 xe.1 xe.2
          else fg.2 ⟨p, hp⟩
        left_inv := fun ω => by
          ext p
          by_cases hp : p ∈ CrossSet
          · simp only [dif_pos hp]
            have hspec := (Classical.choose_spec (Finset.mem_map.1 hp)).2
            rw [hspec]
          · simp only [dif_neg hp]
        right_inv := fun ⟨f, g⟩ => by
          ext1
          · ext x e
            have hp : crossEmb (x, e) ∈ CrossSet :=
              Finset.mem_map.2 ⟨(x, e), Finset.mem_univ _, rfl⟩
            simp only [dif_pos hp]
            have hspec := (Classical.choose_spec (Finset.mem_map.1 hp)).2
            have heq := crossEmb.injective hspec
            rw [heq]
          · ext ⟨q, hq⟩
            simp only [dif_neg hq] }
    let GoodX (x : XE) : Finset (EE → Bool) :=
      Finset.univ.erase (fun e : EE => omaWinBit x.1 e.1)
    have hGoodX_card : ∀ x : XE, (GoodX x).card = 2 ^ n - 1 := by
      intro x
      dsimp [GoodX]
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
        Fintype.card_fun, Fintype.card_bool, hEE_card]
    let GoodF : Finset (XE → (EE → Bool)) :=
      Finset.univ.filter (fun f => ∀ x : XE, f x ∈ GoodX x)
    have hGoodF_card : GoodF.card = (2 ^ n - 1) ^ (m - n) := by
      have hpi : GoodF = Fintype.piFinset GoodX := by
        ext f
        simp [GoodF, Fintype.mem_piFinset]
      rw [hpi, Fintype.card_piFinset, Finset.prod_congr rfl (fun x _ => hGoodX_card x),
        Finset.prod_const, Finset.card_univ, hXE_card]
    have hBad_equiv : (BadFor E).card = GoodF.card * Fintype.card (Rest → Bool) := by
      rw [← Finset.card_univ (α := Rest → Bool), ← Finset.card_product]
      refine Finset.card_bij (fun ω _ => splitEquiv ω) ?_ ?_ ?_
      · intro ω hω
        have hbad := (Finset.mem_filter.1 hω).2
        refine Finset.mem_product.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, fun x => ?_⟩,
          Finset.mem_univ _⟩
        dsimp [GoodX]
        rw [Finset.mem_erase]
        refine ⟨?_, Finset.mem_univ _⟩
        intro heq_fn
        apply hbad x.1 x.2
        intro e he
        have hx_ne_e : x.1 ≠ e := fun h => (Finset.mem_sdiff.1 x.2).2 (h ▸ he)
        rw [omaTourOf_adj_iff ω hx_ne_e]
        have hedge : omaEdgeOf hx_ne_e = crossEmb (x, ⟨e, he⟩) := rfl
        rw [hedge]
        exact congr_fun heq_fn ⟨e, he⟩
      · intro ω₁ _ ω₂ _ heq
        exact splitEquiv.injective heq
      · intro fg hfg
        rcases Finset.mem_product.1 hfg with ⟨hf, _⟩
        have hf_good := (Finset.mem_filter.1 hf).2
        refine ⟨splitEquiv.symm fg, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩,
          splitEquiv.apply_symm_apply fg⟩
        intro x hx hall
        have hx_good := hf_good ⟨x, hx⟩
        dsimp [GoodX] at hx_good
        have hne_fn := (Finset.mem_erase.1 hx_good).1
        apply hne_fn
        ext ⟨e, he⟩
        have hx_ne_e : x ≠ e := fun h => (Finset.mem_sdiff.1 hx).2 (h ▸ he)
        have hadj := hall e he
        rw [omaTourOf_adj_iff _ hx_ne_e] at hadj
        have hedge : omaEdgeOf hx_ne_e = crossEmb (⟨x, hx⟩, ⟨e, he⟩) := rfl
        rw [hedge] at hadj
        have hsymm : splitEquiv (splitEquiv.symm fg) = fg := splitEquiv.apply_symm_apply fg
        have h1 : splitEquiv.symm fg (crossEmb (⟨x, hx⟩, ⟨e, he⟩)) = fg.1 ⟨x, hx⟩ ⟨e, he⟩ :=
          congr_fun (congr_fun (congrArg Prod.fst hsymm) ⟨x, hx⟩) ⟨e, he⟩
        exact h1.symm.trans hadj
    have hTotal_equiv : Fintype.card (omaUpperPairs m → Bool) =
        (2 ^ n) ^ (m - n) * Fintype.card (Rest → Bool) := by
      rw [Fintype.card_congr splitEquiv, Fintype.card_prod, Fintype.card_fun,
        Fintype.card_fun, Fintype.card_bool, hEE_card, hXE_card]
    rw [hBad_equiv, hGoodF_card, hTotal_equiv]
    ring
  have hUnion_lt : (AllSub.biUnion BadFor).card < Fintype.card (omaUpperPairs m → Bool) := by
    have hmul_lt : (AllSub.biUnion BadFor).card * (2 ^ n) ^ (m - n) <
        Fintype.card (omaUpperPairs m → Bool) * (2 ^ n) ^ (m - n) := by
      calc (AllSub.biUnion BadFor).card * (2 ^ n) ^ (m - n)
        _ ≤ (∑ E ∈ AllSub, (BadFor E).card) * (2 ^ n) ^ (m - n) :=
            Nat.mul_le_mul_right _ Finset.card_biUnion_le
        _ = ∑ E ∈ AllSub, (BadFor E).card * (2 ^ n) ^ (m - n) := Finset.sum_mul _ _ _
        _ = ∑ E ∈ AllSub, (2 ^ n - 1) ^ (m - n) * Fintype.card (omaUpperPairs m → Bool) :=
            Finset.sum_congr rfl hBad_card
        _ = AllSub.card * ((2 ^ n - 1) ^ (m - n) * Fintype.card (omaUpperPairs m → Bool)) := by
            rw [Finset.sum_const, smul_eq_mul]
        _ = (m.choose n * (2 ^ n - 1) ^ (m - n)) * Fintype.card (omaUpperPairs m → Bool) := by
            have hAll_card : AllSub.card = m.choose n := by
              dsimp [AllSub]; rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
            rw [hAll_card]; ring
        _ < (2 ^ n) ^ (m - n) * Fintype.card (omaUpperPairs m → Bool) :=
            Nat.mul_lt_mul_of_pos_right hineq Fintype.card_pos
        _ = Fintype.card (omaUpperPairs m → Bool) * (2 ^ n) ^ (m - n) := mul_comm _ _
    exact lt_of_mul_lt_mul_right hmul_lt (Nat.zero_le _)
  have hNotUniv : AllSub.biUnion BadFor ≠ Finset.univ := by
    intro heq
    rw [heq, Finset.card_univ] at hUnion_lt
    exact lt_irrefl _ hUnion_lt
  obtain ⟨ω, hω_not⟩ : ∃ ω : omaUpperPairs m → Bool, ω ∉ AllSub.biUnion BadFor := by
    by_contra hall
    push Not at hall
    exact hNotUniv (Finset.eq_univ_iff_forall.2 hall)
  refine ⟨omaTourOf ω, omaTourOf_isTournament ω, ?_⟩
  intro E hE_card
  have hE_mem : E ∈ AllSub := Finset.mem_powersetCard.2 ⟨Finset.subset_univ E, hE_card⟩
  have hω_not_E : ω ∉ BadFor E := fun h => hω_not (Finset.mem_biUnion.2 ⟨E, hE_mem, h⟩)
  dsimp [BadFor] at hω_not_E
  rw [Finset.mem_filter] at hω_not_E
  push Not at hω_not_E
  obtain ⟨x, hx, hdom⟩ := hω_not_E (Finset.mem_univ ω)
  exact ⟨x, (Finset.mem_sdiff.1 hx).2, hdom⟩

lemma oma_choose_le_pow : ∀ (m n : ℕ), m.choose n ≤ m ^ n
  | _, 0 => by simp
  | 0, _ + 1 => by simp
  | m + 1, n + 1 => by
    rw [Nat.choose_succ_succ, pow_succ]
    have ih1 := oma_choose_le_pow m n
    have ih2 := oma_choose_le_pow m (n + 1)
    have hmono : m ^ n ≤ (m + 1) ^ n := Nat.pow_le_pow_left (Nat.le_succ m) n
    calc m.choose n + m.choose (n + 1)
      _ ≤ m ^ n + m ^ (n + 1) := Nat.add_le_add ih1 ih2
      _ = m ^ n * (m + 1) := by rw [pow_succ]; ring
      _ ≤ (m + 1) ^ n * (m + 1) := Nat.mul_le_mul_right (m + 1) hmono

lemma oma_nonempty_propertyS (n : ℕ) :
    {m : ℕ | n ≤ m ∧ ∃ G : Digraph (Fin m), G.IsTournament ∧ HasPropertyS G n}.Nonempty := by
  rcases Nat.eq_zero_or_pos n with rfl | hn_pos
  · refine ⟨1, Nat.zero_le 1, oma_exists_tournament_of_ineq (by decide)⟩
  · set b := 2 ^ n - 1
    have hb_pos : 1 ≤ b := by
      have h2n : 2 ≤ 2 ^ n := by
        calc 2 = 2 ^ 1 := rfl
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn_pos
      omega
    have hb_add : b + 1 = 2 ^ n := by omega
    set α : ℝ := 1 / (b : ℝ)
    have hα_pos : 0 < α := by positivity
    set C : ℝ := ((2 * n + 2 : ℕ) : ℝ)
    have hC_pos : 0 < C := by positivity
    obtain ⟨k, hk⟩ := exists_nat_gt (max 1 ((C / α) ^ n / α))
    have hk_gt1 : (1 : ℝ) < (k : ℝ) := lt_of_le_of_lt (le_max_left _ _) hk
    have hk_pos : 1 ≤ k := by exact_mod_cast (le_of_lt hk_gt1)
    have hk_thresh : (C / α) ^ n / α < (k : ℝ) := lt_of_le_of_lt (le_max_right _ _) hk
    set m := n + (n + 1) * k
    have hnm : n ≤ m := Nat.le_add_right _ _
    have hsub : m - n = (n + 1) * k := Nat.add_sub_cancel_left _ _
    refine ⟨m, hnm, oma_exists_tournament_of_ineq ?_⟩
    rw [hsub]
    refine lt_of_le_of_lt (Nat.mul_le_mul_right _ (oma_choose_le_pow m n)) ?_
    have hreal_lt : ((m : ℝ) ^ n) * ((b : ℝ) ^ ((n + 1) * k)) <
        ((b + 1 : ℝ)) ^ ((n + 1) * k) := by
      have hm_le : (m : ℝ) ^ n ≤ (C * (k : ℝ)) ^ n := by
        refine pow_le_pow_left₀ (Nat.cast_nonneg m) ?_ n
        dsimp [m, C]
        push_cast
        nlinarith
      have hbern : ((k : ℝ) * α) ^ (n + 1) ≤ (1 + α) ^ ((n + 1) * k) := by
        have hb0 : 1 + (k : ℝ) * α ≤ (1 + α) ^ k :=
          one_add_mul_le_pow (by linarith) k
        have hb1 : (k : ℝ) * α ≤ (1 + α) ^ k := by linarith
        have hpow := pow_le_pow_left₀ (by positivity) hb1 (n + 1)
        rwa [← pow_mul, mul_comm k (n + 1)] at hpow
      have hstrict_C : (C * (k : ℝ)) ^ n < ((k : ℝ) * α) ^ (n + 1) := by
        have hpos_kn : 0 < (k : ℝ) ^ n := by positivity
        have hpos_αn : 0 < α ^ n := by positivity
        have hmul1 : (C / α) ^ n < (k : ℝ) * α := (div_lt_iff₀ hα_pos).1 hk_thresh
        have hmul2 := mul_lt_mul_of_pos_right hmul1 hpos_αn
        rw [div_pow, div_mul_cancel₀ _ (ne_of_gt hpos_αn)] at hmul2
        have hmul3 := mul_lt_mul_of_pos_right hmul2 hpos_kn
        calc (C * (k : ℝ)) ^ n
          _ = C ^ n * (k : ℝ) ^ n := by ring
          _ < ((k : ℝ) * α * α ^ n) * (k : ℝ) ^ n := hmul3
          _ = ((k : ℝ) * α) ^ (n + 1) := by rw [pow_succ]; ring
      have hdiv_lt : (m : ℝ) ^ n < (1 + α) ^ ((n + 1) * k) :=
        lt_of_le_of_lt hm_le (lt_of_lt_of_le hstrict_C hbern)
      have hb_real_pos : 0 < (b : ℝ) := by exact_mod_cast hb_pos
      have hmul_b := mul_lt_mul_of_pos_right hdiv_lt (pow_pos hb_real_pos ((n + 1) * k))
      have hrhs_eq : (1 + α) ^ ((n + 1) * k) * (b : ℝ) ^ ((n + 1) * k) =
          (b + 1 : ℝ) ^ ((n + 1) * k) := by
        rw [← mul_pow]
        congr 1
        dsimp [α]
        field_simp [ne_of_gt hb_real_pos]
      rwa [hrhs_eq] at hmul_b
    rw [← hb_add]
    exact_mod_cast hreal_lt

open Classical in
lemma oma_exists_small_indegree {m : ℕ} {G : Digraph (Fin m)} (hG : G.IsTournament)
    {S : Finset (Fin m)} (hS : S.Nonempty) :
    ∃ v ∈ S, 2 * (S.filter (fun u => G.Adj u v)).card + 1 ≤ S.card := by
  let A := S.offDiag.filter (fun p : Fin m × Fin m => G.Adj p.1 p.2)
  have h2A : 2 * A.card = S.card * (S.card - 1) := by
    let Aswap := A.image Prod.swap
    have hdisj : Disjoint A Aswap := by
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      obtain ⟨q, hqA, hswap⟩ := Finset.mem_image.1 hp2
      have hp_adj : G.Adj p.1 p.2 := (Finset.mem_filter.1 hp1).2
      have hq_adj : G.Adj q.1 q.2 := (Finset.mem_filter.1 hqA).2
      have hne : p.1 ≠ p.2 := (Finset.mem_offDiag.1 (Finset.mem_filter.1 hp1).1).2.2
      have hp21 : G.Adj p.2 p.1 := by
        have h1 : q.1 = p.2 := congrArg Prod.snd hswap
        have h2 : q.2 = p.1 := congrArg Prod.fst hswap
        rwa [← h1, ← h2]
      exact (hG.2 p.1 p.2 hne).1 hp_adj hp21
    have hunion : A ∪ Aswap = S.offDiag := by
      ext p
      simp only [Finset.mem_union, A, Aswap, Finset.mem_filter, Finset.mem_image]
      refine ⟨fun h => ?_, fun hoff => ?_⟩
      · rcases h with ⟨hoff, _⟩ | ⟨q, ⟨hqoff, _⟩, rfl⟩
        · exact hoff
        · rcases Finset.mem_offDiag.1 hqoff with ⟨hq1, hq2, hqne⟩
          exact Finset.mem_offDiag.2 ⟨hq2, hq1, hqne.symm⟩
      · rcases Finset.mem_offDiag.1 hoff with ⟨hp1, hp2, hpne⟩
        by_cases hadj : G.Adj p.1 p.2
        · exact Or.inl ⟨hoff, hadj⟩
        · refine Or.inr ⟨p.swap, ⟨Finset.mem_offDiag.2 ⟨hp2, hp1, hpne.symm⟩, ?_⟩,
            Prod.swap_swap p⟩
          exact ((hG.2 p.1 p.2 hpne).not_left.1 hadj)
    have hcard_u := Finset.card_union_of_disjoint hdisj
    have hcard_sw : Aswap.card = A.card := Finset.card_image_of_injective A Prod.swap_injective
    have hoff : S.card * (S.card - 1) = S.offDiag.card := by
      rw [Finset.offDiag_card]
      rcases S.card with _ | k <;> simp [Nat.succ_mul, Nat.mul_succ]
    rw [hunion, hcard_sw] at hcard_u
    omega
  have hAsum : A.card = ∑ v ∈ S, (S.filter (fun u => G.Adj u v)).card := by
    have hbiU : A = S.biUnion (fun v =>
        (S.filter (fun u => G.Adj u v)).image (fun u => (u, v))) := by
      ext p
      simp only [A, Finset.mem_filter, Finset.mem_offDiag, Finset.mem_biUnion, Finset.mem_image]
      refine ⟨fun ⟨⟨hp1, hp2, _⟩, hadj⟩ => ⟨p.2, hp2, p.1, ⟨hp1, hadj⟩, Prod.mk.eta⟩,
        fun ⟨v, hv, u, ⟨hu, hadj⟩, huv⟩ => ?_⟩
      subst huv
      exact ⟨⟨hu, hv, fun heq => by dsimp at heq; subst heq; exact hG.1 u hadj⟩, hadj⟩
    have hdisj_v : (S : Set (Fin m)).PairwiseDisjoint (fun v =>
        (S.filter (fun u => G.Adj u v)).image (fun u => (u, v))) := by
      intro v₁ _ v₂ _ hne
      dsimp [Function.onFun]
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      obtain ⟨u₁, _, rfl⟩ := Finset.mem_image.1 hp1
      obtain ⟨u₂, _, heq2⟩ := Finset.mem_image.1 hp2
      exact hne (congrArg Prod.snd heq2).symm
    rw [hbiU, Finset.card_biUnion hdisj_v]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    exact Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.fst h)
  have hsum_eq : ∑ v ∈ S, (2 * (S.filter (fun u => G.Adj u v)).card) =
      ∑ _v ∈ S, (S.card - 1) := by
    rw [← Finset.mul_sum, ← hAsum, h2A, Finset.sum_const, smul_eq_mul]
  have hex_le : ∃ v ∈ S, 2 * (S.filter (fun u => G.Adj u v)).card ≤ S.card - 1 := by
    by_contra hall_gt
    push Not at hall_gt
    have hlt := Finset.sum_lt_sum_of_nonempty hS hall_gt
    omega
  obtain ⟨v, hvS, hle⟩ := hex_le
  have hS_pos : 1 ≤ S.card := Finset.card_pos.2 hS
  exact ⟨v, hvS, by omega⟩

end OMA902Lower

theorem OMA.solution : type_of% @Erdos902.erdos_902.variants.erdos_lower := by
  intro n
  classical
  refine le_csInf (oma_nonempty_propertyS n) ?_
  rintro m ⟨hnm, G, hG, hS_prop⟩
  by_contra hlt_m
  have hm_lt : m + 1 < 2 ^ (n + 1) := by
    have h2pos : 1 ≤ 2 ^ (n + 1) := Nat.one_le_pow _ _ (by omega)
    omega
  have hind : ∀ j : ℕ, j ≤ n →
      ∃ E : Finset (Fin m), E.card = j ∧
        ((Finset.univ \ E).filter (fun x => ∀ e ∈ E, G.Adj x e)).card + 1 <
          2 ^ (n - j + 1) := by
    intro j hj
    induction j with
    | zero =>
      refine ⟨∅, rfl, ?_⟩
      have huniv_eq : ((Finset.univ \ (∅ : Finset (Fin m))).filter
          (fun x => ∀ e ∈ (∅ : Finset (Fin m)), G.Adj x e)) = Finset.univ := by
        ext x; simp
      rw [huniv_eq, Finset.card_univ, Fintype.card_fin, Nat.sub_zero]
      exact hm_lt
    | succ j ih =>
      obtain ⟨E, hE_card, hS_lt⟩ := ih (Nat.le_of_succ_le hj)
      set S := (Finset.univ \ E).filter (fun x => ∀ e ∈ E, G.Adj x e)
      by_cases hSne : S.Nonempty
      · obtain ⟨v, hvS, hv_deg⟩ := oma_exists_small_indegree hG hSne
        have hv_notE : v ∉ E := (Finset.mem_sdiff.1 (Finset.mem_filter.1 hvS).1).2
        let E' := insert v E
        have hE'_card : E'.card = j + 1 := by
          dsimp [E']; rw [Finset.card_insert_of_notMem hv_notE, hE_card]
        have hS'_sub : (Finset.univ \ E').filter (fun x => ∀ e ∈ E', G.Adj x e) ⊆
            S.filter (fun u => G.Adj u v) := by
          intro x hx
          rcases Finset.mem_filter.1 hx with ⟨hx_notE', hx_all⟩
          have hx_notE : x ∉ E := fun h => (Finset.mem_sdiff.1 hx_notE').2 (Finset.mem_insert_of_mem h)
          refine Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hx_notE⟩,
            fun e he => hx_all e (Finset.mem_insert_of_mem he)⟩,
            hx_all v (Finset.mem_insert_self v E)⟩
        have hc_le := Finset.card_le_card hS'_sub
        have hexp : n - j + 1 = (n - (j + 1) + 1) + 1 := by omega
        rw [hexp, pow_succ] at hS_lt
        refine ⟨E', hE'_card, by omega⟩
      · have hEc_pos : 0 < (Finset.univ \ E).card := by
          rw [Finset.card_sdiff, Finset.inter_eq_left.2 (Finset.subset_univ E),
            Finset.card_univ, Fintype.card_fin, hE_card]
          omega
        obtain ⟨v, hvEc⟩ := Finset.card_pos.1 hEc_pos
        have hv_notE : v ∉ E := (Finset.mem_sdiff.1 hvEc).2
        let E' := insert v E
        have hE'_card : E'.card = j + 1 := by
          dsimp [E']; rw [Finset.card_insert_of_notMem hv_notE, hE_card]
        have hS'_empty : ((Finset.univ \ E').filter (fun x => ∀ e ∈ E', G.Adj x e)).card = 0 := by
          rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
          intro x hx
          rcases Finset.mem_filter.1 hx with ⟨hx_notE', hx_all⟩
          have hx_notE : x ∉ E := fun h => (Finset.mem_sdiff.1 hx_notE').2 (Finset.mem_insert_of_mem h)
          have hxS : x ∈ S := Finset.mem_filter.2 ⟨Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hx_notE⟩,
            fun e he => hx_all e (Finset.mem_insert_of_mem he)⟩
          exact hSne ⟨x, hxS⟩
        have hpow_ge2 : 2 ≤ 2 ^ (n - (j + 1) + 1) := by
          calc 2 = 2 ^ 1 := rfl
            _ ≤ 2 ^ (n - (j + 1) + 1) := Nat.pow_le_pow_right (by omega) (by omega)
        refine ⟨E', hE'_card, by omega⟩
  obtain ⟨E, hE_card, hSn_lt⟩ := hind n (le_refl n)
  rw [Nat.sub_self, zero_add, pow_one] at hSn_lt
  obtain ⟨x, hx_notE, hx_dom⟩ := hS_prop E hE_card
  have hx_mem : x ∈ (Finset.univ \ E).filter (fun x => ∀ e ∈ E, G.Adj x e) :=
    Finset.mem_filter.2 ⟨Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hx_notE⟩, hx_dom⟩
  have hpos : 1 ≤ ((Finset.univ \ E).filter (fun x => ∀ e ∈ E, G.Adj x e)).card :=
    Finset.card_pos.2 ⟨x, hx_mem⟩
  omega
