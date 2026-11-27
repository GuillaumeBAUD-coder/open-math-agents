import FormalConjectures.GreensOpenProblems.«76»
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

-- Problem: Ben Green's Open Problem 76 — subset
-- Upstream: formal-conjectures FormalConjectures/GreensOpenProblems/76.lean:105 (declaration Green76.green_76.variants.subset)
-- Credit: @caa1982 (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.Green76Proof

open Finset

/-! ### Step 1: Permutation avoidance bound -/

lemma card_perm_avoid_prefix {k d : ℕ} (hkd : k ≤ d) (S : Finset (Fin d)) (hS : k ≤ S.card) :
    ((Finset.univ.filter (fun σ : Equiv.Perm (Fin d) =>
        ¬ ∀ t : Fin d, t.val < k → σ t ∈ S)).card : ℝ) ≤
      (1 - 1 / (d.choose k : ℝ)) * (Fintype.card (Equiv.Perm (Fin d)) : ℝ) := by
  classical
  obtain ⟨T, hTS, hTcard⟩ := Finset.exists_subset_card_eq hS
  let K : Finset (Fin d) := Finset.univ.filter (fun t : Fin d => t.val < k)
  have hKcard : K.card = k := by
    have hbij : K = Finset.univ.map (Fin.castLEEmb hkd) := by
      ext t
      simp only [K, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
        Fin.castLEEmb_apply]
      constructor
      · intro ht
        exact ⟨⟨t.val, ht⟩, rfl⟩
      · rintro ⟨a, rfl⟩
        exact a.isLt
    rw [hbij, Finset.card_map, Finset.card_univ, Fintype.card_fin]
  have hK_card' : Fintype.card {x : Fin d // x ∈ K} = k := by
    rw [Fintype.card_coe, hKcard]
  have hT_card' : Fintype.card {x : Fin d // x ∈ T} = k := by
    rw [Fintype.card_coe, hTcard]
  have hKc_card : Fintype.card {x : Fin d // x ∉ K} = d - k := by
    rw [Fintype.card_subtype_compl, hK_card', Fintype.card_fin]
  have hTc_card : Fintype.card {x : Fin d // x ∉ T} = d - k := by
    rw [Fintype.card_subtype_compl, hT_card', Fintype.card_fin]
  let e1 : {x : Fin d // x ∈ K} ≃ {x : Fin d // x ∈ T} :=
    Fintype.equivOfCardEq (hK_card'.trans hT_card'.symm)
  let e2 : {x : Fin d // x ∉ K} ≃ {x : Fin d // x ∉ T} :=
    Fintype.equivOfCardEq (hKc_card.trans hTc_card.symm)
  let mkPerm : Equiv.Perm {x : Fin d // x ∈ K} × Equiv.Perm {x : Fin d // x ∉ K} →
      Equiv.Perm (Fin d) := fun ⟨p1, p2⟩ =>
    ((Equiv.sumCompl (· ∈ K)).symm.trans
      (Equiv.sumCongr (p1.trans e1) (p2.trans e2))).trans
      (Equiv.sumCompl (· ∈ T))
  have hmk_inj : Function.Injective mkPerm := by
    intro ⟨p1, p2⟩ ⟨q1, q2⟩ h
    have h1 : p1 = q1 := by
      apply Equiv.ext
      intro x
      have hx := Equiv.congr_fun h x.val
      simp only [mkPerm, Equiv.trans_apply, Equiv.sumCompl_symm_apply_of_pos x.property,
        Equiv.sumCongr_apply, Sum.map_inl, Equiv.sumCompl_apply_inl] at hx
      exact e1.injective (Subtype.ext hx)
    have h2 : p2 = q2 := by
      apply Equiv.ext
      intro x
      have hx := Equiv.congr_fun h x.val
      simp only [mkPerm, Equiv.trans_apply, Equiv.sumCompl_symm_apply_of_neg x.property,
        Equiv.sumCongr_apply, Sum.map_inr, Equiv.sumCompl_apply_inr] at hx
      exact e2.injective (Subtype.ext hx)
    exact Prod.ext h1 h2
  have hmk_good : ∀ p, ∀ t : Fin d, t.val < k → mkPerm p t ∈ S := by
    intro ⟨p1, p2⟩ t ht
    have htK : t ∈ K := by simp [K, ht]
    simp only [mkPerm, Equiv.trans_apply, Equiv.sumCompl_symm_apply_of_pos htK,
      Equiv.sumCongr_apply, Sum.map_inl, Equiv.sumCompl_apply_inl]
    exact hTS (e1 (p1 ⟨t, htK⟩)).property
  let goodSet := Finset.univ.filter (fun σ : Equiv.Perm (Fin d) =>
    ∀ t : Fin d, t.val < k → σ t ∈ S)
  let badSet := Finset.univ.filter (fun σ : Equiv.Perm (Fin d) =>
    ¬ ∀ t : Fin d, t.val < k → σ t ∈ S)
  have hgood_ge : k.factorial * (d - k).factorial ≤ goodSet.card := by
    have hsub : Finset.univ.image mkPerm ⊆ goodSet := by
      intro σ hσ
      rcases Finset.mem_image.mp hσ with ⟨p, _, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmk_good p⟩
    have hcard_img : (Finset.univ.image mkPerm).card = k.factorial * (d - k).factorial := by
      rw [Finset.card_image_of_injective _ hmk_inj, Finset.card_univ, Fintype.card_prod,
        Fintype.card_perm, Fintype.card_perm, hK_card', hKc_card]
    rw [← hcard_img]
    exact Finset.card_le_card hsub
  have hsum : goodSet.card + badSet.card = Fintype.card (Equiv.Perm (Fin d)) := by
    rw [← Finset.card_univ]
    exact Finset.card_filter_add_card_filter_not _
  have hbad_nat : badSet.card ≤ d.factorial - k.factorial * (d - k).factorial := by
    have hperm : Fintype.card (Equiv.Perm (Fin d)) = d.factorial := by
      rw [Fintype.card_perm, Fintype.card_fin]
    omega
  have hchoose_pos : (0 : ℝ) < (d.choose k : ℝ) := by
    exact_mod_cast Nat.choose_pos hkd
  have hfac_nat : d.choose k * (k.factorial * (d - k).factorial) = d.factorial := by
    rw [← mul_assoc]
    exact Nat.choose_mul_factorial_mul_factorial hkd
  have hfac_eq : (d.choose k : ℝ) * ((k.factorial * (d - k).factorial : ℕ) : ℝ) =
      (d.factorial : ℝ) := by
    exact_mod_cast hfac_nat
  have hperm_eq : (Fintype.card (Equiv.Perm (Fin d)) : ℝ) = (d.factorial : ℝ) := by
    rw [Fintype.card_perm, Fintype.card_fin]
  have hbad_real : (badSet.card : ℝ) ≤ (d.factorial : ℝ) - ((k.factorial * (d - k).factorial : ℕ) : ℝ) := by
    have hle : k.factorial * (d - k).factorial ≤ d.factorial := by
      rw [← hfac_nat]
      exact Nat.le_mul_of_pos_left _ (Nat.choose_pos hkd)
    have h1 : (badSet.card : ℝ) ≤ ((d.factorial - k.factorial * (d - k).factorial : ℕ) : ℝ) := by
      exact_mod_cast hbad_nat
    rwa [Nat.cast_sub hle] at h1
  rw [hperm_eq]
  have hdiv : ((k.factorial * (d - k).factorial : ℕ) : ℝ) = (d.factorial : ℝ) / (d.choose k : ℝ) := by
    rw [eq_div_iff (ne_of_gt hchoose_pos), mul_comm, hfac_eq]
  rw [hdiv] at hbad_real
  have hrhs : (1 - 1 / (d.choose k : ℝ)) * (d.factorial : ℝ) =
      (d.factorial : ℝ) - (d.factorial : ℝ) / (d.choose k : ℝ) := by ring
  linarith

/-! ### Step 2: Block-interleaving tree and permutation -/

abbrev Level (d D h : ℕ) := Fin (d ^ (D - (h + 1))) → Fin (d ^ h) → Equiv.Perm (Fin d)

def State (d D : ℕ) : ℕ → Type
  | 0 => Unit
  | h + 1 => State d D h × Level d D h

instance instFintypeState (d D : ℕ) : ∀ h, Fintype (State d D h)
  | 0 => inferInstanceAs (Fintype Unit)
  | h + 1 => @instFintypeProd _ _ (instFintypeState d D h) inferInstance

def childNode (d D h : ℕ) (hh : h + 1 ≤ D) (u : Fin (d ^ (D - (h + 1)))) (c : Fin d) :
    Fin (d ^ (D - h)) :=
  ⟨u.val * d + c.val, by
    have h1 : D - h = (D - (h + 1)) + 1 := by omega
    rw [h1, pow_succ]
    have hu := u.isLt
    have hc := c.isLt
    nlinarith⟩

def ord (d D : ℕ) : ∀ {h : ℕ}, h ≤ D → State d D h → Fin (d ^ (D - h)) → Equiv.Perm (Fin (d ^ h))
  | 0, _, _, _ => Equiv.refl (Fin 1)
  | h + 1, hh, (ω, σ), u =>
    let e1 : Fin (d ^ (h + 1)) ≃ Fin (d ^ h) × Fin d := finProdFinEquiv.symm
    let e2 : Fin (d ^ h) × Fin d ≃ Fin (d ^ h) × Fin d :=
      { toFun := fun p => (p.1, σ u p.1 p.2)
        invFun := fun p => (p.1, (σ u p.1).symm p.2)
        left_inv := fun ⟨j, t⟩ => by simp
        right_inv := fun ⟨j, c⟩ => by simp }
    let e3 : Fin (d ^ h) × Fin d ≃ Fin d × Fin (d ^ h) :=
      { toFun := fun p => (p.2, ord d D (Nat.le_of_succ_le hh) ω (childNode d D h hh u p.2) p.1)
        invFun := fun p =>
          ((ord d D (Nat.le_of_succ_le hh) ω (childNode d D h hh u p.1)).symm p.2, p.1)
        left_inv := fun ⟨j, c⟩ => by simp
        right_inv := fun ⟨c, x⟩ => by simp }
    let e4 : Fin d × Fin (d ^ h) ≃ Fin (d ^ (h + 1)) :=
      finProdFinEquiv.trans (finCongr (by rw [pow_succ, mul_comm]))
    ((e1.trans e2).trans e3).trans e4

def globalLeaf (d D h : ℕ) (hh : h ≤ D) (u : Fin (d ^ (D - h))) (x : Fin (d ^ h)) :
    Fin (d ^ D) :=
  ⟨u.val * d ^ h + x.val, by
    have hpow : d ^ (D - h) * d ^ h = d ^ D := by
      rw [← pow_add, Nat.sub_add_cancel hh]
    rw [← hpow]
    have hu := u.isLt
    have hx := x.isLt
    nlinarith⟩

def statePrefix (d D : ℕ) : ∀ {h1 h2 : ℕ}, h1 ≤ h2 → State d D h2 → State d D h1
  | h1, 0, hle, ω => (Nat.le_zero.mp hle).symm ▸ ω
  | h1, h2 + 1, hle, ω =>
    if heq : h1 = h2 + 1 then
      heq.symm ▸ ω
    else
      statePrefix d D (Nat.le_of_lt_succ (lt_of_le_of_ne hle heq)) ω.1

lemma statePrefix_self (d D h : ℕ) (ω : State d D h) :
    statePrefix d D (le_refl h) ω = ω := by
  cases h with
  | zero => rfl
  | succ h => simp [statePrefix]

lemma statePrefix_succ (d D h1 h2 : ℕ) (hle : h1 ≤ h2) (ω : State d D h2) (σ : Level d D h2) :
    statePrefix d D (Nat.le_succ_of_le hle) (ω, σ) = statePrefix d D hle ω := by
  have hne : h1 ≠ h2 + 1 := by omega
  simp [statePrefix, hne]

lemma ord_succ_apply_val (d D h : ℕ) (hh : h + 1 ≤ D) (ω : State d D h) (σ : Level d D h)
    (u : Fin (d ^ (D - (h + 1)))) (j : Fin (d ^ h)) (t : Fin d) :
    (ord d D hh (ω, σ) u (finProdFinEquiv (j, t))).val =
      (σ u j t).val * d ^ h +
        (ord d D (Nat.le_of_succ_le hh) ω (childNode d D h hh u (σ u j t)) j).val := by
  have h1 : (finProdFinEquiv.symm (finProdFinEquiv (j, t)) : Fin (d ^ h) × Fin d) = (j, t) :=
    finProdFinEquiv.symm_apply_apply (j, t)
  change (finProdFinEquiv (σ u (finProdFinEquiv.symm (finProdFinEquiv (j, t))).1
      (finProdFinEquiv.symm (finProdFinEquiv (j, t))).2,
      ord d D (Nat.le_of_succ_le hh) ω
        (childNode d D h hh u (σ u (finProdFinEquiv.symm (finProdFinEquiv (j, t))).1
          (finProdFinEquiv.symm (finProdFinEquiv (j, t))).2))
        (finProdFinEquiv.symm (finProdFinEquiv (j, t))).1)).val = _
  rw [h1]
  change (ord d D (Nat.le_of_succ_le hh) ω (childNode d D h hh u (σ u j t)) j).val +
      d ^ h * (σ u j t).val = _
  ring

lemma globalLeaf_ord_succ (d D h : ℕ) (hh : h + 1 ≤ D) (ω : State d D h) (σ : Level d D h)
    (u : Fin (d ^ (D - (h + 1)))) (j : Fin (d ^ h)) (t : Fin d) :
    globalLeaf d D (h + 1) hh u (ord d D hh (ω, σ) u (finProdFinEquiv (j, t))) =
      globalLeaf d D h (Nat.le_of_succ_le hh) (childNode d D h hh u (σ u j t))
        (ord d D (Nat.le_of_succ_le hh) ω (childNode d D h hh u (σ u j t)) j) := by
  ext
  simp only [globalLeaf, childNode, ord_succ_apply_val, pow_succ]
  ring

lemma ord_step_mono (d D h : ℕ) (hh : h + 1 ≤ D) (hd : 0 < d)
    (ω : State d D h) (σ : Level d D h)
    (u : Fin (d ^ (D - (h + 1)))) (c : Fin d) (j1 j2 : Fin (d ^ h)) (hj : j1 < j2) :
    let u' := childNode d D h hh u c
    let x1 := ord d D (Nat.le_of_succ_le hh) ω u' j1
    let x2 := ord d D (Nat.le_of_succ_le hh) ω u' j2
    let y1 : Fin (d ^ (h + 1)) := ⟨c.val * d ^ h + x1.val, by
      rw [pow_succ, mul_comm]; have := c.isLt; have := x1.isLt; nlinarith⟩
    let y2 : Fin (d ^ (h + 1)) := ⟨c.val * d ^ h + x2.val, by
      rw [pow_succ, mul_comm]; have := c.isLt; have := x2.isLt; nlinarith⟩
    (ord d D hh (ω, σ) u).symm y1 < (ord d D hh (ω, σ) u).symm y2 := by
  intro u' x1 x2 y1 y2
  have hr : ∀ (j : Fin (d ^ h)),
      let x := ord d D (Nat.le_of_succ_le hh) ω u' j
      let y : Fin (d ^ (h + 1)) := ⟨c.val * d ^ h + x.val, by
        rw [pow_succ, mul_comm]; have := c.isLt; have := x.isLt; nlinarith⟩
      (ord d D hh (ω, σ) u).symm y = finProdFinEquiv (j, (σ u j).symm c) := by
    intro j x y
    apply (ord d D hh (ω, σ) u).injective
    rw [Equiv.apply_symm_apply]
    ext
    rw [ord_succ_apply_val]
    simp [y, x, u']
  rw [hr j1, hr j2]
  change ((σ u j1).symm c).val + d * j1.val < ((σ u j2).symm c).val + d * j2.val
  have h1 := ((σ u j1).symm c).isLt
  have hjv : j1.val + 1 ≤ j2.val := hj
  nlinarith

lemma ord_mono_to_top (d D : ℕ) (hd : 0 < d) :
    ∀ {h2 : ℕ} (hh2 : h2 ≤ D) (ω2 : State d D h2) {h1 : ℕ} (hle : h1 ≤ h2)
      (u1 : Fin (d ^ (D - h1))) (r1 r2 : Fin (d ^ h1)),
      r1 < r2 →
      ∃ (u2 : Fin (d ^ (D - h2))) (y1 y2 : Fin (d ^ h2)),
        globalLeaf d D h2 hh2 u2 y1 =
          globalLeaf d D h1 (hle.trans hh2) u1 (ord d D (hle.trans hh2) (statePrefix d D hle ω2) u1 r1) ∧
        globalLeaf d D h2 hh2 u2 y2 =
          globalLeaf d D h1 (hle.trans hh2) u1 (ord d D (hle.trans hh2) (statePrefix d D hle ω2) u1 r2) ∧
        (ord d D hh2 ω2 u2).symm y1 < (ord d D hh2 ω2 u2).symm y2 := by
  intro h2
  induction h2 with
  | zero =>
    intro hh2 ω2 h1 hle u1 r1 r2 hr
    have h1z : h1 = 0 := Nat.le_zero.mp hle
    subst h1z
    have hlt1 : r1.val < 1 := r1.isLt
    have hlt2 : r2.val < 1 := r2.isLt
    exact absurd hr (by change ¬ r1.val < r2.val; omega)
  | succ h2 ih =>
    intro hh2 ω2 h1 hle u1 r1 r2 hr
    rcases ω2 with ⟨ω, σ⟩
    by_cases heq : h1 = h2 + 1
    · subst heq
      refine ⟨u1, ord d D hh2 (ω, σ) u1 r1, ord d D hh2 (ω, σ) u1 r2, ?_, ?_, ?_⟩
      · rw [statePrefix_self d D (h2 + 1) (ω, σ)]
      · rw [statePrefix_self d D (h2 + 1) (ω, σ)]
      · simpa using hr
    · have hle' : h1 ≤ h2 := by omega
      have hh : h2 ≤ D := Nat.le_of_succ_le hh2
      obtain ⟨u2, y1, y2, hg1, hg2, hlt⟩ := ih hh ω hle' u1 r1 r2 hr
      let u3 : Fin (d ^ (D - (h2 + 1))) := ⟨u2.val / d, by
        have hsub : D - h2 = (D - (h2 + 1)) + 1 := by omega
        have hu2 : u2.val < d ^ (D - (h2 + 1)) * d := by
          have hlt0 : u2.val < d ^ (D - h2) := u2.isLt
          rw [← pow_succ, ← hsub]
          exact hlt0
        exact Nat.div_lt_of_lt_mul (by rwa [mul_comm])⟩
      let c : Fin d := ⟨u2.val % d, Nat.mod_lt _ hd⟩
      have hu2_eq : childNode d D h2 hh2 u3 c = u2 := by
        ext
        simp only [childNode, u3, c]
        have := Nat.div_add_mod u2.val d
        linarith
      let j1 := (ord d D hh ω u2).symm y1
      let j2 := (ord d D hh ω u2).symm y2
      have hord1 : ord d D hh ω (childNode d D h2 hh2 u3 c) j1 = y1 := by
        rw [hu2_eq]; exact (ord d D hh ω u2).apply_symm_apply y1
      have hord2 : ord d D hh ω (childNode d D h2 hh2 u3 c) j2 = y2 := by
        rw [hu2_eq]; exact (ord d D hh ω u2).apply_symm_apply y2
      let z1 : Fin (d ^ (h2 + 1)) := ⟨c.val * d ^ h2 + y1.val, by
        rw [pow_succ, mul_comm]; have := c.isLt; have := y1.isLt; nlinarith⟩
      let z2 : Fin (d ^ (h2 + 1)) := ⟨c.val * d ^ h2 + y2.val, by
        rw [pow_succ, mul_comm]; have := c.isLt; have := y2.isLt; nlinarith⟩
      refine ⟨u3, z1, z2, ?_, ?_, ?_⟩
      · rw [statePrefix_succ d D h1 h2 hle' ω σ, ← hg1]
        ext
        simp only [globalLeaf, z1, u3, c]
        have hdiv : (d * (u2.val / d) + u2.val % d) * d ^ h2 = u2.val * d ^ h2 :=
          congrArg (· * d ^ h2) (Nat.div_add_mod u2.val d)
        rw [pow_succ]
        linarith
      · rw [statePrefix_succ d D h1 h2 hle' ω σ, ← hg2]
        ext
        simp only [globalLeaf, z2, u3, c]
        have hdiv : (d * (u2.val / d) + u2.val % d) * d ^ h2 = u2.val * d ^ h2 :=
          congrArg (· * d ^ h2) (Nat.div_add_mod u2.val d)
        rw [pow_succ]
        linarith
      · have hstep := ord_step_mono d D h2 hh2 hd ω σ u3 c j1 j2 hlt
        have hz1 : (⟨c.val * d ^ h2 + (ord d D hh ω (childNode d D h2 hh2 u3 c) j1).val, by
            rw [pow_succ, mul_comm]; have := c.isLt; have := (ord d D hh ω (childNode d D h2 hh2 u3 c) j1).isLt; nlinarith⟩ : Fin (d ^ (h2 + 1))) = z1 := by
          ext; simp [z1, hord1]
        have hz2 : (⟨c.val * d ^ h2 + (ord d D hh ω (childNode d D h2 hh2 u3 c) j2).val, by
            rw [pow_succ, mul_comm]; have := c.isLt; have := (ord d D hh ω (childNode d D h2 hh2 u3 c) j2).isLt; nlinarith⟩ : Fin (d ^ (h2 + 1))) = z2 := by
          ext; simp [z2, hord2]
        simpa only [hz1, hz2] using hstep

lemma final_perm_strictMono_on_node (d D : ℕ) (hd : 0 < d) (ωD : State d D D)
    {h : ℕ} (hh : h ≤ D) (u : Fin (d ^ (D - h))) (r1 r2 : Fin (d ^ h)) (hr : r1 < r2) :
    let π := (ord d D (le_refl D) ωD ⟨0, by simp⟩).symm
    let x1 := globalLeaf d D h hh u (ord d D hh (statePrefix d D hh ωD) u r1)
    let x2 := globalLeaf d D h hh u (ord d D hh (statePrefix d D hh ωD) u r2)
    π x1 < π x2 := by
  intro π x1 x2
  obtain ⟨u2, y1, y2, hg1, hg2, hlt⟩ := ord_mono_to_top d D hd (le_refl D) ωD hh u r1 r2 hr
  have hu2 : u2 = ⟨0, by simp⟩ := by
    ext
    have := u2.isLt
    simp at this
    omega
  subst hu2
  have hy1 : y1 = x1 := by
    ext
    have := congrArg Fin.val hg1
    simpa [globalLeaf, x1] using this
  have hy2 : y2 = x2 := by
    ext
    have := congrArg Fin.val hg2
    simpa [globalLeaf, x2] using this
  simpa only [π, hy1, hy2] using hlt

/-! ### Step 3: Counting bad states across all levels -/

def HasGoodBlock (k d D h : ℕ) (hh : h + 1 ≤ D) (ω : State d D h) (σ : Level d D h)
    (B : Finset (Fin (d ^ D))) : Prop :=
  ∃ (u : Fin (d ^ (D - (h + 1)))) (j : Fin (d ^ h)),
    ∀ t : Fin d, t.val < k →
      globalLeaf d D h (Nat.le_of_succ_le hh) (childNode d D h hh u (σ u j t))
        (ord d D (Nat.le_of_succ_le hh) ω (childNode d D h hh u (σ u j t)) j) ∈ B

def AllBad (k d D : ℕ) : ∀ {h : ℕ}, h ≤ D → State d D h → Finset (Fin (d ^ D)) → Prop
  | 0, _, _, _ => True
  | h + 1, hh, (ω, σ), B =>
    AllBad k d D (Nat.le_of_succ_le hh) ω B ∧ ¬ HasGoodBlock k d D h hh ω σ B

lemma card_filter_pi_prod {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*}
    [∀ i, Fintype (α i)]
    (P : ∀ i, α i → Prop) [∀ i, DecidablePred (P i)] :
    (Finset.univ.filter (fun f : ∀ i, α i => ∀ i, P i (f i))).card =
      ∏ i : ι, (Finset.univ.filter (P i)).card := by
  classical
  have h1 : Finset.univ.filter (fun f : ∀ i, α i => ∀ i, P i (f i)) =
      Fintype.piFinset (fun i => Finset.univ.filter (P i)) := by
    ext f
    simp [Fintype.mem_piFinset]
  rw [h1, Fintype.card_piFinset]

lemma count_rich_pairs {k d D h : ℕ} (hk : 1 ≤ k) (hd : d = 4 * k) (hh : h + 1 ≤ D)
    (ω : State d D h) (B : Finset (Fin (d ^ D))) (hB : d ^ D ≤ 2 * B.card) :
    let idx := Fin (d ^ (D - (h + 1))) × Fin (d ^ h)
    let S (p : idx) : Finset (Fin d) :=
      Finset.univ.filter (fun c : Fin d =>
        globalLeaf d D h (Nat.le_of_succ_le hh) (childNode d D h hh p.1 c)
          (ord d D (Nat.le_of_succ_le hh) ω (childNode d D h hh p.1 c) p.2) ∈ B)
    let R : Finset idx := Finset.univ.filter (fun p : idx => k ≤ (S p).card)
    d ^ (D - 1) ≤ 4 * R.card := by
  classical
  intro idx S R
  have hd_pos : 0 < d := by omega
  let φ : idx × Fin d → Fin (d ^ D) := fun ⟨⟨u, j⟩, c⟩ =>
    globalLeaf d D h (Nat.le_of_succ_le hh) (childNode d D h hh u c)
      (ord d D (Nat.le_of_succ_le hh) ω (childNode d D h hh u c) j)
  have hφ_inj : Function.Injective φ := by
    intro ⟨⟨u1, j1⟩, c1⟩ ⟨⟨u2, j2⟩, c2⟩ heq
    have hval := congrArg Fin.val heq
    simp only [φ, globalLeaf, childNode] at hval
    have hdh : 0 < d ^ h := pow_pos hd_pos h
    have hlt1 := (ord d D (Nat.le_of_succ_le hh) ω (childNode d D h hh u1 c1) j1).isLt
    have hlt2 := (ord d D (Nat.le_of_succ_le hh) ω (childNode d D h hh u2 c2) j2).isLt
    have hq : u1.val * d + c1.val = u2.val * d + c2.val := by
      have hdiv1 : ((u1.val * d + c1.val) * d ^ h +
          (ord d D (Nat.le_of_succ_le hh) ω (childNode d D h hh u1 c1) j1).val) / d ^ h =
          u1.val * d + c1.val := by
        rw [mul_comm _ (d ^ h), Nat.mul_add_div hdh, Nat.div_eq_of_lt hlt1, add_zero]
      have hdiv2 : ((u2.val * d + c2.val) * d ^ h +
          (ord d D (Nat.le_of_succ_le hh) ω (childNode d D h hh u2 c2) j2).val) / d ^ h =
          u2.val * d + c2.val := by
        rw [mul_comm _ (d ^ h), Nat.mul_add_div hdh, Nat.div_eq_of_lt hlt2, add_zero]
      have hval' : (u1.val * d + c1.val) * d ^ h +
          (ord d D (Nat.le_of_succ_le hh) ω (childNode d D h hh u1 c1) j1).val =
          (u2.val * d + c2.val) * d ^ h +
          (ord d D (Nat.le_of_succ_le hh) ω (childNode d D h hh u2 c2) j2).val := hval
      rw [← hdiv1, hval', hdiv2]
    have hc1 := c1.isLt
    have hc2 := c2.isLt
    have hu_eq : u1 = u2 := by
      ext
      have h1 : (u1.val * d + c1.val) / d = u1.val := by
        rw [mul_comm _ d, Nat.mul_add_div hd_pos, Nat.div_eq_of_lt hc1, add_zero]
      have h2 : (u2.val * d + c2.val) / d = u2.val := by
        rw [mul_comm _ d, Nat.mul_add_div hd_pos, Nat.div_eq_of_lt hc2, add_zero]
      rw [← h1, hq, h2]
    subst hu_eq
    have hc_eq : c1 = c2 := by ext; omega
    subst hc_eq
    have hord_eq : ord d D (Nat.le_of_succ_le hh) ω (childNode d D h hh u1 c1) j1 =
        ord d D (Nat.le_of_succ_le hh) ω (childNode d D h hh u1 c1) j2 := by
      ext
      have hval' : (u1.val * d + c1.val) * d ^ h +
          (ord d D (Nat.le_of_succ_le hh) ω (childNode d D h hh u1 c1) j1).val =
          (u1.val * d + c1.val) * d ^ h +
          (ord d D (Nat.le_of_succ_le hh) ω (childNode d D h hh u1 c1) j2).val := hval
      omega
    have hj_eq : j1 = j2 := (ord d D (Nat.le_of_succ_le hh) ω (childNode d D h hh u1 c1)).injective hord_eq
    subst hj_eq
    rfl
  have hcard_dom : Fintype.card (idx × Fin d) = d ^ D := by
    simp only [idx, Fintype.card_prod, Fintype.card_fin]
    rw [← pow_add, ← pow_succ]
    congr 1
    omega
  have hφ_bij : Function.Bijective φ :=
    (Fintype.bijective_iff_injective_and_card φ).mpr ⟨hφ_inj, by rw [hcard_dom, Fintype.card_fin]⟩
  have hsum_eq : ∑ p : idx, (S p).card = B.card := by
    have h1 : ∑ p : idx, (S p).card =
        (Finset.univ.filter (fun q : idx × Fin d => φ q ∈ B)).card := by
      rw [Finset.card_filter, Fintype.sum_prod_type (fun q : idx × Fin d => if φ q ∈ B then 1 else 0)]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Finset.card_filter]
    rw [h1]
    have h2 : (Finset.univ.filter (fun q : idx × Fin d => φ q ∈ B)).card =
        ((Finset.univ.filter (fun q : idx × Fin d => φ q ∈ B)).image φ).card :=
      (Finset.card_image_of_injective _ hφ_inj).symm
    rw [h2]
    congr 1
    ext x
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨q, hq, rfl⟩; exact hq
    · intro hx
      obtain ⟨q, rfl⟩ := hφ_bij.2 x
      exact ⟨q, hx, rfl⟩
  have hN : Fintype.card idx = d ^ (D - 1) := by
    simp only [idx, Fintype.card_prod, Fintype.card_fin]
    rw [← pow_add]
    congr 1
    omega
  have hsum_le : ∑ p : idx, (S p).card ≤ R.card * d + Fintype.card idx * k := by
    calc ∑ p : idx, (S p).card
        = ∑ p ∈ R, (S p).card + ∑ p ∈ Rᶜ, (S p).card := by
          rw [Finset.sum_add_sum_compl]
      _ ≤ ∑ _p ∈ R, d + ∑ _p ∈ Rᶜ, k := by
          apply Nat.add_le_add
          · refine Finset.sum_le_sum fun p _ => ?_
            exact (Finset.card_le_univ _).trans (by simp)
          · refine Finset.sum_le_sum fun p hp => ?_
            have hnot : ¬ k ≤ (S p).card := by
              simpa [R] using hp
            omega
      _ = R.card * d + Rᶜ.card * k := by simp
      _ ≤ R.card * d + Fintype.card idx * k := by
          apply Nat.add_le_add_left
          exact Nat.mul_le_mul_right k (Finset.card_le_univ _)
  have hpow : d ^ D = d ^ (D - 1) * d := by
    conv_lhs => rw [show D = (D - 1) + 1 by omega, pow_succ]
  rw [hsum_eq, hN] at hsum_le
  have hB' : d ^ (D - 1) * d ≤ 2 * B.card := by rw [← hpow]; exact hB
  nlinarith

open Classical in
lemma step_bad_bound {k d D h : ℕ} (hk : 1 ≤ k) (hd : d = 4 * k) (hh : h + 1 ≤ D)
    (ω : State d D h) (B : Finset (Fin (d ^ D))) (hB : d ^ D ≤ 2 * B.card) :
    let c : ℝ := 1 - 1 / (d.choose k : ℝ)
    ((Finset.univ.filter (fun σ : Level d D h => ¬ HasGoodBlock k d D h hh ω σ B)).card : ℝ) ≤
      c ^ (d ^ (D - 1) / 4) * (Fintype.card (Level d D h) : ℝ) := by
  intro c
  have hkd : k ≤ d := by omega
  have hchoose_ge : 1 ≤ d.choose k := Nat.choose_pos hkd
  have hc_nonneg : 0 ≤ c := by
    have h1 : (1 : ℝ) ≤ (d.choose k : ℝ) := by exact_mod_cast hchoose_ge
    have h2 : 1 / (d.choose k : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact h1
    linarith
  have hc_le_one : c ≤ 1 := by
    have h1 : (0 : ℝ) < (d.choose k : ℝ) := by exact_mod_cast hchoose_ge
    have h2 : 0 ≤ 1 / (d.choose k : ℝ) := by positivity
    linarith
  let idx := Fin (d ^ (D - (h + 1))) × Fin (d ^ h)
  let S (p : idx) : Finset (Fin d) :=
    Finset.univ.filter (fun c0 : Fin d =>
      globalLeaf d D h (Nat.le_of_succ_le hh) (childNode d D h hh p.1 c0)
        (ord d D (Nat.le_of_succ_le hh) ω (childNode d D h hh p.1 c0) p.2) ∈ B)
  let R : Finset idx := Finset.univ.filter (fun p : idx => k ≤ (S p).card)
  let eLevel : Level d D h ≃ (idx → Equiv.Perm (Fin d)) :=
    (Equiv.curry (Fin (d ^ (D - (h + 1)))) (Fin (d ^ h)) (Equiv.Perm (Fin d))).symm
  have hcard_eq :
      (Finset.univ.filter (fun σ : Level d D h => ¬ HasGoodBlock k d D h hh ω σ B)).card =
      (Finset.univ.filter (fun f : idx → Equiv.Perm (Fin d) =>
        ∀ p : idx, ¬ ∀ t : Fin d, t.val < k → f p t ∈ S p)).card := by
    refine Finset.card_bij (fun σ _ => eLevel σ) ?_ ?_ ?_
    · intro σ hσ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
      intro ⟨u, j⟩ hgood
      apply hσ
      refine ⟨u, j, fun t ht => ?_⟩
      have hmem : σ u j t ∈ S (u, j) := hgood t ht
      exact (Finset.mem_filter.mp hmem).2
    · intro σ1 _ σ2 _ h; exact eLevel.injective h
    · intro f hf
      refine ⟨eLevel.symm f, ?_, eLevel.apply_symm_apply f⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf ⊢
      rintro ⟨u, j, hgood⟩
      apply hf ⟨u, j⟩
      intro t ht
      have hmem : globalLeaf d D h (Nat.le_of_succ_le hh) (childNode d D h hh u (f (u, j) t))
          (ord d D (Nat.le_of_succ_le hh) ω (childNode d D h hh u (f (u, j) t)) j) ∈ B :=
        hgood t ht
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmem⟩
  rw [hcard_eq, card_filter_pi_prod (fun p (σ : Equiv.Perm (Fin d)) => ¬ ∀ t : Fin d, t.val < k → σ t ∈ S p)]
  have hFintype_level : (Fintype.card (Level d D h) : ℝ) =
      ∏ _p : idx, (Fintype.card (Equiv.Perm (Fin d)) : ℝ) := by
    rw [Fintype.card_congr eLevel, Fintype.card_pi, Nat.cast_prod]
  rw [hFintype_level, Nat.cast_prod]
  have hprod_le :
      (∏ p : idx, ((Finset.univ.filter (fun σ : Equiv.Perm (Fin d) =>
          ¬ ∀ t : Fin d, t.val < k → σ t ∈ S p)).card : ℝ)) ≤
      ∏ p : idx, ((if p ∈ R then c else 1) * (Fintype.card (Equiv.Perm (Fin d)) : ℝ)) := by
    refine Finset.prod_le_prod (fun p _ => Nat.cast_nonneg _) (fun p _ => ?_)
    split_ifs with hp
    · have hSp : k ≤ (S p).card := (Finset.mem_filter.mp hp).2
      exact card_perm_avoid_prefix hkd (S p) hSp
    · rw [one_mul]
      exact_mod_cast Finset.card_le_univ _
  have hprod_split :
      (∏ p : idx, ((if p ∈ R then c else 1) * (Fintype.card (Equiv.Perm (Fin d)) : ℝ))) =
      c ^ R.card * ∏ _p : idx, (Fintype.card (Equiv.Perm (Fin d)) : ℝ) := by
    rw [Finset.prod_mul_distrib]
    congr 1
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
    congr 2
    ext p
    simp
  have hR_ge : d ^ (D - 1) / 4 ≤ R.card := by
    have h4R := count_rich_pairs hk hd hh ω B hB
    have h4R' : d ^ (D - 1) ≤ 4 * R.card := by
      convert h4R using 2
    omega
  have hpow_le : c ^ R.card ≤ c ^ (d ^ (D - 1) / 4) :=
    pow_le_pow_of_le_one hc_nonneg hc_le_one hR_ge
  calc (∏ p : idx, ((Finset.univ.filter (fun σ : Equiv.Perm (Fin d) =>
          ¬ ∀ t : Fin d, t.val < k → σ t ∈ S p)).card : ℝ))
      ≤ c ^ R.card * ∏ _p : idx, (Fintype.card (Equiv.Perm (Fin d)) : ℝ) := by
        rw [← hprod_split]; exact hprod_le
    _ ≤ c ^ (d ^ (D - 1) / 4) * ∏ _p : idx, (Fintype.card (Equiv.Perm (Fin d)) : ℝ) := by
        exact mul_le_mul_of_nonneg_right hpow_le (Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _)

open Classical in
lemma card_allBad_le {k d D : ℕ} (hk : 1 ≤ k) (hd : d = 4 * k)
    (B : Finset (Fin (d ^ D))) (hB : d ^ D ≤ 2 * B.card) :
    let c : ℝ := 1 - 1 / (d.choose k : ℝ)
    ∀ {h : ℕ} (hh : h ≤ D),
      ((Finset.univ.filter (fun ω : State d D h => AllBad k d D hh ω B)).card : ℝ) ≤
        (c ^ (d ^ (D - 1) / 4)) ^ h * (Fintype.card (State d D h) : ℝ) := by
  intro c h
  induction h with
  | zero =>
    intro hh
    rw [pow_zero, one_mul]
    exact_mod_cast Finset.card_le_univ _
  | succ h ih =>
    intro hh
    have hh' : h ≤ D := Nat.le_of_succ_le hh
    have hfilter_eq :
        (Finset.univ.filter (fun p : State d D (h + 1) => AllBad k d D hh p B)).card =
        ∑ ω ∈ Finset.univ.filter (fun ω : State d D h => AllBad k d D hh' ω B),
          (Finset.univ.filter (fun σ : Level d D h => ¬ HasGoodBlock k d D h hh ω σ B)).card := by
      rw [Finset.card_filter]
      have hcongr :
          (∑ p : State d D (h + 1), if AllBad k d D hh p B then 1 else 0) =
          ∑ p : State d D h × Level d D h,
            if AllBad k d D hh' p.1 B ∧ ¬ HasGoodBlock k d D h hh p.1 p.2 B then 1 else 0 := by
        refine Finset.sum_congr rfl fun ⟨ω, σ⟩ _ => ?_
        by_cases h1 : AllBad k d D hh' ω B ∧ ¬ HasGoodBlock k d D h hh ω σ B
        · simp [AllBad, h1]
        · simp [AllBad, h1]
      rw [hcongr, Fintype.sum_prod_type, Finset.sum_filter]
      refine Finset.sum_congr rfl fun ω _ => ?_
      by_cases hω : AllBad k d D hh' ω B
      · simp [hω, Finset.card_filter]
      · simp [hω]
    rw [hfilter_eq, Nat.cast_sum]
    have hsum_le :
        (∑ ω ∈ Finset.univ.filter (fun ω : State d D h => AllBad k d D hh' ω B),
          ((Finset.univ.filter (fun σ : Level d D h => ¬ HasGoodBlock k d D h hh ω σ B)).card : ℝ)) ≤
        ∑ _ω ∈ Finset.univ.filter (fun ω : State d D h => AllBad k d D hh' ω B),
          (c ^ (d ^ (D - 1) / 4) * (Fintype.card (Level d D h) : ℝ)) := by
      refine Finset.sum_le_sum fun ω _ => step_bad_bound hk hd hh ω B hB
    rw [Finset.sum_const, nsmul_eq_mul] at hsum_le
    have hih := ih hh'
    have hkd : k ≤ d := by omega
    have hchoose_ge : 1 ≤ d.choose k := Nat.choose_pos hkd
    have hc_nonneg : 0 ≤ c := by
      have h1 : (1 : ℝ) ≤ (d.choose k : ℝ) := by exact_mod_cast hchoose_ge
      have h2 : 1 / (d.choose k : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact h1
      linarith
    have hfactor_nonneg : 0 ≤ c ^ (d ^ (D - 1) / 4) * (Fintype.card (Level d D h) : ℝ) := by
      positivity
    have hprod_card : (Fintype.card (State d D (h + 1)) : ℝ) =
        (Fintype.card (State d D h) : ℝ) * (Fintype.card (Level d D h) : ℝ) := by
      change (Fintype.card (State d D h × Level d D h) : ℝ) = _
      rw [Fintype.card_prod, Nat.cast_mul]
    rw [hprod_card, pow_succ]
    calc _ ≤ _ := hsum_le
      _ ≤ ((c ^ (d ^ (D - 1) / 4)) ^ h * (Fintype.card (State d D h) : ℝ)) *
            (c ^ (d ^ (D - 1) / 4) * (Fintype.card (Level d D h) : ℝ)) :=
          mul_le_mul_of_nonneg_right hih hfactor_nonneg
      _ = (c ^ (d ^ (D - 1) / 4)) ^ h * c ^ (d ^ (D - 1) / 4) *
            ((Fintype.card (State d D h) : ℝ) * (Fintype.card (Level d D h) : ℝ)) := by ring

/-! ### Step 4: Existence of a good state and geometric rectangle extraction -/

lemma exists_good_state (k : ℕ) (hk : 1 ≤ k) :
    let d := 4 * k
    ∃ D : ℕ, 1 ≤ D ∧ ∃ ωD : State d D D,
      ∀ B : Finset (Fin (d ^ D)), d ^ D ≤ 2 * B.card → ¬ AllBad k d D (le_refl D) ωD B := by
  classical
  intro d
  have hkd : k ≤ d := by omega
  have hd_ge4 : 4 ≤ d := by omega
  have hchoose_gt1 : 1 < d.choose k := by
    have hpos1 : 1 ≤ (d - 1).choose k := Nat.choose_pos (by omega)
    have hpos2 : 1 ≤ (d - 1).choose (k - 1) := Nat.choose_pos (by omega)
    have hrec : d.choose k = (d - 1).choose (k - 1) + (d - 1).choose k := by
      have h0 := Nat.choose_succ_succ (d - 1) (k - 1)
      rw [Nat.succ_eq_add_one, Nat.succ_eq_add_one,
        show (d - 1) + 1 = d by omega, show (k - 1) + 1 = k by omega] at h0
      exact h0
    omega
  let c : ℝ := 1 - 1 / (d.choose k : ℝ)
  have hc_nonneg : 0 ≤ c := by
    have h1 : (1 : ℝ) < (d.choose k : ℝ) := by exact_mod_cast hchoose_gt1
    have h2 : 1 / (d.choose k : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    linarith
  have hc_lt_one : c < 1 := by
    have h1 : (0 : ℝ) < (d.choose k : ℝ) := by exact_mod_cast lt_trans Nat.zero_lt_one hchoose_gt1
    have h2 : 0 < 1 / (d.choose k : ℝ) := by positivity
    linarith
  obtain ⟨M, hM⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < 1 / 2 by norm_num) hc_lt_one
  have hM_pos : 1 ≤ M := by
    by_contra h
    have hM0 : M = 0 := by omega
    subst hM0
    norm_num at hM
  let D := 4 * d * M
  have hD_pos : 1 ≤ D := by
    have : 4 * d ≥ 1 := by omega
    dsimp only [D]
    nlinarith
  refine ⟨D, hD_pos, ?_⟩
  let goodB : Finset (Finset (Fin (d ^ D))) :=
    Finset.univ.filter (fun B : Finset (Fin (d ^ D)) => d ^ D ≤ 2 * B.card)
  let unionBad : Finset (State d D D) :=
    goodB.biUnion (fun B => Finset.univ.filter (fun ω : State d D D => AllBad k d D (le_refl D) ω B))
  have hD_div : d ^ (D - 1) / 4 * D = M * d ^ D := by
    have hd4 : 4 ∣ d := ⟨k, rfl⟩
    have hdiv_pow : 4 ∣ d ^ (D - 1) := by
      have hD_ge2 : 2 ≤ D := by
        have : 4 * d ≥ 16 := by omega
        dsimp only [D]
        nlinarith
      have hD1 : 1 ≤ D - 1 := by omega
      rw [show D - 1 = (D - 2) + 1 by omega, pow_succ]
      exact dvd_mul_of_dvd_right hd4 _
    have hmul_div : d ^ (D - 1) / 4 * 4 = d ^ (D - 1) := Nat.div_mul_cancel hdiv_pow
    have hpow : d ^ (D - 1) * d = d ^ D := by
      conv_rhs => rw [show D = (D - 1) + 1 by omega, pow_succ]
    calc d ^ (D - 1) / 4 * D
        = (d ^ (D - 1) / 4 * 4) * d * M := by simp only [D]; ring
      _ = d ^ (D - 1) * d * M := by rw [hmul_div]
      _ = d ^ D * M := by rw [hpow]
      _ = M * d ^ D := mul_comm _ _
  have hcard_lt : (unionBad.card : ℝ) < (Fintype.card (State d D D) : ℝ) := by
    have hstate_pos : (0 : ℝ) < (Fintype.card (State d D D) : ℝ) := by
      have hne : ∀ h, Nonempty (State d D h) := by
        intro h
        induction h with
        | zero => exact ⟨()⟩
        | succ h ih =>
          rcases ih with ⟨ω⟩
          exact ⟨(ω, fun _ _ => Equiv.refl _)⟩
      haveI : Nonempty (State d D D) := hne D
      exact_mod_cast Fintype.card_pos
    have hle1 : (unionBad.card : ℝ) ≤
        ∑ B ∈ goodB, ((Finset.univ.filter (fun ω : State d D D => AllBad k d D (le_refl D) ω B)).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    have hle2 :
        (∑ B ∈ goodB, ((Finset.univ.filter (fun ω : State d D D => AllBad k d D (le_refl D) ω B)).card : ℝ)) ≤
        ∑ _B ∈ goodB, ((c ^ (d ^ (D - 1) / 4)) ^ D * (Fintype.card (State d D D) : ℝ)) := by
      refine Finset.sum_le_sum fun B hB => ?_
      exact card_allBad_le hk rfl B (Finset.mem_filter.mp hB).2 (le_refl D)
    rw [Finset.sum_const, nsmul_eq_mul] at hle2
    have hpow_eq : (c ^ (d ^ (D - 1) / 4)) ^ D = (c ^ M) ^ (d ^ D) := by
      rw [← pow_mul, hD_div, pow_mul]
    rw [hpow_eq] at hle2
    have hgoodB_le : (goodB.card : ℝ) ≤ (2 : ℝ) ^ (d ^ D) := by
      have h1 : goodB.card ≤ Fintype.card (Finset (Fin (d ^ D))) := Finset.card_le_univ _
      rw [Fintype.card_finset, Fintype.card_fin] at h1
      exact_mod_cast h1
    have hpow_lt : (c ^ M) ^ (d ^ D) < (1 / 2 : ℝ) ^ (d ^ D) := by
      have hnd : 0 < d ^ D := pow_pos (by omega) D
      exact pow_lt_pow_left₀ hM (pow_nonneg hc_nonneg M) (ne_of_gt hnd)
    have hstrict : (goodB.card : ℝ) * ((c ^ M) ^ (d ^ D) * (Fintype.card (State d D D) : ℝ)) <
        (2 : ℝ) ^ (d ^ D) * ((1 / 2 : ℝ) ^ (d ^ D) * (Fintype.card (State d D D) : ℝ)) := by
      by_cases h0 : goodB.card = 0
      · rw [h0, Nat.cast_zero, zero_mul]
        positivity
      · have hposB : (0 : ℝ) < (goodB.card : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero h0
        have hstep1 : (goodB.card : ℝ) * ((c ^ M) ^ (d ^ D) * (Fintype.card (State d D D) : ℝ)) <
            (goodB.card : ℝ) * ((1 / 2 : ℝ) ^ (d ^ D) * (Fintype.card (State d D D) : ℝ)) := by
          exact mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_right hpow_lt hstate_pos) hposB
        have hstep2 : (goodB.card : ℝ) * ((1 / 2 : ℝ) ^ (d ^ D) * (Fintype.card (State d D D) : ℝ)) ≤
            (2 : ℝ) ^ (d ^ D) * ((1 / 2 : ℝ) ^ (d ^ D) * (Fintype.card (State d D D) : ℝ)) := by
          exact mul_le_mul_of_nonneg_right hgoodB_le (by positivity)
        exact lt_of_lt_of_le hstep1 hstep2
    have hcancel : (2 : ℝ) ^ (d ^ D) * ((1 / 2 : ℝ) ^ (d ^ D) * (Fintype.card (State d D D) : ℝ)) =
        (Fintype.card (State d D D) : ℝ) := by
      rw [← mul_assoc, ← mul_pow]
      norm_num
    linarith
  have hcard_lt_nat : unionBad.card < (Finset.univ : Finset (State d D D)).card := by
    rw [Finset.card_univ]
    exact_mod_cast hcard_lt
  obtain ⟨ωD, _, hωD⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard_lt_nat
  refine ⟨ωD, fun B hB hall => hωD ?_⟩
  exact Finset.mem_biUnion.mpr ⟨B, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hB⟩,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hall⟩⟩

lemma not_allBad_exists_goodBlock {k d D : ℕ} :
    ∀ {h : ℕ} (hh : h ≤ D) (ω : State d D h) (B : Finset (Fin (d ^ D))),
      ¬ AllBad k d D hh ω B →
      ∃ (h' : ℕ) (hle : h' + 1 ≤ h),
        HasGoodBlock k d D h' (hle.trans hh) (statePrefix d D hle ω).1 (statePrefix d D hle ω).2 B := by
  intro h
  induction h with
  | zero =>
    intro hh ω B hnot
    exact absurd trivial hnot
  | succ h ih =>
    intro hh ω B hnot
    rcases ω with ⟨ω', σ⟩
    by_cases hgood : HasGoodBlock k d D h hh ω' σ B
    · refine ⟨h, le_refl (h + 1), ?_⟩
      rw [statePrefix_self d D (h + 1) (ω', σ)]
      exact hgood
    · have hnot' : ¬ AllBad k d D (Nat.le_of_succ_le hh) ω' B := by
        intro hall
        exact hnot ⟨hall, hgood⟩
      obtain ⟨h', hle, hg⟩ := ih (Nat.le_of_succ_le hh) ω' B hnot'
      refine ⟨h', Nat.le_succ_of_le hle, ?_⟩
      rw [statePrefix_succ]
      exact hg

end OMA.Green76Proof

theorem OMA.solution : type_of% @Green76.green_76.variants.subset := by
  classical
  rintro ⟨k, hk⟩
  by_cases hk0 : k = 0
  · subst hk0
    obtain ⟨A', hA'sub, _, hhit⟩ := hk ∅
    obtain ⟨p, hp, _⟩ := hhit (0, 0) (0, 0) (Nat.zero_le _)
    exact absurd (hA'sub hp) (Finset.notMem_empty p)
  have hk_pos : 1 ≤ k := Nat.pos_of_ne_zero hk0
  set d := 4 * k with hd_def
  have hd_pos : 0 < d := by omega
  have hkd : k ≤ d := by omega
  obtain ⟨D, hD_pos, ωD, hωD⟩ := OMA.Green76Proof.exists_good_state k hk_pos
  let π : Equiv.Perm (Fin (d ^ D)) :=
    (OMA.Green76Proof.ord d D (le_refl D) ωD ⟨0, by simp⟩).symm
  let pt : Fin (d ^ D) → ℝ × ℝ := fun x => ((x.val : ℝ), ((π x).val : ℝ))
  have hpt_inj : Function.Injective pt := by
    intro x y hxy
    have hx : (x.val : ℝ) = (y.val : ℝ) := congrArg Prod.fst hxy
    exact Fin.ext (Nat.cast_injective hx)
  let A : Finset (ℝ × ℝ) := Finset.univ.image pt
  have hA_card : A.card = d ^ D := by
    rw [Finset.card_image_of_injective _ hpt_inj, Finset.card_univ, Fintype.card_fin]
  obtain ⟨A', hA'sub, hA'card, hhit⟩ := hk A
  let S' : Finset (Fin (d ^ D)) := Finset.univ.filter (fun x => pt x ∈ A')
  have hS'_card : S'.card = A'.card := by
    have himg : S'.image pt = A' := by
      ext p
      simp only [Finset.mem_image, S', Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨x, hx, rfl⟩; exact hx
      · intro hp
        obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp (hA'sub hp)
        exact ⟨x, hp, rfl⟩
    rw [← himg, Finset.card_image_of_injective _ hpt_inj]
  let B : Finset (Fin (d ^ D)) := S'ᶜ
  have hB_card : d ^ D ≤ 2 * B.card := by
    have hcomp : B.card + S'.card = d ^ D := by
      rw [Finset.card_compl, Fintype.card_fin]
      have hle : S'.card ≤ d ^ D := (Finset.card_le_univ _).trans (by simp)
      omega
    rw [hA_card] at hA'card
    omega
  have hnotBad := hωD B hB_card
  obtain ⟨h, hh, hgood⟩ := OMA.Green76Proof.not_allBad_exists_goodBlock (le_refl D) ωD B hnotBad
  obtain ⟨u, j, hblock⟩ := hgood
  let pSt := OMA.Green76Proof.statePrefix d D hh ωD
  let r_of (t : Fin d) : Fin (d ^ (h + 1)) := finProdFinEquiv (j, t)
  let x_of (t : Fin d) : Fin (d ^ D) :=
    OMA.Green76Proof.globalLeaf d D (h + 1) hh u (OMA.Green76Proof.ord d D hh pSt u (r_of t))
  have hx_mem_B : ∀ t : Fin d, t.val < k → x_of t ∈ B := by
    intro t ht
    have hgx := OMA.Green76Proof.globalLeaf_ord_succ d D h hh pSt.1 pSt.2 u j t
    have hbt := hblock t ht
    change OMA.Green76Proof.globalLeaf d D (h + 1) hh u
      (OMA.Green76Proof.ord d D hh (pSt.1, pSt.2) u (finProdFinEquiv (j, t))) ∈ B
    rw [hgx]
    exact hbt
  let t_lo : Fin d := ⟨0, hd_pos⟩
  let t_hi : Fin d := ⟨k - 1, by omega⟩
  let a : ℝ × ℝ := (((u.val * d ^ (h + 1) : ℕ) : ℝ), ((π (x_of t_lo)).val : ℝ))
  let b : ℝ × ℝ := ((((u.val + 1) * d ^ (h + 1) - 1 : ℕ) : ℝ), ((π (x_of t_hi)).val : ℝ))
  have hmem_rect : ∀ x : Fin (d ^ D),
      pt x ∈ Set.Icc a b ↔ ∃ t : Fin d, t.val < k ∧ x = x_of t := by
    intro x
    have hdh_pos : 0 < d ^ (h + 1) := pow_pos hd_pos (h + 1)
    constructor
    · rintro ⟨⟨hax, hay⟩, ⟨hbx, hby⟩⟩
      have hax_nat : u.val * d ^ (h + 1) ≤ x.val := by dsimp only [a, pt] at hax; exact_mod_cast hax
      have hbx_nat : x.val ≤ (u.val + 1) * d ^ (h + 1) - 1 := by dsimp only [b, pt] at hbx; exact_mod_cast hbx
      have hay_nat : (π (x_of t_lo)).val ≤ (π x).val := by dsimp only [a, pt] at hay; exact_mod_cast hay
      have hby_nat : (π x).val ≤ (π (x_of t_hi)).val := by dsimp only [b, pt] at hby; exact_mod_cast hby
      let x' : Fin (d ^ (h + 1)) := ⟨x.val - u.val * d ^ (h + 1), by
        have hsum : u.val * d ^ (h + 1) + d ^ (h + 1) = (u.val + 1) * d ^ (h + 1) := by ring
        omega⟩
      let r : Fin (d ^ (h + 1)) := (OMA.Green76Proof.ord d D hh pSt u).symm x'
      have hx_eq : x = OMA.Green76Proof.globalLeaf d D (h + 1) hh u
          (OMA.Green76Proof.ord d D hh pSt u r) := by
        ext
        simp only [OMA.Green76Proof.globalLeaf, r, Equiv.apply_symm_apply, x']
        omega
      have hr_lo : r_of t_lo ≤ r := by
        by_contra hlt
        have hlt' : r < r_of t_lo := lt_of_not_ge hlt
        have hmono := OMA.Green76Proof.final_perm_strictMono_on_node d D hd_pos ωD hh u r (r_of t_lo) hlt'
        have hmono' : π x < π (x_of t_lo) := by simpa only [← hx_eq, x_of, pSt] using hmono
        exact absurd hmono' (not_lt_of_ge hay_nat)
      have hr_hi : r ≤ r_of t_hi := by
        by_contra hlt
        have hlt' : r_of t_hi < r := lt_of_not_ge hlt
        have hmono := OMA.Green76Proof.final_perm_strictMono_on_node d D hd_pos ωD hh u (r_of t_hi) r hlt'
        have hmono' : π (x_of t_hi) < π x := by simpa only [← hx_eq, x_of, pSt] using hmono
        exact absurd hmono' (not_lt_of_ge hby_nat)
      have hr_lo_val : d * j.val ≤ r.val := by
        have : 0 + d * j.val ≤ r.val := hr_lo
        omega
      have hr_hi_val : r.val ≤ (k - 1) + d * j.val := hr_hi
      let t : Fin d := ⟨r.val - d * j.val, by omega⟩
      have ht_lt : t.val < k := by simp only [t]; omega
      have hr_eq : r = r_of t := by
        ext
        change r.val = (r.val - d * j.val) + d * j.val
        omega
      refine ⟨t, ht_lt, ?_⟩
      rw [hx_eq, hr_eq]
    · rintro ⟨t, ht, rfl⟩
      have h_lo_le : r_of t_lo ≤ r_of t := by
        change 0 + d * j.val ≤ t.val + d * j.val
        omega
      have h_le_hi : r_of t ≤ r_of t_hi := by
        change t.val + d * j.val ≤ (k - 1) + d * j.val
        omega
      have hy_lo : (π (x_of t_lo)).val ≤ (π (x_of t)).val := by
        rcases eq_or_lt_of_le h_lo_le with heq | hlt
        · rw [show x_of t_lo = x_of t by simp [x_of, heq]]
        · exact le_of_lt (OMA.Green76Proof.final_perm_strictMono_on_node d D hd_pos ωD hh u (r_of t_lo) (r_of t) hlt)
      have hy_hi : (π (x_of t)).val ≤ (π (x_of t_hi)).val := by
        rcases eq_or_lt_of_le h_le_hi with heq | hlt
        · rw [show x_of t = x_of t_hi by simp [x_of, heq]]
        · exact le_of_lt (OMA.Green76Proof.final_perm_strictMono_on_node d D hd_pos ωD hh u (r_of t) (r_of t_hi) hlt)
      have hx_lo : u.val * d ^ (h + 1) ≤ (x_of t).val := by
        simp only [x_of, OMA.Green76Proof.globalLeaf]
        omega
      have hx_hi : (x_of t).val ≤ (u.val + 1) * d ^ (h + 1) - 1 := by
        simp only [x_of, OMA.Green76Proof.globalLeaf]
        have hlt := (OMA.Green76Proof.ord d D hh pSt u (r_of t)).isLt
        have hsum : u.val * d ^ (h + 1) + d ^ (h + 1) = (u.val + 1) * d ^ (h + 1) := by ring
        omega
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
      · dsimp only [a, pt]; exact_mod_cast hx_lo
      · dsimp only [a, pt]; exact_mod_cast hy_lo
      · dsimp only [b, pt]; exact_mod_cast hx_hi
      · dsimp only [b, pt]; exact_mod_cast hy_hi
  have hrich : k ≤ (A.filter (fun p => p ∈ Set.Icc a b)).card := by
    let T : Finset (Fin d) := Finset.univ.filter (fun t : Fin d => t.val < k)
    have hT_card : T.card = k := by
      have hbij : T = Finset.univ.map (Fin.castLEEmb hkd) := by
        ext t
        simp only [T, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
          Fin.castLEEmb_apply]
        constructor
        · intro ht; exact ⟨⟨t.val, ht⟩, rfl⟩
        · rintro ⟨m, rfl⟩; exact m.isLt
      rw [hbij, Finset.card_map, Finset.card_univ, Fintype.card_fin]
    have hx_inj : Function.Injective x_of := by
      intro t1 t2 h12
      have hval := congrArg Fin.val h12
      simp only [x_of, OMA.Green76Proof.globalLeaf] at hval
      have hord : OMA.Green76Proof.ord d D hh pSt u (r_of t1) =
          OMA.Green76Proof.ord d D hh pSt u (r_of t2) := by
        ext; omega
      have hr : r_of t1 = r_of t2 := (OMA.Green76Proof.ord d D hh pSt u).injective hord
      have hp : (j, t1) = (j, t2) := finProdFinEquiv.injective hr
      exact congrArg Prod.snd hp
    have hsub : T.image (fun t => pt (x_of t)) ⊆ A.filter (fun p => p ∈ Set.Icc a b) := by
      intro p hp
      rcases Finset.mem_image.mp hp with ⟨t, ht, rfl⟩
      have ht' : t.val < k := (Finset.mem_filter.mp ht).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨x_of t, Finset.mem_univ _, rfl⟩, ?_⟩
      exact (hmem_rect (x_of t)).mpr ⟨t, ht', rfl⟩
    have hcard_img : (T.image (fun t => pt (x_of t))).card = k := by
      have hinj : Function.Injective (fun t => pt (x_of t)) := hpt_inj.comp hx_inj
      rw [Finset.card_image_of_injective T hinj, hT_card]
    rw [← hcard_img]
    exact Finset.card_le_card hsub
  obtain ⟨p, hpA', hpRect⟩ := hhit a b hrich
  obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp (hA'sub hpA')
  obtain ⟨t, ht, rfl⟩ := (hmem_rect x).mp hpRect
  have hxB : x_of t ∈ B := hx_mem_B t ht
  have hxS' : x_of t ∈ S' := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpA'⟩
  exact Finset.mem_compl.mp hxB hxS'
