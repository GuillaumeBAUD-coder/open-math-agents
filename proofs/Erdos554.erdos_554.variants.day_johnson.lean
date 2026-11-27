import FormalConjectures.ErdosProblems.«554»
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions

/-! Day–Johnson (arXiv:1602.07607) : colorations « rooted round » (RRC), doublement par rondes,
puis coloration produit itérée et inégalité finale. -/

open SimpleGraph Finset Filter Topology

namespace OMA

-- ## Fait A : un cycle `C_R` ne reçoit aucune marche fermée impaire de longueur `m < R`

/-- Adjacence de deux niveaux entiers dans le cycle `C_R` : pas de ±1, ou de ±(R-1) par la racine. -/
def AdjR (R a b : ℤ) : Prop := a - b = 1 ∨ b - a = 1 ∨ a - b = R - 1 ∨ b - a = R - 1

theorem adjR_comm {R a b : ℤ} : AdjR R a b ↔ AdjR R b a := by
  unfold AdjR; omega

theorem no_odd_closed_walk {m : ℕ} [NeZero m] (hm : Odd m) (hm3 : 3 ≤ m) {R : ℤ}
    (hR : (m : ℤ) < R) (g : Fin m → ℤ) (hg : ∀ j : Fin m, AdjR R (g j) (g (j + 1))) : False := by
  classical
  -- Chaque pas s'écrit comme un signe, codé par 2 * u - 1, plus un multiple de R.
  have hpas (j : Fin m) : ∃ u v : ℤ, 0 ≤ u ∧ u ≤ 1 ∧
      g (j + 1) - g j = 2 * u - 1 + R * v := by
    rcases hg j with h | h | h | h
    · exact ⟨0, 0, by decide, by decide, by omega⟩
    · exact ⟨1, 0, by decide, by decide, by omega⟩
    · exact ⟨1, -1, by decide, by decide, by simp; omega⟩
    · exact ⟨0, 1, by decide, by decide, by simp; omega⟩
  choose u v hu0 hu1 huv using hpas
  have hcycle : ∑ j : Fin m, g (j + 1) = ∑ j, g j :=
    Equiv.sum_comp (Equiv.addRight (1 : Fin m)) g
  have hsum := Finset.sum_congr (s₁ := (univ : Finset (Fin m))) rfl (fun j _ => huv j)
  rw [sum_sub_distrib, hcycle, sub_self, sum_add_distrib, sum_sub_distrib,
    ← mul_sum, ← mul_sum] at hsum
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hsum
  have hlo : 0 ≤ ∑ j, u j := sum_nonneg fun j _ => hu0 j
  have hhi : ∑ j, u j ≤ (m : ℤ) := by
    simpa using (sum_le_sum (s := univ) fun j _ => hu1 j)
  have hv : ∑ j, v j = 0 := by
    by_contra h
    rcases lt_or_gt_of_ne h with hn | hp
    · have ha : ∑ j, v j ≤ -1 := by omega
      have hb := mul_le_mul_of_nonneg_left ha (show 0 ≤ R by omega)
      linarith
    · have ha : 1 ≤ ∑ j, v j := by omega
      have hb := mul_le_mul_of_nonneg_left ha (show 0 ≤ R by omega)
      linarith
  rw [hv, mul_zero, add_zero] at hsum
  obtain ⟨k, hk⟩ := hm
  omega

-- ## Colorations « rooted round » (section 2 de l'article)

/-- Racine `o` au niveau 0, autres sommets aux niveaux `1 … R i - 1` dans chaque couleur `i`,
deux sommets distincts toujours adjacents dans `C_{R i}` pour au moins une couleur `i`. -/
def IsRRC {ι W : Type*} (R : ι → ℤ) (o : W) (lev : W → ι → ℤ) : Prop :=
  lev o = 0 ∧ (∀ w, w ≠ o → ∀ i, 1 ≤ lev w i ∧ lev w i + 1 ≤ R i) ∧
    ∀ w w', w ≠ w' → ∃ i, AdjR (R i) (lev w i) (lev w' i)

/-- La (5,5)-RRC de `K_5` : pentagone et pentagramme, niveaux `v` et `3v mod 5`. -/
def baseLev (v : Fin 5) (i : Fin 2) : ℤ := if i = 0 then (v.val : ℤ) else ((3 * v.val % 5 : ℕ) : ℤ)

theorem isRRC_base : IsRRC (fun _ : Fin 2 => (5 : ℤ)) (0 : Fin 5) baseLev := by
  unfold IsRRC AdjR baseLev
  decide

def bit (b : Bool) : ℤ := if b then 1 else 0

/-- Une ronde de doublements (Lemme 5 appliqué une fois à chaque couleur) : `R ↦ (R + 2, 2R - 1)`. -/
def roundR {ι : Type*} (R : ι → ℤ) : ι ⊕ ι → ℤ :=
  Sum.elim (fun i => R i + 2) (fun i => 2 * R i - 1)

def roundLev {ι W : Type*} (o : W) (lev : W → ι → ℤ) :
    Option ({w // w ≠ o} × (ι → Bool)) → ι ⊕ ι → ℤ
  | none => 0
  | some (w, σ) =>
      Sum.elim (fun i => lev w.1 i + 2 * bit (σ i)) (fun i => 2 * lev w.1 i - bit (σ i))

theorem isRRC_round {ι W : Type*} {R : ι → ℤ} {o : W} {lev : W → ι → ℤ} (h : IsRRC R o lev) :
    IsRRC (roundR R) none (roundLev o lev) := by
  obtain ⟨h0, hb, ha⟩ := h
  have key0 : ∀ (w : {w // w ≠ o}) (σ : ι → Bool),
      ∃ p, AdjR (roundR R p) 0 (roundLev o lev (some (w, σ)) p) := by
    intro w σ
    obtain ⟨i, hi⟩ := ha o w.1 (Ne.symm w.2)
    rw [h0] at hi
    have hbi := hb w.1 w.2 i
    simp only [Pi.zero_apply, AdjR] at hi
    have h1 : lev w.1 i = 1 ∨ lev w.1 i = R i - 1 := by omega
    cases hσ : σ i <;> rcases h1 with h1 | h1
    · exact ⟨Sum.inl i, by simp [roundLev, roundR, bit, hσ, AdjR]; omega⟩
    · exact ⟨Sum.inr i, by simp [roundLev, roundR, bit, hσ, AdjR]; omega⟩
    · exact ⟨Sum.inr i, by simp [roundLev, roundR, bit, hσ, AdjR]; omega⟩
    · exact ⟨Sum.inl i, by simp [roundLev, roundR, bit, hσ, AdjR]; omega⟩
  refine ⟨rfl, ?_, ?_⟩
  · rintro (_ | ⟨w, σ⟩) hne p
    · exact absurd rfl hne
    · rcases p with i | i <;>
      · have := hb w.1 w.2 i
        cases hσ : σ i <;> simp [roundLev, roundR, bit, hσ] <;> omega
  · rintro (_ | ⟨w, σ⟩) (_ | ⟨w', σ'⟩) hne
    · exact absurd rfl hne
    · exact key0 w' σ'
    · obtain ⟨p, hp⟩ := key0 w σ
      exact ⟨p, adjR_comm.mp hp⟩
    · by_cases hw : w = w'
      · subst hw
        have hσ : σ ≠ σ' := fun h => hne (by rw [h])
        obtain ⟨i, hi⟩ := Function.ne_iff.mp hσ
        refine ⟨Sum.inr i, ?_⟩
        cases hs : σ i <;> cases hs' : σ' i <;> simp_all [roundLev, roundR, bit, AdjR]
      · obtain ⟨i, hi⟩ := ha w.1 w'.1 (fun h => hw (Subtype.ext h))
        have hb1 := hb w.1 w.2 i
        have hb2 := hb w'.1 w'.2 i
        simp only [AdjR] at hi
        have hd : lev w.1 i - lev w'.1 i = 1 ∨ lev w'.1 i - lev w.1 i = 1 := by omega
        rcases hd with hd | hd <;> cases hs : σ i <;> cases hs' : σ' i <;>
          first
          | exact ⟨Sum.inl i, by simp [roundLev, roundR, bit, hs, hs', AdjR]; omega⟩
          | exact ⟨Sum.inr i, by simp [roundLev, roundR, bit, hs, hs', AdjR]; omega⟩

theorem card_round {ι W : Type*} [Fintype ι] [DecidableEq ι] [Fintype W] [DecidableEq W] (o : W) :
    Fintype.card (Option ({w // w ≠ o} × (ι → Bool))) =
      (Fintype.card W - 1) * 2 ^ Fintype.card ι + 1 := by
  simp [Fintype.card_option, Fintype.card_prod, Fintype.card_subtype_compl]

theorem exists_rrc (s : ℕ) : ∃ (ι : Type) (_ : Fintype ι) (W : Type) (_ : Fintype W)
    (R : ι → ℤ) (o : W) (lev : W → ι → ℤ), IsRRC R o lev ∧ (∀ i, 5 + 2 * (s : ℤ) ≤ R i) ∧
      0 < Fintype.card ι ∧ 2 ^ Fintype.card ι < Fintype.card W := by
  induction s with
  | zero =>
    exact ⟨Fin 2, inferInstance, Fin 5, inferInstance, fun _ => 5, 0, baseLev, isRRC_base,
      fun _ => by norm_num, by simp, by simp⟩
  | succ s ih =>
    obtain ⟨ι, hι, W, hW, R, o, lev, h, hR, hpos, hcard⟩ := ih
    classical
    refine ⟨ι ⊕ ι, inferInstance, Option ({w // w ≠ o} × (ι → Bool)), inferInstance,
      roundR R, none, roundLev o lev, isRRC_round h, ?_, ?_, ?_⟩
    · rintro (i | i) <;> simp only [roundR, Sum.elim_inl, Sum.elim_inr] <;> have := hR i <;>
        push_cast <;> omega
    · rw [Fintype.card_sum]; omega
    · rw [card_round, Fintype.card_sum]
      have h1 : 2 ^ Fintype.card ι ≤ Fintype.card W - 1 := by omega
      calc 2 ^ (Fintype.card ι + Fintype.card ι)
          = 2 ^ Fintype.card ι * 2 ^ Fintype.card ι := pow_add _ _ _
        _ ≤ (Fintype.card W - 1) * 2 ^ Fintype.card ι := Nat.mul_le_mul_right _ h1
        _ < _ := Nat.lt_succ_self _

-- ## Coloration produit itérée (Lemme 7.2)

def diffs {t : ℕ} {W : Type*} [DecidableEq W] (x y : Fin t → W) : Finset (Fin t) :=
  Finset.univ.filter (fun j => x j ≠ y j)

theorem diffs_comm {t : ℕ} {W : Type*} [DecidableEq W] (x y : Fin t → W) :
    diffs y x = diffs x y := by
  ext j; simp [diffs, ne_comm]

noncomputable def baseCol {ι W : Type*} [Nonempty ι] (R : ι → ℤ) (lev : W → ι → ℤ) (x y : W) : ι :=
  Classical.epsilon (fun i => AdjR (R i) (lev x i) (lev y i))

theorem baseCol_comm {ι W : Type*} [Nonempty ι] (R : ι → ℤ) (lev : W → ι → ℤ) (x y : W) :
    baseCol R lev y x = baseCol R lev x y := by
  unfold baseCol
  congr 1
  funext i
  exact propext adjR_comm

theorem baseCol_spec {ι W : Type*} [Nonempty ι] {R : ι → ℤ} {lev : W → ι → ℤ}
    (hadj : ∀ w w', w ≠ w' → ∃ i, AdjR (R i) (lev w i) (lev w' i)) {x y : W} (h : x ≠ y) :
    AdjR (R (baseCol R lev x y)) (lev x (baseCol R lev x y)) (lev y (baseCol R lev x y)) :=
  Classical.epsilon_spec (hadj x y h)

/-- Couleur d'une paire de mots : `none` s'ils sont égaux, sinon la première coordonnée `j` où ils
diffèrent et la couleur de base de la paire de lettres en `j`. -/
noncomputable def powCol {ι W : Type*} [Nonempty ι] [DecidableEq W] (R : ι → ℤ)
    (lev : W → ι → ℤ) {t : ℕ} (x y : Fin t → W) : Option (Fin t × ι) :=
  if h : (diffs x y).Nonempty then
    some ((diffs x y).min' h, baseCol R lev (x ((diffs x y).min' h)) (y ((diffs x y).min' h)))
  else none

theorem powCol_comm {ι W : Type*} [Nonempty ι] [DecidableEq W] (R : ι → ℤ)
    (lev : W → ι → ℤ) {t : ℕ} (x y : Fin t → W) : powCol R lev y x = powCol R lev x y := by
  unfold powCol
  rw [diffs_comm x y]
  by_cases h : (diffs x y).Nonempty
  · rw [dif_pos h, dif_pos h, baseCol_comm]
  · rw [dif_neg h, dif_neg h]

theorem power_bad {ι W : Type*} [Nonempty ι] [Fintype W] [DecidableEq W] (R : ι → ℤ)
    (lev : W → ι → ℤ) (hadj : ∀ w w', w ≠ w' → ∃ i, AdjR (R i) (lev w i) (lev w' i))
    {n : ℕ} (hn : 1 ≤ n) (hR : ∀ i, (2 * n + 1 : ℤ) < R i) (t : ℕ) :
    ∃ C : TopEdgeLabeling (Fin (2 * n) × (Fin t → W)) (Option (Fin t × ι)),
      ∀ c, ¬ (cycleGraph (2 * n + 1)).IsContained (C.labelGraph c) := by
  classical
  let C : TopEdgeLabeling (Fin (2 * n) × (Fin t → W)) (Option (Fin t × ι)) :=
    EdgeLabeling.mk (fun p q _ => powCol R lev p.2 q.2) (fun p q _ => powCol_comm R lev p.2 q.2)
  refine ⟨C, fun c hc => ?_⟩
  obtain ⟨f⟩ := hc
  have hcolor : ∀ {v w : Fin (2 * n + 1)}, (cycleGraph (2 * n + 1)).Adj v w →
      powCol R lev (f v).2 (f w).2 = c := by
    intro v w hvw
    obtain ⟨h, hh⟩ := (TopEdgeLabeling.labelGraph_adj _ _).mp (f.toHom.map_adj hvw)
    simpa [C, EdgeLabeling.get_mk] using hh
  have hstep : ∀ v : Fin (2 * n + 1), (cycleGraph (2 * n + 1)).Adj v (v + 1) := by
    intro v
    obtain ⟨n', hn'⟩ : ∃ n', 2 * n + 1 = n' + 2 := ⟨2 * n - 1, by omega⟩
    rw [cycleGraph_adj']
    right
    rw [add_sub_cancel_left, Fin.val_one', Nat.mod_eq_of_lt (by omega)]
  rcases c with _ | ⟨j, i⟩
  · have hsame : ∀ v w : Fin (2 * n + 1), (f v).2 = (f w).2 := by
      intro v w
      obtain ⟨p⟩ := cycleGraph_preconnected v w
      induction p with
      | nil => rfl
      | cons hvw _ ih =>
        refine Eq.trans ?_ ih
        have h1 := hcolor hvw
        unfold powCol at h1
        split_ifs at h1 with hd
        funext j
        by_contra hj
        exact hd ⟨j, by simp [diffs, hj]⟩
    have hinj : Function.Injective (fun v => (f v).1) := by
      intro v w heq
      exact f.injective (Prod.ext heq (hsame v w))
    have := Fintype.card_le_of_injective _ hinj
    simp at this
  · have hadjw : ∀ v : Fin (2 * n + 1),
        AdjR (R i) (lev ((f v).2 j) i) (lev ((f (v + 1)).2 j) i) := by
      intro v
      have h1 := hcolor (hstep v)
      unfold powCol at h1
      split_ifs at h1 with hd
      simp only [Option.some.injEq, Prod.mk.injEq] at h1
      obtain ⟨hj, hi⟩ := h1
      have hmem := Finset.min'_mem _ hd
      have hne : (f v).2 ((diffs (f v).2 (f (v + 1)).2).min' hd) ≠
          (f (v + 1)).2 ((diffs (f v).2 (f (v + 1)).2).min' hd) := by
        simpa [diffs] using hmem
      have := baseCol_spec hadj hne
      rw [hi, hj] at this
      exact this
    exact no_odd_closed_walk (m := 2 * n + 1) ⟨n, rfl⟩ (by omega) (by push_cast; exact hR i)
      (fun v => lev ((f v).2 j) i) hadjw

-- ## Transport vers `Fin N` et `Fin k`

theorem bad_transfer {V K : Type*} [Fintype V] [Fintype K] {m : ℕ} (hm : 2 ≤ m)
    (C : TopEdgeLabeling V K) (hC : ∀ c, ¬ (cycleGraph m).IsContained (C.labelGraph c))
    {N k : ℕ} (hN : N ≤ Fintype.card V) (hk : Fintype.card K ≤ k) :
    ∃ C' : TopEdgeLabeling (Fin N) (Fin k),
      ∀ c, ¬ (cycleGraph m).IsContained (C'.labelGraph c) := by
  classical
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
  obtain ⟨e⟩ : Nonempty (Fin N ↪ V) := Function.Embedding.nonempty_of_card_le (by simpa using hN)
  obtain ⟨φ⟩ : Nonempty (K ↪ Fin k) := Function.Embedding.nonempty_of_card_le (by simpa using hk)
  refine ⟨(C.pullback e).compRight φ, fun c hc => ?_⟩
  obtain ⟨f⟩ := hc
  have hget : ∀ {v w : Fin (m' + 2)}, (cycleGraph (m' + 2)).Adj v w →
      ∃ h : e (f v) ≠ e (f w), φ (C.get (e (f v)) (e (f w)) h) = c := by
    intro v w hvw
    obtain ⟨h, hh⟩ := (TopEdgeLabeling.labelGraph_adj _ _).mp (f.toHom.map_adj hvw)
    simp only [EdgeLabeling.compRight_get] at hh
    exact ⟨e.injective.ne h, hh⟩
  have h01 : (cycleGraph (m' + 2)).Adj 0 1 := cycleGraph_adj.mpr (Or.inr (sub_zero 1))
  obtain ⟨h0, hc0⟩ := hget h01
  apply hC (C.get (e (f 0)) (e (f 1)) h0)
  refine ⟨⟨⟨fun v => e (f v), fun {v w} hvw => ?_⟩, ?_⟩⟩
  · obtain ⟨h, hh⟩ := hget hvw
    rw [TopEdgeLabeling.labelGraph_adj]
    exact ⟨h, φ.injective (hh.trans hc0.symm)⟩
  · exact e.injective.comp f.injective

-- ## Existence du nombre de Ramsey (recopié de la preuve fusionnée `lower_bound`)

theorem finiteMulticolorClique (t k : ℕ) : ∃ N : ℕ,
    ∀ {m : ℕ} (c : Finset (Fin m) → Fin (k + 1)) (V : Finset (Fin m)), N ≤ V.card →
      ∃ i : Fin (k + 1), ∃ S ⊆ V, S.card = t ∧ ∀ e ⊆ S, e.card = 2 → c e = i := by
  classical
  induction k with
  | zero =>
    refine ⟨t, fun c V hV ↦ ?_⟩
    obtain ⟨S, hSV, hS⟩ := Finset.exists_subset_card_eq hV
    refine ⟨0, S, hSV, hS, fun e he hcard ↦ Fin.ext ?_⟩
    have := (c e).isLt
    change (c e).val = 0
    omega
  | succ k ih =>
    obtain ⟨N, hN⟩ := ih
    refine ⟨(N + t).choose N, fun c V hV ↦ ?_⟩
    let isLast (e : Finset _) := decide ((c e).val = k + 1)
    rcases Combinatorics.Diagonal.hasRamseyProperty_choose N t isLast V hV with
      ⟨U, hUV, hU, hu⟩ | ⟨S, hSV, hS, hs⟩
    · let lowColor (e : Finset _) : Fin (k + 1) :=
        if h : (c e).val < k + 1 then ⟨(c e).val, h⟩ else 0
      obtain ⟨i, S, hSU, hS, hs⟩ := hN lowColor U hU.ge
      refine ⟨i.castSucc, S, hSU.trans hUV, hS, fun e he hcard ↦ ?_⟩
      have hlast : (c e).val ≠ k + 1 := of_decide_eq_false (hu e (he.trans hSU) hcard)
      have hlt := (c e).isLt
      have hlow : (c e).val < k + 1 := by omega
      apply Fin.ext
      simpa only [lowColor, dif_pos hlow, Fin.val_castSucc] using congrArg Fin.val (hs e he hcard)
    · refine ⟨Fin.last (k + 1), S, hSV, hS, fun e he hcard ↦ Fin.ext ?_⟩
      exact of_decide_eq_true (hs e he hcard)

noncomputable def cliqueEdgeColor {m k : ℕ} (C : TopEdgeLabeling (Fin m) (Fin (k + 1)))
    (s : Finset (Fin m)) : Fin (k + 1) :=
  if hs : s.Nonempty then
    if h : s.min' hs ≠ s.max' hs then C.get (s.min' hs) (s.max' hs) h else 0
  else 0

theorem cliqueEdgeColor_pair {m k : ℕ} (C : TopEdgeLabeling (Fin m) (Fin (k + 1)))
    {x y : Fin m} (h : x ≠ y) : cliqueEdgeColor C {x, y} = C.get x y h := by
  classical
  unfold cliqueEdgeColor
  rw [dif_pos (Finset.insert_nonempty _ _)]
  by_cases hxy : x ≤ y
  · simp [min_eq_left hxy, max_eq_right hxy, h]
  · have hyx : y ≤ x := le_of_not_ge hxy
    simpa [Finset.min'_pair, Finset.max'_pair, min_eq_right hyx, max_eq_left hyx, h.symm] using
      (EdgeLabeling.get_comm (C := C) x y h.symm)

theorem cycleRamseyFinite (t k : ℕ) :
    {N : ℕ | ∀ C : TopEdgeLabeling (Fin N) (Fin (k + 1)),
      ∃ i, (cycleGraph t).IsContained (C.labelGraph i)}.Nonempty := by
  obtain ⟨N, hN⟩ := finiteMulticolorClique t k
  refine ⟨N, fun C ↦ ?_⟩
  obtain ⟨i, S, _, hS, hs⟩ := hN (cliqueEdgeColor C) Finset.univ (by simp)
  let f : Fin t ≃ S := Fintype.equivOfCardEq (by simpa using hS.symm)
  refine ⟨i, (isContained_iff_exists_le_comap).mpr ⟨f.toEmbedding.trans
    (Function.Embedding.subtype _), fun v w hvw ↦ ?_⟩⟩
  rw [comap_adj, TopEdgeLabeling.labelGraph_adj]
  change ∃ h : (f v).val ≠ (f w).val, C.get (f v).val (f w).val h = i
  have hne : (f v).val ≠ (f w).val :=
    fun h ↦ hvw.ne (f.injective (Subtype.ext h))
  refine ⟨hne, ?_⟩
  rw [← cliqueEdgeColor_pair C hne]
  exact hs _ (Finset.insert_subset (f v).property (Finset.singleton_subset_iff.mpr (f w).property))
    (Finset.card_pair hne)

-- ## Minoration du nombre de Ramsey et inégalité finale

theorem lt_ramsey {k N m : ℕ} (hk : 1 ≤ k)
    (h : ∀ N' ≤ N, ∃ C : TopEdgeLabeling (Fin N') (Fin k),
      ∀ c, ¬ (cycleGraph m).IsContained (C.labelGraph c)) :
    N < multicolourGraphRamsey k (cycleGraph m) := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  unfold multicolourGraphRamsey
  by_contra hle
  push Not at hle
  obtain ⟨C, hC⟩ := h _ hle
  obtain ⟨i, hi⟩ := Nat.sInf_mem (cycleRamseyFinite m k) C
  exact hC i hi

theorem eventually_bound (r : ℕ) (hr : 0 < r) (N0 : ℕ) (hN0 : 2 ^ r < N0) :
    ∃ c > (0 : ℝ), ∀ᶠ k : ℕ in atTop, (2 + c) ^ (k - 1) ≤ (N0 : ℝ) ^ ((k - 1) / r) := by
  have hN : (2 : ℝ) ^ r < (N0 : ℝ) := by exact_mod_cast hN0
  have hlim : Tendsto (fun x : ℝ => x ^ r) (𝓝[>] 2) (𝓝 ((2 : ℝ) ^ r)) :=
    ((continuous_id.pow r).tendsto (2 : ℝ)).mono_left nhdsWithin_le_nhds
  have hgt : ∀ᶠ x : ℝ in 𝓝[>] 2, 2 < x := self_mem_nhdsWithin
  obtain ⟨β, hβ, hβN⟩ := (hgt.and (hlim.eventually_lt_const hN)).exists
  refine ⟨β - 2, sub_pos.mpr hβ, ?_⟩
  rw [show 2 + (β - 2) = β by ring]
  have hβ1 : 1 ≤ β := by linarith
  let B := β ^ r
  have hB : 0 < B := pow_pos (by linarith : 0 < β) r
  let α := (N0 : ℝ) / B
  have hα : 1 < α := (one_lt_div hB).mpr hβN
  have hprod : B * α = (N0 : ℝ) := by unfold α; field_simp [hB.ne']
  obtain ⟨T, hT⟩ := pow_unbounded_of_one_lt B hα
  filter_upwards [eventually_ge_atTop (T * r + 1)] with k hk
  let t := (k - 1) / r
  have ht : T ≤ t := (Nat.le_div_iff_mul_le hr).mpr (by omega)
  have he : k - 1 ≤ r * (t + 1) := (Nat.lt_mul_div_succ (k - 1) hr).le
  calc
    β ^ (k - 1) ≤ β ^ (r * (t + 1)) := pow_le_pow_right₀ hβ1 he
    _ = B ^ t * B := by rw [pow_mul, pow_succ]
    _ ≤ B ^ t * α ^ t := mul_le_mul_of_nonneg_left
      (hT.le.trans (pow_le_pow_right₀ hα.le ht)) (pow_nonneg hB.le _)
    _ = (N0 : ℝ) ^ t := by rw [← mul_pow, hprod]

end OMA

theorem OMA.solution : type_of% @Erdos554.erdos_554.variants.day_johnson := by
  intro n hn
  obtain ⟨ι, hιF, W, hWF, R, o, lev, hrrc, hR, hι, hW⟩ := OMA.exists_rrc n
  classical
  have : Nonempty ι := Fintype.card_pos_iff.mp hι
  obtain ⟨c, hc, hev⟩ := OMA.eventually_bound (Fintype.card ι) hι (Fintype.card W) hW
  refine ⟨c, hc, ?_⟩
  filter_upwards [hev, Filter.eventually_ge_atTop 1] with k hk hk1
  obtain ⟨C, hC⟩ := OMA.power_bad R lev hrrc.2.2 hn
    (fun i => by have := hR i; omega) ((k - 1) / Fintype.card ι)
  have hK : Fintype.card (Option (Fin ((k - 1) / Fintype.card ι) × ι)) ≤ k := by
    rw [Fintype.card_option, Fintype.card_prod, Fintype.card_fin]
    have := Nat.div_mul_le_self (k - 1) (Fintype.card ι)
    omega
  have hV : Fintype.card (Fin (2 * n) × (Fin ((k - 1) / Fintype.card ι) → W)) =
      2 * n * Fintype.card W ^ ((k - 1) / Fintype.card ι) := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fun, Fintype.card_fin]
  have hlt : 2 * n * Fintype.card W ^ ((k - 1) / Fintype.card ι) <
      multicolourGraphRamsey k (cycleGraph (2 * n + 1)) :=
    OMA.lt_ramsey hk1 fun N' hN' => OMA.bad_transfer (by omega) C hC (by rw [hV]; exact hN') hK
  calc (2 * n : ℝ) * (2 + c) ^ (k - 1)
      ≤ 2 * n * (Fintype.card W : ℝ) ^ ((k - 1) / Fintype.card ι) := by gcongr
    _ < (multicolourGraphRamsey k (cycleGraph (2 * n + 1)) : ℝ) := by exact_mod_cast hlt
