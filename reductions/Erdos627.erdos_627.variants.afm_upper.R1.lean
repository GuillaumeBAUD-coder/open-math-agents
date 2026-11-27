import FormalConjectures.ErdosProblems.«627»

/-!
Reduction of the AFM upper bound, following Sections 2 and 3 of Araujo, Filipe and
Miyazaki, arXiv:2512.16062. The Ramsey input is stated in its graph form. The greedy coloring estimate and the analytic
cutoff are proved below. The two remaining steps are uniform Ramsey asymptotics
and a one-variable inequality.
-/
namespace OMA.R_Erdos627_erdos_627_variants_afm_upper_R1

open Filter SimpleGraph

/-- The uniform off-diagonal Ramsey estimate in graph form. Write a and b for
the largest clique and independent-set sizes, and x for the smaller share of
a+b. This is the entropy bound from Section 3 with the shifted Ramsey
parameters a+1 and b+1 absorbed in the error term. -/
def H1 : Prop :=
  ∀ δ > (0 : ℝ), ∀ᶠ k : ℕ in atTop, ∀ H : SimpleGraph (Fin k),
    let a : ℝ := H.cliqueNum
    let b : ℝ := H.indepNum
    let x := min a b / (a + b)
    (Real.logb 2 k) ^ 2 ≤
      (((Real.binEntropy x - (0.14 / Real.exp 1) * x) /
        (Real.log 2 * Real.sqrt (x * (1 - x)))) ^ 2 + δ) * (a * b)

/-- The one-variable numerical bound. Mathlib measures binary entropy in
natural logarithms, so the denominator converts the expression to base two. -/
def H2 : Prop :=
  ∀ x : ℝ, 0 ≤ x → x ≤ 1 / 2 →
    ((Real.binEntropy x - (0.14 / Real.exp 1) * x) /
      (Real.log 2 * Real.sqrt (x * (1 - x)))) ^ 2 ≤ 3.71943

lemma product_bound (hR : H1) (hE : H2) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ k : ℕ in atTop, ∀ H : SimpleGraph (Fin k),
      (Real.logb 2 k) ^ 2 ≤ (3.71943 + δ) * ((H.cliqueNum : ℝ) * H.indepNum) := by
  filter_upwards [hR δ hδ] with k hk
  intro H
  let a : ℝ := H.cliqueNum
  let b : ℝ := H.indepNum
  let x := min a b / (a + b)
  have ha : 0 ≤ a := Nat.cast_nonneg _
  have hb : 0 ≤ b := Nat.cast_nonneg _
  have hx : 0 ≤ x := div_nonneg (le_min ha hb) (add_nonneg ha hb)
  have hx' : x ≤ 1 / 2 := by
    by_cases hzero : a + b = 0
    · simp [x, hzero]
    · apply (div_le_iff₀ (lt_of_le_of_ne (add_nonneg ha hb) (Ne.symm hzero))).2
      linarith [min_le_left a b, min_le_right a b]
  exact (hk H).trans (mul_le_mul_of_nonneg_right (add_le_add_left (hE x hx hx') δ) (mul_nonneg ha hb))

lemma peel {k : ℕ} (G : SimpleGraph (Fin k)) :
    ∃ j : ℕ, ∃ H : SimpleGraph (Fin j), j + G.indepNum = k ∧
      H.cliqueNum ≤ G.cliqueNum ∧ G.chromaticNumber.toNat ≤ H.chromaticNumber.toNat + 1 := by
  classical
  obtain ⟨s, hs⟩ := G.exists_isNIndepSet_indepNum
  let t := sᶜ
  let e : t ≃ Fin t.card := t.equivFin
  let emb : Fin t.card ↪ Fin k := e.symm.toEmbedding.trans (.subtype _)
  let H := G.comap emb
  refine ⟨t.card, H, ?_, ?_, ?_⟩
  · simp [t, ← hs.card_eq]
  · obtain ⟨u, hu⟩ := H.exists_isNClique_cliqueNum
    have hv := (hu.map (f := emb)).mono (map_comap_le emb G)
    rw [← hv.card_eq]
    exact hv.isClique.card_le_cliqueNum
  · let c := H.colorable_chromaticNumber_of_fintype.some
    let col (x : Fin k) : Fin (H.chromaticNumber.toNat + 1) :=
      if h : x ∈ t then (c (e ⟨x, h⟩)).succ else 0
    have valid {v w : Fin k} (hvw : G.Adj v w) : col v ≠ col w := by
      by_cases hv : v ∈ t <;> by_cases hw : w ∈ t
      · simp only [col, dif_pos hv, dif_pos hw]
        apply (Fin.succ_injective _).ne
        apply c.valid
        change G.Adj (e.symm (e ⟨v, hv⟩)).val (e.symm (e ⟨w, hw⟩)).val
        simpa using hvw
      · simp [col, hv, hw]
      · simp only [col, dif_neg hv, dif_pos hw]
        exact Ne.symm (Fin.succ_ne_zero _)
      · have hv' : v ∈ s := by simpa [t] using hv
        have hw' : w ∈ s := by simpa [t] using hw
        exact False.elim (hs.isIndepSet hv' hw' (G.ne_of_adj hvw) hvw)
    have hc : G.Colorable (H.chromaticNumber.toNat + 1) := ⟨Coloring.mk col valid⟩
    exact ENat.toNat_le_of_le_natCast hc.chromaticNumber_le

lemma greedy_ratio (n m : ℕ) (q : ℝ) (hm : 2 ≤ m) (hq : 0 < q)
    (hprod : ∀ k : ℕ, m ≤ k → k ≤ n → ∀ H : SimpleGraph (Fin k),
      q ≤ (H.cliqueNum : ℝ) * H.indepNum) (G : SimpleGraph (Fin n)) :
    (G.chromaticNumber.toNat : ℝ) / G.cliqueNum ≤ (n : ℝ) / q + m := by
  have aux (k : ℕ) : k ≤ n → ∀ K : SimpleGraph (Fin k),
      (K.chromaticNumber.toNat : ℝ) ≤ (k : ℝ) * K.cliqueNum / q + m := by
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hkn K
      by_cases hmk : m ≤ k
      · have hK := hprod k hmk hkn K
        have hα : 0 < K.indepNum := by
          by_contra! hz
          have hz' : K.indepNum = 0 := by omega
          simp [hz'] at hK
          linarith
        obtain ⟨j, J, hj, hω, hχ⟩ := peel K
        have hjk : j < k := by omega
        have hJ := ih j hjk (hjk.le.trans hkn) J
        have hcuts : (j : ℝ) + K.indepNum = k := by exact_mod_cast hj
        have hone : (1 : ℝ) ≤ (K.indepNum : ℝ) * K.cliqueNum / q := by
          apply (le_div_iff₀ hq).2
          simpa only [one_mul, mul_one, mul_comm] using hK
        have hbound : (j : ℝ) * J.cliqueNum / q ≤ (j : ℝ) * K.cliqueNum / q :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (by exact_mod_cast hω) (by positivity)) hq.le
        calc
          _ ≤ (J.chromaticNumber.toNat : ℝ) + 1 := by exact_mod_cast hχ
          _ ≤ ((j : ℝ) * K.cliqueNum / q + m) + ((K.indepNum : ℝ) * K.cliqueNum / q) :=
            add_le_add (hJ.trans (add_le_add_left hbound _)) hone
          _ = (((j : ℝ) + K.indepNum) * K.cliqueNum / q) + m := by ring
          _ = _ := by rw [hcuts]
      · have hc : K.chromaticNumber.toNat ≤ k :=
          ENat.toNat_le_of_le_natCast (by simpa using K.chromaticNumber_le_card)
        have hkm : k ≤ m := by omega
        calc
          _ ≤ (m : ℝ) := by exact_mod_cast hc.trans hkm
          _ ≤ _ := le_add_of_nonneg_left (by positivity)
  by_cases hz : G.cliqueNum = 0
  · rw [hz]
    simp only [Nat.cast_zero, div_zero]
    positivity
  · have hnat : 1 ≤ G.cliqueNum := by omega
    have hone : (1 : ℝ) ≤ G.cliqueNum := by exact_mod_cast hnat
    apply (div_le_iff₀ (zero_lt_one.trans_le hone)).2
    calc
      _ ≤ (n : ℝ) * G.cliqueNum / q + m := aux n le_rfl G
      _ ≤ (n : ℝ) * G.cliqueNum / q + (m : ℝ) * G.cliqueNum :=
        add_le_add_right (by simpa using mul_le_mul_of_nonneg_left hone (show (0 : ℝ) ≤ m by positivity)) _
      _ = _ := by ring

/-- A power cutoff m = ⌈n^a⌉ with a just below one makes the uncolored
remainder negligible and keeps log m ≥ a log n. -/
lemma scalar_cutoff (C : ℝ) (hC : 0 < C) (δ : ℝ) (hδ : 0 < δ) (N : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∃ m : ℕ, 2 ≤ m ∧ N ≤ m ∧
      C * ((n : ℝ) / (Real.logb 2 m) ^ 2) + m ≤
        (C + δ) * ((n : ℝ) / (Real.logb 2 n) ^ 2) := by
  let D := C + δ / 2
  have hD : 0 < D := by dsimp [D]; positivity
  let a := Real.sqrt (C / D)
  have ha : 0 < a := Real.sqrt_pos.2 (div_pos hC hD)
  have ha2 : a ^ 2 = C / D := Real.sq_sqrt (div_nonneg hC.le hD.le)
  have hCa : a ^ 2 * D = C := by rw [ha2, div_mul_cancel₀ _ hD.ne']
  have ha1 : a < 1 := by
    have h : C / D < 1 := (div_lt_one hD).2 (by dsimp [D]; linarith)
    by_contra! hge
    have hs := (sq_le_sq₀ (zero_le_one : (0 : ℝ) ≤ 1) ha.le).2 hge
    nlinarith
  have ht : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hpow := (tendsto_rpow_atTop ha).comp ht
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsmall := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (sub_pos.2 ha1)).comp_tendsto ht
  have hc : 0 < δ / 4 * (Real.log 2) ^ 2 := by positivity
  filter_upwards [hsmall.bound hc, hpow.eventually_ge_atTop ((max 2 N : ℕ) : ℝ),
    eventually_ge_atTop (2 : ℕ)] with n hcost hlarge hn
  let x : ℝ := n
  have hx : 1 < x := by
    change (1 : ℝ) < (n : ℝ)
    exact_mod_cast (show 1 < n by omega)
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hxa : 0 < x ^ a := Real.rpow_pos_of_pos hx0 _
  let m := ⌈x ^ a⌉₊
  have hm : x ^ a ≤ (m : ℝ) := Nat.le_ceil _
  change ((max 2 N : ℕ) : ℝ) ≤ x ^ a at hlarge
  have hbig : max 2 N ≤ m := by exact_mod_cast hlarge.trans hm
  refine ⟨m, (le_max_left _ _).trans hbig, (le_max_right _ _).trans hbig, ?_⟩
  have hlogx : 0 < Real.logb 2 x := Real.logb_pos (by norm_num) hx
  have halog : a * Real.logb 2 x ≤ Real.logb 2 m := by
    rw [← Real.logb_rpow_eq_mul_logb_of_pos hx0]
    exact Real.logb_le_logb_of_le (by norm_num) hxa hm
  have hlogm := (mul_pos ha hlogx).trans_le halog
  have hsq := (sq_le_sq₀ (mul_pos ha hlogx).le hlogm.le).2 halog
  have hmain : C * (x / (Real.logb 2 m) ^ 2) ≤ D * (x / (Real.logb 2 x) ^ 2) := by
    rw [← mul_div_assoc, ← mul_div_assoc]
    apply (div_le_div_iff₀ (sq_pos_of_pos hlogm) (sq_pos_of_pos hlogx)).2
    calc
      _ = (D * x) * (a * Real.logb 2 x) ^ 2 := by rw [← hCa]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hsq (mul_pos hD hx0).le
  change ‖Real.log x ^ (2 : ℝ)‖ ≤ _ * ‖x ^ (1 - a)‖ at hcost
  rw [Real.rpow_two, Real.norm_of_nonneg (sq_nonneg _),
    Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _)] at hcost
  have hbase : (Real.logb 2 x) ^ 2 ≤ (δ / 4) * x ^ (1 - a) := by
    rw [Real.logb, div_pow]
    apply (div_le_iff₀ (sq_pos_of_pos hlog2)).2
    calc
      _ ≤ _ := hcost
      _ = _ := by ring
  have hmul : x ^ a * x ^ (1 - a) = x := by
    rw [← Real.rpow_add hx0, show a + (1 - a) = 1 by ring, Real.rpow_one]
  have hxa1 : 1 ≤ x ^ a := Real.one_le_rpow hx.le ha.le
  have hmr : (m : ℝ) ≤ 2 * x ^ a := (Nat.ceil_lt_add_one hxa.le).le.trans (by linarith)
  have hrem : (m : ℝ) ≤ (δ / 2) * (x / (Real.logb 2 x) ^ 2) := by
    rw [← mul_div_assoc]
    apply (le_div_iff₀ (sq_pos_of_pos hlogx)).2
    calc
      _ ≤ (2 * x ^ a) * ((δ / 4) * x ^ (1 - a)) :=
        mul_le_mul hmr hbase (sq_nonneg _) (by positivity)
      _ = δ / 2 * (x ^ a * x ^ (1 - a)) := by ring
      _ = _ := by rw [hmul]
  calc
    _ ≤ D * (x / (Real.logb 2 x) ^ 2) + (δ / 2) * (x / (Real.logb 2 x) ^ 2) :=
      add_le_add hmain hrem
    _ = _ := by change _ = (C + δ) * (x / (Real.logb 2 x) ^ 2); dsimp [D]; ring

theorem main : H1 → H2 → type_of% @Erdos627.erdos_627.variants.afm_upper := by
  intro hRamsey hEntropy ε hε
  have hδ : 0 < ε / 2 := half_pos hε
  let C : ℝ := 3.71943 + ε / 2
  have hC : 0 < C := by dsimp [C]; positivity
  obtain ⟨N, hN⟩ := eventually_atTop.1 (product_bound hRamsey hEntropy _ hδ)
  filter_upwards [scalar_cutoff C hC _ hδ N] with n hn
  obtain ⟨m, hm, hNm, hbudget⟩ := hn
  have hm' : (1 : ℝ) < m := by exact_mod_cast (show 1 < m by omega)
  have hlog : 0 < Real.logb 2 (m : ℝ) := Real.logb_pos (by norm_num) hm'
  let q : ℝ := (Real.logb 2 m) ^ 2 / C
  have hq : 0 < q := div_pos (sq_pos_of_pos hlog) hC
  have hprod (k : ℕ) (hmk : m ≤ k) (_ : k ≤ n) (H : SimpleGraph (Fin k)) :
      q ≤ (H.cliqueNum : ℝ) * H.indepNum := by
    have hlogs := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (zero_lt_one.trans hm') (show (m : ℝ) ≤ k by exact_mod_cast hmk)
    have hsquares := (sq_le_sq₀ hlog.le (hlog.le.trans hlogs)).2 hlogs
    apply (div_le_iff₀ hC).2
    calc
      _ ≤ (Real.logb 2 k) ^ 2 := hsquares
      _ ≤ C * ((H.cliqueNum : ℝ) * H.indepNum) := hN k (hNm.trans hmk) H
      _ = _ := mul_comm _ _
  have hcoeff : C + ε / 2 = 3.71943 + ε := by dsimp [C]; ring
  rw [hcoeff] at hbudget
  unfold Erdos627.maxChromaticCliqueRatio
  apply ciSup_le
  intro G
  calc
    _ ≤ (n : ℝ) / q + m := greedy_ratio n m q hm hq hprod G
    _ = C * ((n : ℝ) / (Real.logb 2 m) ^ 2) + m := by
      dsimp [q]
      rw [div_div_eq_mul_div]
      ring
    _ ≤ _ := hbudget

end OMA.R_Erdos627_erdos_627_variants_afm_upper_R1
