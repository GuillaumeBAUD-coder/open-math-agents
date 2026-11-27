import FormalConjectures.ErdosProblems.«82»

/-!
Reduction Erdos82.erdos_82.variants.F_upper_bound.R1 of Erdős Problem 82 — F upper bound
Credit: @green-notes
Splits Alon-Krivelevich-Sudakov Theorem 1.4 into:
  H1: vertex-exposure regularity bound on a fixed subset in G(n, p_i p_j)
  H2: counting bound for small-span subsets (Case 1)
  H3: edge-imbalance concentration for large-span subsets (Case 2)
-/

namespace OMA.R_Erdos82_erdos_82_variants_F_upper_bound_R1

open SimpleGraph Filter Asymptotics

def H1 : Prop :=
  open scoped Classical in
  ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ n : ℕ, 1 ≤ n → ∀ U : Finset (Fin n), 2 ≤ U.card →
    (∑ G : SimpleGraph (Fin n),
      (if ∃ d : ℕ, ∀ u ∈ U, (U.filter (fun v => G.Adj u v)).card = d then (1 : ℝ) else 0) *
      (∏ e ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2),
        if G.Adj e.1 e.2
        then (1 / 4 + (e.1 : ℝ) / (2 * n)) * (1 / 4 + (e.2 : ℝ) / (2 * n))
        else 1 - (1 / 4 + (e.1 : ℝ) / (2 * n)) * (1 / 4 + (e.2 : ℝ) / (2 * n))))
    ≤ (n : ℝ) * (C₁ / (U.card : ℝ)) ^ ((U.card : ℝ) / 2)

def H2 : Prop :=
  open scoped Classical in
  ∀ C₁ : ℝ, 0 < C₁ → ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
    ∀ k : ℕ, Real.sqrt (n : ℝ) ≤ (k : ℝ) → k ≤ n →
      (((Finset.univ : Finset (Finset (Fin n))).filter (fun U =>
        U.card = k ∧ ∃ a b : Fin n, a ≤ b ∧ (b : ℝ) - (a : ℝ) ≤ c₂ * (k : ℝ) ^ (3 / 2 : ℝ) ∧
          (U.filter (· < a)).card ≤ k / (Nat.log 2 k + 1) ∧
          (U.filter (b < ·)).card ≤ k / (Nat.log 2 k + 1))).card : ℝ) *
      ((n : ℝ) * (C₁ / (k : ℝ)) ^ ((k : ℝ) / 2)) < 1 / (2 * (n : ℝ) ^ 2)

def H3 : Prop :=
  open scoped Classical in
  ∀ c₂ : ℝ, 0 < c₂ → ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
    ∀ k : ℕ, C * Real.sqrt (n : ℝ) * (Real.log (n : ℝ)) ^ (3 / 4 : ℝ) ≤ (k : ℝ) → k ≤ n →
      (∑ G : SimpleGraph (Fin n),
        (if ∃ U : Finset (Fin n), U.card = k ∧
            (∃ d : ℕ, ∀ u ∈ U, (U.filter (fun v => G.Adj u v)).card = d) ∧
            (∃ a b : Fin n, a < b ∧ c₂ * (k : ℝ) ^ (3 / 2 : ℝ) ≤ (b : ℝ) - (a : ℝ) ∧
              k / (Nat.log 2 k + 1) ≤ (U.filter (· ≤ a)).card ∧
              k / (Nat.log 2 k + 1) ≤ (U.filter (b ≤ ·)).card)
          then (1 : ℝ) else 0) *
        (∏ e ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2),
          if G.Adj e.1 e.2
          then (1 / 4 + (e.1 : ℝ) / (2 * n)) * (1 / 4 + (e.2 : ℝ) / (2 * n))
          else 1 - (1 / 4 + (e.1 : ℝ) / (2 * n)) * (1 / 4 + (e.2 : ℝ) / (2 * n))))
      < 1 / (2 * (n : ℝ) ^ 2)

section Helpers

open scoped Classical

private lemma prob_factor_bounds {n : ℕ} (hn : 1 ≤ n) (u v : Fin n) :
    0 ≤ (1 / 4 + (u : ℝ) / (2 * n)) * (1 / 4 + (v : ℝ) / (2 * n)) ∧
    (1 / 4 + (u : ℝ) / (2 * n)) * (1 / 4 + (v : ℝ) / (2 * n)) ≤ 1 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hbound (w : Fin n) : 0 ≤ 1 / 4 + (w : ℝ) / (2 * n) ∧ 1 / 4 + (w : ℝ) / (2 * n) ≤ 1 := by
    have hw0 : (0 : ℝ) ≤ w := Nat.cast_nonneg w
    have hw1 : (w : ℝ) ≤ n := Nat.cast_le.mpr w.isLt.le
    constructor
    · positivity
    · have h1 : (w : ℝ) / (2 * (n : ℝ)) ≤ 1 / 2 := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        linarith
      linarith
  obtain ⟨hu0, hu1⟩ := hbound u
  obtain ⟨hv0, hv1⟩ := hbound v
  exact ⟨mul_nonneg hu0 hv0, mul_le_one₀ hu1 hv0 hv1⟩

private lemma weight_nonneg {n : ℕ} (hn : 1 ≤ n) (G : SimpleGraph (Fin n)) :
    0 ≤ ∏ e ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2),
      if G.Adj e.1 e.2
      then (1 / 4 + (e.1 : ℝ) / (2 * n)) * (1 / 4 + (e.2 : ℝ) / (2 * n))
      else 1 - (1 / 4 + (e.1 : ℝ) / (2 * n)) * (1 / 4 + (e.2 : ℝ) / (2 * n)) := by
  refine Finset.prod_nonneg fun e _ => ?_
  obtain ⟨h0, h1⟩ := prob_factor_bounds hn e.1 e.2
  split_ifs
  · exact h0
  · linarith

private lemma sum_weight_eq_one (n : ℕ) :
    (∑ G : SimpleGraph (Fin n),
      ∏ e ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2),
        if G.Adj e.1 e.2
        then (1 / 4 + (e.1 : ℝ) / (2 * n)) * (1 / 4 + (e.2 : ℝ) / (2 * n))
        else 1 - (1 / 4 + (e.1 : ℝ) / (2 * n)) * (1 / 4 + (e.2 : ℝ) / (2 * n))) = 1 := by
  let E := Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2)
  let eGraph : SimpleGraph (Fin n) ≃ ({p : Fin n × Fin n // p ∈ E} → Bool) :=
    { toFun := fun G e => decide (G.Adj e.1.1 e.1.2)
      invFun := fun f =>
        { Adj := fun u v =>
            if h : u < v then f ⟨(u, v), Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩ = true
            else if h' : v < u then f ⟨(v, u), Finset.mem_filter.mpr ⟨Finset.mem_univ _, h'⟩⟩ = true
            else False
          symm := ⟨by
            intro u v h
            rcases lt_trichotomy u v with huv | rfl | hvu
            · have hn : ¬ v < u := lt_asymm huv
              simpa [huv, hn] using h
            · simp at h
            · have hn : ¬ u < v := lt_asymm hvu
              simpa [hvu, hn] using h⟩
          loopless := ⟨by
            intro u h
            simp at h⟩ }
      left_inv := fun G => by
        ext u v
        rcases lt_trichotomy u v with huv | rfl | hvu
        · simp [huv]
        · simp
        · have hn : ¬ u < v := lt_asymm hvu
          simp [hn, hvu, G.adj_comm]
      right_inv := fun f => by
        ext ⟨⟨u, v⟩, he⟩
        have huv : u < v := (Finset.mem_filter.mp he).2
        simp [huv] }
  let q : {p : Fin n × Fin n // p ∈ E} → ℝ := fun e =>
    (1 / 4 + (e.1.1 : ℝ) / (2 * n)) * (1 / 4 + (e.1.2 : ℝ) / (2 * n))
  have h1 :
      (∑ G : SimpleGraph (Fin n),
        ∏ e ∈ E,
          if G.Adj e.1 e.2
          then (1 / 4 + (e.1 : ℝ) / (2 * n)) * (1 / 4 + (e.2 : ℝ) / (2 * n))
          else 1 - (1 / 4 + (e.1 : ℝ) / (2 * n)) * (1 / 4 + (e.2 : ℝ) / (2 * n))) =
      ∑ f : ({p : Fin n × Fin n // p ∈ E} → Bool),
        ∏ e : {p : Fin n × Fin n // p ∈ E}, if f e = true then q e else 1 - q e := by
    refine Fintype.sum_equiv eGraph _ _ fun G => ?_
    rw [← Finset.prod_coe_sort E]
    refine Finset.prod_congr rfl fun ⟨e, he⟩ _ => ?_
    simp [eGraph, q]
  have hps := Fintype.prod_sum (fun (e : {p : Fin n × Fin n // p ∈ E}) (b : Bool) =>
    if b = true then q e else 1 - q e)
  rw [h1, ← hps]
  refine Finset.prod_eq_one fun e _ => ?_
  simp

private lemma regular_of_isRegularInduced {n : ℕ} {G : SimpleGraph (Fin n)} {S : Subgraph G}
    (hS : Erdos82.IsRegularInduced S) :
    ∃ d : ℕ, ∀ u ∈ S.verts.toFinset, (S.verts.toFinset.filter (fun v => G.Adj u v)).card = d := by
  obtain ⟨hind, d, hd⟩ := hS
  refine ⟨d, fun u hu => ?_⟩
  have hu' : u ∈ S.verts := Set.mem_toFinset.mp hu
  have h1 : (S.verts.toFinset.filter (fun v => G.Adj u v)).card =
      Fintype.card (S.coe.neighborSet ⟨u, hu'⟩) := by
    rw [← Fintype.card_coe]
    refine Fintype.card_congr ?_
    exact
      { toFun := fun ⟨v, hv⟩ => ⟨⟨v, Set.mem_toFinset.mp (Finset.mem_filter.mp hv).1⟩,
          hind.adj.mpr (Finset.mem_filter.mp hv).2⟩
        invFun := fun ⟨⟨v, hv⟩, hadj⟩ => ⟨v, Finset.mem_filter.mpr
          ⟨Set.mem_toFinset.mpr hv, S.coe_adj_sub _ _ hadj⟩⟩
        left_inv := fun ⟨_, _⟩ => rfl
        right_inv := fun ⟨⟨_, _⟩, _⟩ => rfl }
  rw [h1, Fintype.card_eq_nat_card]
  have h2 := hd ⟨u, hu'⟩
  dsimp only [SimpleGraph.degree, SimpleGraph.neighborFinset] at h2
  rw [@Set.toFinset_card _ _ ((fun v => Subgraph.coeFiniteAt v) ⟨u, hu'⟩),
    @Fintype.card_eq_nat_card _ ((fun v => Subgraph.coeFiniteAt v) ⟨u, hu'⟩)] at h2
  exact h2

private lemma partition_subset {n k : ℕ} (hk : 16 ≤ k) (U : Finset (Fin n)) (hU : U.card = k)
    (c₂ : ℝ) :
    (∃ a b : Fin n, a ≤ b ∧ (b : ℝ) - (a : ℝ) ≤ c₂ * (k : ℝ) ^ (3 / 2 : ℝ) ∧
      (U.filter (· < a)).card ≤ k / (Nat.log 2 k + 1) ∧
      (U.filter (b < ·)).card ≤ k / (Nat.log 2 k + 1)) ∨
    (∃ a b : Fin n, a < b ∧ c₂ * (k : ℝ) ^ (3 / 2 : ℝ) ≤ (b : ℝ) - (a : ℝ) ∧
      k / (Nat.log 2 k + 1) ≤ (U.filter (· ≤ a)).card ∧
      k / (Nat.log 2 k + 1) ≤ (U.filter (b ≤ ·)).card) := by
  set m := k / (Nat.log 2 k + 1)
  have hlog : 4 ≤ Nat.log 2 k := by
    have : Nat.log 2 16 ≤ Nat.log 2 k := Nat.log_mono_right hk
    have h16 : Nat.log 2 16 = 4 := by decide
    omega
  have hm5 : 5 * m ≤ k := by
    have hmul : (Nat.log 2 k + 1) * m ≤ k := Nat.mul_div_le k (Nat.log 2 k + 1)
    have hle : 5 * m ≤ (Nat.log 2 k + 1) * m := Nat.mul_le_mul_right m (by omega)
    omega
  have hm_lt : m < k - 1 - m := by omega
  have hbm_lt : k - 1 - m < k := by omega
  let e := U.orderEmbOfFin hU
  let a := e ⟨m, by omega⟩
  let b := e ⟨k - 1 - m, hbm_lt⟩
  have hab : a < b := by
    change e ⟨m, by omega⟩ < e ⟨k - 1 - m, hbm_lt⟩
    rw [e.lt_iff_lt]
    exact Fin.mk_lt_mk.mpr hm_lt
  have hlt_card : (U.filter (· < a)).card = m := by
    have himg : U.filter (· < a) = Finset.image (fun i : Fin m => e ⟨i.1, by omega⟩) Finset.univ := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hxU, hxa⟩
        have hxmem : x ∈ Set.range e := by rw [Finset.range_orderEmbOfFin]; exact hxU
        obtain ⟨j, rfl⟩ := hxmem
        have hj : j < ⟨m, by omega⟩ := (e.lt_iff_lt).mp hxa
        exact ⟨⟨j.1, hj⟩, rfl⟩
      · rintro ⟨i, rfl⟩
        refine ⟨?_, ?_⟩
        · have : e ⟨i.1, by omega⟩ ∈ Set.range e := Set.mem_range_self _
          rwa [Finset.range_orderEmbOfFin] at this
        · exact (e.lt_iff_lt).mpr (Fin.mk_lt_mk.mpr i.isLt)
    rw [himg, Finset.card_image_of_injective _ (fun i j hij => by
      have := e.injective hij
      exact Fin.ext (by simpa using congrArg Fin.val this)), Finset.card_fin]
  have hgt_card : (U.filter (b < ·)).card = m := by
    have himg : U.filter (b < ·) =
        Finset.image (fun i : Fin m => e ⟨k - 1 - i.1, by omega⟩) Finset.univ := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hxU, hbx⟩
        have hxmem : x ∈ Set.range e := by rw [Finset.range_orderEmbOfFin]; exact hxU
        obtain ⟨j, rfl⟩ := hxmem
        have hj : k - 1 - m < j.1 := (e.lt_iff_lt).mp hbx
        refine ⟨⟨k - 1 - j.1, by omega⟩, ?_⟩
        have hidx : (⟨k - 1 - (k - 1 - j.1), by omega⟩ : Fin k) = j := by
          apply Fin.ext
          dsimp
          omega
        rw [hidx]
      · rintro ⟨i, rfl⟩
        refine ⟨?_, ?_⟩
        · have : e ⟨k - 1 - i.1, by omega⟩ ∈ Set.range e := Set.mem_range_self _
          rwa [Finset.range_orderEmbOfFin] at this
        · exact (e.lt_iff_lt).mpr (Fin.mk_lt_mk.mpr (by omega))
    rw [himg, Finset.card_image_of_injective _ (fun i j hij => by
      have := congrArg Fin.val (e.injective hij)
      dsimp at this
      exact Fin.ext (by omega)), Finset.card_fin]
  by_cases hspan : (b : ℝ) - (a : ℝ) ≤ c₂ * (k : ℝ) ^ (3 / 2 : ℝ)
  · left
    exact ⟨a, b, hab.le, hspan, hlt_card.le, hgt_card.le⟩
  · right
    have hle1 : m ≤ (U.filter (· ≤ a)).card := by
      rw [← hlt_card]
      refine Finset.card_le_card fun x hx => ?_
      simp only [Finset.mem_filter] at hx ⊢
      exact ⟨hx.1, le_of_lt hx.2⟩
    have hle2 : m ≤ (U.filter (b ≤ ·)).card := by
      rw [← hgt_card]
      refine Finset.card_le_card fun x hx => ?_
      simp only [Finset.mem_filter] at hx ⊢
      exact ⟨hx.1, le_of_lt hx.2⟩
    exact ⟨a, b, hab, le_of_not_ge hspan, hle1, hle2⟩

end Helpers

theorem main : H1 → H2 → H3 → type_of% @Erdos82.erdos_82.variants.F_upper_bound := by
  classical
  intro h1 h2 h3
  obtain ⟨C₁, hC₁, h_single⟩ := h1
  obtain ⟨c₂, hc₂, N₁, h_case1⟩ := h2 C₁ hC₁
  obtain ⟨C, hC, N₂, h_case2⟩ := h3 c₂ hc₂
  have htend : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ) * (Real.log (n : ℝ)) ^ (3 / 4 : ℝ))
      atTop atTop := by
    refine Tendsto.atTop_mul_atTop₀ (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop) ?_
    exact (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 4)).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hlog_tend : Tendsto (fun n : ℕ => (Real.log (n : ℝ)) ^ (3 / 4 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 4)).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  obtain ⟨N₃, hN₃⟩ := eventually_atTop.mp (htend.eventually_ge_atTop (16 / C))
  obtain ⟨N₄, hN₄⟩ := eventually_atTop.mp (hlog_tend.eventually_ge_atTop (1 / C))
  obtain ⟨N₅, hN₅⟩ := eventually_atTop.mp (htend.eventually_ge_atTop 1)
  let N := max (max N₁ N₂) (max (max N₃ N₄) (max N₅ 2))
  have hF_bound : ∀ n : ℕ, N ≤ n →
      (Erdos82.F n : ℝ) ≤ (C + 1) * (Real.sqrt (n : ℝ) * (Real.log (n : ℝ)) ^ (3 / 4 : ℝ)) := by
    intro n hn
    have hn1 : 1 ≤ n := by omega
    have hnN₁ : N₁ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
    have hnN₂ : N₂ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
    have hnN₃ : N₃ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_trans (le_max_right _ _) hn)
    have hnN₄ : N₄ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_trans (le_max_right _ _) hn)
    have hnN₅ : N₅ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_trans (le_max_right _ _) hn)
    let bound : ℝ := C * Real.sqrt (n : ℝ) * (Real.log (n : ℝ)) ^ (3 / 4 : ℝ)
    let K : ℕ := Nat.ceil bound
    have hbound16 : 16 ≤ bound := by
      have h3 := hN₃ n hnN₃
      dsimp only [bound]
      rw [mul_assoc]
      exact (div_le_iff₀' hC).mp h3
    have hlog1 : 1 ≤ C * (Real.log (n : ℝ)) ^ (3 / 4 : ℝ) := (div_le_iff₀' hC).mp (hN₄ n hnN₄)
    have hbound_sqrt : Real.sqrt (n : ℝ) ≤ bound := by
      dsimp only [bound]
      calc Real.sqrt (n : ℝ)
          = 1 * Real.sqrt (n : ℝ) := (one_mul _).symm
        _ ≤ (C * (Real.log (n : ℝ)) ^ (3 / 4 : ℝ)) * Real.sqrt (n : ℝ) :=
            mul_le_mul_of_nonneg_right hlog1 (Real.sqrt_nonneg _)
        _ = C * Real.sqrt (n : ℝ) * (Real.log (n : ℝ)) ^ (3 / 4 : ℝ) := by ring
    have hK16 : 16 ≤ K := by
      exact_mod_cast (hbound16.trans (Nat.le_ceil bound))
    have hK_real : bound ≤ (K : ℝ) := Nat.le_ceil bound
    have h_exists_G : ∃ G : SimpleGraph (Fin n),
        ∀ S : Subgraph G, Erdos82.IsRegularInduced S → S.verts.ncard < K := by
      by_cases hKn : K ≤ n
      · let w : SimpleGraph (Fin n) → ℝ := fun G =>
          ∏ e ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2),
            if G.Adj e.1 e.2
            then (1 / 4 + (e.1 : ℝ) / (2 * n)) * (1 / 4 + (e.2 : ℝ) / (2 * n))
            else 1 - (1 / 4 + (e.1 : ℝ) / (2 * n)) * (1 / 4 + (e.2 : ℝ) / (2 * n))
        let bad : SimpleGraph (Fin n) → Prop := fun G =>
          ∃ S : Subgraph G, Erdos82.IsRegularInduced S ∧ K ≤ S.verts.ncard
        have hbad_sum : (∑ G : SimpleGraph (Fin n), (if bad G then (1 : ℝ) else 0) * w G) < 1 := by
          have hstep : ∀ k ∈ Finset.Icc K n,
              (∑ G : SimpleGraph (Fin n),
                (if ∃ U : Finset (Fin n), U.card = k ∧
                    (∃ d : ℕ, ∀ u ∈ U, (U.filter (fun v => G.Adj u v)).card = d)
                  then (1 : ℝ) else 0) * w G) < 1 / (n : ℝ) ^ 2 := by
            intro k hk
            rw [Finset.mem_Icc] at hk
            have hk16 : 16 ≤ k := le_trans hK16 hk.1
            have hk2 : 2 ≤ k := by omega
            have hk_bound : bound ≤ (k : ℝ) := hK_real.trans (Nat.cast_le.mpr hk.1)
            have hk_sqrt : Real.sqrt (n : ℝ) ≤ (k : ℝ) := hbound_sqrt.trans hk_bound
            let Small := (Finset.univ : Finset (Finset (Fin n))).filter (fun U =>
              U.card = k ∧ ∃ a b : Fin n, a ≤ b ∧ (b : ℝ) - (a : ℝ) ≤ c₂ * (k : ℝ) ^ (3 / 2 : ℝ) ∧
                (U.filter (· < a)).card ≤ k / (Nat.log 2 k + 1) ∧
                (U.filter (b < ·)).card ≤ k / (Nat.log 2 k + 1))
            have hpt : ∀ G : SimpleGraph (Fin n),
                (if ∃ U : Finset (Fin n), U.card = k ∧
                    (∃ d : ℕ, ∀ u ∈ U, (U.filter (fun v => G.Adj u v)).card = d)
                  then (1 : ℝ) else 0) * w G ≤
                (∑ U ∈ Small,
                  (if ∃ d : ℕ, ∀ u ∈ U, (U.filter (fun v => G.Adj u v)).card = d then (1 : ℝ) else 0) * w G) +
                (if ∃ U : Finset (Fin n), U.card = k ∧
                    (∃ d : ℕ, ∀ u ∈ U, (U.filter (fun v => G.Adj u v)).card = d) ∧
                    (∃ a b : Fin n, a < b ∧ c₂ * (k : ℝ) ^ (3 / 2 : ℝ) ≤ (b : ℝ) - (a : ℝ) ∧
                      k / (Nat.log 2 k + 1) ≤ (U.filter (· ≤ a)).card ∧
                      k / (Nat.log 2 k + 1) ≤ (U.filter (b ≤ ·)).card)
                  then (1 : ℝ) else 0) * w G := by
              intro G
              have hwG := weight_nonneg hn1 G
              by_cases hG : ∃ U : Finset (Fin n), U.card = k ∧
                  (∃ d : ℕ, ∀ u ∈ U, (U.filter (fun v => G.Adj u v)).card = d)
              · simp only [hG, ↓reduceIte, one_mul]
                obtain ⟨U, hUk, hUreg⟩ := hG
                rcases partition_subset hk16 U hUk c₂ with hsm | hlg
                · have hUSm : U ∈ Small := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hUk, hsm⟩
                  have hle1 : w G ≤ ∑ U' ∈ Small,
                      (if ∃ d : ℕ, ∀ u ∈ U', (U'.filter (fun v => G.Adj u v)).card = d
                        then (1 : ℝ) else 0) * w G := by
                    refine Finset.single_le_sum (f := fun U' =>
                        (if ∃ d : ℕ, ∀ u ∈ U', (U'.filter (fun v => G.Adj u v)).card = d
                          then (1 : ℝ) else 0) * w G)
                      (fun U' _ => mul_nonneg (by split_ifs <;> norm_num) hwG) hUSm |>.trans_eq' ?_
                    simp [hUreg]
                  have hle2 : 0 ≤ (if ∃ U : Finset (Fin n), U.card = k ∧
                      (∃ d : ℕ, ∀ u ∈ U, (U.filter (fun v => G.Adj u v)).card = d) ∧
                      (∃ a b : Fin n, a < b ∧ c₂ * (k : ℝ) ^ (3 / 2 : ℝ) ≤ (b : ℝ) - (a : ℝ) ∧
                        k / (Nat.log 2 k + 1) ≤ (U.filter (· ≤ a)).card ∧
                        k / (Nat.log 2 k + 1) ≤ (U.filter (b ≤ ·)).card)
                      then (1 : ℝ) else 0) * w G := mul_nonneg (by split_ifs <;> norm_num) hwG
                  linarith
                · have hGlg : ∃ U : Finset (Fin n), U.card = k ∧
                      (∃ d : ℕ, ∀ u ∈ U, (U.filter (fun v => G.Adj u v)).card = d) ∧
                      (∃ a b : Fin n, a < b ∧ c₂ * (k : ℝ) ^ (3 / 2 : ℝ) ≤ (b : ℝ) - (a : ℝ) ∧
                        k / (Nat.log 2 k + 1) ≤ (U.filter (· ≤ a)).card ∧
                        k / (Nat.log 2 k + 1) ≤ (U.filter (b ≤ ·)).card) := ⟨U, hUk, hUreg, hlg⟩
                  have hsum0 : 0 ≤ ∑ U' ∈ Small,
                      (if ∃ d : ℕ, ∀ u ∈ U', (U'.filter (fun v => G.Adj u v)).card = d
                        then (1 : ℝ) else 0) * w G :=
                    Finset.sum_nonneg fun U' _ => mul_nonneg (by split_ifs <;> norm_num) hwG
                  simp only [hGlg, ↓reduceIte, one_mul]
                  linarith
              · simp only [hG, ↓reduceIte, zero_mul]
                have hsum0 : 0 ≤ ∑ U' ∈ Small,
                    (if ∃ d : ℕ, ∀ u ∈ U', (U'.filter (fun v => G.Adj u v)).card = d
                      then (1 : ℝ) else 0) * w G :=
                  Finset.sum_nonneg fun U' _ => mul_nonneg (by split_ifs <;> norm_num) hwG
                have hle2 : 0 ≤ (if ∃ U : Finset (Fin n), U.card = k ∧
                    (∃ d : ℕ, ∀ u ∈ U, (U.filter (fun v => G.Adj u v)).card = d) ∧
                    (∃ a b : Fin n, a < b ∧ c₂ * (k : ℝ) ^ (3 / 2 : ℝ) ≤ (b : ℝ) - (a : ℝ) ∧
                      k / (Nat.log 2 k + 1) ≤ (U.filter (· ≤ a)).card ∧
                      k / (Nat.log 2 k + 1) ≤ (U.filter (b ≤ ·)).card)
                    then (1 : ℝ) else 0) * w G := mul_nonneg (by split_ifs <;> norm_num) hwG
                linarith
            have hsum_le :
                (∑ G : SimpleGraph (Fin n),
                  (if ∃ U : Finset (Fin n), U.card = k ∧
                      (∃ d : ℕ, ∀ u ∈ U, (U.filter (fun v => G.Adj u v)).card = d)
                    then (1 : ℝ) else 0) * w G) ≤
                (∑ U ∈ Small, ∑ G : SimpleGraph (Fin n),
                  (if ∃ d : ℕ, ∀ u ∈ U, (U.filter (fun v => G.Adj u v)).card = d then (1 : ℝ) else 0) * w G) +
                (∑ G : SimpleGraph (Fin n),
                  (if ∃ U : Finset (Fin n), U.card = k ∧
                      (∃ d : ℕ, ∀ u ∈ U, (U.filter (fun v => G.Adj u v)).card = d) ∧
                      (∃ a b : Fin n, a < b ∧ c₂ * (k : ℝ) ^ (3 / 2 : ℝ) ≤ (b : ℝ) - (a : ℝ) ∧
                        k / (Nat.log 2 k + 1) ≤ (U.filter (· ≤ a)).card ∧
                        k / (Nat.log 2 k + 1) ≤ (U.filter (b ≤ ·)).card)
                    then (1 : ℝ) else 0) * w G) := by
              calc (∑ G : SimpleGraph (Fin n),
                      (if ∃ U : Finset (Fin n), U.card = k ∧
                          (∃ d : ℕ, ∀ u ∈ U, (U.filter (fun v => G.Adj u v)).card = d)
                        then (1 : ℝ) else 0) * w G)
                  ≤ ∑ G : SimpleGraph (Fin n),
                      ((∑ U ∈ Small,
                        (if ∃ d : ℕ, ∀ u ∈ U, (U.filter (fun v => G.Adj u v)).card = d
                          then (1 : ℝ) else 0) * w G) +
                      (if ∃ U : Finset (Fin n), U.card = k ∧
                          (∃ d : ℕ, ∀ u ∈ U, (U.filter (fun v => G.Adj u v)).card = d) ∧
                          (∃ a b : Fin n, a < b ∧ c₂ * (k : ℝ) ^ (3 / 2 : ℝ) ≤ (b : ℝ) - (a : ℝ) ∧
                            k / (Nat.log 2 k + 1) ≤ (U.filter (· ≤ a)).card ∧
                            k / (Nat.log 2 k + 1) ≤ (U.filter (b ≤ ·)).card)
                        then (1 : ℝ) else 0) * w G) := Finset.sum_le_sum fun G _ => hpt G
                _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_comm]
            have hb1 :
                (∑ U ∈ Small, ∑ G : SimpleGraph (Fin n),
                  (if ∃ d : ℕ, ∀ u ∈ U, (U.filter (fun v => G.Adj u v)).card = d then (1 : ℝ) else 0) * w G)
                < 1 / (2 * (n : ℝ) ^ 2) := by
              have hb1a :
                  (∑ U ∈ Small, ∑ G : SimpleGraph (Fin n),
                    (if ∃ d : ℕ, ∀ u ∈ U, (U.filter (fun v => G.Adj u v)).card = d then (1 : ℝ) else 0) * w G)
                  ≤ (Small.card : ℝ) * ((n : ℝ) * (C₁ / (k : ℝ)) ^ ((k : ℝ) / 2)) := by
                calc _ ≤ ∑ U ∈ Small, (n : ℝ) * (C₁ / (k : ℝ)) ^ ((k : ℝ) / 2) := by
                        refine Finset.sum_le_sum fun U hU => ?_
                        have hUk : U.card = k := (Finset.mem_filter.mp hU).2.1
                        have hs := h_single n hn1 U (by omega)
                        dsimp only [w]
                        rw [hUk] at hs
                        exact hs
                  _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
              exact hb1a.trans_lt (h_case1 n hnN₁ k hk_sqrt hk.2)
            have hb2 := h_case2 n hnN₂ k hk_bound hk.2
            have heq : 1 / (2 * (n : ℝ) ^ 2) + 1 / (2 * (n : ℝ) ^ 2) = 1 / (n : ℝ) ^ 2 := by ring
            linarith
          have hpt_bad : ∀ G : SimpleGraph (Fin n),
              (if bad G then (1 : ℝ) else 0) * w G ≤
              ∑ k ∈ Finset.Icc K n,
                (if ∃ U : Finset (Fin n), U.card = k ∧
                    (∃ d : ℕ, ∀ u ∈ U, (U.filter (fun v => G.Adj u v)).card = d)
                  then (1 : ℝ) else 0) * w G := by
            intro G
            have hwG := weight_nonneg hn1 G
            by_cases hG : bad G
            · simp only [hG, ↓reduceIte, one_mul]
              obtain ⟨S, hSreg, hSK⟩ := hG
              let U := S.verts.toFinset
              have hUk : U.card = S.verts.ncard := Set.ncard_eq_toFinset_card' S.verts |>.symm
              have hUle : U.card ≤ n := by
                simpa using (U.card_le_univ.trans_eq (Fintype.card_fin n))
              have hmem : U.card ∈ Finset.Icc K n := Finset.mem_Icc.mpr ⟨by omega, hUle⟩
              have hUreg := regular_of_isRegularInduced hSreg
              have hex : ∃ U' : Finset (Fin n), U'.card = U.card ∧
                  (∃ d : ℕ, ∀ u ∈ U', (U'.filter (fun v => G.Adj u v)).card = d) := ⟨U, rfl, hUreg⟩
              refine Finset.single_le_sum (f := fun k =>
                  (if ∃ U' : Finset (Fin n), U'.card = k ∧
                      (∃ d : ℕ, ∀ u ∈ U', (U'.filter (fun v => G.Adj u v)).card = d)
                    then (1 : ℝ) else 0) * w G)
                (fun k _ => mul_nonneg (by split_ifs <;> norm_num) hwG) hmem |>.trans_eq' ?_
              simp [hex]
            · simp only [hG, ↓reduceIte, zero_mul]
              exact Finset.sum_nonneg fun k _ => mul_nonneg (by split_ifs <;> norm_num) hwG
          have hsum_bad :
              (∑ G : SimpleGraph (Fin n), (if bad G then (1 : ℝ) else 0) * w G) ≤
              ∑ k ∈ Finset.Icc K n, ∑ G : SimpleGraph (Fin n),
                (if ∃ U : Finset (Fin n), U.card = k ∧
                    (∃ d : ℕ, ∀ u ∈ U, (U.filter (fun v => G.Adj u v)).card = d)
                  then (1 : ℝ) else 0) * w G := by
            calc _ ≤ ∑ G : SimpleGraph (Fin n), ∑ k ∈ Finset.Icc K n,
                      (if ∃ U : Finset (Fin n), U.card = k ∧
                          (∃ d : ℕ, ∀ u ∈ U, (U.filter (fun v => G.Adj u v)).card = d)
                        then (1 : ℝ) else 0) * w G := Finset.sum_le_sum fun G _ => hpt_bad G
              _ = _ := Finset.sum_comm
          have hIcc_ne : (Finset.Icc K n).Nonempty := ⟨K, Finset.mem_Icc.mpr ⟨le_rfl, hKn⟩⟩
          have hsum_lt :
              (∑ k ∈ Finset.Icc K n, ∑ G : SimpleGraph (Fin n),
                (if ∃ U : Finset (Fin n), U.card = k ∧
                    (∃ d : ℕ, ∀ u ∈ U, (U.filter (fun v => G.Adj u v)).card = d)
                  then (1 : ℝ) else 0) * w G) <
              ∑ _ ∈ Finset.Icc K n, (1 / (n : ℝ) ^ 2) :=
            Finset.sum_lt_sum (fun k hk => (hstep k hk).le) ⟨K, Finset.mem_Icc.mpr ⟨le_rfl, hKn⟩, hstep K (Finset.mem_Icc.mpr ⟨le_rfl, hKn⟩)⟩
          have hcard_le : ((Finset.Icc K n).card : ℝ) ≤ (n : ℝ) := by
            have : (Finset.Icc K n).card ≤ n := by
              rw [Nat.card_Icc]
              omega
            exact_mod_cast this
          have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
          have hbound1 : (∑ _ ∈ Finset.Icc K n, (1 / (n : ℝ) ^ 2)) ≤ 1 := by
            rw [Finset.sum_const, nsmul_eq_mul]
            calc ((Finset.Icc K n).card : ℝ) * (1 / (n : ℝ) ^ 2)
                ≤ (n : ℝ) * (1 / (n : ℝ) ^ 2) := mul_le_mul_of_nonneg_right hcard_le (by positivity)
              _ = 1 / (n : ℝ) := by field_simp
              _ ≤ 1 := div_le_one_of_le₀ (by exact_mod_cast hn1) (by positivity)
          linarith
        by_contra! hall
        have hsum_eq : (∑ G : SimpleGraph (Fin n), (if bad G then (1 : ℝ) else 0) * w G) = 1 := by
          have h1 : ∀ G : SimpleGraph (Fin n), (if bad G then (1 : ℝ) else 0) * w G = w G := by
            intro G
            obtain ⟨S, hS1, hS2⟩ := hall G
            have hbadG : bad G := ⟨S, hS1, hS2⟩
            simp [hbadG]
          simp_rw [h1]
          exact sum_weight_eq_one n
        linarith
      · refine ⟨⊥, fun S _ => ?_⟩
        have hcard : S.verts.ncard ≤ n := by
          have := S.verts.toFinset.card_le_univ
          rw [Fintype.card_fin] at this
          rwa [Set.ncard_eq_toFinset_card']
        omega
    obtain ⟨G, hG⟩ := h_exists_G
    have hF_le_K : Erdos82.F n ≤ K := by
      rw [Erdos82.F]
      refine csSup_le ⟨0, fun G' => ⟨⊥, ⟨fun _ hv _ => False.elim hv, 0, fun v => False.elim v.2⟩, Nat.zero_le _⟩⟩ ?_
      · intro k hk
        obtain ⟨S, hSreg, hSk⟩ := hk G
        exact le_trans hSk (hG S hSreg).le
    have hK_ub : (K : ℝ) ≤ bound + 1 := by
      have := Nat.ceil_lt_add_one (by linarith : 0 ≤ bound)
      exact le_of_lt this
    have hsq1 : 1 ≤ Real.sqrt (n : ℝ) * (Real.log (n : ℝ)) ^ (3 / 4 : ℝ) := hN₅ n hnN₅
    calc (Erdos82.F n : ℝ)
        ≤ (K : ℝ) := by exact_mod_cast hF_le_K
      _ ≤ bound + 1 := hK_ub
      _ ≤ bound + Real.sqrt (n : ℝ) * (Real.log (n : ℝ)) ^ (3 / 4 : ℝ) := by linarith
      _ = (C + 1) * (Real.sqrt (n : ℝ) * (Real.log (n : ℝ)) ^ (3 / 4 : ℝ)) := by
          dsimp only [bound]
          ring
  rw [Asymptotics.isBigO_iff]
  refine ⟨C + 1, eventually_atTop.mpr ⟨N, fun n hn => ?_⟩⟩
  have h1 : 1 ≤ n := by omega
  have hsq : 0 ≤ Real.sqrt (n : ℝ) * (Real.log (n : ℝ)) ^ (3 / 4 : ℝ) := by
    have : 0 ≤ (Real.log (n : ℝ)) ^ (3 / 4 : ℝ) := Real.rpow_nonneg (Real.log_nonneg (by exact_mod_cast h1)) _
    positivity
  rw [Real.norm_natCast, Real.norm_of_nonneg hsq]
  exact hF_bound n hn

end OMA.R_Erdos82_erdos_82_variants_F_upper_bound_R1
