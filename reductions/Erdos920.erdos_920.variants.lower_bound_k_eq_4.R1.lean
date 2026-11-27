import FormalConjectures.ErdosProblems.«920»

-- Reduction Erdos920.erdos_920.variants.lower_bound_k_eq_4.R1 of Erdős Problem 920 — lower bound k eq 4
-- Credit: @hyprspacecoyote
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# `f₄(n) ≫ n^{2/3} / (log n)^{4/3}` from `R(4, m) ≫ m³ / (log m)⁴`

* `H1` is the Mattheus–Verstraete bound `R(4, m) ≥ C m³ / (log m)⁴` for large `m`, exactly as
  `Erdos166.erdos_166.variants.mattheus_verstraete`.
* `H2` unfolds the Ramsey number: below `R(4, m)` there is a `K₄`-free graph whose independence
  number is less than `m`.

Given `n`, take `m = ⌈K n^{1/3} (log n)^{4/3}⌉` with `C K³ ≥ 2`. For large `n`, `m ≤ n`, so
`C m³ / (log m)⁴ ≥ C K³ n > n` and `H2` gives a `K₄`-free graph `G` on `n` vertices with
`α(G) < m`. Then `f₄(n) ≥ χ(G) ≥ n / α(G) ≥ n / m ≥ n^{2/3} / (2K (log n)^{4/3})`.
Everything except `H1` and `H2` is proved here.
-/

namespace OMA.R_Erdos920_erdos_920_variants_lower_bound_k_eq_4_R1

open Filter Asymptotics SimpleGraph

/-- Mattheus–Verstraete [MaVe23]: `R(4, m) ≥ C m³ / (log m)⁴` for all large `m`. -/
def H1 : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ᶠ m : ℕ in atTop,
    (SimpleGraph.classicalRamsey 4 m : ℝ) ≥ C * (m : ℝ) ^ 3 / (Real.log m) ^ 4

/-- Below the Ramsey number `R(4, m)` there is a `K₄`-free graph with independence number `< m`. -/
def H2 : Prop :=
  ∀ m N : ℕ, N < SimpleGraph.classicalRamsey 4 m →
    ∃ G : SimpleGraph (Fin N), G.CliqueFree 4 ∧ G.indepNum < m

/-- `f₄(n)` is at least the chromatic number of any `K₄`-free graph on `n` vertices. -/
lemma chi_le_f (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 4) :
    G.chromaticNumber ≤ (Erdos920.f 4 n : ℕ∞) := by
  have hle : G.chromaticNumber ≤ (n : ℕ∞) := by
    have := G.chromaticNumber_le_card
    simpa using this
  have hfin : G.chromaticNumber ≠ ⊤ := ne_top_of_le_ne_top (by simp) hle
  obtain ⟨x, hx⟩ := ENat.ne_top_iff_exists.1 hfin
  have hbdd : BddAbove {x : ℕ | ∃ G : SimpleGraph (Fin n), ∃ (_ : G.CliqueFree 4),
      G.chromaticNumber = ↑x} := by
    refine ⟨n, fun y ⟨H, _, hH⟩ => ?_⟩
    have := H.chromaticNumber_le_card
    rw [hH] at this
    simpa using this
  have hmem : x ∈ {x : ℕ | ∃ G : SimpleGraph (Fin n), ∃ (_ : G.CliqueFree 4),
      G.chromaticNumber = ↑x} := ⟨G, hG, hx.symm⟩
  rw [← hx]
  exact_mod_cast le_csSup hbdd hmem

/-- `χ(G) ≥ n / α(G)` in real form. -/
lemma n_div_le_f (n : ℕ) (hn : 1 ≤ n) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 4)
    (m : ℕ) (hα : G.indepNum < m) : (n : ℝ) / m ≤ Erdos920.f 4 n := by
  have hα1 : 1 ≤ G.indepNum := by
    have : ({⟨0, by omega⟩} : Finset (Fin n)).card ≤ G.indepNum := by
      apply IsIndepSet.card_le_indepNum
      intro u hu v hv huv
      simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hu hv
      exact absurd (hu.trans hv.symm) huv
    simpa using this
  have h1 := G.card_div_indepNum_le_chromaticNumber
  have h2 := h1.trans (chi_le_f n G hG)
  have h3 : ⌈((Nat.card (Fin n) : ℚ≥0) / (G.indepNum : ℚ≥0))⌉₊ ≤ Erdos920.f 4 n := by
    exact_mod_cast h2
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at h3
  have h4 : ((n : ℚ≥0) / (G.indepNum : ℚ≥0)) ≤ Erdos920.f 4 n :=
    (Nat.le_ceil _).trans (by exact_mod_cast h3)
  have h5 : (n : ℝ) / G.indepNum ≤ Erdos920.f 4 n := by
    have := (NNRat.cast_le (K := ℝ)).2 h4
    push_cast at this
    exact this
  have hmR : (G.indepNum : ℝ) ≤ m := by exact_mod_cast hα.le
  have hαpos : (0 : ℝ) < G.indepNum := by exact_mod_cast hα1
  refine le_trans ?_ h5
  exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hαpos hmR

theorem main : H1 → H2 → type_of% @Erdos920.erdos_920.variants.lower_bound_k_eq_4 := by
  intro h1 h2
  obtain ⟨C, hC, hev⟩ := h1
  obtain ⟨M0, hM0⟩ := eventually_atTop.1 hev
  set K : ℝ := max 1 (2 / C) with hK
  have hK1 : 1 ≤ K := le_max_left _ _
  have hKC : 2 ≤ C * K ^ 3 := by
    have : 2 / C ≤ K := le_max_right _ _
    have hK2 : 1 ≤ K ^ 2 := by nlinarith
    have hK3 : K ≤ K ^ 3 := by
      calc K = K * 1 := (mul_one K).symm
        _ ≤ K * K ^ 2 := by gcongr
        _ = K ^ 3 := by ring
    rw [div_le_iff₀ hC] at this
    nlinarith
  have hKpos : 0 < K := by linarith
  apply IsBigO.of_bound (2 * K)
  have hcast := tendsto_natCast_atTop_atTop (R := ℝ)
  -- `(log n)^{4/3} ≤ (1 / (4K)) n^{2/3}` eventually
  have hlo := (isLittleO_log_rpow_rpow_atTop (4 / 3 : ℝ) (by norm_num : (0 : ℝ) < 2 / 3)).bound
    (by positivity : (0 : ℝ) < 1 / (4 * K))
  have hlo' := hcast.eventually hlo
  have ht := hcast.eventually ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).eventually_ge_atTop
    ((M0 : ℝ) + 2))
  filter_upwards [hlo', ht, eventually_ge_atTop 3] with n hlog htM hn3
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn3
  have hnpos : (0 : ℝ) < n := by linarith
  set L := Real.log n with hL
  have hL1 : 1 ≤ L := by
    rw [hL, ← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
  set t := (n : ℝ) ^ (1 / 3 : ℝ) with ht'
  set u := (n : ℝ) ^ (2 / 3 : ℝ) with hu
  set ℓ := L ^ (4 / 3 : ℝ) with hℓ
  have htu : t * u = n := by
    rw [ht', hu, ← Real.rpow_add hnpos]; norm_num
  have ht3 : t ^ 3 = n := by
    rw [ht', ← Real.rpow_natCast, ← Real.rpow_mul hnpos.le]; norm_num
  have hℓ3 : ℓ ^ 3 = L ^ 4 := by
    rw [hℓ, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
  have htpos : 0 < t := Real.rpow_pos_of_pos hnpos _
  have hupos : 0 < u := Real.rpow_pos_of_pos hnpos _
  have hℓ1 : 1 ≤ ℓ := Real.one_le_rpow hL1 (by norm_num)
  have hℓu : ℓ ≤ u / (4 * K) := by
    have := hlog
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      abs_of_nonneg (by positivity)] at this
    linarith [show 1 / (4 * K) * u = u / (4 * K) by ring]
  set x := K * t * ℓ with hx
  have hx1 : 1 ≤ x := by
    have : 1 ≤ t := by
      rw [ht']; exact Real.one_le_rpow (by linarith) (by norm_num)
    have : 1 ≤ K * t := by nlinarith
    nlinarith
  have hxn : x + 1 ≤ n := by
    have : x ≤ n / 4 := by
      calc x = K * t * ℓ := rfl
        _ ≤ K * t * (u / (4 * K)) := by gcongr
        _ = t * u / 4 := by field_simp
        _ = n / 4 := by rw [htu]
    linarith
  set m := ⌈x⌉₊ with hm
  have hmx : x ≤ m := Nat.le_ceil x
  have hmx1 : (m : ℝ) ≤ x + 1 := (Nat.ceil_lt_add_one (by linarith)).le
  have hm2 : (2 : ℝ) ≤ m := by
    have : (M0 : ℝ) + 2 ≤ t := htM
    have : t ≤ x := by
      rw [hx]; nlinarith [mul_le_mul hK1 hℓ1 zero_le_one (by linarith)]
    have : (0 : ℝ) ≤ M0 := Nat.cast_nonneg _
    linarith
  have hmM0 : M0 ≤ m := by
    have h0 : (M0 : ℝ) + 2 ≤ t := htM
    have : t ≤ x := by
      rw [hx]; nlinarith [mul_le_mul hK1 hℓ1 zero_le_one (by linarith)]
    have : (M0 : ℝ) ≤ m := by linarith
    exact_mod_cast this
  have hR := hM0 m hmM0
  -- `C m³ / (log m)⁴ > n`
  have hlogm_pos : 0 < Real.log m := Real.log_pos (by linarith)
  have hlogm : Real.log m ≤ L := Real.log_le_log (by linarith) (by linarith)
  have hbig : (n : ℝ) < C * (m : ℝ) ^ 3 / (Real.log m) ^ 4 := by
    rw [lt_div_iff₀ (by positivity)]
    have hm3 : x ^ 3 ≤ (m : ℝ) ^ 3 := by gcongr
    have hx3 : x ^ 3 = K ^ 3 * n * L ^ 4 := by
      rw [hx, mul_pow, mul_pow, ht3, hℓ3]
    have hl4 : (Real.log m) ^ 4 ≤ L ^ 4 := by gcongr
    have hL4 : 0 < L ^ 4 := by positivity
    calc (n : ℝ) * (Real.log m) ^ 4 ≤ n * L ^ 4 := by gcongr
      _ < 2 * n * L ^ 4 := by nlinarith
      _ ≤ C * K ^ 3 * n * L ^ 4 := by gcongr
      _ = C * x ^ 3 := by rw [hx3]; ring
      _ ≤ C * (m : ℝ) ^ 3 := by gcongr
  have hNR : n < SimpleGraph.classicalRamsey 4 m := by
    have : (n : ℝ) < SimpleGraph.classicalRamsey 4 m := lt_of_lt_of_le hbig hR
    exact_mod_cast this
  obtain ⟨G, hG, hα⟩ := h2 m n hNR
  have hf := n_div_le_f n (by omega) G hG m hα
  -- final comparison
  have hmpos : (0 : ℝ) < m := by linarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    abs_of_nonneg (Nat.cast_nonneg _)]
  change u / ℓ ≤ 2 * K * (Erdos920.f 4 n : ℝ)
  have hstep : u / ℓ ≤ 2 * K * ((n : ℝ) / m) := by
    rw [div_le_iff₀ (by linarith)]
    have : (n : ℝ) / m ≥ n / (2 * x) := by
      apply div_le_div_of_nonneg_left (by positivity) hmpos
      linarith
    have hnx : (n : ℝ) / (2 * x) * ℓ = u / (2 * K) := by
      rw [hx, ← htu]; field_simp
    have : 2 * K * ((n : ℝ) / m) * ℓ ≥ 2 * K * (n / (2 * x)) * ℓ := by gcongr
    have : 2 * K * (n / (2 * x)) * ℓ = u := by
      rw [mul_assoc, hnx]; field_simp
    linarith
  calc u / ℓ ≤ 2 * K * ((n : ℝ) / m) := hstep
    _ ≤ 2 * K * (Erdos920.f 4 n : ℝ) := by gcongr

end OMA.R_Erdos920_erdos_920_variants_lower_bound_k_eq_4_R1
