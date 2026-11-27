import FormalConjectures.ErdosProblems.«1182»

-- Reduction Erdos1182.erdos_1182.variants.f_lower.R1 of Erdős Problem 1182 — f lower
-- Credit: @minimumnz
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# `f(n) ≫ n^(3/2) (log n)^(1/2)`: Ramsey bound + explicit construction

* `H1` is the Ajtai–Komlós–Szemerédi / Shearer bound `R(3, m) ≤ C m² / log m`.
* `H2` is a finite construction. Take a hub vertex, `k` cliques `K_m` each joined to the hub by one
  edge, and pendant leaves at the hub, `n` vertices in all. In a colouring of `K_(2n-1)` with no
  triangle in the first colour, either some vertex has `n` first-colour neighbours (they form a
  second-colour `K_n`), or every second-colour degree is at least `n - 1`; then the cliques are
  found greedily inside the second-colour neighbourhood of any hub, as long as
  `R(3, m) + (k - 1) m + 1 ≤ n`, and the remaining neighbours serve as leaves.
* `main` chooses `m ≈ c √(n log n)` and `k = ⌊n / (2m)⌋` and does the asymptotic bookkeeping.
-/

namespace OMA.R_Erdos1182_erdos_1182_variants_f_lower_R1

open Filter

-- Ajtai–Komlós–Szemerédi (1980), Shearer (1983): `R(K_3, K_m) = O(m² / log m)`.
def H1 : Prop := ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 2 ≤ m →
    (SimpleGraph.graphRamsey (⊤ : SimpleGraph (Fin 3)) (⊤ : SimpleGraph (Fin m)) : ℝ)
      ≤ C * (m : ℝ) ^ 2 / Real.log m

-- Hub with `k` pendant cliques `K_m` and leaves: a connected `3`-good graph on `n` vertices.
def H2 : Prop := ∀ n m k : ℕ, 2 ≤ m → 1 ≤ k → k * m + 1 ≤ n →
    SimpleGraph.graphRamsey (⊤ : SimpleGraph (Fin 3)) (⊤ : SimpleGraph (Fin m))
      + (k - 1) * m + 1 ≤ n →
    ∃ G : SimpleGraph (Fin n), G.Connected ∧ Erdos1182.IsTriangleGood G ∧
      k * m.choose 2 ≤ G.edgeSet.ncard

theorem le_f {n q : ℕ} (G : SimpleGraph (Fin n)) (hc : G.Connected)
    (hg : Erdos1182.IsTriangleGood G) (hq : q ≤ G.edgeSet.ncard) : q ≤ Erdos1182.f n := by
  unfold Erdos1182.f
  refine hq.trans (le_csSup ?_ ⟨G, hc, rfl, hg⟩)
  refine ((Set.finite_range fun G : SimpleGraph (Fin n) => G.edgeSet.ncard).subset ?_).bddAbove
  rintro q ⟨G, -, rfl, -⟩
  exact ⟨G, rfl⟩

set_option maxHeartbeats 1600000 in
theorem main : H1 → H2 → type_of% @Erdos1182.erdos_1182.variants.f_lower := by
  rintro ⟨C, hC, hR⟩ hcon
  set c : ℝ := min 1 (1 / (32 * C)) with hc
  have hc0 : 0 < c := lt_min one_pos (by positivity)
  have hc1 : c ≤ 1 := min_le_left _ _
  have hcC : c * (32 * C) ≤ 1 := by
    have : c ≤ 1 / (32 * C) := min_le_right _ _
    rwa [le_div_iff₀ (by positivity)] at this
  refine ⟨c / 32, by positivity, ?_⟩
  have hlog : ∀ᶠ n : ℕ in atTop, 1 / c ^ 2 ≤ Real.log n :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  filter_upwards [hlog, eventually_ge_atTop 16384] with n hL hn
  have hnR : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  set L : ℝ := Real.log n with hLdef
  have hL0 : 0 < L := lt_of_lt_of_le (by positivity) hL
  have hcL : 1 ≤ c ^ 2 * L := by
    rw [div_le_iff₀ (by positivity)] at hL
    linarith
  set s : ℝ := Real.sqrt n with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr hn0
  have hss : s * s = n := Real.mul_self_sqrt hn0.le
  have hs128 : 128 ≤ s := by
    rw [hs]
    apply Real.le_sqrt_of_sq_le
    norm_num
    linarith
  set t : ℝ := Real.sqrt L with ht
  have ht0 : 0 < t := Real.sqrt_pos.mpr hL0
  have htt : t * t = L := Real.mul_self_sqrt hL0.le
  -- `log n ≤ 2 √n`
  have hLs : L ≤ 2 * s := by
    have h1 : Real.log s ≤ s - 1 := Real.log_le_sub_one_of_pos hs0
    have h2 : L = 2 * Real.log s := by
      rw [hLdef, ← hss, Real.log_mul hs0.ne' hs0.ne']
      ring
    linarith
  have hct : 1 ≤ c * t := by
    have h : 1 ≤ (c * t) ^ 2 := by rw [mul_pow, sq t, htt]; exact hcL
    by_contra hlt
    push Not at hlt
    have : (c * t) ^ 2 < 1 := by
      have h0 : 0 ≤ c * t := by positivity
      nlinarith
    linarith
  have ht_s : t * t ≤ 2 * s := by rw [htt]; exact hLs
  -- the clique size
  set x : ℝ := c * (s * t) with hx
  have hxs : s ≤ x := by
    rw [hx]
    nlinarith
  set m : ℕ := ⌈x⌉₊ with hm
  have hmx : x ≤ m := Nat.le_ceil x
  have hmx' : (m : ℝ) < x + 1 := Nat.ceil_lt_add_one (by positivity)
  have hm128 : (128 : ℝ) ≤ m := by linarith
  have hm2 : 2 ≤ m := by
    have : (2 : ℝ) ≤ m := by linarith
    exact_mod_cast this
  have hm2x : (m : ℝ) ≤ 2 * x := by linarith
  -- `x ≤ √n · t ≤ √n · √(2√n)`, so `8 x ≤ n`
  have hx8 : 8 * x ≤ n := by
    have h1 : x ≤ s * t := by
      rw [hx]
      have : 0 ≤ s * t := by positivity
      nlinarith
    have h2 : t ≤ s / 8 := by
      by_contra hlt
      push Not at hlt
      have : (s / 8) * (s / 8) < t * t := by
        have : 0 ≤ s / 8 := by positivity
        nlinarith
      nlinarith
    calc 8 * x ≤ 8 * (s * t) := by linarith
      _ ≤ 8 * (s * (s / 8)) := by
        have := mul_le_mul_of_nonneg_left h2 hs0.le
        linarith
      _ = n := by rw [← hss]; ring
  have h4m : 4 * m ≤ n := by
    have : (4 : ℝ) * m ≤ n := by linarith
    exact_mod_cast this
  -- the Ramsey number is at most `n / 4`
  have hlogm : L / 2 ≤ Real.log m := by
    have h1 : Real.log s ≤ Real.log m := Real.log_le_log hs0 (by linarith)
    have h2 : L = 2 * Real.log s := by
      rw [hLdef, ← hss, Real.log_mul hs0.ne' hs0.ne']
      ring
    linarith
  have hlogm0 : 0 < Real.log m := by linarith
  have hRam : 4 * SimpleGraph.graphRamsey (⊤ : SimpleGraph (Fin 3)) (⊤ : SimpleGraph (Fin m))
      ≤ n := by
    have h1 := hR m hm2
    have h2 : C * (m : ℝ) ^ 2 / Real.log m ≤ n / 4 := by
      rw [div_le_iff₀ hlogm0]
      have hm2' : (m : ℝ) ^ 2 ≤ 4 * x ^ 2 := by nlinarith
      have hx2 : x ^ 2 = c ^ 2 * (n * L) := by
        rw [hx, ← hss, ← htt]
        ring
      have h3 : C * (m : ℝ) ^ 2 ≤ C * (4 * (c ^ 2 * (n * L))) := by
        rw [← hx2]
        exact mul_le_mul_of_nonneg_left hm2' hC.le
      have h4 : C * (4 * (c ^ 2 * (n * L))) ≤ (n / 4) * (L / 2) := by
        have h5 : c ^ 2 * (32 * C) ≤ 1 := by nlinarith
        have h6 : 0 ≤ (n : ℝ) * L := by positivity
        nlinarith
      calc C * (m : ℝ) ^ 2 ≤ (n / 4) * (L / 2) := h3.trans h4
        _ ≤ (n / 4) * Real.log m := mul_le_mul_of_nonneg_left hlogm (by positivity)
    have h3 : (4 : ℝ) * (SimpleGraph.graphRamsey (⊤ : SimpleGraph (Fin 3))
        (⊤ : SimpleGraph (Fin m)) : ℝ) ≤ n := by linarith
    exact_mod_cast h3
  -- the number of cliques
  obtain ⟨k, hk1, hkm2, hkR', hside⟩ : ∃ k : ℕ, 1 ≤ k ∧ 2 * (k * m) ≤ n ∧ n ≤ 4 * (m * k) ∧
      SimpleGraph.graphRamsey (⊤ : SimpleGraph (Fin 3)) (⊤ : SimpleGraph (Fin m))
        + (k - 1) * m + 1 ≤ n := by
    have hm0 : 0 < 2 * m := by omega
    have e1 : 2 * m * (n / (2 * m)) ≤ n := Nat.mul_div_le n (2 * m)
    have e2 : n < 2 * m * (n / (2 * m) + 1) := Nat.lt_mul_div_succ n hm0
    have e3 : 1 ≤ n / (2 * m) := (Nat.one_le_div_iff hm0).mpr (by omega)
    generalize n / (2 * m) = k at e1 e2 e3
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have e4 : 2 * m * (j + 1) = 2 * (j * m) + 2 * m := by ring
    have e5 : 2 * m * (j + 1 + 1) = 2 * (j * m) + 4 * m := by ring
    have e6 : (j + 1) * m = j * m + m := by ring
    have e7 : m * (j + 1) = j * m + m := by ring
    rw [e4] at e1
    rw [e5] at e2
    refine ⟨j + 1, by omega, ?_, ?_, ?_⟩
    · rw [e6]; omega
    · rw [e7]; omega
    · rw [Nat.add_sub_cancel]
      generalize j * m = P at e1 e2
      generalize SimpleGraph.graphRamsey (⊤ : SimpleGraph (Fin 3)) (⊤ : SimpleGraph (Fin m)) = R
        at hRam
      omega
  obtain ⟨G, hGc, hGg, hGe⟩ := hcon n m k hm2 hk1 (by omega) hside
  have hf := le_f G hGc hGg hGe
  have hfR : ((k * m.choose 2 : ℕ) : ℝ) ≤ Erdos1182.f n := by exact_mod_cast hf
  have hkR : (n : ℝ) ≤ 4 * (m * k) := by exact_mod_cast hkR'
  have hch : ((m.choose 2 : ℕ) : ℝ) = m * (m - 1) / 2 := Nat.cast_choose_two ℝ m
  have hch' : (m : ℝ) ^ 2 / 4 ≤ ((m.choose 2 : ℕ) : ℝ) := by
    rw [hch]
    nlinarith
  have hpow : (n : ℝ) ^ (3 / 2 : ℝ) = n * s := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hn0, Real.rpow_one,
      hs, Real.sqrt_eq_rpow]
  rw [hpow]
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hmpos : (0 : ℝ) < m := by linarith
  have key : (n : ℝ) * x / 16 ≤ ((k * m.choose 2 : ℕ) : ℝ) := by
    push_cast
    calc (n : ℝ) * x / 16 ≤ (4 * (m * k)) * m / 16 := by
          have : (n : ℝ) * x ≤ (4 * (m * k)) * m :=
            mul_le_mul hkR hmx (by positivity) (by positivity)
          linarith
      _ = k * ((m : ℝ) ^ 2 / 4) := by ring
      _ ≤ k * ((m.choose 2 : ℕ) : ℝ) := mul_le_mul_of_nonneg_left hch' hk0
  have hpos : 0 < (n : ℝ) * s * t := by positivity
  calc c / 32 * (n * s) * t = (n * (c * (s * t))) / 32 := by ring
    _ < (n * (c * (s * t))) / 16 := by
      have : 0 < (n : ℝ) * (c * (s * t)) := by positivity
      linarith
    _ = (n : ℝ) * x / 16 := by rw [hx]
    _ ≤ ((k * m.choose 2 : ℕ) : ℝ) := key
    _ ≤ Erdos1182.f n := hfR

end OMA.R_Erdos1182_erdos_1182_variants_f_lower_R1
