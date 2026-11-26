import FormalConjectures.ErdosProblems.«1191»

-- Reduction Erdos1191.erdos_1191.parts.i.R1 of Erdős Problem 1191 — i
-- Credit: @kenanwienberg
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# A finite reduction of Erdős Problem 1191 (i)

Both hypotheses concern finite Sidon sets. In H1, at least one dyadic scale in
each exponent interval `[R, 2R]` satisfies an explicit counting bound.
H2 asks for a scale satisfying that bound at which the next `L` dyadic
intervals contain few new points. Adding the two counts and taking `L`
arbitrarily large yields the required zero liminf.
-/

namespace OMA.R_Erdos1191_erdos_1191_parts_i_R1

open scoped ENNReal

lemma rpow_half_sq {z : ℝ} (hz : 0 ≤ z) : (z ^ (1 / 2 : ℝ)) ^ 2 = z := by
  rw [← Real.rpow_natCast (z ^ (1 / 2 : ℝ)) 2, ← Real.rpow_mul hz]
  norm_num

lemma liminf_ofReal_eq_zero {u : ℕ → ℝ}
    (h : ∀ ε : ℝ, 0 < ε → ∀ b : ℕ, ∃ x ≥ b, u x ≤ ε) :
    Filter.liminf (fun x ↦ ENNReal.ofReal (u x)) Filter.atTop = 0 := by
  refine le_antisymm ?_ bot_le
  have hle : ∀ ε : ℝ, 0 < ε →
      Filter.liminf (fun x ↦ ENNReal.ofReal (u x)) Filter.atTop ≤ ENNReal.ofReal ε := by
    intro ε hε
    apply Filter.liminf_le_of_frequently_le'
    rw [Filter.frequently_atTop]
    intro b
    obtain ⟨x, hxb, hux⟩ := h ε hε b
    exact ⟨x, hxb, ENNReal.ofReal_le_ofReal hux⟩
  by_contra hne
  have hpos : 0 < Filter.liminf (fun x ↦ ENNReal.ofReal (u x)) Filter.atTop :=
    pos_iff_ne_zero.mpr (by simpa using hne)
  have hlt_top : Filter.liminf (fun x ↦ ENNReal.ofReal (u x)) Filter.atTop < ⊤ :=
    lt_of_le_of_lt (hle 1 zero_lt_one) ENNReal.ofReal_lt_top
  set y := Filter.liminf (fun x ↦ ENNReal.ofReal (u x)) Filter.atTop
  have hy_pos : 0 < y.toReal := ENNReal.toReal_pos hpos.ne' hlt_top.ne
  have hy_half : y ≤ ENNReal.ofReal (y.toReal / 2) := hle (y.toReal / 2) (half_pos hy_pos)
  have hy_eq : ENNReal.ofReal y.toReal = y := ENNReal.ofReal_toReal hlt_top.ne
  have hy_le := hy_eq.le.trans hy_half
  have hreal_le : y.toReal ≤ y.toReal / 2 :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hy_le
  linarith

def H1 : Prop :=
  ∀ (R : ℕ) (S : Finset ℕ), 16 ≤ R → (↑S : Set ℕ) ⊆ Set.Icc 1 (2 ^ (2 * R)) →
    IsSidon (↑S : Set ℕ) →
      ∃ k ∈ Set.Icc R (2 * R), (S.filter (· ≤ 2 ^ k)).card ^ 2 * k ≤ 512 * 2 ^ k

def H2 : Prop :=
  ∀ L R₀ : ℕ, 16 ≤ R₀ → 1 ≤ L →
    ∃ K : ℕ, 2 * R₀ + L ≤ K ∧
      ∀ S : Finset ℕ, (↑S : Set ℕ) ⊆ Set.Icc 1 (2 ^ K) → IsSidon (↑S : Set ℕ) →
        (∃ R ∈ Set.Icc R₀ (K - L), (S.filter (· ≤ 2 ^ R)).card ^ 2 * R ≤ 512 * 2 ^ R) →
        ∃ R ∈ Set.Icc R₀ (K - L),
          (S.filter (· ≤ 2 ^ R)).card ^ 2 * R ≤ 512 * 2 ^ R ∧
          2 ^ L * (S.filter (fun a => 2 ^ R < a ∧ a ≤ 2 ^ (R + L))).card ^ 2 * (R + L) ≤
            2 ^ (R + L)

theorem main : H1 → H2 → type_of% @Erdos1191.erdos_1191.parts.i := by
  intro hH1 hH2 A _hAinf hAsid
  classical
  apply liminf_ofReal_eq_zero
  intro ε hε b
  obtain ⟨L₀, hL₀⟩ := exists_nat_ge (2050 * Real.log 2 / ε ^ 2)
  let L : ℕ := max 1 L₀
  have hL1 : 1 ≤ L := le_max_left 1 L₀
  have hL_bound : 2050 * Real.log 2 ≤ ε ^ 2 * (2 : ℝ) ^ L := by
    have hε2 : 0 < ε ^ 2 := sq_pos_of_pos hε
    have h1 : 2050 * Real.log 2 / ε ^ 2 ≤ (L : ℝ) :=
      hL₀.trans (Nat.cast_le.mpr (le_max_right 1 L₀))
    have h2 : (L : ℝ) ≤ (2 : ℝ) ^ L := by
      exact_mod_cast Nat.lt_two_pow_self.le
    have h3 : 2050 * Real.log 2 / ε ^ 2 ≤ (2 : ℝ) ^ L := h1.trans h2
    rwa [div_le_iff₀ hε2, mul_comm ((2 : ℝ) ^ L)] at h3
  let R₀ : ℕ := max 16 (max b L)
  have hR₀16 : 16 ≤ R₀ := le_max_left _ _
  have hR₀b : b ≤ R₀ := (le_max_left b L).trans (le_max_right 16 _)
  have hR₀L : L ≤ R₀ := (le_max_right b L).trans (le_max_right 16 _)
  obtain ⟨K, hK, hK_prop⟩ := hH2 L R₀ hR₀16 hL1
  let S : Finset ℕ := (Finset.Icc 1 (2 ^ K)).filter (· ∈ A)
  have hS_sub : (↑S : Set ℕ) ⊆ Set.Icc 1 (2 ^ K) := by
    intro z hz
    dsimp only [S] at hz
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hz
    exact hz.1
  have hS_sidon : IsSidon (↑S : Set ℕ) := by
    refine Set.IsSidon.subset hAsid ?_
    intro z hz
    dsimp only [S] at hz
    rw [Finset.mem_coe, Finset.mem_filter] at hz
    exact hz.2
  let S₀ : Finset ℕ := S.filter (· ≤ 2 ^ (2 * R₀))
  have hS₀_sub : (↑S₀ : Set ℕ) ⊆ Set.Icc 1 (2 ^ (2 * R₀)) := by
    intro z hz
    dsimp only [S₀, S] at hz
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc, Set.mem_Icc] at hz ⊢
    exact ⟨hz.1.1.1, hz.2⟩
  have hS₀_sidon : IsSidon (↑S₀ : Set ℕ) :=
    Set.IsSidon.subset hS_sidon (by
      intro z hz
      dsimp only [S₀] at hz
      rw [Finset.mem_coe, Finset.mem_filter] at hz
      exact Finset.mem_coe.mpr hz.1)
  obtain ⟨k₀, hk₀_mem, hk₀_le⟩ := hH1 R₀ S₀ hR₀16 hS₀_sub hS₀_sidon
  have hk₀_filter : S₀.filter (· ≤ 2 ^ k₀) = S.filter (· ≤ 2 ^ k₀) := by
    ext z
    dsimp only [S₀]
    simp only [Finset.mem_filter]
    have hpow : 2 ^ k₀ ≤ 2 ^ (2 * R₀) := Nat.pow_le_pow_right (by omega) hk₀_mem.2
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, h.2.trans hpow⟩, h.2⟩⟩
  rw [hk₀_filter] at hk₀_le
  have h_wit : ∃ R ∈ Set.Icc R₀ (K - L), (S.filter (· ≤ 2 ^ R)).card ^ 2 * R ≤ 512 * 2 ^ R :=
    ⟨k₀, ⟨hk₀_mem.1, by have := hk₀_mem.2; omega⟩, hk₀_le⟩
  obtain ⟨R, hR_mem, hR_base, hR_ann⟩ := hK_prop S hS_sub hS_sidon h_wit
  let m : ℕ := R + L
  let x : ℕ := 2 ^ m
  have hmK : m ≤ K := by have := hR_mem.2; omega
  have hxb : b ≤ x := by
    have hbm : b ≤ m := by have := hR_mem.1; omega
    exact hbm.trans Nat.lt_two_pow_self.le
  let w : ℕ := (S.filter (· ≤ 2 ^ m)).card
  have hw_eq : (A ∩ Set.Icc 1 x).ncard = w := by
    have hset : A ∩ Set.Icc 1 x = ↑(S.filter (· ≤ 2 ^ m)) := by
      ext z
      dsimp only [S, x]
      rw [Set.mem_inter_iff, Set.mem_Icc, Finset.mem_coe, Finset.mem_filter, Finset.mem_filter,
        Finset.mem_Icc]
      have hpow : 2 ^ m ≤ 2 ^ K := Nat.pow_le_pow_right (by omega) hmK
      exact ⟨fun h => ⟨⟨⟨h.2.1, h.2.2.trans hpow⟩, h.1⟩, h.2.2⟩,
        fun h => ⟨h.1.2, h.1.1.1, h.2⟩⟩
    rw [hset, Set.ncard_coe_finset]
  let u : ℕ := (S.filter (· ≤ 2 ^ R)).card
  let v : ℕ := (S.filter (fun a => 2 ^ R < a ∧ a ≤ 2 ^ m)).card
  have hw_uv : w ≤ u + v := by
    have hsub : S.filter (· ≤ 2 ^ m) ⊆
        S.filter (· ≤ 2 ^ R) ∪ S.filter (fun a => 2 ^ R < a ∧ a ≤ 2 ^ m) := by
      intro z hz
      simp only [Finset.mem_union, Finset.mem_filter] at hz ⊢
      by_cases hle : z ≤ 2 ^ R
      · exact Or.inl ⟨hz.1, hle⟩
      · exact Or.inr ⟨hz.1, Nat.lt_of_not_le hle, hz.2⟩
    exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hw_sq : w ^ 2 ≤ 2 * u ^ 2 + 2 * v ^ 2 := by
    have hw_int : (w : ℤ) ≤ (u : ℤ) + (v : ℤ) := by exact_mod_cast hw_uv
    have hsq_int : (w : ℤ) ^ 2 ≤ 2 * (u : ℤ) ^ 2 + 2 * (v : ℤ) ^ 2 := by
      nlinarith [sq_nonneg ((u : ℤ) - (v : ℤ)), sq_nonneg (w : ℤ),
        (by positivity : (0 : ℤ) ≤ (u : ℤ) + (v : ℤ) + (w : ℤ))]
    exact_mod_cast hsq_int
  have hm_le_2R : m ≤ 2 * R := by
    have := hR_mem.1
    omega
  have h_comb_nat : 2 ^ L * w ^ 2 * m ≤ 2050 * x := by
    have hu_part : 2 ^ L * u ^ 2 * m ≤ 1024 * x := by
      calc
        2 ^ L * u ^ 2 * m ≤ 2 ^ L * u ^ 2 * (2 * R) :=
          Nat.mul_le_mul_left _ hm_le_2R
        _ = 2 * 2 ^ L * (u ^ 2 * R) := by ring
        _ ≤ 2 * 2 ^ L * (512 * 2 ^ R) := Nat.mul_le_mul_left _ hR_base
        _ = 1024 * 2 ^ (R + L) := by rw [pow_add]; ring
        _ = 1024 * x := rfl
    have hv_part : 2 ^ L * v ^ 2 * m ≤ x := hR_ann
    have hstep1 : 2 ^ L * w ^ 2 * m ≤ 2 ^ L * (2 * u ^ 2 + 2 * v ^ 2) * m :=
      Nat.mul_le_mul_right m (Nat.mul_le_mul_left (2 ^ L) hw_sq)
    have hstep2 : 2 ^ L * (2 * u ^ 2 + 2 * v ^ 2) * m =
        2 * (2 ^ L * u ^ 2 * m) + 2 * (2 ^ L * v ^ 2 * m) := by ring
    omega
  refine ⟨x, hxb, ?_⟩
  rw [hw_eq]
  have hx_one_le : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast Nat.one_le_two_pow
  have hx_pos : (0 : ℝ) < (x : ℝ) := by positivity
  have hlog_nonneg : 0 ≤ Real.log (x : ℝ) := Real.log_nonneg hx_one_le
  have hrpow_x_pos : 0 < (x : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hx_pos _
  have hrpow_log_nonneg : 0 ≤ Real.log (x : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_nonneg hlog_nonneg _
  set lhs : ℝ := (w : ℝ) / (x : ℝ) ^ (1 / 2 : ℝ) * Real.log (x : ℝ) ^ (1 / 2 : ℝ)
  have hlhs_nonneg : 0 ≤ lhs := by positivity
  have hlhs_sq : lhs ^ 2 = (w : ℝ) ^ 2 / (x : ℝ) * Real.log (x : ℝ) := by
    dsimp only [lhs]
    rw [mul_pow, div_pow, rpow_half_sq hx_pos.le, rpow_half_sq hlog_nonneg]
  have hlog_x : Real.log (x : ℝ) = (m : ℝ) * Real.log 2 := by
    have hx_cast : (x : ℝ) = (2 : ℝ) ^ m := by simp [x]
    rw [hx_cast, Real.log_pow]
  have h_comb_real : (2 : ℝ) ^ L * (w : ℝ) ^ 2 * (m : ℝ) ≤ 2050 * (x : ℝ) := by
    exact_mod_cast h_comb_nat
  have hlog2_nonneg : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have h2L_pos : (0 : ℝ) < (2 : ℝ) ^ L := by positivity
  have h_prod : (2 : ℝ) ^ L * ((w : ℝ) ^ 2 * ((m : ℝ) * Real.log 2)) ≤
      (2 : ℝ) ^ L * (ε ^ 2 * (x : ℝ)) := by
    calc
      (2 : ℝ) ^ L * ((w : ℝ) ^ 2 * ((m : ℝ) * Real.log 2))
          = ((2 : ℝ) ^ L * (w : ℝ) ^ 2 * (m : ℝ)) * Real.log 2 := by ring
      _ ≤ (2050 * (x : ℝ)) * Real.log 2 :=
          mul_le_mul_of_nonneg_right h_comb_real hlog2_nonneg
      _ = (2050 * Real.log 2) * (x : ℝ) := by ring
      _ ≤ (ε ^ 2 * (2 : ℝ) ^ L) * (x : ℝ) :=
          mul_le_mul_of_nonneg_right hL_bound hx_pos.le
      _ = (2 : ℝ) ^ L * (ε ^ 2 * (x : ℝ)) := by ring
  have h_cancel : (w : ℝ) ^ 2 * Real.log (x : ℝ) ≤ ε ^ 2 * (x : ℝ) := by
    rw [hlog_x]
    exact le_of_mul_le_mul_left h_prod h2L_pos
  have h_sq_le : lhs ^ 2 ≤ ε ^ 2 := by
    rw [hlhs_sq, div_mul_eq_mul_div, div_le_iff₀ hx_pos]
    exact h_cancel
  nlinarith

end OMA.R_Erdos1191_erdos_1191_parts_i_R1
