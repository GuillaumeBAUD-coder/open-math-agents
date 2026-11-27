import OMAReductions.R_FlintCooksonHills_cookson_hills_series_converges_R1
import Mathlib.Tactic

private noncomputable def flintDelta (α : ℝ) (q : ℕ) : ℝ :=
  (q : ℝ) * α - (round ((q : ℝ) * α) : ℝ)

private lemma sum_range_two_pow {g : ℕ → ℝ} (hg0 : g 0 = 0) (K : ℕ) :
    ∑ q ∈ Finset.range (2 ^ K), g q =
      ∑ k ∈ Finset.range K, ∑ q ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)), g q := by
  induction K with
  | zero => simp [hg0]
  | succ K ih =>
    have hle : 2 ^ K ≤ 2 ^ (K + 1) :=
      Nat.pow_le_pow_right (by norm_num) (Nat.le_succ K)
    rw [← Finset.sum_range_add_sum_Ico g hle, ih, Finset.sum_range_succ]

private lemma summable_of_dyadic_blocks {g : ℕ → ℝ} (hg0 : g 0 = 0)
    (hgnn : ∀ q, 0 ≤ g q)
    (hB : Summable (fun k : ℕ => ∑ q ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)), g q)) :
    Summable g := by
  refine summable_of_sum_range_le hgnn (c := ∑' k : ℕ, ∑ q ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)), g q)
    (fun N => ?_)
  have hsub : Finset.range N ⊆ Finset.range (2 ^ N) :=
    Finset.range_mono (Nat.le_of_lt Nat.lt_two_pow_self)
  calc
    ∑ q ∈ Finset.range N, g q
      ≤ ∑ q ∈ Finset.range (2 ^ N), g q :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun q _ _ => hgnn q)
    _ = ∑ k ∈ Finset.range N, ∑ q ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)), g q :=
        sum_range_two_pow hg0 N
    _ ≤ ∑' k : ℕ, ∑ q ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)), g q :=
        hB.sum_le_tsum (Finset.range N) (fun k _ => Finset.sum_nonneg (fun q _ => hgnn q))

private lemma rpow_le_rpow_of_le_of_nonpos {x y z : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hz : z ≤ 0) :
    y ^ z ≤ x ^ z := by
  have hy : 0 < y := hx.trans_le hxy
  rw [show z = -(-z) by ring, Real.rpow_neg hy.le, Real.rpow_neg hx.le, ← one_div, ← one_div]
  exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos hx (-z))
    (Real.rpow_le_rpow hx.le hxy (by linarith))

private lemma sum_inv_sq_le_of_separated (S : Finset ℕ) (u : ℕ → ℝ) (L : ℝ) (hL : 0 < L)
    (hlow : ∀ q ∈ S, L ≤ u q)
    (hsep : ∀ q₁ ∈ S, ∀ q₂ ∈ S, q₁ ≠ q₂ → L ≤ |u q₁ - u q₂|) :
    ∑ q ∈ S, 1 / (u q) ^ 2 ≤ (1 / L ^ 2) * (∑' j : ℕ, 1 / (j : ℝ) ^ 2) := by
  let m : ℕ → ℕ := fun q => ⌊u q / L⌋₊
  let g : ℕ → ℝ := fun j => 1 / (j : ℝ) ^ 2
  have hg_sum : Summable g := Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hinj : ∀ q₁ ∈ S, ∀ q₂ ∈ S, m q₁ = m q₂ → q₁ = q₂ := by
    intro q₁ hq₁ q₂ hq₂ hm
    by_contra hne
    have hgap : L ≤ |u q₁ - u q₂| := hsep q₁ hq₁ q₂ hq₂ hne
    have hu₁ : 0 ≤ u q₁ / L := div_nonneg (hL.le.trans (hlow q₁ hq₁)) hL.le
    have hu₂ : 0 ≤ u q₂ / L := div_nonneg (hL.le.trans (hlow q₂ hq₂)) hL.le
    have h1_lo : (m q₁ : ℝ) ≤ u q₁ / L := Nat.floor_le hu₁
    have h1_hi : u q₁ / L < (m q₁ : ℝ) + 1 := Nat.lt_floor_add_one (u q₁ / L)
    have h2_lo : (m q₂ : ℝ) ≤ u q₂ / L := Nat.floor_le hu₂
    have h2_hi : u q₂ / L < (m q₂ : ℝ) + 1 := Nat.lt_floor_add_one (u q₂ / L)
    have hmR : (m q₁ : ℝ) = (m q₂ : ℝ) := by exact_mod_cast hm
    have hdiff_lt : |u q₁ / L - u q₂ / L| < 1 := abs_lt.mpr ⟨by linarith, by linarith⟩
    have hdiv_eq : |u q₁ / L - u q₂ / L| = |u q₁ - u q₂| / L := by
      rw [← sub_div, abs_div, abs_of_pos hL]
    rw [hdiv_eq, div_lt_one hL] at hdiff_lt
    linarith
  have hterm : ∀ q ∈ S, 1 / (u q) ^ 2 ≤ (1 / L ^ 2) * g (m q) := by
    intro q hq
    have hq_lo : L ≤ u q := hlow q hq
    have huq_div : 1 ≤ u q / L := (one_le_div hL).mpr hq_lo
    have hm_one : 1 ≤ m q := Nat.le_floor (by exact_mod_cast huq_div)
    have hm_posR : (0 : ℝ) < (m q : ℝ) := by exact_mod_cast hm_one
    have hm_le : (m q : ℝ) * L ≤ u q :=
      (le_div_iff₀ hL).mp (Nat.floor_le (div_nonneg (hL.le.trans hq_lo) hL.le))
    have hsq : (m q : ℝ) ^ 2 * L ^ 2 ≤ (u q) ^ 2 := by
      calc
        (m q : ℝ) ^ 2 * L ^ 2 = ((m q : ℝ) * L) ^ 2 := by ring
        _ ≤ (u q) ^ 2 := pow_le_pow_left₀ (by positivity) hm_le 2
    calc
      1 / (u q) ^ 2 ≤ 1 / ((m q : ℝ) ^ 2 * L ^ 2) :=
        one_div_le_one_div_of_le (by positivity) hsq
      _ = (1 / L ^ 2) * g (m q) := by
        dsimp [g]
        ring
  calc
    ∑ q ∈ S, 1 / (u q) ^ 2
      ≤ ∑ q ∈ S, (1 / L ^ 2) * g (m q) := Finset.sum_le_sum hterm
    _ = (1 / L ^ 2) * ∑ q ∈ S, g (m q) := (Finset.mul_sum S _ _).symm
    _ = (1 / L ^ 2) * ∑ j ∈ S.image m, g j := by rw [Finset.sum_image hinj]
    _ ≤ (1 / L ^ 2) * ∑' j : ℕ, g j :=
      mul_le_mul_of_nonneg_left
        (hg_sum.sum_le_tsum (S.image m) (fun j _ => by positivity)) (by positivity)

private lemma flint_gap_lower {α c ν : ℝ} (hc : 0 < c) (hν1 : 1 < ν)
    (hbound : ∀ q : ℕ, 0 < q → c * (q : ℝ) ^ (1 - ν) ≤ |flintDelta α q|)
    (k : ℕ) :
    (∀ d : ℕ, 0 < d → d ≤ 2 ^ (k + 1) →
      c * ((2 ^ (k + 1) : ℕ) : ℝ) ^ (1 - ν) ≤ |flintDelta α d|) ∧
    (∀ q₁ ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)),
      ∀ q₂ ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)),
      q₁ ≠ q₂ →
      c * ((2 ^ (k + 1) : ℕ) : ℝ) ^ (1 - ν) ≤ |flintDelta α q₁ - flintDelta α q₂|) := by
  have hlow_d : ∀ d : ℕ, 0 < d → d ≤ 2 ^ (k + 1) →
      c * ((2 ^ (k + 1) : ℕ) : ℝ) ^ (1 - ν) ≤ |flintDelta α d| := by
    intro d hd0 hd1
    have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd0
    have hdle : (d : ℝ) ≤ ((2 ^ (k + 1) : ℕ) : ℝ) := by exact_mod_cast hd1
    have hrpow : ((2 ^ (k + 1) : ℕ) : ℝ) ^ (1 - ν) ≤ (d : ℝ) ^ (1 - ν) :=
      rpow_le_rpow_of_le_of_nonpos hdR hdle (by linarith)
    exact (mul_le_mul_of_nonneg_left hrpow hc.le).trans (hbound d hd0)
  refine ⟨hlow_d, ?_⟩
  have hlt_case : ∀ q₁ q₂ : ℕ,
      q₁ ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)) →
      q₂ ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)) →
      q₂ < q₁ →
      c * ((2 ^ (k + 1) : ℕ) : ℝ) ^ (1 - ν) ≤ |flintDelta α q₁ - flintDelta α q₂| := by
    intro q₁ q₂ hq₁ hq₂ hlt
    rw [Finset.mem_Ico] at hq₁ hq₂
    set d : ℕ := q₁ - q₂
    have hd0 : 0 < d := by omega
    have hd1 : d ≤ 2 ^ (k + 1) := by omega
    let z : ℤ := round ((q₁ : ℝ) * α) - round ((q₂ : ℝ) * α)
    have hround : |flintDelta α d| ≤ |(d : ℝ) * α - (z : ℝ)| :=
      round_le ((d : ℝ) * α) z
    have hcast_d : (d : ℝ) = (q₁ : ℝ) - (q₂ : ℝ) := by
      exact Nat.cast_sub (Nat.le_of_lt hlt)
    have hdiff : (d : ℝ) * α - (z : ℝ) = flintDelta α q₁ - flintDelta α q₂ := by
      simp only [flintDelta, z, hcast_d, Int.cast_sub]
      ring
    rw [hdiff] at hround
    exact (hlow_d d hd0 hd1).trans hround
  intro q₁ hq₁ q₂ hq₂ hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · rw [abs_sub_comm]
    exact hlt_case q₂ q₁ hq₂ hq₁ hlt
  · exact hlt_case q₁ q₂ hq₁ hq₂ hgt

theorem prove_Flint_H2 :
    ∀ α c ν : ℝ, 0 < c → 1 < ν → ν < 5 / 2 →
      (∀ q : ℕ, 0 < q →
        c * (q : ℝ) ^ (1 - ν) ≤ |(q : ℝ) * α - (round ((q : ℝ) * α) : ℝ)|) →
      Summable (fun q : ℕ =>
        1 / ((q : ℝ) ^ 3 * |(q : ℝ) * α - (round ((q : ℝ) * α) : ℝ)| ^ 2)) := by
  intro α c ν hc hν1 hν2 hbound
  change Summable (fun q : ℕ => 1 / ((q : ℝ) ^ 3 * |flintDelta α q| ^ 2))
  let f : ℕ → ℝ := fun q => 1 / ((q : ℝ) ^ 3 * |flintDelta α q| ^ 2)
  have hf0 : f 0 = 0 := by simp [f]
  have hfnn : ∀ q, 0 ≤ f q := fun q => by dsimp [f]; positivity
  apply summable_of_dyadic_blocks hf0 hfnn
  let P : ℝ := ∑' j : ℕ, 1 / (j : ℝ) ^ 2
  have hPnn : 0 ≤ P := tsum_nonneg (fun j => by positivity)
  let C : ℝ := (2 * P / c ^ 2) * (2 : ℝ) ^ (2 * ν - 2)
  let r : ℝ := (2 : ℝ) ^ (2 * ν - 5)
  have hr_nn : 0 ≤ r := by dsimp [r]; positivity
  have hr_lt : r < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 2) (by linarith)
  have hgeom : Summable (fun k : ℕ => C * r ^ k) :=
    (summable_geometric_of_lt_one hr_nn hr_lt).mul_left C
  refine Summable.of_nonneg_of_le
    (fun k => Finset.sum_nonneg (fun q _ => hfnn q))
    (fun k => ?_) hgeom
  let Ik : Finset ℕ := Finset.Ico (2 ^ k) (2 ^ (k + 1))
  let L : ℝ := c * ((2 ^ (k + 1) : ℕ) : ℝ) ^ (1 - ν)
  have hL : 0 < L := by
    dsimp [L]
    exact mul_pos hc (Real.rpow_pos_of_pos (by positivity) _)
  obtain ⟨hlow_d, hsep_Ik⟩ := flint_gap_lower hc hν1 hbound k
  have hlow_Ik : ∀ q ∈ Ik, L ≤ |flintDelta α q| := by
    intro q hq
    have hq_mem := Finset.mem_Ico.mp hq
    have h2k_pos : 0 < 2 ^ k := Nat.pos_of_ne_zero (by positivity)
    exact hlow_d q (by omega) (by omega)
  let Spos : Finset ℕ := Ik.filter (fun q => 0 ≤ flintDelta α q)
  let Sneg : Finset ℕ := Ik.filter (fun q => ¬ 0 ≤ flintDelta α q)
  have hSpos : ∑ q ∈ Spos, 1 / |flintDelta α q| ^ 2 ≤ (1 / L ^ 2) * P := by
    refine sum_inv_sq_le_of_separated Spos (fun q => |flintDelta α q|) L hL
      (fun q hq => hlow_Ik q (Finset.mem_of_mem_filter q hq)) ?_
    intro q₁ hq₁ q₂ hq₂ hne
    have h1 := (Finset.mem_filter.mp hq₁).2
    have h2 := (Finset.mem_filter.mp hq₂).2
    rw [abs_of_nonneg h1, abs_of_nonneg h2]
    exact hsep_Ik q₁ (Finset.mem_of_mem_filter q₁ hq₁) q₂ (Finset.mem_of_mem_filter q₂ hq₂) hne
  have hSneg : ∑ q ∈ Sneg, 1 / |flintDelta α q| ^ 2 ≤ (1 / L ^ 2) * P := by
    refine sum_inv_sq_le_of_separated Sneg (fun q => |flintDelta α q|) L hL
      (fun q hq => hlow_Ik q (Finset.mem_of_mem_filter q hq)) ?_
    intro q₁ hq₁ q₂ hq₂ hne
    have h1 : flintDelta α q₁ < 0 := lt_of_not_ge (Finset.mem_filter.mp hq₁).2
    have h2 : flintDelta α q₂ < 0 := lt_of_not_ge (Finset.mem_filter.mp hq₂).2
    rw [abs_of_neg h1, abs_of_neg h2,
      show -flintDelta α q₁ - -flintDelta α q₂ = -(flintDelta α q₁ - flintDelta α q₂) by ring,
      abs_neg]
    exact hsep_Ik q₁ (Finset.mem_of_mem_filter q₁ hq₁) q₂ (Finset.mem_of_mem_filter q₂ hq₂) hne
  have hsum_Ik : ∑ q ∈ Ik, 1 / |flintDelta α q| ^ 2 ≤ 2 * P / L ^ 2 := by
    have hsplit := (Finset.sum_filter_add_sum_filter_not Ik (fun q => 0 ≤ flintDelta α q)
      (fun q => 1 / |flintDelta α q| ^ 2)).symm
    calc
      ∑ q ∈ Ik, 1 / |flintDelta α q| ^ 2
        = (∑ q ∈ Spos, 1 / |flintDelta α q| ^ 2) + ∑ q ∈ Sneg, 1 / |flintDelta α q| ^ 2 := hsplit
      _ ≤ (1 / L ^ 2) * P + (1 / L ^ 2) * P := add_le_add hSpos hSneg
      _ = 2 * P / L ^ 2 := by ring
  have hterm_Ik : ∀ q ∈ Ik, f q ≤ (1 / (((2 : ℝ) ^ k) ^ 3)) * (1 / |flintDelta α q| ^ 2) := by
    intro q hq
    have hq_mem := Finset.mem_Ico.mp hq
    have h2k_pos : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
    have h2k_le : (2 : ℝ) ^ k ≤ (q : ℝ) := by exact_mod_cast hq_mem.1
    have hcube : ((2 : ℝ) ^ k) ^ 3 ≤ (q : ℝ) ^ 3 := pow_le_pow_left₀ h2k_pos.le h2k_le 3
    have hδ_pos : 0 < |flintDelta α q| := hL.trans_le (hlow_Ik q hq)
    dsimp [f]
    calc
      1 / ((q : ℝ) ^ 3 * |flintDelta α q| ^ 2)
        ≤ 1 / (((2 : ℝ) ^ k) ^ 3 * |flintDelta α q| ^ 2) :=
          one_div_le_one_div_of_le (by positivity)
            (mul_le_mul_of_nonneg_right hcube (by positivity))
      _ = (1 / (((2 : ℝ) ^ k) ^ 3)) * (1 / |flintDelta α q| ^ 2) := by ring
  have hB_bound : ∑ q ∈ Ik, f q ≤ (1 / (((2 : ℝ) ^ k) ^ 3)) * (2 * P / L ^ 2) := by
    calc
      ∑ q ∈ Ik, f q
        ≤ ∑ q ∈ Ik, (1 / (((2 : ℝ) ^ k) ^ 3)) * (1 / |flintDelta α q| ^ 2) :=
          Finset.sum_le_sum hterm_Ik
      _ = (1 / (((2 : ℝ) ^ k) ^ 3)) * ∑ q ∈ Ik, 1 / |flintDelta α q| ^ 2 :=
          (Finset.mul_sum Ik _ _).symm
      _ ≤ (1 / (((2 : ℝ) ^ k) ^ 3)) * (2 * P / L ^ 2) :=
          mul_le_mul_of_nonneg_left hsum_Ik (by positivity)
  have halg : (1 / (((2 : ℝ) ^ k) ^ 3)) * (2 * P / L ^ 2) = C * r ^ k := by
    have h2pos : (0 : ℝ) < 2 := by norm_num
    have h2nn : (0 : ℝ) ≤ 2 := by norm_num
    have hL_eq : L ^ 2 = c ^ 2 * (2 : ℝ) ^ ((2 - 2 * ν) * ((k : ℝ) + 1)) := by
      dsimp [L]
      rw [mul_pow, Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast (2 : ℝ) (k + 1),
        ← Real.rpow_mul h2nn, sq ((2 : ℝ) ^ _), ← Real.rpow_add h2pos]
      congr 2
      push_cast
      ring
    have h2k3 : 1 / (((2 : ℝ) ^ k) ^ 3) = (2 : ℝ) ^ (-(3 * (k : ℝ))) := by
      rw [← pow_mul', ← Real.rpow_natCast (2 : ℝ) (3 * k), one_div, ← Real.rpow_neg h2nn]
      push_cast
      rfl
    have hrk : r ^ k = (2 : ℝ) ^ ((2 * ν - 5) * (k : ℝ)) := by
      dsimp [r]
      rw [← Real.rpow_natCast _ k, ← Real.rpow_mul h2nn]
    have hdiv : 2 * P / L ^ 2 = (2 * P / c ^ 2) * (2 : ℝ) ^ (-((2 - 2 * ν) * ((k : ℝ) + 1))) := by
      rw [hL_eq, div_eq_mul_inv (2 * P), mul_inv, ← Real.rpow_neg h2nn, div_eq_mul_inv (2 * P)]
      ring
    calc
      (1 / (((2 : ℝ) ^ k) ^ 3)) * (2 * P / L ^ 2)
        = (2 : ℝ) ^ (-(3 * (k : ℝ))) *
            ((2 * P / c ^ 2) * (2 : ℝ) ^ (-((2 - 2 * ν) * ((k : ℝ) + 1)))) := by
          rw [h2k3, hdiv]
      _ = (2 * P / c ^ 2) *
            ((2 : ℝ) ^ (-(3 * (k : ℝ))) * (2 : ℝ) ^ (-((2 - 2 * ν) * ((k : ℝ) + 1)))) := by ring
      _ = (2 * P / c ^ 2) *
            (2 : ℝ) ^ (-(3 * (k : ℝ)) + -((2 - 2 * ν) * ((k : ℝ) + 1))) := by
          rw [← Real.rpow_add h2pos]
      _ = (2 * P / c ^ 2) *
            (2 : ℝ) ^ ((2 * ν - 2) + (2 * ν - 5) * (k : ℝ)) := by
          congr 2
          ring
      _ = (2 * P / c ^ 2) *
            ((2 : ℝ) ^ (2 * ν - 2) * (2 : ℝ) ^ ((2 * ν - 5) * (k : ℝ))) := by
          rw [Real.rpow_add h2pos]
      _ = C * r ^ k := by
          dsimp [C]
          rw [hrk, mul_assoc]
  exact hB_bound.trans_eq halg

theorem OMA.solution : OMA.R_FlintCooksonHills_cookson_hills_series_converges_R1.H2 :=
  prove_Flint_H2
