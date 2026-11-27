import FormalConjectures.ErdosProblems.«651»

/-!
Fix the number of monochromatic clusters in the proof of Pohoata and
Zakharov, Section 3. Their terminal estimate bounds the size of a bad
configuration by t to the power Cn/t. General-position projection transfers
the resulting forcing thresholds to higher dimensions.
-/
-- Credit: @marcusbuffett
open Filter Erdos651
open scoped EuclideanGeometry

namespace OMA.R_Erdos651_erdos_651_variants_pohoata_zakharov_R1

def H1 : Prop :=
  ∃ C > (0 : ℝ), ∀ t : ℕ, 2 ≤ t → ∀ᶠ n : ℕ in atTop,
    ∀ X : Finset (ℝ^3), IsInGeneralPosition X → ¬ HasConvexSubset n X →
      (X.card : ℝ) ≤ (t : ℝ) ^ (C * n / t)

def H2 : Prop :=
  ∀ k n N : ℕ, 3 ≤ k → N ∈ cardSet k n → N ∈ cardSet (k+1) n

theorem main : H1 → H2 → type_of% @Erdos651.erdos_651.variants.pohoata_zakharov := by
  intro hg hp k hk ε hε
  obtain ⟨C, hC, hg⟩ := hg
  have hl : Tendsto (fun t : ℕ => Real.log t / (t : ℝ)) atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have he := hl.eventually_lt_const (show 0 < Real.log 2 * (ε / 2) / C by positivity)
  obtain ⟨t, ht, ht'⟩ := (he.and (eventually_ge_atTop 2)).exists
  have ht0 : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hcoeff : Real.log t * C / t ≤ Real.log 2 * (ε / 2) := by
    have hh := (lt_div_iff₀ hC).mp ht
    calc
      _ = (Real.log t / (t : ℝ)) * C := by ring
      _ ≤ _ := hh.le
  have hnlim : ∀ᶠ n : ℕ in atTop, (2 : ℝ) / ε ≤ n :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop _
  filter_upwards [hg t ht', hnlim] with n hgeom hn
  let B := (t : ℝ) ^ (C * n / t)
  let M := ⌊B⌋₊ + 1
  have hM : M ∈ cardSet 3 n := by
    intro X hX hsize
    by_contra hbad
    have := hgeom X hX hbad
    have hle : (M : ℝ) ≤ X.card := by exact_mod_cast hsize
    dsimp [M] at hle
    push_cast at hle
    linarith [Nat.lt_floor_add_one B]
  have hall : M ∈ cardSet k n := by
    induction k, hk using Nat.le_induction with
    | base => exact hM
    | succ d hd ih => exact hp d n M hd ih
  have hB : B ≤ (2 : ℝ)^(ε / 2 * n) := by
    dsimp [B]
    rw [Real.rpow_def_of_pos ht0, Real.rpow_def_of_pos (by norm_num)]
    apply Real.exp_le_exp.mpr
    calc
      _ = (Real.log t * C / t) * n := by ring
      _ ≤ (Real.log 2 * (ε/2)) * n := mul_le_mul_of_nonneg_right hcoeff (Nat.cast_nonneg n)
      _ = _ := by ring
  have hone : 1 ≤ ε / 2 * n := by
    have h := (div_le_iff₀ hε).mp hn
    linarith
  have htwo : 2 ≤ (2 : ℝ)^(ε / 2 * n) := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hone
  calc
    (f k n : ℝ) ≤ M := by exact_mod_cast f_le hall
    _ ≤ B + 1 := by
      dsimp [M]; push_cast
      have hfloor : (⌊B⌋₊ : ℝ) ≤ B := Nat.floor_le (Real.rpow_nonneg ht0.le _)
      linarith
    _ ≤ 2 * (2 : ℝ)^(ε / 2 * n) := by linarith
    _ ≤ (2 : ℝ)^(ε / 2 * n) * (2 : ℝ)^(ε / 2 * n) := by gcongr
    _ = _ := by rw [← Real.rpow_add (by norm_num)]; congr 1; ring

end OMA.R_Erdos651_erdos_651_variants_pohoata_zakharov_R1

