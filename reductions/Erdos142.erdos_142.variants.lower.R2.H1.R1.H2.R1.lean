import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2_H1_R1

-- Reduction Erdos142.erdos_142.variants.lower.R2.H1.R1.H2.R1 of step Erdos142.erdos_142.variants.lower.R2.H1.R1.H2
-- Credit: @TomsBack

/-!
# Summable extremal densities from a density gain under squaring the scale

The target is step H2 of reduction R2.H1.R1 of Erdős 142: for every k at least four the
normalized extremal numbers r_k(4^j) / 4^j are summable. The hypotheses say that squaring the
scale along a tower N₀^(2^m) gains a density factor 2^(1+ε) for some ε > 0 (H1 for k = 4,
H2 for every k at least five). Iterating the gain along the tower gives a density at most
(2^m)^(-(1+ε)) at the scale N₀^(2^m), whose logarithm is 2^m log N₀. Subadditivity of r_k
transfers this bound to every power of four between consecutive tower scales, so that
r_k(4^j) / 4^j is at most a constant times j^(-(1+ε)), and the p-series test concludes.
The subadditivity facts are those of reduction R2 of Erdős 142.
-/

namespace OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R1

open Erdos142 Filter

/-- Squaring the scale gains density factor 2^(1+ε) along a tower, for 4-term progressions. -/
def H1 : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ m : ℕ,
    (r 4 ((N₀ ^ 2 ^ m) ^ 2) : ℝ) * (2 : ℝ) ^ (1 + ε) ≤ (r 4 (N₀ ^ 2 ^ m) : ℝ) * ((N₀ ^ 2 ^ m : ℕ) : ℝ)

/-- The same gain for every progression length at least five. -/
def H2 : Prop :=
  ∀ k : ℕ, 5 ≤ k → ∃ ε : ℝ, 0 < ε ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ m : ℕ,
    (r k ((N₀ ^ 2 ^ m) ^ 2) : ℝ) * (2 : ℝ) ^ (1 + ε) ≤ (r k (N₀ ^ 2 ^ m) : ℝ) * ((N₀ ^ 2 ^ m : ℕ) : ℝ)

lemma rk_le_self {k : ℕ} (hk : 1 < k) (N : ℕ) : r k N ≤ N := by
  obtain ⟨S, hS, -, hcard⟩ := OMA.R_Erdos142_erdos_142_variants_lower_R2.extremizer hk N
  rw [← hcard]
  simpa using Finset.card_le_card hS

lemma rk_mono (k : ℕ) : Monotone (r k) :=
  OMA.R_Erdos142_erdos_142_variants_lower_R2.maxCard_monotone k

lemma rk_mul_le {k : ℕ} (hk : 1 < k) (N q : ℕ) : r k (q * N) ≤ q * r k N := by
  induction q with
  | zero =>
    rw [zero_mul, zero_mul]
    exact rk_le_self hk 0
  | succ q ih =>
    rw [Nat.succ_mul, Nat.succ_mul]
    exact (OMA.R_Erdos142_erdos_142_variants_lower_R2.maxCard_add_le k (q * N) N).trans
      (Nat.add_le_add_right ih _)

lemma interp {k : ℕ} (hk : 1 < k) {M X : ℕ} (hM : 0 < M) (hMX : M ≤ X) :
    r k X * M ≤ 2 * X * r k M := by
  have hdm := Nat.div_add_mod' X M
  have hmod := Nat.mod_lt X hM
  have hqM : X / M * M ≤ X := Nat.div_mul_le_self X M
  set q := X / M with hq
  have hX : X ≤ (q + 1) * M := by
    rw [Nat.add_mul, one_mul]
    omega
  have h1 : r k X ≤ (q + 1) * r k M :=
    (rk_mono k hX).trans (rk_mul_le hk M (q + 1))
  calc r k X * M ≤ (q + 1) * r k M * M := Nat.mul_le_mul_right _ h1
    _ = (q * M + M) * r k M := by ring
    _ ≤ 2 * X * r k M := Nat.mul_le_mul_right _ (by omega)

lemma tower {k : ℕ} (hk : 1 < k) {g : ℝ} (hg0 : 0 ≤ g) {N₀ : ℕ}
    (hgain : ∀ m : ℕ, (r k ((N₀ ^ 2 ^ m) ^ 2) : ℝ) * g ≤
      (r k (N₀ ^ 2 ^ m) : ℝ) * ((N₀ ^ 2 ^ m : ℕ) : ℝ)) :
    ∀ m : ℕ, (r k (N₀ ^ 2 ^ m) : ℝ) * g ^ m ≤ ((N₀ ^ 2 ^ m : ℕ) : ℝ)
  | 0 => by
    simp only [pow_zero, pow_one, mul_one]
    exact_mod_cast rk_le_self hk N₀
  | m + 1 => by
    have e : N₀ ^ 2 ^ (m + 1) = (N₀ ^ 2 ^ m) ^ 2 := by rw [pow_succ, pow_mul]
    have ih := tower hk hg0 hgain m
    have h := hgain m
    rw [e]
    have hM : (0 : ℝ) ≤ ((N₀ ^ 2 ^ m : ℕ) : ℝ) := Nat.cast_nonneg _
    have hgm : (0 : ℝ) ≤ g ^ m := pow_nonneg hg0 m
    have hcast : (((N₀ ^ 2 ^ m) ^ 2 : ℕ) : ℝ) = ((N₀ ^ 2 ^ m : ℕ) : ℝ) * ((N₀ ^ 2 ^ m : ℕ) : ℝ) := by
      push_cast; ring
    rw [hcast, pow_succ g m]
    nlinarith [mul_le_mul_of_nonneg_right h hgm, mul_le_mul_of_nonneg_left ih hM]

/-- The density at the scale 4^n is at most a constant times n^(-(1+ε)). -/
lemma dens_bound {k : ℕ} (hk : 1 < k) {ε : ℝ} (hε : 0 < ε) {N₀ : ℕ} (hN₀ : 2 ≤ N₀)
    (hg : ∀ m : ℕ, (r k ((N₀ ^ 2 ^ m) ^ 2) : ℝ) * (2 : ℝ) ^ (1 + ε) ≤
      (r k (N₀ ^ 2 ^ m) : ℝ) * ((N₀ ^ 2 ^ m : ℕ) : ℝ))
    (n : ℕ) (hn : N₀ ≤ n) :
    (r k (4 ^ n) : ℝ) / (4 : ℝ) ^ n ≤
      2 * (2 * (N₀ : ℝ)) ^ (1 + ε) * ((n : ℝ) ^ (1 + ε))⁻¹ := by
  set g : ℝ := (2 : ℝ) ^ (1 + ε) with hgdef
  have hgpos : 0 < g := by
    rw [hgdef]
    exact Real.rpow_pos_of_pos two_pos _
  have hex : ∃ m : ℕ, 4 ^ n < N₀ ^ 2 ^ (m + 1) := by
    refine ⟨n, ?_⟩
    have h4 : 4 ^ n = 2 ^ (2 * n) := by rw [pow_mul]; norm_num
    have h2n : 2 * n < 2 ^ (n + 1) := by
      rw [pow_succ]
      have := Nat.lt_two_pow_self (n := n)
      omega
    rw [h4]
    calc 2 ^ (2 * n) < 2 ^ 2 ^ (n + 1) := Nat.pow_lt_pow_right (by norm_num) h2n
      _ ≤ N₀ ^ 2 ^ (n + 1) := Nat.pow_le_pow_left hN₀ _
  set m := Nat.find hex with hmdef
  have hm : 4 ^ n < N₀ ^ 2 ^ (m + 1) := Nat.find_spec hex
  have hM : N₀ ^ 2 ^ m ≤ 4 ^ n := by
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · rw [h0, pow_zero, pow_one]
      exact hn.trans (Nat.lt_pow_self (by norm_num)).le
    · have := Nat.find_min hex (show m - 1 < m by omega)
      rw [show m - 1 + 1 = m by omega] at this
      omega
  have hnlt : n < N₀ * 2 ^ (m + 1) := by
    have h1 : N₀ ^ 2 ^ (m + 1) ≤ 4 ^ (N₀ * 2 ^ (m + 1)) := by
      rw [pow_mul]
      exact Nat.pow_le_pow_left (Nat.lt_pow_self (by norm_num)).le _
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp (hm.trans_le h1)
  have hMpos : 0 < N₀ ^ 2 ^ m := by positivity
  have hint := interp hk hMpos hM
  have htow := tower hk hgpos.le hg m
  set Mr : ℝ := ((N₀ ^ 2 ^ m : ℕ) : ℝ) with hMr
  set R : ℝ := (r k (4 ^ n) : ℝ) with hR
  set A : ℝ := (r k (N₀ ^ 2 ^ m) : ℝ) with hA
  have hintr : R * Mr ≤ 2 * (4 : ℝ) ^ n * A := by
    have : ((r k (4 ^ n) * N₀ ^ 2 ^ m : ℕ) : ℝ) ≤ ((2 * 4 ^ n * r k (N₀ ^ 2 ^ m) : ℕ) : ℝ) :=
      by exact_mod_cast hint
    push_cast at this
    simpa [hMr, hR, hA] using this
  have hMrpos : 0 < Mr := by rw [hMr]; exact_mod_cast hMpos
  have hgm : 0 < g ^ m := pow_pos hgpos m
  have h4n : (0 : ℝ) < (4 : ℝ) ^ n := by positivity
  have hR0 : 0 ≤ R := Nat.cast_nonneg _
  have key : R * g ^ m ≤ 2 * (4 : ℝ) ^ n := by
    have : (R * g ^ m) * Mr ≤ (2 * (4 : ℝ) ^ n) * Mr := by
      nlinarith [mul_le_mul_of_nonneg_right hintr hgm.le, mul_le_mul_of_nonneg_left htow
        (show (0 : ℝ) ≤ 2 * (4 : ℝ) ^ n by positivity)]
    exact le_of_mul_le_mul_right this hMrpos
  have hnr : (n : ℝ) ≤ 2 * N₀ * (2 : ℝ) ^ m := by
    have : (n : ℝ) ≤ ((N₀ * 2 ^ (m + 1) : ℕ) : ℝ) := by exact_mod_cast hnlt.le
    push_cast at this
    rw [pow_succ] at this
    linarith
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hp1 : (0 : ℝ) ≤ 1 + ε := by linarith
  have hC : (0 : ℝ) ≤ (2 * (N₀ : ℝ)) ^ (1 + ε) := Real.rpow_nonneg (by positivity) _
  have hnp : (0 : ℝ) < (n : ℝ) ^ (1 + ε) := Real.rpow_pos_of_pos hn0 _
  have hpow : (n : ℝ) ^ (1 + ε) ≤ (2 * (N₀ : ℝ)) ^ (1 + ε) * g ^ m := by
    calc (n : ℝ) ^ (1 + ε) ≤ (2 * (N₀ : ℝ) * (2 : ℝ) ^ m) ^ (1 + ε) :=
          Real.rpow_le_rpow hn0.le hnr hp1
      _ = (2 * (N₀ : ℝ)) ^ (1 + ε) * ((2 : ℝ) ^ m) ^ (1 + ε) :=
          Real.mul_rpow (by positivity) (by positivity)
      _ = (2 * (N₀ : ℝ)) ^ (1 + ε) * g ^ m := by
          rw [hgdef, Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2)]
  have hfin : R * (n : ℝ) ^ (1 + ε) ≤ 2 * (2 * (N₀ : ℝ)) ^ (1 + ε) * (4 : ℝ) ^ n := by
    calc R * (n : ℝ) ^ (1 + ε) ≤ R * ((2 * (N₀ : ℝ)) ^ (1 + ε) * g ^ m) :=
          mul_le_mul_of_nonneg_left hpow hR0
      _ = (2 * (N₀ : ℝ)) ^ (1 + ε) * (R * g ^ m) := by ring
      _ ≤ (2 * (N₀ : ℝ)) ^ (1 + ε) * (2 * (4 : ℝ) ^ n) := mul_le_mul_of_nonneg_left key hC
      _ = 2 * (2 * (N₀ : ℝ)) ^ (1 + ε) * (4 : ℝ) ^ n := by ring
  rw [div_le_iff₀ h4n]
  calc R ≤ (2 * (2 * (N₀ : ℝ)) ^ (1 + ε) * (4 : ℝ) ^ n) / (n : ℝ) ^ (1 + ε) :=
        (le_div_iff₀ hnp).mpr hfin
    _ = 2 * (2 * (N₀ : ℝ)) ^ (1 + ε) * ((n : ℝ) ^ (1 + ε))⁻¹ * (4 : ℝ) ^ n := by ring

/-- A density gain along the tower makes the normalized extremal numbers summable. -/
lemma summable_of_gain {k : ℕ} (hk : 1 < k) {ε : ℝ} (hε : 0 < ε) {N₀ : ℕ} (hN₀ : 2 ≤ N₀)
    (hg : ∀ m : ℕ, (r k ((N₀ ^ 2 ^ m) ^ 2) : ℝ) * (2 : ℝ) ^ (1 + ε) ≤
      (r k (N₀ ^ 2 ^ m) : ℝ) * ((N₀ ^ 2 ^ m : ℕ) : ℝ)) :
    Summable (fun j : ℕ ↦ (r k (4 ^ j) : ℝ) / (4 : ℝ) ^ j) := by
  have hp : Summable (fun j : ℕ ↦ 2 * (2 * (N₀ : ℝ)) ^ (1 + ε) * ((j : ℝ) ^ (1 + ε))⁻¹) :=
    (Real.summable_nat_rpow_inv.mpr (by linarith)).mul_left _
  refine Summable.of_norm_bounded_eventually_nat hp ?_
  filter_upwards [eventually_ge_atTop N₀] with j hj
  rw [Real.norm_of_nonneg (by positivity)]
  exact dens_bound hk hε hN₀ hg j hj

theorem main : H1 → H2 → OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1.H2 := by
  intro h1 h2 k hk
  have hgain : ∃ ε : ℝ, 0 < ε ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ m : ℕ,
      (r k ((N₀ ^ 2 ^ m) ^ 2) : ℝ) * (2 : ℝ) ^ (1 + ε) ≤
        (r k (N₀ ^ 2 ^ m) : ℝ) * ((N₀ ^ 2 ^ m : ℕ) : ℝ) := by
    rcases eq_or_lt_of_le hk with rfl | hk5
    · exact h1
    · exact h2 k hk5
  obtain ⟨ε, hε, N₀, hN₀, hg⟩ := hgain
  exact summable_of_gain (by omega) hε hN₀ hg

end OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R1
