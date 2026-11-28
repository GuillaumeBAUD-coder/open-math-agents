import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H3_R2
import Mathlib.NumberTheory.Bertrand

-- Reduction Erdos142.erdos_142.variants.lower.R2.H1.R1.H2.R2.H3.R2.H1.R1 of step Erdos142.erdos_142.variants.lower.R2.H1.R1.H2.R2.H3.R2.H1
-- Credit: @jktcv2kz4f-cyber

/-!
# Prime-cyclic Bertrand reduction for stretched-exponential k-AP bounds (k ≥ 5)

We reduce the interval stretched-exponential upper bound
`r k N / N ≤ C * exp (-c * (log N) ^ e)` (`k ≥ 5`) to the corresponding prime-cyclic
bounds on `ZMod p`, split between `k = 5` (`H1`) and `k ≥ 6` (`H2`).

Given an extremal `k`-AP-free subset `S ⊆ [1, N]`, Bertrand's postulate supplies a prime
`p` with `2 * N < p ≤ 4 * N`. Reducing `S` modulo `p` preserves cardinality and forbids
nontrivial modular `k`-APs because consecutive differences in `[-(N - 1), N - 1]` cannot
wrap around modulo `p > 2 * N`. Monotonicity of `exp (-c * (log x) ^ e)` then transfers
the `ZMod p` bound back to `[1, N]` at the cost of a constant factor `4`.
-/

namespace OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H3_R2_H1_R1

open Erdos142 Filter Real

/-- Stretched-exponential 5-AP-free density bound on prime cyclic groups ZMod p. -/
def H1 : Prop :=
  ∃ C c e : ℝ, 0 < C ∧ 0 < c ∧ 0 < e ∧ ∀ᶠ p : ℕ in atTop, p.Prime →
    ∀ A : Finset (ZMod p),
      (¬ ∃ a d : ZMod p, d ≠ 0 ∧ ∀ i : ℕ, i < 5 → a + (i : ZMod p) * d ∈ A) →
      (A.card : ℝ) ≤ C * (p : ℝ) * Real.exp (-c * Real.log (p : ℝ) ^ e)

/-- Stretched-exponential k-AP-free density bound on prime cyclic groups ZMod p for k ≥ 6. -/
def H2 : Prop :=
  ∀ k : ℕ, 6 ≤ k → ∃ C c e : ℝ, 0 < C ∧ 0 < c ∧ 0 < e ∧ ∀ᶠ p : ℕ in atTop, p.Prime →
    ∀ A : Finset (ZMod p),
      (¬ ∃ a d : ZMod p, d ≠ 0 ∧ ∀ i : ℕ, i < k → a + (i : ZMod p) * d ∈ A) →
      (A.card : ℝ) ≤ C * (p : ℝ) * Real.exp (-c * Real.log (p : ℝ) ^ e)

lemma mod_ap_lift {k N p : ℕ} (hk : 2 ≤ k) (hp : 2 * N < p)
    {S : Finset ℕ} (hS : S ⊆ Finset.Icc 1 N)
    (hfree : ¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ S) :
    ¬ ∃ a d : ZMod p, d ≠ 0 ∧
      ∀ i : ℕ, i < k → a + (i : ZMod p) * d ∈ S.image (fun x : ℕ => (x : ZMod p)) := by
  rintro ⟨a, d, hd, hmem⟩
  have hlift : ∀ i : ℕ, i < k → ∃ x ∈ S, (x : ZMod p) = a + (i : ZMod p) * d := by
    intro i hi
    obtain ⟨x, hxS, hxEq⟩ := Finset.mem_image.mp (hmem i hi)
    exact ⟨x, hxS, hxEq⟩
  choose x hxS hxEq using hlift
  have hxBounds : ∀ i (hi : i < k), 1 ≤ x i hi ∧ x i hi ≤ N := fun i hi =>
    Finset.mem_Icc.mp (hS (hxS i hi))
  let d_int : ∀ i, i + 1 < k → ℤ := fun i hi => (x (i + 1) hi : ℤ) - (x i (by omega) : ℤ)
  have hdiff_mod : ∀ i (hi : i + 1 < k), (d_int i hi : ZMod p) = d := by
    intro i hi
    dsimp only [d_int]
    rw [Int.cast_sub, Int.cast_natCast, Int.cast_natCast, hxEq (i + 1) hi, hxEq i (by omega)]
    push_cast
    ring
  have hdiff_eq : ∀ i (hi : i + 1 < k), d_int i hi = d_int 0 (by omega) := by
    intro i hi
    have h0 : ((d_int i hi - d_int 0 (by omega) : ℤ) : ZMod p) = 0 := by
      rw [Int.cast_sub, hdiff_mod i hi, hdiff_mod 0 (by omega), sub_self]
    have hdvd : (p : ℤ) ∣ (d_int i hi - d_int 0 (by omega)) :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h0
    have hb1 := hxBounds (i + 1) hi
    have hb2 := hxBounds i (by omega)
    have hb3 := hxBounds 1 (by omega)
    have hb4 := hxBounds 0 (by omega)
    obtain ⟨q, hq⟩ := hdvd
    dsimp only [d_int] at hq ⊢
    have hq0 : q = 0 := by nlinarith
    rw [hq0, mul_zero] at hq
    omega
  set Δ : ℤ := d_int 0 (by omega)
  have hΔ_ne : Δ ≠ 0 := by
    intro h0
    have hd0 : d = 0 := by
      rw [← hdiff_mod 0 (by omega)]
      change (Δ : ZMod p) = 0
      rw [h0, Int.cast_zero]
    exact hd hd0
  have hlinear : ∀ i (hi : i < k), (x i hi : ℤ) = (x 0 (by omega) : ℤ) + (i : ℤ) * Δ := by
    intro i
    induction i with
    | zero =>
      intro hi
      simp
    | succ j ih =>
      intro hj
      have hstep := hdiff_eq j hj
      have hjprev := ih (by omega)
      push_cast
      linarith
  rcases lt_or_gt_of_ne hΔ_ne with hneg | hpos
  · apply hfree
    refine ⟨x (k - 1) (by omega), (-Δ).toNat, by omega, fun i hi => ?_⟩
    have hidx : k - 1 - i < k := by omega
    have hval : x (k - 1) (by omega) + i * (-Δ).toNat = x (k - 1 - i) hidx := by
      have h1 := hlinear (k - 1) (by omega)
      have h2 := hlinear (k - 1 - i) hidx
      have htoNat : ((-Δ).toNat : ℤ) = -Δ := Int.toNat_of_nonneg (by omega)
      have hsub : ((k - 1 - i : ℕ) : ℤ) = ((k - 1 : ℕ) : ℤ) - (i : ℤ) := by omega
      have hcast : ((x (k - 1) (by omega) + i * (-Δ).toNat : ℕ) : ℤ) =
          (x (k - 1 - i) hidx : ℤ) := by
        push_cast
        rw [htoNat, h1, h2, hsub]
        ring
      exact_mod_cast hcast
    rw [hval]
    exact hxS (k - 1 - i) hidx
  · apply hfree
    refine ⟨x 0 (by omega), Δ.toNat, by omega, fun i hi => ?_⟩
    have hval : x 0 (by omega) + i * Δ.toNat = x i hi := by
      have h1 := hlinear i hi
      have htoNat : (Δ.toNat : ℤ) = Δ := Int.toNat_of_nonneg (by omega)
      have hcast : ((x 0 (by omega) + i * Δ.toNat : ℕ) : ℤ) = (x i hi : ℤ) := by
        push_cast
        rw [htoNat, h1]
      exact_mod_cast hcast
    rw [hval]
    exact hxS i hi

lemma interval_of_zmod {k : ℕ} (hk : 2 ≤ k)
    (hz : ∃ C c e : ℝ, 0 < C ∧ 0 < c ∧ 0 < e ∧ ∀ᶠ p : ℕ in atTop, p.Prime →
      ∀ A : Finset (ZMod p),
        (¬ ∃ a d : ZMod p, d ≠ 0 ∧ ∀ i : ℕ, i < k → a + (i : ZMod p) * d ∈ A) →
        (A.card : ℝ) ≤ C * (p : ℝ) * Real.exp (-c * Real.log (p : ℝ) ^ e)) :
    ∃ C c e : ℝ, 0 < C ∧ 0 < c ∧ 0 < e ∧
      ∀ᶠ N : ℕ in atTop,
        (r k N : ℝ) / (N : ℝ) ≤ C * Real.exp (-c * Real.log (N : ℝ) ^ e) := by
  obtain ⟨C, c, e, hC, hc, he, hEv⟩ := hz
  obtain ⟨P₀, hP₀⟩ := eventually_atTop.mp hEv
  refine ⟨4 * C, c, e, by positivity, hc, he, ?_⟩
  filter_upwards [eventually_ge_atTop (max P₀ 2)] with N hN
  have hNP : P₀ ≤ N := (le_max_left _ _).trans hN
  have hN2 : 2 ≤ N := (le_max_right _ _).trans hN
  obtain ⟨p, hp_prime, hp_gt, hp_le⟩ :=
    Nat.exists_prime_lt_and_le_two_mul (2 * N) (by omega)
  have hp_ge : P₀ ≤ p := by omega
  obtain ⟨S, hSsub, hSfree, hScard⟩ :=
    OMA.R_Erdos142_erdos_142_variants_lower_R2.extremizer (by omega : 1 < k) N
  let A : Finset (ZMod p) := S.image (fun x : ℕ => (x : ZMod p))
  have hAcard : A.card = S.card := by
    apply Finset.card_image_of_injOn
    intro x hx y hy hxy
    have hxB := Finset.mem_Icc.mp (hSsub hx)
    have hyB := Finset.mem_Icc.mp (hSsub hy)
    have hxp : x < p := by omega
    have hyp : y < p := by omega
    have hval := congrArg ZMod.val hxy
    haveI : NeZero p := ⟨hp_prime.ne_zero⟩
    simpa [ZMod.val_natCast_of_lt hxp, ZMod.val_natCast_of_lt hyp] using hval
  have hAfree : ¬ ∃ a d : ZMod p, d ≠ 0 ∧ ∀ i : ℕ, i < k → a + (i : ZMod p) * d ∈ A :=
    mod_ap_lift hk hp_gt hSsub
      (OMA.R_Erdos142_erdos_142_variants_lower_R2.no_positive_step (by omega) hSfree)
  have hbound := hP₀ p hp_ge hp_prime A hAfree
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hp_leR : (p : ℝ) ≤ 4 * (N : ℝ) := by exact_mod_cast (show p ≤ 4 * N by omega)
  have hlog_le : Real.log (N : ℝ) ≤ Real.log (p : ℝ) :=
    Real.log_le_log hNpos (by exact_mod_cast (show N ≤ p by omega))
  have hlogN0 : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hrpow_le : Real.log (N : ℝ) ^ e ≤ Real.log (p : ℝ) ^ e :=
    Real.rpow_le_rpow hlogN0 hlog_le he.le
  have hexp_le : Real.exp (-c * Real.log (p : ℝ) ^ e) ≤ Real.exp (-c * Real.log (N : ℝ) ^ e) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hrk_le : (r k N : ℝ) ≤ 4 * C * (N : ℝ) * Real.exp (-c * Real.log (N : ℝ) ^ e) := by
    rw [← hScard, ← hAcard]
    calc
      (A.card : ℝ) ≤ C * (p : ℝ) * Real.exp (-c * Real.log (p : ℝ) ^ e) := hbound
      _ ≤ C * (4 * (N : ℝ)) * Real.exp (-c * Real.log (N : ℝ) ^ e) := by
        gcongr
      _ = 4 * C * (N : ℝ) * Real.exp (-c * Real.log (N : ℝ) ^ e) := by ring
  rw [div_le_iff₀ hNpos]
  linarith

theorem main :
    H1 → H2 → OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H3_R2.H1 := by
  intro h5 h6 k hk
  by_cases hk5 : k = 5
  · subst hk5
    exact interval_of_zmod (by decide) h5
  · exact interval_of_zmod (by omega) (h6 k (by omega))

end OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H3_R2_H1_R1
