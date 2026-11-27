import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1

/-!
# A finite density increment for progressions of length at least four

The sparse step seeks a denser restriction on an arithmetic progression.
The fixed-density step is qualitative Szemerédi. Iterating the first until
the second applies gives the eventual bound N / (log N)^2.

The invariant and its terminal case follow OpenAI, Quasipolynomial Bounds for
Arithmetic Progressions (openai/math, commit 4eaee8754825). The relevant
lemmas are subquadratic_patch_descent and fixed_density_terminal. The
extremizer and positive-step lemmas are from reduction R2 of Erdős 142.
Credit: @NicholasWierenga.
-/

namespace OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R1

open Erdos142 Filter Real
open scoped Topology

/-- Sparse finite sets admit an affine density increment preserving the log-log budget. -/
def H1 : Prop :=
  ∀ k : ℕ, 4 ≤ k →
    ∃ (β C T R₀ : ℝ), 0 < β ∧ β < 1 ∧ 0 < C ∧
      ∀ R : ℝ, R₀ ≤ R → ∀ (N : ℕ) (S : Finset ℕ),
        2 ≤ N → S ⊆ Finset.Icc 1 N → 0 < S.card →
          (¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ S) →
        let p := max 2 (Real.log (2 * (N : ℝ) / (S.card : ℝ)))
        T < p → C * p ^ β + R ≤ Real.log (Real.log (N : ℝ)) →
          ∃ (a q M : ℕ), 0 < q ∧ 2 ≤ M ∧
            (∀ i ∈ Finset.Icc 1 M, a + (i - 1) * q ∈ Finset.Icc 1 N) ∧
            let U := (Finset.Icc 1 M).filter (fun i ↦ a + (i - 1) * q ∈ S)
            let p' := max 2 (Real.log (2 * (M : ℝ) / (U.card : ℝ)))
            0 < U.card ∧ p' + 1 ≤ p ∧ C * p' ^ β + R ≤ Real.log (Real.log (M : ℝ))

/-- Fixed positive density forces a progression once the interval is long enough. -/
def H2 : Prop :=
  ∀ k : ℕ, 4 ≤ k → ∀ T : ℝ, ∃ Q : ℝ, ∀ (N : ℕ) (S : Finset ℕ),
    2 ≤ N → S ⊆ Finset.Icc 1 N → 0 < S.card →
    (¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ S) →
    max 2 (Real.log (2 * (N : ℝ) / (S.card : ℝ))) ≤ T →
      Real.log (Real.log (N : ℝ)) < Q

lemma no_positive_step {A : Set ℕ} {k : ℕ} (hk : 1 < k) (hfree : A.IsAPOfLengthFree k) :
    ¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ A := by
  rintro ⟨a, d, hd, hmem⟩
  let T := (Finset.range k).image fun i => a + i * d
  have hcard : T.card = k := by
    have hinj : Function.Injective (fun i : ℕ => a + i * d) := by
      intro x y h
      exact Nat.eq_of_mul_eq_mul_right hd (Nat.add_left_cancel h)
    simp [T, Finset.card_image_of_injective _ hinj]
  have hsub : (T : Set ℕ) ⊆ A := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    exact hmem i (Finset.mem_range.mp hi)
  have hap' : (T : Set ℕ).IsAPOfLength k := by
    refine ⟨a, d, by simp [hcard], ?_⟩
    ext x
    simp [T]
  have hle := hfree (T : Set ℕ) hsub hap'
  exact (not_le_of_gt hk) (by exact_mod_cast hle)

/-- The natural-number supremum defining the extremal cardinality is attained. -/
lemma extremizer {k : ℕ} (hk : 1 < k) (N : ℕ) :
    ∃ S : Finset ℕ, S ⊆ Finset.Icc 1 N ∧ (S : Set ℕ).IsAPOfLengthFree k ∧
      S.card = r k N := by
  let c : Set ℕ := {Finset.card S | (S) (_ : S ⊆ Finset.Icc 1 N)
    (_ : (S : Set ℕ).IsAPOfLengthFree k)}
  have hnon : c.Nonempty := by
    refine ⟨0, ∅, by simp, ?_, by simp⟩
    intro t ht hprogression
    have ht' : t = ∅ := Set.subset_empty_iff.mp (by simpa using ht)
    have hpos : 0 < (k : ℕ∞) := by exact_mod_cast (show 0 < k by omega)
    exact (Set.not_isAPOfLength_empty hpos (ht' ▸ hprogression)).elim
  have hbound : BddAbove c := by
    refine ⟨N, ?_⟩
    rintro _ ⟨S, hs, _, rfl⟩
    exact (Finset.card_mono hs).trans_eq (Nat.card_Icc 1 N)
  obtain ⟨S, hS, hfree, hcard⟩ := Nat.sSup_mem hnon hbound
  exact ⟨S, hS, hfree, hcard⟩

lemma eliminate_descent {X : Type} (p : X → ℝ) (P : X → Prop)
    (hp : ∀ x, 0 ≤ p x)
    (decrease : ∀ x, P x → ∃ y, P y ∧ p y + 1 ≤ p x) :
    ∀ x, ¬ P x := by
  suffices H : ∀ n : ℕ, ∀ x, P x → ⌊p x⌋₊ = n → False from
    fun x hx ↦ H _ x hx rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro x hx he
    obtain ⟨y, hy, hdrop⟩ := decrease x hx
    have hlt : ⌊p y⌋₊ < ⌊p x⌋₊ := (Nat.floor_lt (hp y)).mpr (by
      linarith [Nat.lt_floor_add_one (p x)])
    exact ih _ (by simpa only [he] using hlt) y hy rfl

lemma progression_preimage_free {k a q M : ℕ} {S : Finset ℕ}
    (hk : 4 ≤ k) (hq : 0 < q)
    (hfree : ¬ ∃ b d : ℕ, 0 < d ∧ ∀ i < k, b + i * d ∈ S) :
    ¬ ∃ b d : ℕ, 0 < d ∧ ∀ i < k,
      b + i * d ∈ (Finset.Icc 1 M).filter (fun j ↦ a + (j - 1) * q ∈ S) := by
  rintro ⟨b, d, hd, hAP⟩
  have hbase : b ∈ Finset.Icc 1 M := by
    simpa only [zero_mul, add_zero] using (Finset.mem_filter.mp (hAP 0 (by omega))).1
  have hb : 1 ≤ b := (Finset.mem_Icc.mp hbase).1
  refine hfree ⟨a + (b - 1) * q, d * q, Nat.mul_pos hd hq, fun i hi ↦ ?_⟩
  have hmem := (Finset.mem_filter.mp (hAP i hi)).2
  have he : b + i * d - 1 = b - 1 + i * d := by omega
  rw [he] at hmem
  simpa only [add_mul, Nat.add_assoc, Nat.mul_assoc] using hmem

lemma no_budget (hdesc : H1) (hterm : H2) {k : ℕ} (hk : 4 ≤ k) :
    ∃ (β C R : ℝ), 0 < β ∧ β < 1 ∧ 0 < C ∧
      ∀ (N : ℕ) (S : Finset ℕ), 2 ≤ N → S ⊆ Finset.Icc 1 N → 0 < S.card →
        (¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ S) →
        ¬ C * (max 2 (Real.log (2 * (N : ℝ) / (S.card : ℝ)))) ^ β + R ≤
          Real.log (Real.log (N : ℝ)) := by
  obtain ⟨β, C, T, R₀, hβ, hβ1, hC, hstep⟩ := hdesc k hk
  obtain ⟨Q, hstop⟩ := hterm k hk T
  let R := max R₀ Q
  refine ⟨β, C, R, hβ, hβ1, hC, ?_⟩
  let X := ℕ × Finset ℕ
  let p (x : X) := max 2 (Real.log (2 * (x.1 : ℝ) / (x.2.card : ℝ)))
  let admissible (x : X) :=
    2 ≤ x.1 ∧ x.2 ⊆ Finset.Icc 1 x.1 ∧ 0 < x.2.card ∧
      (¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ x.2) ∧
      C * (p x) ^ β + R ≤ Real.log (Real.log (x.1 : ℝ))
  have hp (x : X) : 0 ≤ p x := (by norm_num : (0 : ℝ) ≤ 2).trans (le_max_left _ _)
  have decrease (x : X) (hx : admissible x) :
      ∃ y, admissible y ∧ p y + 1 ≤ p x := by
    obtain ⟨hN, hS, hcard, hfree, hbudget⟩ := hx
    have hlarge : T < p x := by
      by_contra! hsmall
      have hlt := hstop x.1 x.2 hN hS hcard hfree hsmall
      have hnonneg := mul_nonneg hC.le (Real.rpow_nonneg (hp x) β)
      have hQR : Q ≤ R := le_max_right _ _
      linarith
    obtain ⟨a, q, M, hq, hM, _, hcard', hdrop, hbudget'⟩ :=
      hstep R (le_max_left _ _) x.1 x.2 hN hS hcard hfree hlarge hbudget
    let U := (Finset.Icc 1 M).filter (fun i ↦ a + (i - 1) * q ∈ x.2)
    refine ⟨(M, U), ⟨hM, Finset.filter_subset _ _, hcard', ?_, hbudget'⟩, hdrop⟩
    exact progression_preimage_free hk hq hfree
  intro N S hN hS hcard hfree hbudget
  exact eliminate_descent p admissible hp decrease (N, S) ⟨hN, hS, hcard, hfree, hbudget⟩

lemma eventually_budget (β C R : ℝ) (hβ : β < 1) :
    ∀ᶠ t : ℝ in atTop, 1 ≤ t ∧ C * (4 * t) ^ β + R ≤ t := by
  have hlim : Tendsto (fun t : ℝ ↦ (C * (4 : ℝ) ^ β) * t ^ (β - 1)) atTop (𝓝 0) := by
    simpa only [neg_sub, mul_zero] using
      (tendsto_rpow_neg_atTop (sub_pos.mpr hβ)).const_mul (C * (4 : ℝ) ^ β)
  filter_upwards [eventually_ge_atTop (max 1 (2 * R)),
    hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with t ht hs
  have ht1 : 1 ≤ t := (le_max_left _ _).trans ht
  have ht0 : 0 < t := by linarith
  have hR : R ≤ t / 2 := by linarith [(le_max_right 1 (2 * R)).trans ht]
  refine ⟨ht1, ?_⟩
  have he : t ^ (β - 1) * t = t ^ β := by
    calc
      t ^ (β - 1) * t = t ^ (β - 1) * t ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = t ^ β := by rw [← Real.rpow_add ht0]; congr 1; ring
  have hm : C * (4 * t) ^ β = ((C * (4 : ℝ) ^ β) * t ^ (β - 1)) * t := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) ht0.le]
    rw [mul_assoc (C * (4 : ℝ) ^ β), he, ← mul_assoc]
  rw [hm]
  linarith [mul_le_mul_of_nonneg_right hs.le ht0.le]

lemma parameter_le_of_large_card {N : ℕ} {S : Finset ℕ}
    (hN : 0 < (N : ℝ)) (hL : 0 < Real.log (N : ℝ))
    (ht : 1 ≤ Real.log (Real.log (N : ℝ)))
    (hS : (N : ℝ) / Real.log (N : ℝ) ^ 2 < (S.card : ℝ)) :
    max 2 (Real.log (2 * (N : ℝ) / (S.card : ℝ))) ≤
      4 * Real.log (Real.log (N : ℝ)) := by
  have hcard : 0 < (S.card : ℝ) := (div_pos hN (sq_pos_of_pos hL)).trans hS
  have hcross := (div_lt_iff₀ (sq_pos_of_pos hL)).mp hS
  have hratio : 2 * (N : ℝ) / (S.card : ℝ) ≤ 2 * Real.log (N : ℝ) ^ 2 := by
    apply (div_le_iff₀ hcard).mpr
    nlinarith only [hcross]
  have hlog := Real.log_le_log (div_pos (by positivity) hcard) hratio
  have h2 : Real.log 2 < 1 := by
    have h := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)
    norm_num at h ⊢
    exact h
  rw [Real.log_mul (by norm_num) (pow_ne_zero 2 hL.ne'), Real.log_pow] at hlog
  push_cast at hlog
  exact max_le (by linarith) (by linarith)

lemma eventual_log_sq_bound (hdesc : H1) (hterm : H2) :
    ∀ k : ℕ, 4 ≤ k → ∀ᶠ N : ℕ in atTop,
      (r k N : ℝ) ≤ (N : ℝ) / Real.log (N : ℝ) ^ 2 := by
  intro k hk
  obtain ⟨β, C, R, hβ, hβ1, hC, hno⟩ := no_budget hdesc hterm hk
  have hlog : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglog : Tendsto (fun N : ℕ ↦ Real.log (Real.log (N : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hlog
  filter_upwards [eventually_ge_atTop (2 : ℕ), hlog.eventually (eventually_gt_atTop 0),
    hloglog.eventually (eventually_budget β C R hβ1)] with N hN hL hbudget
  obtain ⟨S, hS, hfree, hcard⟩ :=
    extremizer (by omega : 1 < k) N
  rw [← hcard]
  by_contra! hlarge
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hSpos : 0 < S.card := by
    exact_mod_cast (div_pos hNpos (sq_pos_of_pos hL)).trans hlarge
  have hp := parameter_le_of_large_card hNpos hL hbudget.1 hlarge
  apply hno N S hN hS hSpos
    (no_positive_step (by omega) hfree)
  refine le_trans ?_ hbudget.2
  gcongr

theorem main : H1 → H2 → OMA.R_Erdos142_erdos_142_variants_lower_R1.H2 := by
  intro hstep hfixed k hk
  refine ⟨1, zero_lt_one, ?_⟩
  have h : (1 : ℝ) + 1 = 2 := by norm_num
  simpa only [h, Real.rpow_two] using eventual_log_sq_bound hstep hfixed k hk

end OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R1
