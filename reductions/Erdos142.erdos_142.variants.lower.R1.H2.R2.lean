import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1

/-!
# From monochromatic arithmetic progressions to the logarithmic power saving

For each fixed length at least four, assume a monochromatic progression exists for every coloring
of [1,N] with (ceil(log N) + 1)^4 colors, for large N. This is a consequence of the
fixed-length van der Waerden bound in OpenAI, Quasipolynomial Bounds for Arithmetic
Progressions (2026), section 1.4, equation (1.3). At this many colors the logarithm of
the Ramsey threshold is O_k((log log N)^A_k), eventually less than log N. The second
input is a finite covering lemma. The theorem coloring_hypothesis_of_ramsey_bound below
checks the specialization of equation (1.3), including its integer cutoff.

Given a dense progression-free set S, color x by a shift of S containing x + N.
Every monochromatic progression then lies in one translate and gives a progression
in S. The covering threshold yields the stronger bound N / (log N)^2. The
translate-cover argument also appears in Fox and Hunter, Three-color van der Waerden
numbers grow super-exponentially (2026), page 2.

The target is the remaining long-progression step of reduction R1 (pull request 373).
The extremizer argument is from reduction R2 of the parent problem (pull request 3320).
-/

namespace OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R2

open Asymptotics Erdos142 Filter Real
open scoped Topology

/-- Each fixed length at least four admits a monochromatic progression with polylogarithmically many colors. -/
def H1 : Prop :=
  ∀ k : ℕ, 4 ≤ k → ∀ᶠ N : ℕ in atTop,
    ∀ c : ℕ → Fin ((⌈Real.log (N : ℝ)⌉₊ + 1) ^ 4), ∃ a d : ℕ, 0 < d ∧
      ∀ i < k, a + i * d ∈ Finset.Icc 1 N ∧ c (a + i * d) = c a

/-- A sufficiently large set covers a translated interval with at most the specified number of shifts. -/
def H2 : Prop :=
  ∀ (N q : ℕ) (S : Finset ℕ), 0 < N → 0 < q → S ⊆ Finset.Icc 1 N →
    2 * (N : ℝ) * Real.log (N : ℝ) < (q : ℝ) * (S.card : ℝ) →
    ∃ shifts : Fin q → ℕ, ∀ x ∈ Finset.Icc 1 N,
      ∃ t : Fin q, ∃ b ∈ S, x + N = shifts t + b

lemma polylog_color_threshold (A : ℝ) (hA : 1 ≤ A) :
    ∀ᶠ N : ℕ in atTop,
      ⌈Real.exp (A * (2 + Real.log (((⌈Real.log (N : ℝ)⌉₊ + 1) ^ 4 : ℕ) : ℝ)) ^ A)⌉₊ ≤ N := by
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  have hlogN : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hgrowth :
      (fun x : ℝ => (A * (10 : ℝ) ^ A) * Real.log x ^ A) =o[atTop] (fun x => x) := by
    simpa only [Real.rpow_one] using
      (isLittleO_log_rpow_rpow_atTop A (s := 1) zero_lt_one).const_mul_left
        (A * (10 : ℝ) ^ A)
  filter_upwards [eventually_gt_atTop (0 : ℕ), hlogN.eventually_ge_atTop 2,
    (Real.tendsto_log_atTop.comp hlogN).eventually_ge_atTop 1,
    hlogN.eventually (hgrowth.def zero_lt_one)] with N hN hx hlog hlinear
  have hN0 : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  set x : ℝ := Real.log (N : ℝ)
  change 1 ≤ Real.log x at hlog
  let y : ℝ := (⌈x⌉₊ : ℝ) + 1
  have hy : 1 ≤ y := le_add_of_nonneg_left (Nat.cast_nonneg _)
  have hy_sq : y ≤ x ^ 2 := by
    have hx0 : 0 ≤ x := by linarith
    have hceil := Nat.ceil_lt_add_one hx0
    have hprod : 0 ≤ (x - 2) * (x + 1) := mul_nonneg (by linarith) (by positivity)
    dsimp [y]
    nlinarith
  have hlogy : Real.log y ≤ 2 * Real.log x := by
    simpa only [Real.log_pow, Nat.cast_ofNat] using
      Real.log_le_log (show 0 < y by linarith) hy_sq
  have hbase : 0 ≤ 2 + 4 * Real.log y := by
    have hlogy0 := Real.log_nonneg hy
    positivity
  apply Nat.ceil_le.mpr
  rw [← Real.le_log_iff_exp_le hN0]
  change A * (2 + Real.log (((⌈x⌉₊ + 1) ^ 4 : ℕ) : ℝ)) ^ A ≤ x
  calc
    _ = A * (2 + 4 * Real.log y) ^ A := by
      simp only [Nat.cast_pow, Nat.cast_add, Nat.cast_one, Real.log_pow, Nat.cast_ofNat, y]
    _ ≤ A * (10 * Real.log x) ^ A :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hbase (by linarith) hA0) hA0
    _ = (A * (10 : ℝ) ^ A) * Real.log x ^ A := by
      rw [Real.mul_rpow (by norm_num) (zero_le_one.trans hlog), mul_assoc]
    _ ≤ x := by
      refine (le_abs_self _).trans ?_
      simpa only [Real.norm_eq_abs, one_mul, abs_of_nonneg (show 0 ≤ x by linarith)]
        using hlinear

/-- The published quasipolynomial bound for van der Waerden numbers supplies H1.
The hypothesis states that all q-colorings already contain a progression at the
length given by the bound, for each fixed progression length k. -/
lemma coloring_hypothesis_of_ramsey_bound
    (h : ∀ k : ℕ, 4 ≤ k → ∃ A : ℝ, 1 ≤ A ∧ ∀ q : ℕ, 0 < q →
      ∀ c : ℕ → Fin q, ∃ a d : ℕ, 0 < d ∧ ∀ i < k,
        a + i * d ∈ Finset.Icc 1 ⌈Real.exp (A * (2 + Real.log (q : ℝ)) ^ A)⌉₊ ∧
          c (a + i * d) = c a) : H1 := by
  intro k hk
  obtain ⟨A, hA, hmono⟩ := h k hk
  filter_upwards [polylog_color_threshold A hA] with N hN
  intro c
  let q := (⌈Real.log (N : ℝ)⌉₊ + 1) ^ 4
  have hq : 0 < q := by dsimp [q]; positivity
  obtain ⟨a, d, hd, hap⟩ := hmono q hq c
  refine ⟨a, d, hd, ?_⟩
  intro i hi
  obtain ⟨hx, hc⟩ := hap i hi
  obtain ⟨hx1, hx2⟩ := Finset.mem_Icc.mp hx
  exact ⟨Finset.mem_Icc.mpr ⟨hx1, hx2.trans hN⟩, hc⟩

lemma contains_progression {k b d : ℕ} {S : Finset ℕ} (hk : 4 ≤ k) (hd : 0 < d)
    (hmem : ∀ i < k, b + i * d ∈ S) : ¬ (S : Set ℕ).IsAPOfLengthFree k := by
  intro hfree
  let f : ℕ → ℕ := fun i ↦ b + i * d
  have hf : Function.Injective f := by
    intro i j hij
    exact Nat.eq_of_mul_eq_mul_right hd (Nat.add_left_cancel hij)
  let P := (Finset.range k).image f
  have hcard : P.card = k := by
    simp [P, Finset.card_image_of_injective _ hf]
  have hsub : (P : Set ℕ) ⊆ (S : Set ℕ) := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    exact hmem i (Finset.mem_range.mp hi)
  have hap : (P : Set ℕ).IsAPOfLength k := by
    refine ⟨b, d, ?_, ?_⟩
    · simpa using congrArg (fun n : ℕ ↦ (n : ℕ∞)) hcard
    · ext x
      simp [P, f]
  have hkle : (k : ℕ∞) ≤ 1 := hfree _ hsub hap
  have hkle' : k ≤ 1 := by exact_mod_cast hkle
  omega

lemma shift_coloring {N q k : ℕ} {S : Finset ℕ} (hq : 0 < q) (hk : 4 ≤ k)
    (hmono : ∀ c : ℕ → Fin q, ∃ a d : ℕ, 0 < d ∧
      ∀ i < k, a + i * d ∈ Finset.Icc 1 N ∧ c (a + i * d) = c a)
    (shifts : Fin q → ℕ)
    (hcover : ∀ x ∈ Finset.Icc 1 N, ∃ t : Fin q, ∃ b ∈ S, x + N = shifts t + b) :
    ¬ (S : Set ℕ).IsAPOfLengthFree k := by
  classical
  let color (x : ℕ) : Fin q :=
    if hx : x ∈ Finset.Icc 1 N then (hcover x hx).choose else ⟨0, hq⟩
  have color_witness (x : ℕ) (hx : x ∈ Finset.Icc 1 N) :
      ∃ b ∈ S, x + N = shifts (color x) + b := by
    simpa only [color, dif_pos hx] using (hcover x hx).choose_spec
  obtain ⟨a, d, hd, hmono⟩ := hmono color
  have ha : a ∈ Finset.Icc 1 N := by simpa using (hmono 0 (by omega)).1
  obtain ⟨b, _, hbase⟩ := color_witness a ha
  refine contains_progression (b := b) hk hd ?_
  intro i hi
  obtain ⟨x, hx, hshift⟩ := color_witness (a + i * d) (hmono i hi).1
  rw [(hmono i hi).2] at hshift
  have hterm : b + i * d = x := by omega
  simpa only [hterm] using hx

lemma covering_threshold {N : ℕ} {S : Finset ℕ} (hN : 0 < N)
    (hlog : 2 < log (N : ℝ))
    (hlarge : (N : ℝ) / log (N : ℝ) ^ 2 < S.card) :
    2 * (N : ℝ) * log (N : ℝ) <
      (((⌈log (N : ℝ)⌉₊ + 1) ^ 4 : ℕ) : ℝ) * S.card := by
  let L := log (N : ℝ)
  change 2 < L at hlog
  change (N : ℝ) / L ^ 2 < S.card at hlarge
  change 2 * (N : ℝ) * L < (((⌈L⌉₊ + 1) ^ 4 : ℕ) : ℝ) * S.card
  have hLpos : 0 < L := by linarith
  have hNs : 0 < (N : ℝ) := by exact_mod_cast hN
  have hLbound : L ≤ ((⌈L⌉₊ + 1 : ℕ) : ℝ) := by
    have hceil : L ≤ (⌈L⌉₊ : ℝ) := Nat.le_ceil L
    push_cast
    linarith
  have hpow : L ^ 4 ≤ (((⌈L⌉₊ + 1) ^ 4 : ℕ) : ℝ) := by
    exact_mod_cast pow_le_pow_left₀ hLpos.le hLbound 4
  have hquad : 2 * L < L ^ 2 := by nlinarith [mul_pos (sub_pos.mpr hlog) hLpos]
  have hmass : (N : ℝ) < (S.card : ℝ) * L ^ 2 :=
    (div_lt_iff₀ (sq_pos_of_pos hLpos)).1 hlarge
  calc
    2 * (N : ℝ) * L = (2 * L) * N := by ring
    _ < L ^ 2 * N := mul_lt_mul_of_pos_right hquad hNs
    _ < L ^ 2 * ((S.card : ℝ) * L ^ 2) := mul_lt_mul_of_pos_left hmass (sq_pos_of_pos hLpos)
    _ = L ^ 4 * (S.card : ℝ) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hpow (Nat.cast_nonneg _)

lemma eventual_card_bound (hcolor : H1) (hcover : H2) {k : ℕ} (hk : 4 ≤ k) :
    ∀ᶠ N : ℕ in atTop, (r k N : ℝ) ≤ (N : ℝ) / log (N : ℝ) ^ 2 := by
  have hLog : Tendsto (fun N : ℕ ↦ log (N : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hcolor k hk, hLog.eventually (eventually_gt_atTop (2 : ℝ)),
    eventually_gt_atTop (0 : ℕ)] with N hmono hlog hN
  let sizes : Set ℕ := {Finset.card S | (S) (_ : S ⊆ Finset.Icc 1 N)
    (_ : (S : Set ℕ).IsAPOfLengthFree k)}
  have hbound : BddAbove sizes := by
    refine ⟨N, ?_⟩
    rintro _ ⟨S, hS, _, rfl⟩
    exact (Finset.card_mono hS).trans_eq (Nat.card_Icc 1 N)
  have hnonempty : sizes.Nonempty := by
    refine ⟨0, ∅, by simp, ?_, by simp⟩
    intro A hA hAP
    have hEmpty : A = ∅ := Set.subset_empty_iff.mp (by simpa using hA)
    have hpos : 0 < (k : ℕ∞) := by exact_mod_cast (show 0 < k by omega)
    exact (Set.not_isAPOfLength_empty hpos (hEmpty ▸ hAP)).elim
  obtain ⟨S, hS, hfree, hcard⟩ := Nat.sSup_mem hnonempty hbound
  change S.card = r k N at hcard
  rw [← hcard]
  by_contra! hlarge
  let q := (⌈log (N : ℝ)⌉₊ + 1) ^ 4
  have hq : 0 < q := by positivity
  obtain ⟨shifts, hshifts⟩ := hcover N q S hN hq hS (covering_threshold hN hlog hlarge)
  exact shift_coloring hq hk hmono shifts hshifts hfree

theorem main : H1 → H2 → OMA.R_Erdos142_erdos_142_variants_lower_R1.H2 := by
  intro hcolor hcover k hk
  refine ⟨1, by norm_num, ?_⟩
  simpa only [show (1 : ℝ) + 1 = 2 by norm_num, Real.rpow_two] using
    eventual_card_bound hcolor hcover (k := k) hk

end OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R2
