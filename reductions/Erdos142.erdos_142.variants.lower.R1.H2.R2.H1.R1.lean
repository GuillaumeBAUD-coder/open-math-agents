import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R2

/-!
# Monochromatic progressions from the super-polylogarithmic density bound

The target is the van der Waerden statement with (ceil(log N) + 1)^4 colours for every
progression length at least four. It is reduced to the two density statements
r k N ≤ N exp(-c (log log N)^A) with A > 1, for k = 4 and for k at least five. They are word
for word the hypotheses H1 and H2 of reduction R1 of the step lower.R1.H2.R1.H1 (pull request
29521), so proofs of those two bounds close this branch as well. Both follow from the
quantitative theorem of OpenAI, Quasipolynomial Bounds for Arithmetic Progressions (2026).

Everything else is proved here. The lemma saving_beats_colours shows that the saving
exp(-c (log log N)^(1+eta)) eventually beats the number of colours, and mono_of_card_bound is
the pigeonhole principle over the colour classes: each class in [1,N] has no progression, the
classes partition [1,N], and their number times the density bound is eventually less than N.
-/

namespace OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R2_H1_R1

open Erdos142 Filter

/-- A super-polylogarithmic saving for 4-term progressions. -/
def H1 : Prop :=
  ∃ A c : ℝ, 1 < A ∧ 0 < c ∧ ∀ᶠ N : ℕ in atTop,
    (r 4 N : ℝ) ≤ (N : ℝ) * Real.exp (-c * Real.log (Real.log (N : ℝ)) ^ A)

/-- The same saving for every progression length at least five. -/
def H2 : Prop :=
  ∀ k : ℕ, 5 ≤ k → ∃ A c : ℝ, 1 < A ∧ 0 < c ∧ ∀ᶠ N : ℕ in atTop,
    (r k N : ℝ) ≤ (N : ℝ) * Real.exp (-c * Real.log (Real.log (N : ℝ)) ^ A)

/-- A set with no k-term progression of positive step is k-AP-free in the library sense. -/
lemma free_of_no_step {A : Set ℕ} {k : ℕ} (hk : 1 < k)
    (hno : ¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ A) : A.IsAPOfLengthFree k := by
  have hk' : (1 : ℕ∞) < (k : ℕ∞) := by exact_mod_cast hk
  intro T hsub hT
  obtain ⟨a, d, hcard, hterms⟩ := hT
  have hmem (i : ℕ) (hi : i < k) : a + i * d ∈ T := by
    rw [hterms]
    exact ⟨i, by exact_mod_cast hi, by simp⟩
  have hd : 0 < d := by
    by_contra! h
    have he : d = 0 := Nat.eq_zero_of_le_zero h
    have hs : T = {a} := by
      apply Set.Subset.antisymm
      · rw [hterms, he]
        rintro _ ⟨i, -, rfl⟩
        simp
      · apply Set.singleton_subset_iff.mpr
        simpa using hmem 0 (by omega)
    rw [hs] at hcard
    exact hk'.ne (by simpa using hcard)
  exact (hno ⟨a, d, hd, fun i hi => hsub (hmem i hi)⟩).elim

lemma card_le_r {k N : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.Icc 1 N)
    (hf : (S : Set ℕ).IsAPOfLengthFree k) : S.card ≤ r k N := by
  unfold r Set.IsAPOfLengthFree.maxCard
  refine le_csSup ?_ ⟨S, hS, hf, rfl⟩
  refine ⟨N, ?_⟩
  rintro _ ⟨U, hU, -, rfl⟩
  simpa using Finset.card_le_card hU

/-- The saving eventually beats the fourth power of the logarithm. -/
lemma saving_beats_colours : ∀ C c η : ℝ, 0 < C → 0 < c → 0 < η → ∀ᶠ N : ℕ in atTop,
    C * (((⌈Real.log (N : ℝ)⌉₊ + 1) ^ 4 : ℕ) : ℝ) *
      Real.exp (-c * (Real.log (Real.log (N : ℝ))) ^ (1 + η)) < 1 := by
  intro C c η hC hc hη
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hll := Real.tendsto_log_atTop.comp hlog
  have hp := (tendsto_rpow_atTop hη).comp hll
  filter_upwards [hlog.eventually_ge_atTop 1, hlog.eventually_gt_atTop (81 * C),
    hll.eventually_ge_atTop 0, hp.eventually_ge_atTop (5 / c)] with N hx1 hxC hL0 hLη
  simp only [Function.comp] at hL0 hLη
  generalize Real.log (N : ℝ) = x at *
  generalize hLd : Real.log x = L at *
  have hx0 : 0 < x := by linarith
  have hceil : ((⌈x⌉₊ : ℕ) : ℝ) + 1 ≤ 3 * x := by
    have := Nat.ceil_lt_add_one hx0.le
    linarith
  have hpow : (((⌈x⌉₊ + 1) ^ 4 : ℕ) : ℝ) ≤ 81 * x ^ 4 := by
    push_cast
    calc ((⌈x⌉₊ : ℝ) + 1) ^ 4 ≤ (3 * x) ^ 4 := pow_le_pow_left₀ (by positivity) hceil 4
      _ = 81 * x ^ 4 := by ring
  have hrp : L ^ (1 + η) = L * L ^ η := by
    rcases hL0.eq_or_lt with h | h
    · rw [← h, Real.zero_rpow (by linarith), zero_mul]
    · rw [Real.rpow_add h, Real.rpow_one]
  have h5 : 5 * L ≤ c * L ^ (1 + η) := by
    rw [hrp]
    have h5' : 5 ≤ L ^ η * c := (div_le_iff₀ hc).mp hLη
    nlinarith
  have hexpL : Real.exp (-(5 * L)) = (x ^ 5)⁻¹ := by
    rw [Real.exp_neg, ← hLd, mul_comm, Real.exp_mul, Real.exp_log hx0]
    norm_cast
  have hexp : Real.exp (-c * L ^ (1 + η)) ≤ (x ^ 5)⁻¹ :=
    (Real.exp_le_exp.mpr (by linarith)).trans hexpL.le
  calc C * (((⌈x⌉₊ + 1) ^ 4 : ℕ) : ℝ) * Real.exp (-c * L ^ (1 + η))
      ≤ C * (81 * x ^ 4) * (x ^ 5)⁻¹ := by gcongr
    _ = 81 * C / x := by field_simp
    _ < 1 := by rw [div_lt_one hx0]; exact hxC

/-- Pigeonhole: if every progression-free subset of [1,N] has at most B elements and
m * B < N, then every colouring with m colours has a monochromatic progression in [1,N]. -/
lemma mono_of_card_bound {k N m : ℕ} {B : ℝ} (hk : 1 ≤ k)
    (hB : ∀ S : Finset ℕ, S ⊆ Finset.Icc 1 N →
      (¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ S) → (S.card : ℝ) ≤ B)
    (hm : (m : ℝ) * B < N) (c : ℕ → Fin m) :
    ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ Finset.Icc 1 N ∧ c (a + i * d) = c a := by
  by_contra hno
  have hcls : ∀ t : Fin m, (((Finset.Icc 1 N).filter (fun x => c x = t)).card : ℝ) ≤ B := by
    intro t
    refine hB _ (Finset.filter_subset _ _) ?_
    rintro ⟨a, d, hd, h⟩
    refine hno ⟨a, d, hd, fun i hi => ?_⟩
    have h0 := h 0 (by omega)
    have hi' := h i hi
    simp only [Finset.mem_filter, zero_mul, add_zero] at h0 hi'
    exact ⟨hi'.1, hi'.2.trans h0.2.symm⟩
  have hsum : ((Finset.Icc 1 N).card : ℝ) =
      ∑ t : Fin m, (((Finset.Icc 1 N).filter (fun x => c x = t)).card : ℝ) := by
    have := Finset.card_eq_sum_card_fiberwise (s := Finset.Icc 1 N) (t := Finset.univ)
      (f := c) (fun x _ => Finset.mem_univ _)
    exact_mod_cast this
  have hle : ((Finset.Icc 1 N).card : ℝ) ≤ (m : ℝ) * B := by
    rw [hsum]
    calc ∑ t : Fin m, (((Finset.Icc 1 N).filter (fun x => c x = t)).card : ℝ)
        ≤ ∑ _t : Fin m, B := Finset.sum_le_sum (fun t _ => hcls t)
      _ = (m : ℝ) * B := by simp
  rw [Nat.card_Icc, Nat.add_sub_cancel] at hle
  linarith

theorem main : H1 → H2 → OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R2.H1 := by
  intro h4 h5 k hk
  obtain ⟨A, c, hA, hc, hb⟩ : ∃ A c : ℝ, 1 < A ∧ 0 < c ∧ ∀ᶠ N : ℕ in atTop,
      (r k N : ℝ) ≤ (N : ℝ) * Real.exp (-c * Real.log (Real.log (N : ℝ)) ^ A) := by
    rcases eq_or_lt_of_le hk with rfl | hlt
    · exact h4
    · exact h5 k hlt
  obtain ⟨η, rfl⟩ : ∃ η : ℝ, A = 1 + η := ⟨A - 1, by ring⟩
  have hη : 0 < η := by linarith
  filter_upwards [hb, saving_beats_colours 1 c η one_pos hc hη, eventually_ge_atTop 1]
    with N hN hsav hN1 col
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  refine mono_of_card_bound
    (B := (N : ℝ) * Real.exp (-c * Real.log (Real.log (N : ℝ)) ^ (1 + η)))
    (by omega) (fun S hS hfree => ?_) ?_ col
  · have hcard : (S.card : ℝ) ≤ (r k N : ℝ) := by
      exact_mod_cast card_le_r hS (free_of_no_step (by omega) hfree)
    exact hcard.trans hN
  · have := mul_lt_mul_of_pos_right hsav hNpos
    nlinarith [this]

end OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R2_H1_R1
