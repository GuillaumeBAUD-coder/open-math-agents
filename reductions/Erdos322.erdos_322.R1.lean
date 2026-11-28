import FormalConjectures.ErdosProblems.«322»

/-!
# Erdős 322: reduction to k = 4 and k ≥ 5; case k = 3 proved (Mahler's theorem with every exponent below 1/12)

Alternative route: instead of a fixed exponent 1/24, we prove the full strength of Mahler [Ma36]
in the form available from his identity
  (9 t^4)^3 + (3 t y^3 - 9 t^4)^3 + (y^4 - 9 t^3 y)^3 = y^12:
for every real c < 1/12 there are infinitely many n with n ^ c < representationCount 3 n.
(The exponent 1/12 is the limit of the method: the family gives about n^(1/12)/3 representations.)
-/

namespace OMA.R_Erdos322_erdos_322_R1

open Erdos322 Filter

/-- Sums of four fourth powers: some power lower bound n ^ c holds infinitely often (open). -/
def H1 : Prop :=
  ∃ c > (0 : ℝ), {n : ℕ | (n : ℝ) ^ c < representationCount 4 n}.Infinite

/-- Every exponent k ≥ 5: some power lower bound n ^ c holds infinitely often (open). -/
def H2 : Prop :=
  ∀ k : ℕ, 5 ≤ k → ∃ c > (0 : ℝ),
    {n : ℕ | (n : ℝ) ^ c < representationCount k n}.Infinite

theorem count_ge (y m : ℕ) (hm : 27 * m ^ 3 ≤ y ^ 3) :
    m ≤ representationCount 3 (y ^ 12) := by
  unfold representationCount
  let g : ℕ → Fin 3 → ℕ := fun t => ![9 * t ^ 4, 3 * t * y ^ 3 - 9 * t ^ 4, y ^ 4 - 9 * t ^ 3 * y]
  have key : ∀ t ∈ Finset.Icc 1 m, 9 * t ^ 4 < 3 * t * y ^ 3 ∧ 9 * t ^ 3 * y < y ^ 4 ∧
      3 * t * y ^ 3 ≤ y ^ 4 ∧ 9 * t ^ 4 ≤ y ^ 4 ∧ y ^ 4 ≤ y ^ 12 := by
    intro t ht
    rw [Finset.mem_Icc] at ht
    have ht3 : t ^ 3 ≤ m ^ 3 := Nat.pow_le_pow_left ht.2 3
    have h27 : 27 * t ^ 3 ≤ y ^ 3 := le_trans (by omega) hm
    have hty : 3 * t ≤ y := by
      have : (3 * t) ^ 3 ≤ y ^ 3 := by ring_nf; ring_nf at h27; omega
      exact (Nat.pow_le_pow_iff_left (by norm_num)).mp this
    have hy : 1 ≤ y := by omega
    have htp : 0 < t ^ 3 := pow_pos (by omega) 3
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · have : 9 * t ^ 4 = 9 * t * t ^ 3 := by ring
      rw [this]; nlinarith
    · have : y ^ 4 = y * y ^ 3 := by ring
      rw [this]; nlinarith
    · have : y ^ 4 = y * y ^ 3 := by ring
      rw [this]; exact Nat.mul_le_mul_right _ hty
    · calc 9 * t ^ 4 ≤ (3 * t) ^ 4 := by ring_nf; omega
        _ ≤ y ^ 4 := Nat.pow_le_pow_left hty 4
    · exact Nat.pow_le_pow_right hy (by norm_num)
  have hmod : ∀ t ∈ Finset.Icc 1 m, ∀ i : Fin 3, g t i % (y ^ 12 + 1) = g t i := by
    intro t ht i
    obtain ⟨h1, h2, h3, h4, h5⟩ := key t ht
    rw [Nat.mod_eq_of_lt]
    fin_cases i
    · show 9 * t ^ 4 < y ^ 12 + 1
      omega
    · show 3 * t * y ^ 3 - 9 * t ^ 4 < y ^ 12 + 1
      omega
    · show y ^ 4 - 9 * t ^ 3 * y < y ^ 12 + 1
      omega
  calc m = (Finset.Icc 1 m).card := by simp
    _ ≤ _ := by
      refine Finset.card_le_card_of_injOn
        (fun t i => (⟨g t i % (y ^ 12 + 1), Nat.mod_lt _ (by omega)⟩ : Fin (y ^ 12 + 1)))
        (fun t ht => ?_) (fun a ha b hb hab => ?_)
      · obtain ⟨h1, h2, h3, h4, h5⟩ := key t ht
        refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun i => ?_, ?_⟩)
        · show 0 < g t i % (y ^ 12 + 1)
          rw [hmod t ht i]
          fin_cases i
          · show 0 < 9 * t ^ 4
            have := (Finset.mem_Icc.mp ht).1
            positivity
          · show 0 < 3 * t * y ^ 3 - 9 * t ^ 4
            omega
          · show 0 < y ^ 4 - 9 * t ^ 3 * y
            omega
        · show ∑ i, (g t i % (y ^ 12 + 1)) ^ 3 = y ^ 12
          rw [Fin.sum_univ_three, hmod t ht 0, hmod t ht 1, hmod t ht 2]
          show (9 * t ^ 4) ^ 3 + (3 * t * y ^ 3 - 9 * t ^ 4) ^ 3 + (y ^ 4 - 9 * t ^ 3 * y) ^ 3
            = y ^ 12
          zify [h1.le, h2.le]
          ring
      · have h0 := congrArg (fun v : Fin 3 → Fin (y ^ 12 + 1) => ((v 0 : Fin (y ^ 12 + 1)) : ℕ)) hab
        have h0' : g a 0 % (y ^ 12 + 1) = g b 0 % (y ^ 12 + 1) := h0
        rw [hmod a ha 0, hmod b hb 0] at h0'
        have h0'' : 9 * a ^ 4 = 9 * b ^ 4 := h0'
        exact Nat.pow_left_injective (by norm_num : (4 : ℕ) ≠ 0) (by simpa using h0'')


/-- For d < 1, eventually (in the natural number m) (3 m) ^ d < m. -/
theorem eventually_rpow_lt (d : ℝ) (hd : d < 1) :
    ∃ M : ℕ, ∀ m : ℕ, M ≤ m → ((3 * m : ℕ) : ℝ) ^ d < (m : ℝ) := by
  have ht := tendsto_rpow_neg_atTop (y := 1 - d) (by linarith)
  have hev : ∀ᶠ x : ℝ in atTop, x ^ (-(1 - d)) < 1 / 3 ∧ 1 ≤ x :=
    (ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 3))).and (eventually_ge_atTop 1)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  refine ⟨⌈N⌉₊, fun m hm => ?_⟩
  have hmN : N ≤ ((3 * m : ℕ) : ℝ) := by
    have h1 : N ≤ (m : ℝ) := le_trans (Nat.le_ceil N) (by exact_mod_cast hm)
    push_cast
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  obtain ⟨h1, h2⟩ := hN _ hmN
  set x : ℝ := ((3 * m : ℕ) : ℝ) with hx
  have hxpos : 0 < x := by linarith
  have hsplit : x ^ d = x ^ (-(1 - d)) * x := by
    rw [show d = -(1 - d) + 1 by ring, Real.rpow_add hxpos, Real.rpow_one]
    congr 1
    ring_nf
  have hxm : x = 3 * (m : ℝ) := by rw [hx]; push_cast; ring
  rw [hsplit]
  calc x ^ (-(1 - d)) * x < 1 / 3 * x := by
        exact mul_lt_mul_of_pos_right h1 hxpos
    _ = (m : ℝ) := by rw [hxm]; ring

/-- Mahler (1936), sharp-exponent form: for every c < 1/12 there are infinitely many n with
n ^ c < representationCount 3 n. -/
theorem mahler_three_sharp (c : ℝ) (hc : c < 1 / 12) :
    {n : ℕ | (n : ℝ) ^ c < representationCount 3 n}.Infinite := by
  obtain ⟨M, hM⟩ := eventually_rpow_lt (12 * c) (by linarith)
  refine Set.infinite_of_injective_forall_mem (f := fun m : ℕ => (3 * (m + M)) ^ 12) ?_ ?_
  · intro a b hab
    have : 3 * (a + M) = 3 * (b + M) := Nat.pow_left_injective (by norm_num : (12 : ℕ) ≠ 0) hab
    omega
  · intro m
    show (((3 * (m + M)) ^ 12 : ℕ) : ℝ) ^ c < (representationCount 3 ((3 * (m + M)) ^ 12) : ℝ)
    have e : 27 * (m + M) ^ 3 = (3 * (m + M)) ^ 3 := by ring
    have hcnt := count_ge (3 * (m + M)) (m + M) e.le
    have hpow : (((3 * (m + M)) ^ 12 : ℕ) : ℝ) ^ c = ((3 * (m + M) : ℕ) : ℝ) ^ (12 * c) := by
      rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
      norm_num
    rw [hpow]
    calc ((3 * (m + M) : ℕ) : ℝ) ^ (12 * c) < ((m + M : ℕ) : ℝ) := hM (m + M) (by omega)
      _ ≤ _ := by exact_mod_cast hcnt

/-- The k = 3 case of erdos_322, e.g. with c = 1/13. -/
theorem erdos_322_three :
    ∃ c > (0 : ℝ), {n : ℕ | (n : ℝ) ^ c < representationCount 3 n}.Infinite :=
  ⟨1 / 13, by norm_num, mahler_three_sharp _ (by norm_num)⟩

/-- Reduction: the k = 3 case is proved here (Mahler); k = 4 (H1) and k ≥ 5 (H2) remain open. -/
theorem main : H1 → H2 → type_of% @Erdos322.erdos_322 := by
  intro h1 h2 k hk
  rcases (by omega : k = 3 ∨ k = 4 ∨ 5 ≤ k) with rfl | rfl | h
  · exact erdos_322_three
  · exact h1
  · exact h2 k h

end OMA.R_Erdos322_erdos_322_R1
