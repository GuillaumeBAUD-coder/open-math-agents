import FormalConjectures.ErdosProblems.«1190»

namespace OMA.R_Erdos1190_erdos_1190_variants_upper_bound_R1
open Filter Real Finset

private lemma shellSum {m : ℕ} (hm : 0 < m) (w : ℕ → ℝ) (a : ℕ → ℤ)
    (hcount : ∀ N ≥ m, ∀ S : Finset ℕ, (∀ n ∈ S, 0 < n ∧ n ≤ N) →
      (∀ n ∈ S, ∀ j ∈ S, n ≠ j →
        ¬ ∃ x : ℤ, x ≡ a n [ZMOD n] ∧ x ≡ a j [ZMOD j]) →
      (S.card : ℝ) ≤ N * w N)
    (K : ℕ) (S : Finset ℕ) (hb : ∀ n ∈ S, m < n ∧ n ≤ 2 ^ K * m)
    (hd : ∀ n ∈ S, ∀ j ∈ S, n ≠ j →
      ¬ ∃ x : ℤ, x ≡ a n [ZMOD n] ∧ x ≡ a j [ZMOD j]) :
    (∑ n ∈ S, (n : ℝ)⁻¹) ≤ ∑ k ∈ range K, 2 * w (2 ^ (k+1) * m) := by
  classical
  induction K generalizing S with
  | zero =>
    have he : S = ∅ := eq_empty_iff_forall_notMem.2 fun n hn => by
      have := hb n hn
      simp at this
      omega
    simp [he]
  | succ k ih =>
    let A := 2 ^ k * m
    have hA : 0 < A := Nat.mul_pos (pow_pos (by decide) k) hm
    have hmA : m ≤ A := Nat.le_mul_of_pos_left _ (pow_pos (by decide) k)
    have hEnd : 2 ^ (k + 1) * m = 2 * A := by dsimp [A]; ring
    let L := S.filter (fun n => n ≤ A)
    let U := S.filter (fun n => ¬n ≤ A)
    have hL : L ⊆ S := filter_subset _ _
    have hU : U ⊆ S := filter_subset _ _
    have hl := ih L (fun n hn => ⟨(hb n (hL hn)).1, (mem_filter.1 hn).2⟩)
      (fun n hn j hj => hd n (hL hn) j (hL hj))
    have hc := hcount (2*A) (by omega) U
      (fun n hn => ⟨by have := (hb n (hU hn)).1; omega, hEnd ▸ (hb n (hU hn)).2⟩)
      (fun n hn j hj => hd n (hU hn) j (hU hj))
    have hpos : 0 < (A : ℝ) := by exact_mod_cast hA
    have hu : (∑ n ∈ U, (n : ℝ)⁻¹) ≤ 2 * w (2 * A) := by
      calc
        _ ≤ ∑ _n ∈ U, (A : ℝ)⁻¹ := by
          apply sum_le_sum
          intro n hn
          have h : A < n := Nat.lt_of_not_ge (mem_filter.1 hn).2
          exact inv_anti₀ hpos (by exact_mod_cast h.le)
        _ = (U.card : ℝ) / A := by simp [div_eq_mul_inv]
        _ ≤ _ := by
          apply (div_le_iff₀ hpos).2
          push_cast at hc
          linarith only [hc]
    rw [← sum_filter_add_sum_filter_not S (fun n => n ≤ A), sum_range_succ, hEnd]
    exact add_le_add hl hu

/-- The BFV upper count for finite systems below a common cutoff. -/
def H1 : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ᶠ N : ℕ in atTop, ∀ (S : Finset ℕ) (a : ℕ → ℤ),
    (∀ n ∈ S, 0 < n ∧ n ≤ N) →
    (∀ n ∈ S, ∀ j ∈ S, n ≠ j →
      ¬ ∃ x : ℤ, x ≡ a n [ZMOD n] ∧ x ≡ a j [ZMOD j]) →
    (S.card : ℝ) ≤ N * scaleL N ^ (-(sqrt 3 / 2) + δ)

/-- The scale absorbs the dyadic summation after an arbitrarily small loss. -/
def H2 : Prop :=
  ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 → ∀ᶠ m : ℕ in atTop, ∃ B : ℝ,
    B < scaleL m ^ (-(sqrt 3 / 2) + δ) ∧ ∀ K : ℕ,
      (∑ k ∈ range K, 2 * scaleL (2 ^ (k + 1) * m) ^ (-(sqrt 3 / 2) + δ / 2)) ≤ B

theorem main : H1 → H2 → type_of% @Erdos1190.erdos_1190.variants.upper_bound := by
  intro hc ht ε hε
  let δ := min ε (1 / 2)
  have hδ : 0 < δ := lt_min hε (by norm_num)
  obtain ⟨N₀, hN⟩ := eventually_atTop.1 (hc (δ / 2) (by positivity))
  filter_upwards [eventually_ge_atTop (max N₀ 1), ht δ hδ (min_le_right _ _)] with m hm htail
  obtain ⟨B, hB, hsum⟩ := htail
  apply lt_of_le_of_lt _ (lt_of_lt_of_le hB ?_)
  swap
  · apply Real.rpow_le_rpow_of_exponent_le
    · exact Real.one_le_exp (Real.sqrt_nonneg _)
    · exact add_le_add_right (min_le_left _ _) _
  apply csSup_le
  · exact ⟨0, ∅, fun _ => 0, by simp, by simp, by simp⟩
  · rintro s ⟨S, a, hlow, hd, rfl⟩
    have hm1 : 1 ≤ m := le_of_max_le_right hm
    let K := S.sup id
    have hb (n : ℕ) (hn : n ∈ S) : n ≤ 2 ^ K * m := calc
      n ≤ K := Finset.le_sup (f := id) hn
      _ ≤ 2 ^ K := (Nat.lt_two_pow_self).le
      _ ≤ _ := Nat.le_mul_of_pos_right _ hm1
    exact (shellSum hm1 (fun N => scaleL N ^ (-(sqrt 3 / 2) + δ/2)) a
      (fun N hNm S => hN N ((le_of_max_le_left hm).trans hNm) S a)
      K S (fun n hn => ⟨hlow n hn, hb n hn⟩) hd).trans (hsum K)

end OMA.R_Erdos1190_erdos_1190_variants_upper_bound_R1
