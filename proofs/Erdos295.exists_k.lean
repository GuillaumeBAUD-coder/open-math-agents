import FormalConjectures.ErdosProblems.«295»

-- Problem: Erdős Problem 295 — exists k
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/295.lean:37 (declaration Erdos295.exists_k)
-- Credit: @eitanteperman (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA

/-- Greedy (Fibonacci–Sylvester) step: a fraction `a / b < 1 / K` is a sum of distinct unit
fractions whose denominators all exceed `K`. Induction on the numerator, which strictly drops. -/
lemma greedy : ∀ a : ℕ, ∀ b K : ℕ, 0 < a → 1 ≤ K → a * K < b →
    ∃ S : Finset ℕ, (∀ s ∈ S, K < s) ∧ ∑ s ∈ S, (1 / s : ℚ) = a / b := by
  intro a
  induction a using Nat.strong_induction_on with
  | _ a ih =>
  intro b K ha hK hab
  have haK : a ≤ a * K := Nat.le_mul_of_pos_right a hK
  have hab' : a < b := lt_of_le_of_lt haK hab
  set d := (b + a - 1) / a with hd
  have hdiv : a * d ≤ b + a - 1 := Nat.mul_div_le (b + a - 1) a
  have hlt : b + a - 1 < a * d + a := by
    have := Nat.lt_mul_div_succ (b + a - 1) ha
    rw [mul_add, mul_one] at this
    exact this
  have h1 : b ≤ a * d := by omega
  have hKd : K < d := by
    by_contra hc
    push Not at hc
    have : a * d ≤ a * K := Nat.mul_le_mul_left a hc
    omega
  have hd0 : 0 < d := by omega
  by_cases he : a * d = b
  · refine ⟨{d}, by simpa using hKd, ?_⟩
    rw [Finset.sum_singleton, ← he]
    push_cast
    field_simp
  · set a' := a * d - b with ha'
    have ha'pos : 0 < a' := by omega
    have ha'a : a' < a := by omega
    obtain ⟨S, hS, hsum⟩ := ih a' ha'a (b * d) d ha'pos (by omega)
      (Nat.mul_lt_mul_of_pos_right (by omega) hd0)
    refine ⟨insert d S, ?_, ?_⟩
    · intro s hs
      rcases Finset.mem_insert.1 hs with rfl | hs
      · exact hKd
      · exact lt_trans hKd (hS s hs)
    · rw [Finset.sum_insert (fun h => lt_irrefl d (hS d h)), hsum, ha', Nat.cast_sub h1]
      have hb0 : (b : ℚ) ≠ 0 := by exact_mod_cast (show b ≠ 0 by omega)
      have hd0' : (d : ℚ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
      push_cast
      field_simp
      ring

/-- The harmonic sum over `[m, 2m)` is at least one half. -/
lemma block (m : ℕ) (hm : 0 < m) : (1 / 2 : ℚ) ≤ ∑ i ∈ Finset.Ico m (2 * m), (1 / i : ℚ) := by
  have hle : ∀ i ∈ Finset.Ico m (2 * m), (1 / (2 * m) : ℚ) ≤ 1 / i := by
    intro i hi
    rw [Finset.mem_Ico] at hi
    have hi0 : (0 : ℚ) < i := by exact_mod_cast (show 0 < i by omega)
    apply one_div_le_one_div_of_le hi0
    exact_mod_cast hi.2.le
  have := Finset.card_nsmul_le_sum _ _ _ hle
  rw [Nat.card_Ico, show 2 * m - m = m by omega, nsmul_eq_mul] at this
  have hm0 : (m : ℚ) ≠ 0 := by positivity
  calc (1 / 2 : ℚ) = (m : ℚ) * (1 / (2 * m)) := by field_simp
    _ ≤ _ := this

/-- For `N ≥ 2`, `1` is a sum of reciprocals of distinct integers that are all at least `N`. -/
lemma exists_set (N : ℕ) (hN : 2 ≤ N) :
    ∃ S : Finset ℕ, (∀ s ∈ S, N ≤ s) ∧ ∑ s ∈ S, (1 / s : ℚ) = 1 := by
  classical
  let h : ℕ → ℚ := fun M => ∑ i ∈ Finset.Ico N M, (1 / i : ℚ)
  have hex : ∃ M, 1 ≤ h (M + 1) := by
    refine ⟨4 * N - 1, ?_⟩
    have e : 4 * N - 1 + 1 = 2 * (2 * N) := by omega
    show 1 ≤ ∑ i ∈ Finset.Ico N (4 * N - 1 + 1), (1 / i : ℚ)
    rw [e, ← Finset.sum_Ico_consecutive _ (show N ≤ 2 * N by omega) (by omega)]
    have := block N (by omega)
    have := block (2 * N) (by omega)
    linarith
  let M := Nat.find hex
  have hM : 1 ≤ h (M + 1) := Nat.find_spec hex
  have hNM : N ≤ M := by
    by_contra hc
    push Not at hc
    have : h (M + 1) = 0 := Finset.sum_eq_zero (fun i hi => by
      rw [Finset.mem_Ico] at hi; omega)
    linarith
  have hhM : h M < 1 := by
    have hM1 : 1 ≤ M := by omega
    have := Nat.find_min hex (show M - 1 < M by omega)
    rw [show M - 1 + 1 = M by omega] at this
    push Not at this
    exact this
  have hstep : h (M + 1) = h M + 1 / M := Finset.sum_Ico_succ_top hNM _
  have hM0 : (0 : ℚ) < M := by exact_mod_cast (show 0 < M by omega)
  set r := 1 - h M with hr
  have hrpos : 0 < r := by linarith
  have hrle : r ≤ 1 / M := by linarith
  by_cases hre : r = 1 / M
  · refine ⟨Finset.Ico N (M + 1), fun s hs => (Finset.mem_Ico.1 hs).1, ?_⟩
    show h (M + 1) = 1
    linarith
  · have hrlt : r < 1 / M := lt_of_le_of_ne hrle hre
    -- write r = a / b with naturals
    have hnum : 0 < r.num := Rat.num_pos.2 hrpos
    set a := r.num.toNat with ha
    set b := r.den with hb
    have hra : (r : ℚ) = (a : ℚ) / b := by
      rw [ha, show ((r.num.toNat : ℕ) : ℚ) = (r.num : ℚ) by
        exact_mod_cast Int.toNat_of_nonneg hnum.le]
      exact (Rat.num_div_den r).symm
    have ha0 : 0 < a := by omega
    have hb0 : (0 : ℚ) < b := by exact_mod_cast r.den_pos
    have hK : a * (M - 1) < b := by
      have hM1 : (1 : ℚ) ≤ ((M - 1 : ℕ) : ℚ) := by exact_mod_cast (show 1 ≤ M - 1 by omega)
      have hMc : ((M - 1 : ℕ) : ℚ) = (M : ℚ) - 1 := by
        rw [Nat.cast_sub (show 1 ≤ M by omega)]; simp
      have key : (a : ℚ) * ((M - 1 : ℕ) : ℚ) < b := by
        rw [hra] at hrlt
        rw [div_lt_div_iff₀ hb0 hM0] at hrlt
        nlinarith
      exact_mod_cast key
    obtain ⟨S', hS', hsum'⟩ := greedy a b (M - 1) ha0 (by omega) hK
    have hdisj : Disjoint (Finset.Ico N M) S' := by
      rw [Finset.disjoint_left]
      intro x hx hx'
      have := hS' x hx'
      rw [Finset.mem_Ico] at hx
      omega
    refine ⟨Finset.Ico N M ∪ S', ?_, ?_⟩
    · intro s hs
      rcases Finset.mem_union.1 hs with hs | hs
      · exact (Finset.mem_Ico.1 hs).1
      · have := hS' s hs; omega
    · rw [Finset.sum_union hdisj, hsum', ← hra]
      show h M + r = 1
      linarith

end OMA

theorem OMA.solution : type_of% @Erdos295.exists_k := by
  intro N
  obtain ⟨S, hS, hsum⟩ := OMA.exists_set (max N 2) (le_max_right _ _)
  refine ⟨S.card, fun i => S.orderEmbOfFin rfl i,
    fun i => le_trans (le_max_left _ _) (hS _ (S.orderEmbOfFin_mem rfl i)),
    (S.orderEmbOfFin rfl).strictMono, ?_⟩
  have hR : ∑ s ∈ S, (1 / s : ℝ) = 1 := by
    have := congrArg (fun q : ℚ => (q : ℝ)) hsum
    push_cast at this
    exact this
  refine Eq.trans ?_ hR
  rw [← Finset.sum_coe_sort S]
  exact Fintype.sum_equiv (S.orderIsoOfFin rfl).toEquiv _ _ (fun i => rfl)
