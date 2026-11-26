import FormalConjectures.ErdosProblems.«704»

/-! Colour the half-open cubes by their integer indices modulo a common period. -/

-- Problem: Erdős Problem 704 — cube colouring
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/704.lean:91 (declaration Erdos704.erdos_704.variants.cube_colouring)
-- Credit: @dk8827 (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Erdos704 SimpleGraph

lemma OMA.floor_eq_of_close_residues {m : ℕ} {u v : ℝ} (hclose : |u - v| + 1 ≤ (m : ℝ))
    (hmod : (⌊u⌋ : ZMod m) = (⌊v⌋ : ZMod m)) : ⌊u⌋ = ⌊v⌋ := by
  have hdiv := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ m).mp hmod
  have huv := le_abs_self (u - v)
  have hvu := neg_le_abs (u - v)
  have hfu := Int.floor_le u
  have hfv := Int.floor_le v
  have hcu := Int.lt_floor_add_one u
  have hcv := Int.lt_floor_add_one v
  have habs : |(⌊v⌋ : ℝ) - (⌊u⌋ : ℝ)| < (m : ℝ) := by
    apply abs_lt.mpr
    constructor <;> linarith
  have hcast : ((⌊v⌋ - ⌊u⌋).natAbs : ℝ) < (m : ℝ) := by
    simpa only [Nat.cast_natAbs, Int.cast_abs, Int.cast_sub] using habs
  have hsmall : (⌊v⌋ - ⌊u⌋).natAbs < (m : ℤ).natAbs := by
    simp only [Int.natAbs_natCast]
    exact_mod_cast hcast
  exact (sub_eq_zero.mp (Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdiv hsmall)).symm

theorem OMA.solution : type_of% @Erdos704.erdos_704.variants.cube_colouring := by
  intro n
  let s := Real.sqrt (n : ℝ)
  let m : ℕ := ⌈s⌉₊ + 1
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hsSq : s ^ 2 = (n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
  have hmlo : s + 1 ≤ (m : ℝ) := by
    simpa only [m, Nat.cast_add, Nat.cast_one, add_comm] using
      add_le_add_right (Nat.le_ceil s) 1
  have hmhi : (m : ℝ) ≤ 2 + s := by
    have hceil := Nat.ceil_lt_add_one hs
    simp only [m, Nat.cast_add, Nat.cast_one]
    linarith
  letI : NeZero m := ⟨by simp [m]⟩
  let colour (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) : ZMod m := ⌊s * x i⌋
  have coloring : (unitDistanceGraph n).Coloring (Fin n → ZMod m) := by
    apply Coloring.mk colour
    intro x y hxy hcolour
    have hdist : dist x y = 1 := hxy
    have hdistSq : ∑ i, (x i - y i) ^ 2 = 1 := by
      simpa [hdist, Real.dist_eq, sq_abs] using (EuclideanSpace.dist_sq_eq x y).symm
    have hn : 0 < n := by
      by_contra! hn
      have heq : n = 0 := by omega
      subst n
      simp at hdistSq
    letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    have hcoord (i : Fin n) : (s * (x i - y i)) ^ 2 < 1 := by
      have hiSq : (x i - y i) ^ 2 ≤ 1 := by
        rw [← hdistSq]
        exact Finset.single_le_sum (fun j _ => sq_nonneg (x j - y j)) (Finset.mem_univ i)
      have hi : |x i - y i| ≤ 1 := by
        rw [← abs_one (α := ℝ), ← sq_le_sq]
        simpa using hiSq
      have hclose : |s * x i - s * y i| ≤ s := by
        rw [← mul_sub, abs_mul, abs_of_nonneg hs]
        exact mul_le_of_le_one_right hs hi
      have hperiod : |s * x i - s * y i| + 1 ≤ (m : ℝ) := by linarith
      have hf := OMA.floor_eq_of_close_residues hperiod (congrFun hcolour i)
      have hfR : (⌊s * x i⌋ : ℝ) = (⌊s * y i⌋ : ℝ) := by exact_mod_cast hf
      have hfx := Int.floor_le (s * x i)
      have hfy := Int.floor_le (s * y i)
      have hcx := Int.lt_floor_add_one (s * x i)
      have hcy := Int.lt_floor_add_one (s * y i)
      have habs : |s * x i - s * y i| < 1 := by
        apply abs_lt.mpr
        constructor <;> linarith
      rw [mul_sub]
      simpa using (sq_lt_sq.mpr (by simpa using habs : |s * x i - s * y i| < |(1 : ℝ)|))
    have htotal : ∑ i, (s * (x i - y i)) ^ 2 = (n : ℝ) := by
      simp only [mul_pow, ← Finset.mul_sum, hdistSq, mul_one, hsSq]
    have hlt : ∑ i, (s * (x i - y i)) ^ 2 < ∑ _i : Fin n, (1 : ℝ) :=
      Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun i _ => hcoord i
    rw [htotal] at hlt
    simp at hlt
  refine ⟨Fintype.card (Fin n → ZMod m), coloring.colorable, ?_⟩
  simpa [Fintype.card_fun, ZMod.card] using pow_le_pow_left₀ (Nat.cast_nonneg m) hmhi n
