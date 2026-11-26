import FormalConjectures.ErdosProblems.«367»

/-!
# Proof of Erdős Problem 367 (part ii)

We disprove that `∏_{m ∈ [n, n + k)} B 2 m = O(n ^ 2)` holds for every `k ≥ 1`, by refuting `k = 3`:
1. The Pell sequence `(a t, b t)` starting at `(1, 1)` with `a (t + 1) = 3 * a t + 4 * b t`,
   `b (t + 1) = 2 * a t + 3 * b t` satisfies `a t ^ 2 + 1 = 2 * b t ^ 2` and grows strictly.
2. For any `M ≥ 1`, the linear transition on `ZMod (M ^ 2) × ZMod (M ^ 2)` has determinant `1`,
   hence is injective on a finite type, yielding a period `L ≥ 1` with `M ^ 2 ∣ a (r * L) - 1`
   for every `r : ℕ`.
3. For `d ^ 2 ∣ m` (`m ≠ 0`), we show `d ^ 2 ≤ B 2 m`. Taking `n = a (r * L) ^ 2 - 1` gives
   `M ^ 2 ≤ B 2 n`, `a (r * L) ^ 2 ≤ B 2 (n + 1)`, and `b (r * L) ^ 2 ≤ B 2 (n + 2)`, so
   `M ^ 2 * n ^ 2 ≤ 2 * ∏_{m ∈ [n, n + 3)} B 2 m` for arbitrarily large `M` and `n`, refuting
   `O(n ^ 2)`.
-/

-- Problem: Erdős Problem 367 — ii
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/367.lean:59 (declaration Erdos367.erdos_367.parts.ii)
-- Credit: @TheWaler (the owner of the agent is credited as the solver)

namespace Erdos367Proof

open Erdos367 Asymptotics Filter

private def pellPair : ℕ → ℕ × ℕ
  | 0 => (1, 1)
  | t + 1 =>
    let p := pellPair t
    (3 * p.1 + 4 * p.2, 2 * p.1 + 3 * p.2)

private def pellA (t : ℕ) : ℕ := (pellPair t).1
private def pellB (t : ℕ) : ℕ := (pellPair t).2

private lemma pellA_succ (t : ℕ) : pellA (t + 1) = 3 * pellA t + 4 * pellB t := rfl
private lemma pellB_succ (t : ℕ) : pellB (t + 1) = 2 * pellA t + 3 * pellB t := rfl

private lemma pell_eq (t : ℕ) : pellA t ^ 2 + 1 = 2 * pellB t ^ 2 := by
  induction t with
  | zero =>
    norm_num [pellA, pellB, pellPair]
  | succ t ih =>
    rw [pellA_succ, pellB_succ]
    nlinarith

private lemma pell_ge (t : ℕ) : t + 1 ≤ pellA t ∧ 1 ≤ pellB t := by
  induction t with
  | zero =>
    norm_num [pellA, pellB, pellPair]
  | succ t ih =>
    rw [pellA_succ, pellB_succ]
    omega

private lemma exists_period_dvd (M : ℕ) (hM : 1 ≤ M) :
    ∃ L : ℕ, 1 ≤ L ∧ ∀ r : ℕ, M ^ 2 ∣ pellA (r * L) - 1 := by
  have hM2 : M ^ 2 ≠ 0 := pow_ne_zero 2 (by omega)
  have : NeZero (M ^ 2) := ⟨hM2⟩
  let Q := ZMod (M ^ 2) × ZMod (M ^ 2)
  let step : Q → Q := fun p => (3 * p.1 + 4 * p.2, 2 * p.1 + 3 * p.2)
  let stepInv : Q → Q := fun p => (3 * p.1 - 4 * p.2, -2 * p.1 + 3 * p.2)
  have hleft : Function.LeftInverse stepInv step := by
    intro ⟨x, y⟩
    ext <;> dsimp [step, stepInv] <;> ring
  have hinj : Function.Injective step := hleft.injective
  have hpell_mod : ∀ t : ℕ, ((pellA t : ZMod (M ^ 2)), (pellB t : ZMod (M ^ 2))) =
      step^[t] (1, 1) := by
    intro t
    induction t with
    | zero =>
      simp [pellA, pellB, pellPair]
    | succ t ih =>
      rw [Function.iterate_succ_apply', ← ih]
      ext
      · simp [pellA_succ, step]
      · simp [pellB_succ, step]
  rcases Finite.exists_ne_map_eq_of_infinite (fun t : ℕ => step^[t] (1, 1)) with ⟨i, j, hij, hEq⟩
  have hexL : ∃ L : ℕ, 1 ≤ L ∧ step^[L] (1, 1) = (1, 1) := by
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · refine ⟨j - i, by omega, ?_⟩
      have h1 : step^[i] (step^[j - i] (1, 1)) = step^[i] (1, 1) := by
        rw [← Function.iterate_add_apply, Nat.add_sub_of_le hlt.le, hEq]
      exact (hinj.iterate i) h1
    · refine ⟨i - j, by omega, ?_⟩
      have h1 : step^[j] (step^[i - j] (1, 1)) = step^[j] (1, 1) := by
        rw [← Function.iterate_add_apply, Nat.add_sub_of_le hgt.le, hEq.symm]
      exact (hinj.iterate j) h1
  rcases hexL with ⟨L, hL1, hL⟩
  refine ⟨L, hL1, fun r => ?_⟩
  have hiter : step^[r * L] (1, 1) = (1, 1) := by
    induction r with
    | zero =>
      simp
    | succ r ih =>
      rw [add_mul, one_mul, Function.iterate_add_apply, hL, ih]
  have hmod : (pellA (r * L) : ZMod (M ^ 2)) = 1 := by
    have h := congr_arg Prod.fst ((hpell_mod (r * L)).trans hiter)
    exact h
  have hge1 : 1 ≤ pellA (r * L) := by
    have := (pell_ge (r * L)).1
    omega
  have hsub_zero : ((pellA (r * L) - 1 : ℕ) : ZMod (M ^ 2)) = 0 := by
    rw [Nat.cast_sub hge1, Nat.cast_one, hmod, sub_self]
  exact (ZMod.natCast_eq_zero_iff (pellA (r * L) - 1) (M ^ 2)).mp hsub_zero

private lemma B_pos (r m : ℕ) : 0 < B r m := by
  unfold B
  refine Finset.prod_pos fun p hp => ?_
  have hp_mem := (Finset.mem_filter.mp hp).1
  have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors (by simpa [Nat.support_factorization] using hp_mem)
  exact pow_pos hp_prime.pos _

private lemma sq_le_B_two {d m : ℕ} (hm : m ≠ 0) (hd : d ^ 2 ∣ m) : d ^ 2 ≤ B 2 m := by
  have hd0 : d ≠ 0 := by
    intro h
    subst h
    simp at hd
    exact hm hd
  have hd_eq : d ^ 2 = ∏ p ∈ d.factorization.support, p ^ (2 * d.factorization p) := by
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hd0]
    rw [Finsupp.prod, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [← pow_mul, mul_comm]
  have hfac_le : ∀ p, 2 * d.factorization p ≤ m.factorization p := by
    intro p
    have h := (Nat.factorization_le_iff_dvd (pow_ne_zero 2 hd0) hm).mpr hd p
    simpa [Nat.factorization_pow] using h
  have hsub : d.factorization.support ⊆
      m.factorization.support.filter (fun p => 2 ≤ m.factorization p) := by
    intro p hp
    have hdp : 1 ≤ d.factorization p := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp)
    have hle := hfac_le p
    exact Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr (by omega), by omega⟩
  have hdvd : d ^ 2 ∣ B 2 m := by
    rw [hd_eq, B]
    refine dvd_trans (Finset.prod_dvd_prod_of_dvd _ _ fun p _ => Nat.pow_dvd_pow p (hfac_le p))
      (Finset.prod_dvd_prod_of_subset _ _ _ hsub)
  exact Nat.le_of_dvd (B_pos 2 m) hdvd

private lemma prod_Ico_three (f : ℕ → ℕ) (n : ℕ) :
    ∏ m ∈ Finset.Ico n (n + 3), f m = f n * f (n + 1) * f (n + 2) := by
  have h1 : Finset.Ico n (n + 3) = insert (n + 2) (Finset.Ico n (n + 2)) := by
    ext x; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
  have h2 : Finset.Ico n (n + 2) = insert (n + 1) (Finset.Ico n (n + 1)) := by
    ext x; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
  have h3 : Finset.Ico n (n + 1) = {n} := by
    ext x; simp only [Finset.mem_Ico, Finset.mem_singleton]; omega
  rw [h1, Finset.prod_insert (by simp), h2, Finset.prod_insert (by simp), h3, Finset.prod_singleton]
  ring

end Erdos367Proof

open Erdos367 Erdos367Proof Asymptotics Filter

theorem OMA.solution : type_of% @Erdos367.erdos_367.parts.ii := by
  intro H
  have hbig : (fun n => ((∏ m ∈ Finset.Ico n (n + 3), B 2 m : ℕ) : ℝ)) =O[atTop]
      fun n => (n : ℝ) ^ (2 : ℝ) := H 3 (by omega)
  rcases isBigO_iff.mp hbig with ⟨C, hev⟩
  rw [Filter.eventually_atTop] at hev
  rcases hev with ⟨N0, hN0⟩
  set M : ℕ := Nat.ceil (2 * max C 0) + 2
  have hM1 : 1 ≤ M := by omega
  have hM_sq_gt : 2 * C < (M : ℝ) ^ 2 := by
    have hceil : 2 * max C 0 ≤ (Nat.ceil (2 * max C 0) : ℝ) := Nat.le_ceil _
    have hM_ge : (Nat.ceil (2 * max C 0) : ℝ) + 2 ≤ (M : ℝ) := by
      dsimp only [M]
      push_cast
      linarith
    have hC_le : 2 * C ≤ 2 * max C 0 := by linarith [le_max_left C 0]
    have hnonneg : 0 ≤ 2 * max C 0 := by linarith [le_max_right C 0]
    nlinarith
  rcases exists_period_dvd M hM1 with ⟨L, hL1, hL⟩
  set r : ℕ := N0 + 1
  set t : ℕ := r * L
  have ht_ge : N0 + 1 ≤ t := by
    have : N0 + 1 = r * 1 := by simp [r]
    exact this ▸ Nat.mul_le_mul_left r hL1
  set u : ℕ := pellA t
  set v : ℕ := pellB t
  have hu_ge : N0 + 2 ≤ u := by
    have := (pell_ge t).1
    omega
  have hv_ge : 1 ≤ v := (pell_ge t).2
  have hpell : u ^ 2 + 1 = 2 * v ^ 2 := pell_eq t
  set n : ℕ := u ^ 2 - 1
  have hu2_ge : 4 ≤ u ^ 2 := by nlinarith
  have hn_ge_N0 : N0 ≤ n := by
    have : u ≤ u ^ 2 := by nlinarith
    dsimp only [n]
    omega
  have hn_pos : 0 < n := by
    dsimp only [n]
    omega
  have hn_dvd : M ^ 2 ∣ n := by
    have h1 : M ^ 2 ∣ u - 1 := hL r
    have h2 : n = (u - 1) * (u + 1) := by
      dsimp only [n]
      zify [show 1 ≤ u by omega, show 1 ≤ u ^ 2 by omega]
      ring
    rw [h2]
    exact dvd_mul_of_dvd_left h1 (u + 1)
  have hB0 : M ^ 2 ≤ B 2 n := sq_le_B_two hn_pos.ne' hn_dvd
  have hB1 : u ^ 2 ≤ B 2 (n + 1) := by
    have hn1 : n + 1 = u ^ 2 := by dsimp only [n]; omega
    exact sq_le_B_two (by omega) ⟨1, by omega⟩
  have hB2 : v ^ 2 ≤ B 2 (n + 2) := by
    have hn2 : n + 2 = 2 * v ^ 2 := by dsimp only [n]; omega
    exact sq_le_B_two (by omega) ⟨2, by linarith⟩
  have hprod_nat : M ^ 2 * n ^ 2 ≤ 2 * (∏ m ∈ Finset.Ico n (n + 3), B 2 m) := by
    rw [prod_Ico_three]
    have hBprod : M ^ 2 * u ^ 2 * v ^ 2 ≤ B 2 n * B 2 (n + 1) * B 2 (n + 2) :=
      Nat.mul_le_mul (Nat.mul_le_mul hB0 hB1) hB2
    have hnu : n ≤ u ^ 2 := by dsimp only [n]; omega
    have hnv : n ≤ 2 * v ^ 2 := by dsimp only [n]; omega
    have hn2_le : n ^ 2 ≤ u ^ 2 * (2 * v ^ 2) := by
      calc
        n ^ 2 = n * n := sq n
        _ ≤ u ^ 2 * (2 * v ^ 2) := Nat.mul_le_mul hnu hnv
    calc
      M ^ 2 * n ^ 2 ≤ M ^ 2 * (u ^ 2 * (2 * v ^ 2)) := Nat.mul_le_mul_left (M ^ 2) hn2_le
      _ = 2 * (M ^ 2 * u ^ 2 * v ^ 2) := by ring
      _ ≤ 2 * (B 2 n * B 2 (n + 1) * B 2 (n + 2)) := Nat.mul_le_mul_left 2 hBprod
  have hprod_real : (M : ℝ) ^ 2 * (n : ℝ) ^ 2 ≤
      2 * ((∏ m ∈ Finset.Ico n (n + 3), B 2 m : ℕ) : ℝ) := by
    exact_mod_cast hprod_nat
  have hbound := hN0 n hn_ge_N0
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.rpow_two (n : ℝ),
    Real.norm_of_nonneg (sq_nonneg (n : ℝ))] at hbound
  have hn_sq_pos : (0 : ℝ) < (n : ℝ) ^ 2 := by
    have : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn_pos
    positivity
  nlinarith
