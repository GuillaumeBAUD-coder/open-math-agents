import FormalConjectures.ErdosProblems.«349»
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Tactic

/-!
# An even floor sequence below the golden ratio

Take a root `z₀` of the quintic `P` just above 2 and write it as `a + a⁻¹`,
with `1 < a ≤ 8 / 5`. The four other roots lie between −2 and 2. The rescaled
Chebyshev polynomial `Cₙ` takes the value `aⁿ + a⁻ⁿ` at the first root
and has absolute value at most 2 at the others.

Reduce `Fᵏ Cₙ` modulo the monic polynomial `P` over the integers. At 2,
the remainder is congruent to 2 modulo 5, since `P(2) = −5`, `F(2) = 21`
and `Cₙ(2) = 2`. Lagrange interpolation expresses that same integer as a
weighted sum over the five roots. On the four smaller roots, `|F| ≤ 3 / 4`,
so one choice of `k` makes their total contribution small for every `n`.
Shifting the exponent also makes the reciprocal power small. Scaling the
growing term by `2 / 5` then gives an even floor at every exponent.
-/

namespace OMA.Counterexample349

open Polynomial Filter
open scoped BigOperators

noncomputable def P : ℤ[X] := X ^ 5 - C 6 * X ^ 3 - X ^ 2 + C 7 * X + 1

noncomputable def F : ℤ[X] := X ^ 4 + C 2 * X ^ 3 - X ^ 2 - C 3 * X - 1

noncomputable def leftEndpoint (i : Fin 5) : ℝ := (![2223, -1939, -1350, -143, 1207] : Fin 5 → ℤ) i / (1000 : ℝ)

lemma eval_P (x : ℝ) : aeval x P = x ^ 5 - 6 * x ^ 3 - x ^ 2 + 7 * x + 1 := by
  simp only [P, map_add, map_sub, map_pow, map_mul, map_one, aeval_X, aeval_C]
  norm_num

lemma eval_F (x : ℝ) : aeval x F = x ^ 4 + 2 * x ^ 3 - x ^ 2 - 3 * x - 1 := by
  simp only [F, map_add, map_sub, map_pow, map_mul, map_one, aeval_X, aeval_C]
  norm_num

lemma exists_root_in_interval (i : Fin 5) :
    ∃ x ∈ Set.Icc (leftEndpoint i) (leftEndpoint i + 1 / 1000), aeval x P = 0 := by
  let f := fun x : ℝ => x ^ 5 - 6 * x ^ 3 - x ^ 2 + 7 * x + 1
  have hc : Continuous f := by dsimp [f]; fun_prop
  have hl : leftEndpoint i ≤ leftEndpoint i + 1 / 1000 := by linarith
  suffices 0 ∈ f '' (Set.Icc (leftEndpoint i) (leftEndpoint i + 1 / 1000)) by
    obtain ⟨x, hx, h⟩ := this
    exact ⟨x, hx, by simpa [eval_P, f] using h⟩
  fin_cases i <;> first
    | solve | apply intermediate_value_Icc hl hc.continuousOn; norm_num [f, leftEndpoint, Set.mem_Icc, Matrix.cons_val_succ]
    | apply intermediate_value_Icc' hl hc.continuousOn; norm_num [f, leftEndpoint, Set.mem_Icc, Matrix.cons_val_succ]

-- Rational enclosures for F are certified by expanding about each left endpoint.
lemma damping (i : Fin 5) (x : ℝ) (hx : x ∈ Set.Icc (leftEndpoint i) (leftEndpoint i + 1 / 1000)) :
    if i = 0 then 0 < aeval x F else |aeval x F| ≤ (3 / 4 : ℝ) := by
  let u := x - leftEndpoint i
  have hu : 0 ≤ u := sub_nonneg.mpr hx.1
  have hv : u ≤ 1 / 1000 := by dsimp [u]; linarith [hx.2]
  have hpow (n : ℕ) : 0 ≤ u ^ n ∧ u ^ n ≤ (1 / 1000 : ℝ) ^ n :=
    ⟨pow_nonneg hu _, pow_le_pow_left₀ hu hv _⟩
  have h2 := hpow 2
  have h3 := hpow 3
  have h4 := hpow 4
  have he : x = u + leftEndpoint i := by dsimp [u]; ring
  rw [he]
  fin_cases i <;> norm_num [eval_F, leftEndpoint, Matrix.cons_val_succ, abs_le] <;>
    (try constructor) <;> nlinarith only [hu, hv, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2]

lemma expand_cheb (a : ℝ) (ha : 0 < a) (n : ℕ) :
    (Chebyshev.C ℝ n).eval (a + a⁻¹) = a ^ n + (a⁻¹) ^ n := by
  induction n using Nat.twoStepInduction with
  | zero => norm_num
  | one => simp
  | more n h₀ h₁ =>
    rw [Nat.cast_add, Nat.cast_ofNat, Chebyshev.C_add_two]
    simp only [eval_sub, eval_mul, eval_X, ← Nat.cast_add_one, h₀, h₁]
    rw [pow_add, pow_add, pow_succ, pow_succ]
    simp only [inv_pow]
    field_simp [ha.ne']; ring

lemma bounded_cheb {x : ℝ} (hx : |x| ≤ 2) (n : ℕ) :
    |(Chebyshev.C ℝ n).eval x| ≤ 2 := by
  have h := abs_le.mp hx
  have e : x = 2 * Real.cos (Real.arccos (x / 2)) := by
    rw [Real.cos_arccos (by linarith) (by linarith)]; ring
  conv_lhs => arg 1; rw [e, Chebyshev.C_two_mul_real_cos]
  rw [abs_mul]
  exact (by simpa using mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (by norm_num : (0 : ℝ) ≤ 2))

lemma parity_obstruction {t a : ℝ} (h : ∀ n : ℕ, Even ⌊t * a ^ n⌋) : ¬ Erdos349.IsGoodPair t a := by
  intro good
  obtain ⟨b, hb⟩ := eventually_atTop.mp good
  let k := max b 0
  obtain ⟨s, hs, he⟩ := hb (2 * k + 1) (by dsimp [k]; omega)
  have heven : Even (∑ j ∈ s, j) := by
    apply Finset.even_sum
    intro j hj
    obtain ⟨n, rfl⟩ := hs hj
    exact h n
  obtain ⟨u, hu⟩ := heven
  omega

-- Integer remainders evaluated at 2 can be recovered by interpolation at the five roots.
lemma interpolation (z : Fin 5 → ℝ) (hz : Function.Injective z) (hr : ∀ i, aeval (z i) P = 0)
    (g : ℤ[X]) :
    (((g %ₘ P).eval 2 : ℤ) : ℝ) =
      ∑ i, (aeval (z i) g) * ((Lagrange.basis Finset.univ z i).eval 2) := by
  let r := g %ₘ P
  have hmon : P.Monic := by unfold P; monicity!
  have hdeg : P.degree = 5 := by unfold P; compute_degree!
  have hd : (r.map (Int.castRingHom ℝ)).degree < (Finset.univ : Finset (Fin 5)).card := by
    simpa [hdeg] using (degree_map_le.trans_lt (degree_modByMonic_lt g hmon) :
      (r.map (Int.castRingHom ℝ)).degree < P.degree)
  have heval (i : Fin 5) : (r.map (Int.castRingHom ℝ)).eval (z i) = aeval (z i) g := by
    rw [← eval₂_eq_eval_map]
    exact eval₂_modByMonic_eq_self_of_root (hr i)
  have hi := Lagrange.eq_interpolate_of_eval_eq _ hz.injOn hd (fun i _ => heval i)
  have h := congrArg (Polynomial.eval (2 : ℝ)) hi
  have hcast : (r.map (Int.castRingHom ℝ)).eval 2 = (r.eval 2 : ℤ) :=
    eval_map_apply (Int.castRingHom ℝ) 2
  rw [hcast] at h
  simpa [Lagrange.interpolate_apply, eval_finsetSum, r] using h

-- Since P(2) = −5, integer polynomial reduction preserves evaluation at 2 modulo 5.
lemma interpolated_residue (z : Fin 5 → ℝ) (hz : Function.Injective z) (hr : ∀ i, aeval (z i) P = 0)
    (k n : ℕ) :
    ∃ j : ℤ, (5 * j + 2 : ℝ) = ∑ i, (aeval (z i) F) ^ k *
      (Chebyshev.C ℝ n).eval (z i) * (Lagrange.basis Finset.univ z i).eval 2 := by
  let g := F ^ k * Chebyshev.C ℤ n
  have hP : P.eval 2 = -5 := by norm_num [P]
  have hF : F.eval 2 = 21 := by norm_num [F]
  have hg : g.eval 2 = 21 ^ k * 2 := by simp [g, hF, Chebyshev.C_eval_two]
  have hm : (21 : ℤ) ^ k ≡ 1 [ZMOD 5] := by
    simpa using (show (21 : ℤ) ≡ 1 [ZMOD 5] by decide).pow k
  have he := congrArg (Polynomial.eval (2 : ℤ)) (modByMonic_add_div g P)
  simp only [eval_add, eval_mul, hg, hP] at he
  change (21 : ℤ) ^ k % 5 = 1 % 5 at hm
  have hh : (g %ₘ P).eval 2 = 5 * ((g %ₘ P).eval 2 / 5) + 2 := by omega
  refine ⟨(g %ₘ P).eval 2 / 5, ?_⟩
  rw [← show (((g %ₘ P).eval 2 : ℤ) : ℝ) = 5 * (((g %ₘ P).eval 2 / 5 : ℤ) : ℝ) + 2 by exact_mod_cast hh]
  simpa [g, Chebyshev.aeval_C] using interpolation z hz hr g

lemma small_power {b M : ℝ} (hb : b < 1) (hM : 0 ≤ M) :
    ∃ k : ℕ, b ^ k * M < 1 / 5 := by
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (by positivity : 0 < (1 / 5 : ℝ)/(M + 1)) hb
  refine ⟨k, ?_⟩
  have h := (lt_div_iff₀ (by positivity : 0 < M + 1)).mp hk
  by_cases hk' : b ^ k < 0
  · nlinarith [mul_nonpos_of_nonpos_of_nonneg hk'.le hM]
  · linarith

-- The node above 2 gives a growing mode. At the other four exists_root_in_interval the
-- Chebyshev values stay bounded and powers of F damp their contribution.
set_option maxHeartbeats 1600000 in
lemma witness : ∃ a t : ℝ, 0 < t ∧ a ∈ Set.Ioo 1 ((1 + √5) / 2) ∧ ∀ n : ℕ, Even ⌊t * a ^ n⌋ := by
  classical
  choose z hz hr using exists_root_in_interval
  have hi : Function.Injective z := by
    intro i j h
    by_contra hn
    have hsep : leftEndpoint i + 1 / 1000 < leftEndpoint j ∨ leftEndpoint j + 1 / 1000 < leftEndpoint i := by
      fin_cases i <;> fin_cases j <;> first
      | exact (hn rfl).elim
      | norm_num [leftEndpoint, Matrix.cons_val_succ]
    rcases hsep with h' | h' <;> linarith [(hz i).1, (hz i).2, (hz j).1, (hz j).2]
  have hlarge : 2223 / 1000 ≤ z 0 ∧ z 0 ≤ 2224 / 1000 := by
    convert hz 0 using 1; norm_num [leftEndpoint, Set.mem_Icc]
  have hsmall (i : Fin 5) (hi : i ≠ 0) : -2 < z i ∧ z i < 2 := by
    have hb := hz i
    fin_cases i <;> first
    | exact (hi rfl).elim
    | norm_num [leftEndpoint, Matrix.cons_val_succ, Set.mem_Icc] at hb ⊢
      constructor <;> linarith [hb.1, hb.2]
  let f := fun x : ℝ => x ^ 2 + 1 - z 0 * x
  have hc : Continuous f := by dsimp [f]; fun_prop
  obtain ⟨a, ha, he⟩ := intermediate_value_Icc (by norm_num : (1 : ℝ) ≤ 8 / 5) hc.continuousOn
    (show 0 ∈ Set.Icc (f 1) (f (8 / 5)) by constructor <;> dsimp [f] <;> linarith [hlarge.1, hlarge.2])
  have ha1 : 1 < a := lt_of_le_of_ne ha.1 (by rintro rfl; dsimp [f] at he; linarith [hlarge.1])
  have ha0 : 0 < a := by linarith
  have hroot : z 0 = a + a⁻¹ := by dsimp [f] at he; field_simp; nlinarith
  let w := fun i : Fin 5 => (Lagrange.basis Finset.univ z i).eval 2
  let s := (Finset.univ : Finset (Fin 5)).erase 0
  have hw : 0 < w 0 := by
    dsimp [w, Lagrange.basis]
    rw [eval_prod]
    apply Finset.prod_pos
    intro j hj
    have h := hsmall j (Finset.mem_erase.mp hj).1
    simp only [Lagrange.basisDivisor, eval_mul, eval_C, eval_sub, eval_X]
    exact mul_pos (inv_pos.mpr (by linarith [hlarge.1])) (by linarith)
  obtain ⟨k, hk⟩ := small_power (by norm_num : (3 / 4 : ℝ) < 1)
    (Finset.sum_nonneg (fun i _ => mul_nonneg (by norm_num) (abs_nonneg (w i))) : 0 ≤ ∑ i ∈ s, 2 * |w i|)
  let A := (aeval (z 0) F) ^ k * w 0
  have hF : 0 < aeval (z 0) F := by simpa using damping 0 (z 0) (hz 0)
  have hA : 0 < A := mul_pos (pow_pos hF _) hw
  have hinv : a⁻¹ < 1 := inv_lt_one_of_one_lt₀ ha1
  obtain ⟨m, hm⟩ := small_power hinv hA.le
  refine ⟨a, 2 / 5 * A * a ^ m, by positivity, ⟨ha1, ?_⟩, ?_⟩
  · have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
    nlinarith [ha.2, Real.sqrt_nonneg 5]
  intro n
  let N := m + n
  let v := fun i : Fin 5 => (aeval (z i) F) ^ k * (Chebyshev.C ℝ N).eval (z i) * w i
  obtain ⟨j, hj⟩ := interpolated_residue z hi hr k N
  change (5 * j + 2 : ℝ) = ∑ i, v i at hj
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ 0)] at hj
  change (5 * j + 2 : ℝ) = (∑ i ∈ s, v i) + v 0 at hj
  have hsum : |∑ i ∈ s, v i| < 1 / 5 := by
    refine lt_of_le_of_lt ((Finset.abs_sum_le_sum_abs _ _).trans ?_) hk
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hne := (Finset.mem_erase.mp hi).1
    have hd := damping i (z i) (hz i)
    rw [if_neg hne] at hd
    have hb := bounded_cheb (abs_le.mpr ⟨(hsmall i hne).1.le, (hsmall i hne).2.le⟩) N
    dsimp only [v]
    rw [abs_mul, abs_mul, abs_pow, ← mul_assoc]
    gcongr
  have hv0 : v 0 = A * a ^ N + A * (a⁻¹) ^ N := by
    dsimp only [v, A]
    rw [hroot, expand_cheb a ha0]
    ring
  have htail : A * (a⁻¹) ^ N < 1 / 5 := by
    have hle : (a⁻¹) ^ N ≤ (a⁻¹) ^ m := by
      dsimp [N]
      rw [pow_add]
      exact mul_le_of_le_one_right (by positivity) (pow_le_one₀ (by positivity) hinv.le)
    nlinarith [mul_le_mul_of_nonneg_left hle hA.le]
  have hpos : 0 ≤ A * (a⁻¹) ^ N := by positivity
  have hs' := abs_lt.mp hsum
  rw [hv0] at hj
  refine ⟨j, Int.floor_eq_iff.mpr ?_⟩
  push_cast
  have her : 2 / 5 * A * a ^ m * a ^ n = (2 / 5)* (A * a ^ N) := by dsimp [N]; rw [pow_add]; ring
  rw [her]
  constructor <;> linarith [hs'.1, hs'.2]

end OMA.Counterexample349

theorem OMA.solution : type_of% @Erdos349.complete_for_alpha_in_Ioo_one_to_goldenRatio := by
  obtain ⟨a, t, ht, ha, h⟩ := OMA.Counterexample349.witness
  exact fun hgood => OMA.Counterexample349.parity_obstruction h (hgood t a ht ha)
