import FormalConjectures.Wikipedia.CramerConjecture

-- Reduction CramerConjecture.cramer_conjecture.variants.baker_harman_pintz.R2 of Baker–Harman–Pintz Bound
-- Credit: @mucoucah
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-! H1 is the analytic core in von Mangoldt (Chebyshev psi) form, on the plain
interval of length the ceiling of x^0.525 (no tent weights). H2 is the
elementary fact that proper prime powers contribute negligibly to such an
interval. Together they give a prime in every interval of length 2 x^0.525,
and the indexed gap bound follows. -/
namespace OMA.R_CramerConjecture_cramer_conjecture_variants_baker_harman_pintz_R2

open Filter Real Asymptotics ArithmeticFunction Finset

/-- Baker–Harman–Pintz in psi form: psi(x+h)-psi(x) is at least c h for h = ceil(x^0.525). -/
def H1 : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ x : ℕ in atTop,
    c * (⌈(x:ℝ)^(0.525:ℝ)⌉₊ : ℝ) ≤ ∑ k ∈ Ico x (x + ⌈(x:ℝ)^(0.525:ℝ)⌉₊), (Λ k : ℝ)

/-- Proper prime powers carry o(x^0.525) von Mangoldt mass in [x, x + ceil(x^0.525)). -/
def H2 : Prop :=
  (fun x : ℕ => ∑ k ∈ (Ico x (x + ⌈(x:ℝ)^(0.525:ℝ)⌉₊)).filter (fun k => ¬ k.Prime), (Λ k : ℝ))
    =o[atTop] fun x : ℕ => (x:ℝ)^(0.525:ℝ)

theorem glue (C : ℝ) (hC : 0 < C) (hx : ∀ᶠ x : ℕ in atTop,
    ∃ q : ℕ, q.Prime ∧ x ≤ q ∧ (q : ℝ) ≤ x + C * (x : ℝ) ^ (0.525 : ℝ)) :
    (fun n : ℕ => (primeGap n : ℝ)) =O[atTop]
      (fun n : ℕ => (Nat.nth Nat.Prime n : ℝ) ^ (0.525 : ℝ)) := by
  let p := Nat.nth Nat.Prime
  have mono : StrictMono p := Nat.nth_strictMono Nat.infinite_setOfPred_prime
  have ind : Tendsto (fun n => p n + 1) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_succ (p n)) mono.tendsto_atTop
  refine isBigO_iff.mpr ⟨1 + 2 * C, ?_⟩
  filter_upwards [ind.eventually hx] with n hn
  obtain ⟨q, hqp, hq1, hq2⟩ := hn
  have hnq : p (n + 1) ≤ q := by
    by_contra! hlt
    have : q ≤ p n := Nat.le_nth_of_lt_nth_succ hlt hqp
    omega
  have pp : 1 ≤ (p n : ℝ) := by exact_mod_cast (Nat.prime_nth_prime n).one_le
  have pp' := Real.one_le_rpow pp (by norm_num : (0:ℝ) ≤ 0.525)
  have pb : ((p n : ℝ) + 1) ^ (0.525 : ℝ) ≤ 2 * (p n : ℝ) ^ (0.525 : ℝ) := calc
    _ ≤ (2 * (p n : ℝ)) ^ (0.525 : ℝ) := rpow_le_rpow (by positivity) (by linarith) (by norm_num)
    _ = 2 ^ (0.525 : ℝ) * (p n : ℝ) ^ (0.525 : ℝ) := mul_rpow (by norm_num) (Nat.cast_nonneg _)
    _ ≤ _ := by gcongr; exact Real.rpow_le_self_of_one_le (by norm_num) (by norm_num)
  have hle : p n ≤ p (n + 1) := mono.monotone (Nat.le_succ n)
  have gp : (primeGap n : ℝ) = (p (n + 1) : ℝ) - p n := by
    change ((p (n + 1) - p n : ℕ) : ℝ) = _
    push_cast [hle]; ring
  have hq2' : (q : ℝ) ≤ (p n : ℝ) + 1 + C * ((p n : ℝ) + 1) ^ (0.525 : ℝ) := by
    simpa using hq2
  have hnq' : (p (n + 1) : ℝ) ≤ q := by exact_mod_cast hnq
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _),
    Real.norm_of_nonneg (rpow_nonneg (Nat.cast_nonneg _) _)]
  change (primeGap n : ℝ) ≤ (1 + 2 * C) * (p n : ℝ) ^ (0.525 : ℝ)
  rw [gp]
  nlinarith [mul_le_mul_of_nonneg_left pb hC.le]

theorem main : H1 → H2 → type_of% @CramerConjecture.cramer_conjecture.variants.baker_harman_pintz := by
  rintro ⟨c, hc, hψ⟩ hpow
  apply glue 2 (by norm_num)
  have hc2 : 0 < c / 2 := by positivity
  filter_upwards [hψ, hpow.bound hc2, eventually_gt_atTop (0:ℕ)] with x hx hp hx0
  set h := ⌈(x:ℝ)^(0.525:ℝ)⌉₊ with hh
  have x1 : (1:ℝ) ≤ x := by exact_mod_cast hx0
  have xr : 1 ≤ (x:ℝ)^(0.525:ℝ) := Real.one_le_rpow x1 (by norm_num)
  have hge : (x:ℝ)^(0.525:ℝ) ≤ (h:ℝ) := Nat.le_ceil _
  have hlt : (h:ℝ) < (x:ℝ)^(0.525:ℝ) + 1 := Nat.ceil_lt_add_one (by linarith)
  by_contra! absent
  have nop : ∀ k ∈ Ico x (x + h), ¬ k.Prime := by
    intro k hk hkp
    obtain ⟨_, hk2⟩ := mem_Ico.mp hk
    have : (k:ℝ) < x + h := by exact_mod_cast hk2
    exact (absent k hkp (mem_Ico.mp hk).1).not_ge (by linarith)
  have eqn : (Ico x (x + h)).filter (fun k => ¬ k.Prime) = Ico x (x + h) :=
    filter_eq_self.mpr nop
  rw [eqn, Real.norm_of_nonneg (sum_nonneg fun _ _ => vonMangoldt_nonneg),
    Real.norm_of_nonneg (by linarith)] at hp
  nlinarith [mul_le_mul_of_nonneg_left hge hc.le]

end OMA.R_CramerConjecture_cramer_conjecture_variants_baker_harman_pintz_R2
