import OMAReductions.R_CramerConjecture_cramer_conjecture_variants_baker_harman_pintz_R1

/-! Reduction to the BHP prime-counting estimate, with the finite localization proved. -/

open Filter Real ArithmeticFunction Finset
open scoped Topology

namespace OMA.R_CramerConjecture_cramer_conjecture_variants_baker_harman_pintz_R1_H1_R1

/-- The prime-counting lower bound at the end of the BHP proof. -/
def H1 : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ a : ℕ in atTop,
    c * (a : ℝ) ^ (0.525 : ℝ) ≤ Real.log a *
      (((Ioc a (a + ⌊(a : ℝ) ^ (0.525 : ℝ)⌋₊)).filter Nat.Prime).card : ℝ)

/-- The finite localization inequality for the integrated sum. -/
def H2 : Prop :=
  let F (n : ℕ) := ∑ k ∈ range n, (Λ k : ℝ) * ((n : ℝ) - k)
  ∀ a h : ℕ, (h : ℝ) / 2 * (∑ k ∈ Ico (a+h-h/2) (a+h+h/2), (Λ k : ℝ)) ≤
    F (a+2*h) - 2*F (a+h) + F a

lemma tent_nonneg (a h k : ℝ) (hh : 0 ≤ h) :
    0 ≤ max (a + 2 * h - k) 0 - 2 * max (a + h - k) 0 + max (a - k) 0 := by
  simp only [max_def]
  split_ifs <;> linarith

lemma tent_central (a h k : ℝ) (hh : 0 ≤ h)
    (hl : a + h / 2 ≤ k) (hu : k ≤ a + 3 * h / 2) :
    h / 2 ≤ max (a + 2 * h - k) 0 - 2 * max (a + h - k) 0 + max (a - k) 0 := by
  simp only [max_def]
  split_ifs <;> linarith

lemma truncate_eq {n N : ℕ} (hn : n ≤ N) :
    (∑ k ∈ range n, (Λ k : ℝ) * ((n : ℝ) - k)) =
      ∑ k ∈ range N, (Λ k : ℝ) * max ((n : ℝ) - k) 0 := by
  exact OMA.R_CramerConjecture_cramer_conjecture_variants_baker_harman_pintz_R1.truncate_sum hn

lemma finite_tent (a h : ℕ) :
    let F (n : ℕ) := ∑ k ∈ range n, (Λ k : ℝ) * ((n : ℝ) - k)
    (h : ℝ) / 2 * (∑ k ∈ Ico (a+h-h/2) (a+h+h/2), (Λ k : ℝ)) ≤
      F (a+2*h) - 2*F (a+h) + F a := by
  dsimp only
  let W (k : ℕ) := (Λ k : ℝ) *
    (max ((a : ℝ) + 2*h-k) 0 - 2*max ((a : ℝ)+h-k) 0 + max ((a : ℝ)-k) 0)
  have hq : 2 * (h / 2 : ℕ) ≤ h := by omega
  have hqr : 2 * ((h / 2 : ℕ) : ℝ) ≤ h := by exact_mod_cast hq
  have hsub : ((a+h-h/2 : ℕ) : ℝ) = (a : ℝ) + h - (h/2 : ℕ) := by
    rw [Nat.cast_sub (by omega), Nat.cast_add]
  calc
    _ = ∑ k ∈ Ico (a+h-h/2) (a+h+h/2), (h : ℝ)/2 * (Λ k : ℝ) := by rw [mul_sum]
    _ ≤ ∑ k ∈ Ico (a+h-h/2) (a+h+h/2), W k := by
      apply sum_le_sum
      intro k hk
      obtain ⟨hl, hu⟩ := mem_Ico.mp hk
      have hlr : (a : ℝ) + h - (h/2 : ℕ) ≤ k := by
        rw [← hsub]
        exact_mod_cast hl
      have hur : (k : ℝ) < (a : ℝ) + h + (h/2 : ℕ) := by exact_mod_cast hu
      have ht := tent_central (a : ℝ) h k (Nat.cast_nonneg h) (by linarith) (by linarith)
      dsimp only [W]
      nlinarith only [mul_le_mul_of_nonneg_left ht (vonMangoldt_nonneg (n := k))]
    _ ≤ ∑ k ∈ range (a+2*h), W k := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro k hk
        have := (mem_Ico.mp hk).2
        apply mem_range.mpr
        omega
      · intro k hk hnot
        exact mul_nonneg vonMangoldt_nonneg (tent_nonneg _ _ _ (Nat.cast_nonneg h))
    _ = _ := by
      rw [truncate_eq (N := a+2*h) le_rfl,
        truncate_eq (n := a+h) (N := a+2*h) (by omega),
        truncate_eq (n := a) (N := a+2*h) (by omega),
        mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
      apply sum_congr rfl
      intro k hk
      dsimp only [W]
      push_cast
      ring

theorem H2_proved : H2 := by
  intro a h
  exact finite_tent a h

lemma prime_count_le_mass (a b L U : ℕ) (ha : 1 ≤ a) (hL : L ≤ a)
    (hU : a + b < U) :
    Real.log a * (((Ioc a (a+b)).filter Nat.Prime).card : ℝ) ≤
      ∑ k ∈ Ico L U, (Λ k : ℝ) := by
  calc
    _ = ∑ k ∈ (Ioc a (a+b)).filter Nat.Prime, Real.log a := by simp [mul_comm]
    _ ≤ ∑ k ∈ (Ioc a (a+b)).filter Nat.Prime, (Λ k : ℝ) := by
      apply sum_le_sum
      intro k hk
      obtain ⟨hk, hp⟩ := mem_filter.mp hk
      rw [vonMangoldt_apply_prime hp]
      apply Real.log_le_log
      · exact_mod_cast (show 0 < a by omega)
      · exact_mod_cast (mem_Ioc.mp hk).1.le
    _ ≤ ∑ k ∈ Ico L U, (Λ k : ℝ) := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro k hk
        obtain ⟨hk, hp⟩ := mem_filter.mp hk
        obtain ⟨hl, hu⟩ := mem_Ioc.mp hk
        apply mem_Ico.mpr
        omega
      · intro k hk hnot
        exact vonMangoldt_nonneg

lemma scale_small : ∀ᶠ x : ℕ in atTop,
    4 ≤ (x : ℝ) ^ (0.525 : ℝ) ∧ 2 * ⌈2 * (x : ℝ) ^ (0.525 : ℝ)⌉₊ ≤ x := by
  have hn : Tendsto (fun x : ℕ => (x : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hr := ((tendsto_rpow_atTop (y := (0.525 : ℝ)) (by norm_num)).comp hn).eventually
    (eventually_ge_atTop (4 : ℝ))
  have hs := ((tendsto_rpow_atTop (y := (0.475 : ℝ)) (by norm_num)).comp hn).eventually
    (eventually_ge_atTop (8 : ℝ))
  filter_upwards [hr, hs, eventually_ge_atTop (1 : ℕ)] with x hx hs hx1
  change 4 ≤ (x : ℝ) ^ (0.525 : ℝ) at hx
  change 8 ≤ (x : ℝ) ^ (0.475 : ℝ) at hs
  refine ⟨hx, ?_⟩
  have xp : (0 : ℝ) < x := by exact_mod_cast hx1
  have prod : (x : ℝ) ^ (0.525 : ℝ) * (x : ℝ) ^ (0.475 : ℝ) = x := by
    rw [← Real.rpow_add xp]
    norm_num
  have ceil_lt := Nat.ceil_lt_add_one
    (by positivity : 0 ≤ 2 * (x : ℝ) ^ (0.525 : ℝ))
  have eight : 8 * (x : ℝ) ^ (0.525 : ℝ) ≤ x := by
    nlinarith only [prod, mul_le_mul_of_nonneg_left hs
      (Real.rpow_nonneg (Nat.cast_nonneg x) (0.525 : ℝ))]
  have bound : 2 * (⌈2 * (x : ℝ) ^ (0.525 : ℝ)⌉₊ : ℝ) ≤ x := by
    linarith
  exact_mod_cast bound

theorem main : H1 → H2 → OMA.R_CramerConjecture_cramer_conjecture_variants_baker_harman_pintz_R1.H1 := by
  rintro ⟨c, hc, hd⟩ ht
  let h (x : ℕ) := ⌈2 * (x : ℝ) ^ (0.525 : ℝ)⌉₊
  let a (x : ℕ) := x + h x - h x / 2
  let m (x : ℕ) := 2 * (h x / 2)
  let b (x : ℕ) := ⌊(a x : ℝ) ^ (0.525 : ℝ)⌋₊
  have ha : Tendsto a atTop atTop := by
    apply tendsto_atTop_mono (f := fun x : ℕ => x) _ tendsto_id
    intro x
    dsimp only [a]
    omega
  refine ⟨c / 6, by positivity, ?_⟩
  filter_upwards [ha.eventually hd, scale_small, eventually_ge_atTop (1 : ℕ)] with x hd hx hx1
  have hceil : 2 * (x : ℝ) ^ (0.525 : ℝ) ≤ (h x : ℝ) := Nat.le_ceil _
  have hceil_lt : (h x : ℝ) < 2 * (x : ℝ) ^ (0.525 : ℝ) + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hsmall : 2 * h x ≤ x := hx.2
  have hsmallr : 2 * (h x : ℝ) ≤ x := by exact_mod_cast hsmall
  have har : (a x : ℝ) ≤ (3 / 2 : ℝ) * x := by
    have han : a x ≤ x + h x := by dsimp only [a]; omega
    have hanr : (a x : ℝ) ≤ (x : ℝ) + h x := by exact_mod_cast han
    linarith
  have power : (a x : ℝ) ^ (0.525 : ℝ) ≤
      (3 / 2 : ℝ) * (x : ℝ) ^ (0.525 : ℝ) := by
    calc
      _ ≤ ((3 / 2 : ℝ) * (x : ℝ)) ^ (0.525 : ℝ) :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) har (by norm_num)
      _ = (3 / 2 : ℝ) ^ (0.525 : ℝ) * (x : ℝ) ^ (0.525 : ℝ) :=
        Real.mul_rpow (by norm_num) (Nat.cast_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (Real.rpow_le_self_of_one_le (by norm_num) (by norm_num))
        (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hmn : h x ≤ m x + 1 := by dsimp only [m]; omega
  have hmr : (h x : ℝ) ≤ (m x : ℝ) + 1 := by exact_mod_cast hmn
  have hfloor : (b x : ℝ) ≤ (a x : ℝ) ^ (0.525 : ℝ) := Nat.floor_le (by positivity)
  have hbmr : (b x : ℝ) < m x := by linarith [hx.1]
  have hbm : b x < m x := by exact_mod_cast hbmr
  have heq : a x + m x = x + h x + h x / 2 := by dsimp only [a, m]; omega
  have han : x ≤ a x := by dsimp only [a]; omega
  have prime_mass := prime_count_le_mass (a x) (b x)
    (x+h x-h x/2) (x+h x+h x/2) (by omega) (by rfl) (by omega)
  have alower : (x : ℝ) ^ (0.525 : ℝ) ≤ (a x : ℝ) ^ (0.525 : ℝ) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast han) (by norm_num)
  have hrh : (h x : ℝ) / 3 ≤ (a x : ℝ) ^ (0.525 : ℝ) := by linarith [hx.1]
  have mass' : c * (h x : ℝ) / 3 ≤
      ∑ k ∈ Ico (x+h x-h x/2) (x+h x+h x/2), (Λ k : ℝ) := by
    change c * (a x : ℝ) ^ (0.525 : ℝ) ≤ Real.log (a x) *
      (((Ioc (a x) (a x + b x)).filter Nat.Prime).card : ℝ) at hd
    nlinarith only [hd, prime_mass, mul_le_mul_of_nonneg_left hrh hc.le]
  have tent := ht x (h x)
  have scaled := mul_le_mul_of_nonneg_left mass'
    (by positivity : 0 ≤ (h x : ℝ) / 2)
  change c / 6 * (h x : ℝ)^2 ≤ _
  calc
    c / 6 * (h x : ℝ)^2 = (h x : ℝ) / 2 * (c * (h x : ℝ) / 3) := by ring
    _ ≤ (h x : ℝ) / 2 * (∑ k ∈ Ico (x+h x-h x/2) (x+h x+h x/2), (Λ k : ℝ)) := scaled
    _ ≤ _ := tent

theorem analytic_suffices : H1 → OMA.R_CramerConjecture_cramer_conjecture_variants_baker_harman_pintz_R1.H1 := by
  intro h
  exact main h H2_proved

end OMA.R_CramerConjecture_cramer_conjecture_variants_baker_harman_pintz_R1_H1_R1

