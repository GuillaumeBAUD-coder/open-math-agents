import FormalConjectures.OEIS.«1157»

/-! Reduce normalized divisor-sum collisions to pairs with overlapping prime supports
that are incomparable under divisibility, after cancelling common unitary factors. -/

-- Reduction OeisA1157.conjecture.R1 of Sum of squares of divisors of $n$
-- Credit: @JamesSlash
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_OeisA1157_conjecture_R1

open ArithmeticFunction Finset

-- Equal prime supports, with every common unitary factor already removed.
def H1 : Prop :=
  ∀ k : ℕ, 2 ≤ k → ∀ n m : ℕ, 0 < n → 0 < m → ¬ n ∣ m → ¬ m ∣ n → ¬ n.Coprime m →
    (∀ d a b : ℕ, 1 < d → n = d * a → m = d * b → d.Coprime a → ¬ d.Coprime b) →
    n.primeFactors = m.primeFactors →
    sigma k n * m ^ k ≠ sigma k m * n ^ k

-- Intersecting but different prime supports, again after all common unitary factors are removed.
def H2 : Prop :=
  ∀ k : ℕ, 2 ≤ k → ∀ n m : ℕ, 0 < n → 0 < m → ¬ n ∣ m → ¬ m ∣ n → ¬ n.Coprime m →
    (∀ d a b : ℕ, 1 < d → n = d * a → m = d * b → d.Coprime a → ¬ d.Coprime b) →
    n.primeFactors ≠ m.primeFactors →
    sigma k n * m ^ k ≠ sigma k m * n ^ k

theorem ratio_eq_sum (k n : ℕ) (hn : 0 < n) :
    (sigma k n : ℚ) / (n : ℚ) ^ k = ∑ d ∈ n.divisors, 1 / (d : ℚ) ^ k := by
  rw [sigma_eq_sum_div, Nat.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d hd
  have hpos : 0 < (d : ℚ) := by exact_mod_cast Nat.pos_of_mem_divisors hd
  have hnq : 0 < (n : ℚ) := by exact_mod_cast hn
  rw [Nat.cast_pow, Nat.cast_div (Nat.dvd_of_mem_divisors hd) hpos.ne', div_pow]
  field_simp

theorem telescope (N : ℕ) :
    (∑ i ∈ range N, (1 / ((i : ℚ) + 1) - 1 / ((i : ℚ) + 2))) =
      1 - 1 / ((N : ℚ) + 1) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [sum_range_succ, ih, Nat.cast_succ]
    rw [show (N : ℚ) + 1 + 1 = (N : ℚ) + 2 by ring]
    ring

theorem ratio_bounds (k n : ℕ) (hk : 2 ≤ k) (hn : 0 < n) :
    1 ≤ (sigma k n : ℚ) / (n : ℚ) ^ k ∧ (sigma k n : ℚ) / (n : ℚ) ^ k < 2 := by
  rw [ratio_eq_sum k n hn]
  have hsplit := Finset.sum_erase_add n.divisors (fun d ↦ (1 : ℚ) / (d : ℚ) ^ k)
    (Nat.one_mem_divisors.mpr hn.ne')
  simp only [Nat.cast_one, one_pow, div_one] at hsplit
  rw [← hsplit]
  have hnonneg : 0 ≤ ∑ d ∈ n.divisors.erase 1, (1 : ℚ) / (d : ℚ) ^ k := by
    exact Finset.sum_nonneg fun d _ ↦ by positivity
  refine ⟨by linarith, ?_⟩
  have hsubset : n.divisors.erase 1 ⊆ Ico 2 (n + 1) := by
    intro d hd
    have hm := mem_of_mem_erase hd
    have hpos := Nat.pos_of_mem_divisors hm
    have hle := Nat.divisor_le hm
    have hne := ne_of_mem_erase hd
    exact mem_Ico.mpr ⟨by omega, by omega⟩
  have hle : (∑ d ∈ n.divisors.erase 1, (1 : ℚ) / (d : ℚ) ^ k) ≤
      ∑ d ∈ Ico 2 (n + 1), (1 / ((d : ℚ) - 1) - 1 / (d : ℚ)) := by
    calc
      _ ≤ ∑ d ∈ Ico 2 (n + 1), (1 : ℚ) / (d : ℚ) ^ k :=
        sum_le_sum_of_subset_of_nonneg hsubset (fun d _ _ ↦ by positivity)
      _ ≤ _ := by
        apply sum_le_sum
        intro d hd
        have hd2 : (2 : ℚ) ≤ d := by exact_mod_cast (mem_Ico.mp hd).1
        have hdpos : 0 < (d : ℚ) := by linarith
        have hdsub : 0 < (d : ℚ) - 1 := by linarith
        rw [show 1 / ((d : ℚ) - 1) - 1 / (d : ℚ) =
          1 / ((d : ℚ) * ((d : ℚ) - 1)) by field_simp; ring]
        apply one_div_le_one_div_of_le (mul_pos hdpos hdsub)
        calc
          _ ≤ (d : ℚ) ^ 2 := by nlinarith
          _ ≤ _ := pow_le_pow_right₀ (by linarith) hk
  have htel : (∑ d ∈ Ico 2 (n + 1), (1 / ((d : ℚ) - 1) - 1 / (d : ℚ))) =
      1 - 1 / ((n - 1 : ℕ) + 1 : ℚ) := by
    rw [sum_Ico_eq_sum_range]
    rw [show n + 1 - 2 = n - 1 by omega, ← telescope (n - 1)]
    apply sum_congr rfl
    intro i _
    push_cast
    rw [show 2 + (i : ℚ) - 1 = (i : ℚ) + 1 by ring, add_comm (2 : ℚ)]
  rw [htel] at hle
  have hpos : (0 : ℚ) < 1 / ((n - 1 : ℕ) + 1 : ℚ) := by positivity
  linarith

theorem ratio_eq_one_imp (k n : ℕ) (hn : 0 < n)
    (h : (sigma k n : ℚ) / (n : ℚ) ^ k = 1) : n = 1 := by
  by_contra hne
  have hsplit := Finset.sum_erase_add n.divisors (fun d ↦ (1 : ℚ) / (d : ℚ) ^ k)
    (Nat.one_mem_divisors.mpr hn.ne')
  simp only [Nat.cast_one, one_pow, div_one] at hsplit
  rw [ratio_eq_sum k n hn, ← hsplit] at h
  have hmem : n ∈ n.divisors.erase 1 :=
    mem_erase.mpr ⟨hne, Nat.mem_divisors_self n hn.ne'⟩
  have hterm : 1 / (n : ℚ) ^ k ≤ ∑ d ∈ n.divisors.erase 1, (1 : ℚ) / (d : ℚ) ^ k :=
    single_le_sum (f := fun d : ℕ ↦ (1 : ℚ) / (d : ℚ) ^ k) (fun d _ ↦ by positivity) hmem
  have hpos : 0 < (1 : ℚ) / (n : ℚ) ^ k := by positivity
  linarith

theorem cross_product {k n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (h : (sigma k n : ℚ) / (n : ℚ) ^ k = (sigma k m : ℚ) / (m : ℚ) ^ k) :
    sigma k n * m ^ k = sigma k m * n ^ k := by
  have hq := (div_eq_div_iff (by positivity : (n : ℚ) ^ k ≠ 0)
    (by positivity : (m : ℚ) ^ k ≠ 0)).mp h
  exact_mod_cast hq

theorem eq_one_of_coprime_cross_product {k n m : ℕ} (hk : 2 ≤ k) (hn : 0 < n)
    (hc : n.Coprime m)
    (h : sigma k n * m ^ k = sigma k m * n ^ k) : n = 1 := by
  have hkp : 0 < k := by omega
  have hcp : (n ^ k).Coprime (m ^ k) :=
    (Nat.coprime_pow_left_iff hkp n (m ^ k)).mpr ((Nat.coprime_pow_right_iff hkp n m).mpr hc)
  have hd : n ^ k ∣ sigma k n * m ^ k := by rw [h]; exact dvd_mul_left _ _
  obtain ⟨a, ha⟩ := hcp.dvd_of_dvd_mul_right hd
  have hrat : (sigma k n : ℚ) / (n : ℚ) ^ k = (a : ℚ) := by
    rw [ha, Nat.cast_mul, Nat.cast_pow]
    field_simp
  obtain ⟨hlo, hhi⟩ := ratio_bounds k n hk hn
  rw [hrat] at hlo hhi
  have ha₁ : 1 ≤ a := by exact_mod_cast hlo
  have ha₂ : a < 2 := by exact_mod_cast hhi
  apply ratio_eq_one_imp k n hn
  rw [hrat, show a = 1 by omega, Nat.cast_one]

theorem ratio_mul {k d a : ℕ} (hc : d.Coprime a) :
    (sigma k (d * a) : ℚ) / ((d * a : ℕ) : ℚ) ^ k =
      ((sigma k d : ℚ) / (d : ℚ) ^ k) * ((sigma k a : ℚ) / (a : ℚ) ^ k) := by
  rw [isMultiplicative_sigma.map_mul_of_coprime hc, Nat.cast_mul, Nat.cast_mul, mul_pow, div_mul_div_comm]

theorem ratio_lt_of_dvd_of_ne {k n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (hdvd : n ∣ m) (hne : n ≠ m) :
    (sigma k n : ℚ) / (n : ℚ) ^ k < (sigma k m : ℚ) / (m : ℚ) ^ k := by
  rw [ratio_eq_sum k n hn, ratio_eq_sum k m hm]
  have hsub : n.divisors ⊆ m.divisors := by
    intro d hd
    exact Nat.mem_divisors.mpr ⟨(Nat.dvd_of_mem_divisors hd).trans hdvd, hm.ne'⟩
  have hmissing : m ∉ n.divisors := by
    intro hmem
    exact hne (Nat.dvd_antisymm hdvd (Nat.dvd_of_mem_divisors hmem))
  exact sum_lt_sum_of_subset (f := fun d : ℕ ↦ (1 : ℚ) / (d : ℚ) ^ k)
    hsub (Nat.mem_divisors_self m hm.ne') hmissing
    (by positivity) (fun d _ _ ↦ by positivity)

theorem no_collision (h1 : H1) (h2 : H2) (k : ℕ) (hk : 2 ≤ k) :
    ∀ total n m : ℕ, n + m = total → 0 < n → 0 < m → n ≠ m →
      (sigma k n : ℚ) / (n : ℚ) ^ k ≠ (sigma k m : ℚ) / (m : ℚ) ^ k := by
  intro total
  induction total using Nat.strong_induction_on with
  | h total ih =>
    intro n m htotal hn hm hne hr
    have hcross := cross_product hn hm hr
    by_cases hc : n.Coprime m
    · exact hne ((eq_one_of_coprime_cross_product hk hn hc hcross).trans
        (eq_one_of_coprime_cross_product hk hm hc.symm hcross.symm).symm)
    have hnm : ¬ n ∣ m := fun hdvd ↦ (ratio_lt_of_dvd_of_ne hn hm hdvd hne).ne hr
    have hmn : ¬ m ∣ n := fun hdvd ↦ (ratio_lt_of_dvd_of_ne hm hn hdvd hne.symm).ne hr.symm
    by_cases hu : ∀ d a b : ℕ, 1 < d → n = d * a → m = d * b → d.Coprime a → ¬ d.Coprime b
    · by_cases hs : n.primeFactors = m.primeFactors
      · exact h1 k hk n m hn hm hnm hmn hc hu hs hcross
      · exact h2 k hk n m hn hm hnm hmn hc hu hs hcross
    push Not at hu
    obtain ⟨d, a, b, hd, rfl, rfl, hda, hdb⟩ := hu
    have ha : 0 < a := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
    have hb : 0 < b := Nat.pos_of_ne_zero (by rintro rfl; simp at hm)
    have hal : a < d * a := by nlinarith
    have hbl : b < d * b := by nlinarith
    have hd₀ : 0 < d := by omega
    have hratio : (sigma k d : ℚ) / (d : ℚ) ^ k ≠ 0 :=
      ne_of_gt (lt_of_lt_of_le zero_lt_one (ratio_bounds k d hk hd₀).1)
    rw [ratio_mul hda, ratio_mul hdb] at hr
    exact ih (a + b) (by omega) a b rfl ha hb (fun hab ↦ hne (congrArg (d * ·) hab))
      (mul_left_cancel₀ hratio hr)

theorem main : H1 → H2 → type_of% @OeisA1157.conjecture := by
  intro h1 h2 k hk n m hn hm hne hfract
  obtain ⟨hnlo, hnhi⟩ := ratio_bounds k n hk hn
  obtain ⟨hmlo, hmhi⟩ := ratio_bounds k m hk hm
  have hnf : ⌊(sigma k n : ℚ) / (n : ℚ) ^ k⌋ = 1 := Int.floor_eq_iff.mpr (by norm_num; exact ⟨hnlo, hnhi⟩)
  have hmf : ⌊(sigma k m : ℚ) / (m : ℚ) ^ k⌋ = 1 := Int.floor_eq_iff.mpr (by norm_num; exact ⟨hmlo, hmhi⟩)
  apply no_collision h1 h2 k hk (n + m) n m rfl hn hm hne
  simpa [Int.fract, hnf, hmf] using hfract

end OMA.R_OeisA1157_conjecture_R1
