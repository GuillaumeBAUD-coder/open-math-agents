import OMAReductions.R_Erdos830_erdos_830_variants_erdos_R1

/-! Averaging the large-divisor tail over all integers up to the cutoff. -/

open Filter Finset OMA.R_Erdos830_erdos_830_variants_erdos_R1
open scoped ArithmeticFunction.sigma

private theorem divisor_tail_eq {n B : ℕ} (hn : 0 < n) :
    (σ 1 n : ℝ) / n - (∑ d ∈ n.divisors.filter (· ≤ B), (1 : ℝ) / d) =
      ∑ d ∈ n.divisors.filter (B < ·), (1 : ℝ) / d := by
  classical
  rw [ratio_eq hn]
  have h := sum_filter_add_sum_filter_not (s := n.divisors) (p := (· ≤ B)) (fun d => (1 : ℝ) / d)
  simp only [not_le] at h
  linarith only [h]

private theorem card_multiples_le (N d : ℕ) (hd : 0 < d) :
    ((Icc 1 N).filter (d ∣ ·)).card ≤ N / d := by
  have hmap : Set.MapsTo (· / d) (↑((Icc 1 N).filter (d ∣ ·)) : Set ℕ)
      (↑(Icc 1 (N / d)) : Set ℕ) := by
    intro n hn
    obtain ⟨hm, hdiv⟩ := mem_filter.mp (mem_coe.mp hn)
    obtain ⟨hn₁, hn₂⟩ := mem_Icc.mp hm
    apply mem_coe.mpr (mem_Icc.mpr ⟨?_, Nat.div_le_div_right hn₂⟩)
    exact (Nat.le_div_iff_mul_le hd).mpr (by simpa using Nat.le_of_dvd (by omega) hdiv)
  have hinj : Set.InjOn (· / d) (↑((Icc 1 N).filter (d ∣ ·)) : Set ℕ) := by
    intro n hn m hm h
    change n / d = m / d at h
    rw [← Nat.div_mul_cancel (mem_filter.mp (mem_coe.mp hn)).2,
      ← Nat.div_mul_cancel (mem_filter.mp (mem_coe.mp hm)).2, h]
  simpa using card_le_card_of_injOn (· / d) hmap hinj

private theorem recip_square_interval {B N : ℕ} (hB : 0 < B) (hBN : B ≤ N) :
    ∑ d ∈ Icc (B + 1) N, (1 : ℝ) / (d : ℝ)^2 ≤ 1 / B - 1 / N := by
  induction N, hBN using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    have hI : Icc (B + 1) (n + 1) = insert (n + 1) (Icc (B + 1) n) := by
      ext d
      simp only [mem_Icc, mem_insert]
      omega
    rw [hI, sum_insert (by simp)]
    have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hstep : (1 : ℝ) / ((n : ℝ) + 1)^2 ≤ 1 / n - 1 / ((n : ℝ) + 1) := by
      have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      field_simp
      nlinarith only [hn']
    push_cast
    linarith only [ih, hstep]

theorem OMA.solution : OMA.R_Erdos830_erdos_830_variants_erdos_R1.H2 := by
  classical
  intro η ε hη hε
  obtain ⟨B, hB⟩ := exists_nat_gt (max 1 (1 / (ε * η)))
  have hBr : (0 : ℝ) < B := zero_lt_one.trans ((le_max_left _ _).trans_lt hB)
  have hB0 : 0 < B := by exact_mod_cast hBr
  have hsmall : (1 : ℝ) / B ≤ ε * η := by
    apply (div_le_iff₀ hBr).mpr
    have h := (div_lt_iff₀ (mul_pos hε hη)).mp ((le_max_right _ _).trans_lt hB)
    linarith only [h]
  refine ⟨B, ?_⟩
  filter_upwards [eventually_ge_atTop B] with N hBN
  let T : ℕ → ℝ := fun n => ∑ d ∈ n.divisors.filter (B < ·), (1 : ℝ) / d
  let S : Finset ℕ := (Icc 1 N).filter
    (fun n => η ≤ (σ 1 n : ℝ) / n - (∑ d ∈ n.divisors.filter (· ≤ B), (1 : ℝ) / d))
  have hTail : ∀ n ∈ Icc 1 N, T n =
      ∑ d ∈ Icc (B + 1) N, if d ∣ n then (1 : ℝ) / d else 0 := by
    intro n hn
    obtain ⟨hn₁, hn₂⟩ := mem_Icc.mp hn
    rw [← sum_filter]
    dsimp only [T]
    congr 1
    ext d
    simp only [mem_filter, mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hd, _⟩, hBd⟩
      exact ⟨⟨by omega, (Nat.le_of_dvd (by omega) hd).trans hn₂⟩, hd⟩
    · rintro ⟨⟨hBd, _⟩, hd⟩
      exact ⟨⟨hd, by omega⟩, by omega⟩
  have hContrib (d : ℕ) (hd : d ∈ Icc (B + 1) N) :
      (∑ n ∈ Icc 1 N, if d ∣ n then (1 : ℝ) / d else 0) ≤
        (N : ℝ) * ((1 : ℝ) / (d : ℝ)^2) := by
    have hd₀ : 0 < d := by have := (mem_Icc.mp hd).1; omega
    have hd' : (0 : ℝ) < d := by exact_mod_cast hd₀
    have hmultiples : ((((Icc 1 N).filter (d ∣ ·)).card : ℕ) : ℝ) ≤ (N : ℝ) / d := by
      apply (le_div_iff₀ hd').mpr
      exact_mod_cast (Nat.mul_le_mul_right d (card_multiples_le N d hd₀)).trans (Nat.div_mul_le_self N d)
    rw [← sum_filter, sum_const, nsmul_eq_mul]
    calc
      _ ≤ ((N : ℝ) / d) * (1 / (d : ℝ)) := mul_le_mul_of_nonneg_right hmultiples (by positivity)
      _ = _ := by ring
  change (S.card : ℝ) ≤ ε * N
  apply (mul_le_mul_iff_right₀ hη).mp
  calc
    η * (S.card : ℝ) = ∑ _ ∈ S, η := by simp [nsmul_eq_mul, mul_comm]
    _ ≤ ∑ n ∈ S, T n := by
      apply sum_le_sum
      intro n hn
      obtain ⟨hmem, hlarge⟩ := mem_filter.mp hn
      rw [divisor_tail_eq (show 0 < n by have := (mem_Icc.mp hmem).1; omega)] at hlarge
      exact hlarge
    _ ≤ ∑ n ∈ Icc 1 N, T n :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by dsimp [T]; positivity)
    _ = ∑ d ∈ Icc (B + 1) N, ∑ n ∈ Icc 1 N, if d ∣ n then (1 : ℝ) / d else 0 := by
      rw [sum_comm]
      exact sum_congr rfl hTail
    _ ≤ ∑ d ∈ Icc (B + 1) N, (N : ℝ) * ((1 : ℝ) / (d : ℝ)^2) := sum_le_sum hContrib
    _ ≤ (N : ℝ) * (1 / (B : ℝ)) := by
      rw [← mul_sum]
      have h := recip_square_interval hB0 hBN
      have hnonneg : (0 : ℝ) ≤ 1 / (N : ℝ) := by positivity
      exact mul_le_mul_of_nonneg_left (by linarith only [h, hnonneg]) (Nat.cast_nonneg N)
    _ ≤ η * (ε * N) := by
      calc
        _ ≤ (N : ℝ) * (ε * η) := mul_le_mul_of_nonneg_left hsmall (Nat.cast_nonneg _)
        _ = _ := by ring
