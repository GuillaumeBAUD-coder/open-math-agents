import FormalConjectures.Wikipedia.ChebyshevBias

/-!
Compare the ordinary prime race modulo four with the prime-power terms underlying
the logarithm of the Dirichlet L-function of the nontrivial real character.
The first powers give the race exactly. Odd prime squares contribute with positive
sign, and Chebyshev's estimate controls their number. All higher powers together
are eventually bounded by the square-root scale divided by the logarithm.
-/

-- Credit: @zarnab222-dev

open Real Filter Finset

namespace ChebyshevBias

/-- Separate ordinary primes and the positive contribution from prime squares to the
weighted count of prime powers for the nontrivial character modulo four. -/
theorem weighted_prime_power_race (n : ℕ) :
    let layer (a : ℕ) := ∑ p ∈ (Nat.primesLE n).filter (fun p => p^a ≤ n),
      (ZMod.χ₄ (p : ZMod 4) : ℝ)^a / a
    let J := ∑ j ∈ Finset.range (Nat.log 2 n), layer (j+1)
    let oddSquares := (Nat.primesLE n.sqrt).filter (fun p => p%2 = 1)
    |J - ((n.primeCountingMod 4 1 : ℝ) - n.primeCountingMod 4 3) - oddSquares.card/2|
      ≤ (⌊(n:ℝ)^(1/3:ℝ)⌋₊:ℝ) * Nat.log 2 n := by
  let S (a : ℕ) := (Nat.primesLE n).filter fun p => p^a ≤ n
  let w (a : ℕ) := ∑ p ∈ S a, (ZMod.χ₄ (p : ZMod 4) : ℝ)^a / a
  let L := Nat.log 2 n
  let U := (Nat.primesLE n.sqrt).filter fun p => p%2 = 1
  let R := ⌊(n:ℝ)^(1/3:ℝ)⌋₊
  change |(∑ j ∈ Finset.range L, w (j+1)) -
    ((n.primeCountingMod 4 1:ℝ) - n.primeCountingMod 4 3) - (U.card:ℝ)/2| ≤ (R:ℝ)*L
  have hχ (p : ℕ) : (ZMod.χ₄ (p : ZMod 4) : ℝ) =
      (if p%4=1 then 1 else 0) - (if p%4=3 then 1 else 0) := by
    rw [ZMod.χ₄_nat_eq_if_mod_four]
    split_ifs <;> norm_num <;> omega
  have hcount (r : ℕ) : (n.primeCountingMod 4 (r : ZMod 4) : ℝ) =
      ∑ p ∈ Nat.primesLE n, if p%4=r%4 then 1 else 0 := by
    rw [Nat.primeCountingMod_natCast_eq_card_filter_mod,
      Nat.primesLE_eq_filter_Icc_one, Finset.sum_boole, Finset.filter_filter]
  have h₁ : w 1 = (n.primeCountingMod 4 1:ℝ) - n.primeCountingMod 4 3 := by
    have hs : S 1 = Nat.primesLE n := by
      ext p
      simp [S, Nat.mem_primesLE]
      tauto
    have hc₁ := hcount 1
    have hc₃ := hcount 3
    norm_num at hc₁ hc₃
    simp only [w, hs, pow_one, Nat.cast_one, div_one, hχ, Finset.sum_sub_distrib]
    rw [hc₁, hc₃]
    simp
  have h₂ : w 2 = (U.card:ℝ)/2 := by
    have hs : S 2 = Nat.primesLE n.sqrt := by
      ext p
      simp only [S, Finset.mem_filter, Nat.mem_primesLE, Nat.le_sqrt']
      constructor
      · rintro ⟨⟨_, hprime⟩, hpow⟩
        exact ⟨hpow, hprime⟩
      · rintro ⟨hpow, hprime⟩
        exact ⟨⟨(Nat.le_sqrt'.mpr hpow).trans (Nat.sqrt_le_self n), hprime⟩, hpow⟩
    dsimp only [w, U]
    rw [hs, ← Finset.sum_div]
    congr 1
    rw [← Finset.sum_boole (R := ℝ)]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [hχ]
    split_ifs <;> norm_num <;> omega
  have vanish (a : ℕ) (ha : L < a) : w a = 0 := by
    apply Finset.sum_eq_zero
    intro p hp
    obtain ⟨hp, hpow⟩ := Finset.mem_filter.mp hp
    obtain ⟨_, hprime⟩ := Nat.mem_primesLE.mp hp
    have hh := Nat.le_log_of_pow_le (by decide : 1 < 2)
      ((Nat.pow_le_pow_left hprime.two_le a).trans hpow)
    exact (not_lt_of_ge hh ha).elim
  have splitSum : (∑ j ∈ Finset.range L, w (j+1)) =
      w 1 + w 2 + ∑ j ∈ Finset.range L, w (2+j+1) := by
    calc
      _ = ∑ j ∈ Finset.range (L+2), w (j+1) := by
        rw [Finset.sum_range_add]
        have hz : ∑ j ∈ Finset.range 2, w (L+j+1) = 0 :=
          Finset.sum_eq_zero fun j _ => vanish _ (by omega)
        rw [hz, add_zero]
      _ = _ := by
        rw [Nat.add_comm L 2, Finset.sum_range_add]
        simp [Finset.sum_range_succ]
  have tail (a : ℕ) (ha : 3 ≤ a) : |w a| ≤ (R:ℝ) := by
    have hsize : (S a).card ≤ R := by
      calc
        (S a).card ≤ (Finset.Icc 1 R).card := by
          apply Finset.card_le_card
          intro p hp
          obtain ⟨hp, hpow⟩ := Finset.mem_filter.mp hp
          obtain ⟨_, prime⟩ := Nat.mem_primesLE.mp hp
          have cube : p^3 ≤ n := (Nat.pow_le_pow_right prime.pos ha).trans hpow
          have hc : (p:ℝ)^3 ≤ (n:ℝ) := by exact_mod_cast cube
          have hc' := Real.rpow_le_rpow (by positivity) hc (by norm_num : 0 ≤ (1/3:ℝ))
          rw [← Real.rpow_natCast_mul (by positivity)] at hc'
          norm_num at hc'
          exact Finset.mem_Icc.mpr ⟨prime.one_le, (Nat.le_floor_iff (by positivity)).2 hc'⟩
        _ = R := by simp
    calc
      |w a| ≤ ∑ p ∈ S a, |(ZMod.χ₄ (p:ZMod 4):ℝ)^a / a| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _p ∈ S a, (1:ℝ) := by
        refine Finset.sum_le_sum fun p _ => ?_
        have hz : 0 < (a:ℝ) := by exact_mod_cast (show 0 < a by omega)
        rw [abs_div, abs_pow, abs_of_pos hz, div_le_iff₀ hz, one_mul]
        have hh : |(ZMod.χ₄ (p:ZMod 4):ℝ)| ≤ 1 := by
          rw [hχ]
          split_ifs <;> norm_num
        have ht := pow_le_pow_left₀ (abs_nonneg _) hh a
        simpa using ht.trans (by simpa using (show (1:ℝ) ≤ a by exact_mod_cast (show 1 ≤ a by omega)))
      _ ≤ (R:ℝ) := by simpa using (show ((S a).card:ℝ) ≤ R by exact_mod_cast hsize)
  rw [splitSum, ← h₁, ← h₂]
  have he : w 1 + w 2 + ∑ j ∈ Finset.range L, w (2+j+1) - w 1 - w 2 =
      ∑ j ∈ Finset.range L, w (2+j+1) := by abel
  rw [he]
  calc
    _ ≤ ∑ j ∈ Finset.range L, |w (2+j+1)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ Finset.range L, (R:ℝ) := Finset.sum_le_sum fun j _ => tail _ (by omega)
    _ = (R:ℝ)*L := by simp [mul_comm]

end ChebyshevBias

namespace PrimeRaceScale

private theorem budget :
    ∀ᶠ n : ℕ in atTop, 1 < n ∧
      (n.sqrt.primeCounting : ℝ)/2 ≤ 3*(Real.sqrt n / Real.log n) ∧
      (n : ℝ)^(1/3:ℝ) * (Nat.log 2 n : ℝ) ≤ Real.sqrt n / Real.log n := by
  have hn := tendsto_natCast_atTop_atTop (R := ℝ)
  have hp := (Real.tendsto_sqrt_atTop.comp hn).eventually
    (Chebyshev.eventually_primeCounting_le (ε := 1) (by norm_num))
  have ht := hn.eventually
    ((isLittleO_log_rpow_rpow_atTop 2 (by norm_num : (0:ℝ) < 1/6)).bound
       (Real.log_pos (by norm_num : (1:ℝ) < 2)))
  filter_upwards [hp,ht,eventually_gt_atTop 1] with n hp ht hn'
  have n0 : (0:ℝ) ≤ n := by positivity
  have hl : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn')
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hs := Real.sqrt_nonneg (n : ℝ)
  have h4 : Real.log 4 ≤ 2 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
    have hr : Real.log (4:ℝ) = 2*Real.log 2 := by
      rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; norm_num
    linarith
  refine ⟨hn', ?_, ?_⟩
  · change (Nat.primeCounting ⌊Real.sqrt (n:ℝ)⌋₊:ℝ) ≤
      (Real.log 4+1)*Real.sqrt n / Real.log (Real.sqrt n) at hp
    rw [Real.nat_floor_real_sqrt_eq_nat_sqrt, Real.log_sqrt n0] at hp
    have hh := (le_div_iff₀ (half_pos hl)).mp hp
    rw [← mul_div_assoc, le_div_iff₀ hl]
    nlinarith [mul_nonneg (sub_nonneg.mpr h4) hs]
  · have hp3 : 0 ≤ (n:ℝ)^(1/3:ℝ) := by positivity
    have h16 : 0 ≤ (n:ℝ)^(1/6:ℝ) := by positivity
    change ‖Real.log (n:ℝ)^(2:ℝ)‖ ≤ Real.log 2 * ‖(n:ℝ)^(1/6:ℝ)‖ at ht
    rw [Real.rpow_two, Real.norm_of_nonneg (sq_nonneg _), Real.norm_of_nonneg h16] at ht
    have hlog := Real.natLog_le_logb n 2
    rw [Real.logb] at hlog
    push_cast at hlog
    rw [le_div_iff₀ hl2] at hlog
    have hprod : (n:ℝ)^(1/3:ℝ)*(n:ℝ)^(1/6:ℝ) = Real.sqrt n := by
      rw [← Real.rpow_add (by positivity : (0:ℝ) < n), show (1/3:ℝ)+1/6=1/2 by norm_num,
        ← Real.sqrt_eq_rpow]
    apply (le_div_iff₀ hl).mpr
    apply (mul_le_mul_iff_left₀ hl2).mp
    nlinarith only [mul_le_mul_of_nonneg_right ht hp3,
      mul_le_mul_of_nonneg_right hlog (mul_nonneg hp3 hl.le), hprod,
      congrArg (fun x : ℝ => x * Real.log 2) hprod]

end PrimeRaceScale

namespace OMA.R_ChebyshevBias_littlewood_mod_four_sign_changes_R1

private theorem correction :
    ∀ᶠ n : ℕ in atTop,
      let layer (a : ℕ) := ∑ p ∈ (Nat.primesLE n).filter (fun p => p^a ≤ n),
        (ZMod.χ₄ (p : ZMod 4) : ℝ)^a / a
      let J := ∑ j ∈ Finset.range (Nat.log 2 n), layer (j+1)
      let D := (n.primeCountingMod 4 1 : ℝ) - n.primeCountingMod 4 3
      let s := Real.sqrt n / Real.log n;
      -s ≤ J-D ∧ J-D ≤ 4*s := by
  filter_upwards [PrimeRaceScale.budget] with n hn
  obtain ⟨_,hs,ht⟩ := hn
  let layer (a : ℕ) := ∑ p ∈ (Nat.primesLE n).filter (fun p => p^a ≤ n),
    (ZMod.χ₄ (p : ZMod 4) : ℝ)^a / a
  let J := ∑ j ∈ Finset.range (Nat.log 2 n), layer (j+1)
  let D := (n.primeCountingMod 4 1 : ℝ) - n.primeCountingMod 4 3
  let s := Real.sqrt n / Real.log n
  let Q := (Nat.primesLE n.sqrt).filter (fun p => p%2=1)
  change -s ≤ J-D ∧ J-D ≤ 4*s
  change (_ : ℝ) ≤ 3*s at hs
  change _ ≤ s at ht
  have hb := ChebyshevBias.weighted_prime_power_race n
  change |J-D-(Q.card:ℝ)/2| ≤ (⌊(n:ℝ)^(1/3:ℝ)⌋₊:ℝ) * Nat.log 2 n at hb
  have hf := Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg n) (1/3:ℝ))
  have he := hb.trans ((mul_le_mul_of_nonneg_right hf (Nat.cast_nonneg (Nat.log 2 n))).trans ht)
  have hq : (Q.card:ℝ) ≤ n.sqrt.primeCounting := by
    exact_mod_cast (Finset.card_filter_le _ _).trans (Nat.primesLE_card_eq_primeCounting n.sqrt).le
  have ⟨hlo,hhi⟩ := abs_le.mp he
  constructor <;> linarith [Nat.cast_nonneg (α := ℝ) Q.card]

/-- Negative excursions of the prime-power sum on the square-root scale. -/
def H1 : Prop := ∀ N : ℕ, ∃ n ≥ N,
  let layer (a : ℕ) := ∑ p ∈ (Nat.primesLE n).filter (fun p => p^a ≤ n),
    (ZMod.χ₄ (p : ZMod 4) : ℝ)^a / a
  let J := ∑ j ∈ Finset.range (Nat.log 2 n), layer (j+1)
  J < -(Real.sqrt n / Real.log n)

/-- Positive excursions large enough to dominate the prime squares. -/
def H2 : Prop := ∀ N : ℕ, ∃ n ≥ N,
  let layer (a : ℕ) := ∑ p ∈ (Nat.primesLE n).filter (fun p => p^a ≤ n),
    (ZMod.χ₄ (p : ZMod 4) : ℝ)^a / a
  let J := ∑ j ∈ Finset.range (Nat.log 2 n), layer (j+1)
  4*(Real.sqrt n / Real.log n) < J

theorem main : H1 → H2 → type_of% @ChebyshevBias.littlewood_mod_four_sign_changes := by
  intro lo hi
  obtain ⟨K,hK⟩ := Filter.eventually_atTop.mp correction
  constructor
  · apply Set.infinite_of_forall_exists_gt
    intro m
    obtain ⟨n,hn,h⟩ := lo (max K (m+1))
    have hc := (hK n (le_trans (le_max_left ..) hn)).1
    refine ⟨n,?_,by omega⟩
    change n.primeCountingMod 4 1 < n.primeCountingMod 4 3
    exact_mod_cast (by linarith : (n.primeCountingMod 4 1 : ℝ) < n.primeCountingMod 4 3)
  · apply Set.infinite_of_forall_exists_gt
    intro m
    obtain ⟨n,hn,h⟩ := hi (max K (m+1))
    have hc := (hK n (le_trans (le_max_left ..) hn)).2
    refine ⟨n,?_,by omega⟩
    change n.primeCountingMod 4 3 < n.primeCountingMod 4 1
    exact_mod_cast (by linarith : (n.primeCountingMod 4 3 : ℝ) < n.primeCountingMod 4 1)

end OMA.R_ChebyshevBias_littlewood_mod_four_sign_changes_R1
