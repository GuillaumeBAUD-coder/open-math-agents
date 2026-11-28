import FormalConjectures.OEIS.«120424»

/-!
# Half-Fibonacci density from mean gaps

An even transformed term of valuation `s` begins a gap of length `s + 2`.
A geometric valuation law predicts capped mean gaps of `4 - 2 * (1/2)^K`.
-/

-- Credit: @Pockenauer-AI

open Filter Finset
open scoped Topology

namespace OMA.R_OeisA120424_conjecture1_R1

open OeisA120424 (a f)

private theorem b_step (n : ℕ) : f (a (n + 2)) = f (f (a n) + f (a (n + 1))) := by
  rw [a, Nat.add_comm]

private theorem no_two_even (n : ℕ) : ¬ (f (a n) % 2 = 0 ∧ f (a (n + 1)) % 2 = 0) := by
  induction n with
  | zero => decide
  | succ n ih =>
    intro h
    change f (a (n + 1)) % 2 = 0 ∧ f (a (n + 2)) % 2 = 0 at h
    change ¬ (f (a n) % 2 = 0 ∧ f (a (n + 1)) % 2 = 0) at ih
    rw [b_step] at h
    have hodd : (f (a n) + f (a (n + 1))) % 2 ≠ 0 := by omega
    have heq : f (f (a n) + f (a (n + 1))) = f (a n) + f (a (n + 1)) := if_neg hodd
    rw [heq] at h
    exact hodd h.2

private theorem positive_b (n : ℕ) : 0 < f (a n) := by
  induction n using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more n h₀ h₁ =>
    rw [b_step]
    suffices ∀ x : ℕ, 2 ≤ x → 0 < f x from this _ (by omega)
    intro x hx
    unfold f
    split_ifs <;> omega

private theorem consecutive_ne (n : ℕ) : f (a n) ≠ f (a (n + 1)) := by
  induction n with
  | zero => decide
  | succ n ih =>
    change f (a (n + 1)) ≠ f (a (n + 2))
    rw [b_step]
    suffices ∀ x y : ℕ, 0 < x → x ≠ y → y ≠ f (x + y) from this _ _ (positive_b n) ih
    intro x y hx hxy
    unfold f
    split_ifs <;> omega

private theorem infinitely_many_even : (Set.ofPred (fun k => f (a k) % 2 = 0)).Infinite := by
  refine Set.infinite_of_forall_exists_gt fun N => ?_
  by_contra! h
  have odd_above (c : ℕ) (hc : N < c) : f (a c) % 2 ≠ 0 := fun he => hc.not_ge (h c he)
  let difference := fun j : ℕ => (f (a (N + 1 + j + 1)) : ℤ) - f (a (N + 1 + j))
  have decrease (j : ℕ) : (difference (j + 1)).natAbs + 1 ≤ (difference j).natAbs := by
    let n := N + 1 + j
    have h₀ : f (a n) % 2 ≠ 0 := odd_above n (by dsimp [n]; omega)
    have h₁ : f (a (n + 1)) % 2 ≠ 0 := odd_above (n + 1) (by dsimp [n]; omega)
    have hsum : (f (a n) + f (a (n + 1))) % 2 = 0 := by omega
    have hnext : f (a (n + 2)) = (f (a n) + f (a (n + 1))) / 2 := by
      rw [b_step]
      exact if_pos hsum
    have hrel : difference j = (-2) * difference (j + 1) := by
      change (f (a (n + 1)) : ℤ) - f (a n) = (-2) * ((f (a (n + 2)) : ℤ) - f (a (n + 1)))
      omega
    have hne : 0 < (difference (j + 1)).natAbs := by
      have hne' := consecutive_ne (n + 1)
      change 0 < ((f (a (n + 2)) : ℤ) - f (a (n + 1))).natAbs
      exact Int.natAbs_pos.mpr (sub_ne_zero.mpr (by exact_mod_cast hne'.symm))
    rw [hrel, Int.natAbs_mul]
    norm_num
    omega
  have bound (j : ℕ) : j + (difference j).natAbs ≤ (difference 0).natAbs := by
    induction j with
    | zero => simp
    | succ j ih => have hd := decrease j; omega
  have contradiction := bound ((difference 0).natAbs + 1)
  omega

private theorem gap_ge_three (j : ℕ) :
    let position := Nat.nth (fun n => f (a n) % 2 = 0)
    3 ≤ (position (j + 1) : ℝ) - position j := by
  let evenPosition := fun n => f (a n) % 2 = 0
  let position := Nat.nth evenPosition
  change (3 : ℝ) ≤ (position (j + 1) : ℝ) - position j
  let n := position j
  have he : f (a n) % 2 = 0 := Nat.nth_mem_of_infinite infinitely_many_even j
  have hn : f (a (n + 1)) % 2 ≠ 0 := fun h => no_two_even n ⟨he, h⟩
  have hn' : f (a (n + 2)) % 2 ≠ 0 := by
    have hodd : (f (a n) + f (a (n + 1))) % 2 ≠ 0 := by omega
    rw [b_step, show f (f (a n) + f (a (n + 1))) = f (a n) + f (a (n + 1)) from if_neg hodd]
    exact hodd
  have hlt : n < position (j + 1) := Nat.nth_strictMono infinitely_many_even (Nat.lt_succ_self j)
  have hne₁ : position (j + 1) ≠ n + 1 := fun h => hn (h ▸
    (Nat.nth_mem_of_infinite infinitely_many_even (j + 1) : evenPosition (position (j + 1))))
  have hne₂ : position (j + 1) ≠ n + 2 := fun h => hn' (h ▸
    (Nat.nth_mem_of_infinite infinitely_many_even (j + 1) : evenPosition (position (j + 1))))
  apply (le_sub_iff_add_le).2
  exact_mod_cast (show 3 + position j ≤ position (j + 1) by change 3 + n ≤ _; omega)

private theorem bit_step (n : ℕ) :
    (if a (n + 2) % 2 = 0 then 1 else 0) +
      (if f (a n) % 2 = 0 then 1 else 0) + (if f (a (n + 1)) % 2 = 0 then 1 else 0) = (1 : ℕ) := by
  have h := no_two_even n
  change ¬ (f (a n) % 2 = 0 ∧ f (a (n + 1)) % 2 = 0) at h
  have ha : a (n + 2) = f (a n) + f (a (n + 1)) := by rw [a, Nat.add_comm]
  rw [ha]
  split_ifs <;> omega

private theorem count_identity (n : ℕ) :
    Nat.count (fun k => a k % 2 = 0) (n + 2) + 2 * Nat.count (fun k => f (a k) % 2 = 0) n +
      (if f (a n) % 2 = 0 then 1 else 0) = n := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [show n + 1 + 2 = (n + 2) + 1 by omega, Nat.count_succ (fun k => a k % 2 = 0) (n + 2),
      Nat.count_succ (fun k => f (a k) % 2 = 0) n]
    have h := bit_step n
    change Nat.count (fun k => a k % 2 = 0) (n + 2) +
      (if a (n + 2) % 2 = 0 then 1 else 0) +
      2 * (Nat.count (fun k => f (a k) % 2 = 0) n + (if f (a n) % 2 = 0 then 1 else 0)) +
      (if f (a (n + 1)) % 2 = 0 then 1 else 0) = n + 1
    omega

private theorem count_bounds (n : ℕ) :
    Nat.count (fun k => a k % 2 = 0) n + 2 * Nat.count (fun k => f (a k) % 2 = 0) n ≤ n ∧
      n ≤ Nat.count (fun k => a k % 2 = 0) n + 2 * Nat.count (fun k => f (a k) % 2 = 0) n + 2 := by
  cases n with
  | zero => decide
  | succ n =>
    cases n with
    | zero => decide
    | succ n =>
      change Nat.count (fun k => a k % 2 = 0) (n + 2) + 2 * Nat.count (fun k => f (a k) % 2 = 0) (n + 2) ≤ n + 2 ∧
        n + 2 ≤ Nat.count (fun k => a k % 2 = 0) (n + 2) + 2 * Nat.count (fun k => f (a k) % 2 = 0) (n + 2) + 2
      rw [Nat.count_succ (fun k => f (a k) % 2 = 0) (n + 1), Nat.count_succ (fun k => f (a k) % 2 = 0) n]
      have hi := count_identity n
      have hp := no_two_even n
      split_ifs at * <;> omega

private theorem mean_of_capped_and_excess (gap : ℕ → ℝ)
    (hcapped : ∀ K : ℕ, Tendsto (fun m : ℕ =>
      (∑ j ∈ range m, min (gap j) ((K : ℝ) + 2)) / m) atTop (𝓝 (4 - 2 * (1 / 2 : ℝ)^K)))
    (hexcess : ∀ ε : ℝ, 0 < ε → ∀ᶠ K : ℕ in atTop, ∀ᶠ m : ℕ in atTop,
      (∑ j ∈ range m, max (gap j - ((K : ℝ) + 2)) 0) / m ≤ ε) :
    Tendsto (fun m : ℕ => (∑ j ∈ range m, gap j) / m) atTop (𝓝 (4 : ℝ)) := by
  have hpow : Tendsto (fun K : ℕ => (1 / 2 : ℝ)^K) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hlimit : Tendsto (fun K : ℕ => 4 - 2 * (1 / 2 : ℝ)^K) atTop (𝓝 (4 : ℝ)) := by
    simpa only [mul_zero, sub_zero] using
      (tendsto_const_nhds (x := (4 : ℝ))).sub (hpow.const_mul 2)
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  obtain ⟨K, hK, htail⟩ := ((Metric.tendsto_nhds.1 hlimit (ε / 3) (by positivity)).and
    (hexcess (ε / 3) (by positivity))).exists
  filter_upwards [Metric.tendsto_nhds.1 (hcapped K) (ε / 3) (by positivity), htail] with m hm ht
  let cap := (K : ℝ) + 2
  let capped := (∑ j ∈ range m, min (gap j) cap) / (m : ℝ)
  let tail := (∑ j ∈ range m, max (gap j - cap) 0) / (m : ℝ)
  have hnonneg : 0 ≤ tail := div_nonneg (sum_nonneg fun _ _ => le_max_right _ _) (by positivity)
  have hadd : (∑ j ∈ range m, gap j) / (m : ℝ) = capped + tail := by
    dsimp [capped, tail]
    rw [← add_div, ← sum_add_distrib]
    congr 1
    apply sum_congr rfl
    intro j _
    by_cases hj : gap j ≤ cap
    · simp [min_eq_left hj, max_eq_right (sub_nonpos.mpr hj)]
    · rw [min_eq_right (le_of_not_ge hj), max_eq_left (sub_nonneg.mpr (le_of_not_ge hj))]
      ring
  change dist ((∑ j ∈ range m, gap j) / (m : ℝ)) (4 : ℝ) < ε
  change dist capped (4 - 2 * (1 / 2 : ℝ)^K) < ε / 3 at hm
  change tail ≤ ε / 3 at ht
  rw [Real.dist_eq, abs_lt] at hK hm ⊢
  rw [hadd]
  constructor <;> linarith [hK.1, hK.2, hm.1, hm.2]

private theorem count_density_of_nth (p : ℕ → Prop) [DecidablePred p]
    (hp : (Set.ofPred p).Infinite)
    (hnth : Tendsto (fun m : ℕ => (Nat.nth p m : ℝ) / m) atTop (𝓝 (4 : ℝ))) :
    Tendsto (fun n : ℕ => (Nat.count p n : ℝ) / n) atTop (𝓝 (1 / 4 : ℝ)) := by
  have grow : Tendsto (Nat.count p) atTop atTop := by
    refine tendsto_atTop.2 fun j => eventually_atTop.2 ⟨Nat.nth p j, fun n hn => ?_⟩
    simpa only [Nat.count_nth_of_infinite hp] using Nat.count_monotone p hn
  have growPrev : Tendsto (fun n => Nat.count p n - 1) atTop atTop := by
    refine tendsto_atTop.2 fun j => ((tendsto_atTop.1 grow) (j + 1)).mono fun n hn => ?_
    omega
  have shift : Tendsto (fun m : ℕ => (Nat.nth p m : ℝ) / ((m : ℝ) + 1)) atTop (𝓝 (4 : ℝ)) := by
    have hv : Tendsto (fun m : ℕ => 1 - 1 / ((m : ℝ) + 1)) atTop (𝓝 (1 : ℝ)) := by
      simpa only [sub_zero] using (tendsto_const_nhds (x := (1 : ℝ))).sub
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have hmul := hnth.mul hv
    rw [mul_one] at hmul
    refine hmul.congr' ?_
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
    have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
    have hm'' : (m : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring
  have squeezed : Tendsto (fun n : ℕ => (n : ℝ) / Nat.count p n) atTop (𝓝 (4 : ℝ)) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (shift.comp growPrev) (hnth.comp grow) ?_ ?_
    · filter_upwards [(tendsto_atTop.1 grow) 1] with n hn
      have hpos : (0 : ℝ) < Nat.count p n := by exact_mod_cast hn
      have hcast : ((Nat.count p n - 1 : ℕ) : ℝ) + 1 = Nat.count p n := by
        rw [Nat.cast_sub hn, Nat.cast_one, sub_add_cancel]
      simp only [Function.comp_apply, hcast]
      have hlt : Nat.nth p (Nat.count p n - 1) < n := Nat.nth_lt_of_lt_count (by omega)
      exact div_le_div_of_nonneg_right (by exact_mod_cast hlt.le) hpos.le
    · exact Eventually.of_forall fun n =>
        div_le_div_of_nonneg_right (by exact_mod_cast Nat.le_nth_count hp n) (by positivity)
  simpa only [inv_div, one_div] using squeezed.inv₀ (by norm_num : (4 : ℝ) ≠ 0)

/-- The limiting mean of the gaps between even transformed terms, capped at K + 2.
The cases K = 0 and K = 1 follow from the minimum gap of three. -/
def H1 : Prop :=
  let position := Nat.nth (fun n => f (a n) % 2 = 0)
  ∀ K : ℕ, 2 ≤ K → Tendsto (fun m : ℕ =>
    (∑ j ∈ range m, min ((position (j + 1) : ℝ) - position j) ((K : ℝ) + 2)) / m)
    atTop (𝓝 (4 - 2 * (1 / 2 : ℝ)^K))

/-- The mean contribution from the parts of gaps above K + 2 becomes arbitrarily small. -/
def H2 : Prop :=
  let position := Nat.nth (fun n => f (a n) % 2 = 0)
  ∀ ε : ℝ, 0 < ε → ∀ᶠ K : ℕ in atTop, ∀ᶠ m : ℕ in atTop,
    (∑ j ∈ range m, max ((position (j + 1) : ℝ) - position j - ((K : ℝ) + 2)) 0) / m ≤ ε

theorem main : H1 → H2 → type_of% @OeisA120424.conjecture1 := by
  intro hcapped hexcess
  let position := Nat.nth (fun k => f (a k) % 2 = 0)
  have allCapped (K : ℕ) : Tendsto (fun m : ℕ =>
      (∑ j ∈ range m, min ((position (j + 1) : ℝ) - position j) ((K : ℝ) + 2)) / m)
      atTop (𝓝 (4 - 2 * (1 / 2 : ℝ)^K)) := by
    by_cases hK : 2 ≤ K
    · exact hcapped K hK
    · have hcap : (K : ℝ) + 2 ≤ 3 := by exact_mod_cast (show K + 2 ≤ 3 by omega)
      have hvalue : 4 - 2 * (1 / 2 : ℝ)^K = (K : ℝ) + 2 := by
        have : K = 0 ∨ K = 1 := by omega
        rcases this with rfl | rfl <;> norm_num
      rw [hvalue]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
      have hmin (j : ℕ) : min ((position (j + 1) : ℝ) - position j) ((K : ℝ) + 2) = (K : ℝ) + 2 :=
        min_eq_right (hcap.trans (gap_ge_three j))
      have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
      simp only [hmin, sum_const, card_range, nsmul_eq_mul]
      field_simp
  have hmean := mean_of_capped_and_excess (fun j => (position (j + 1) : ℝ) - position j)
    allCapped hexcess
  have htel (m : ℕ) : (∑ j ∈ range m, ((position (j + 1) : ℝ) - position j)) =
      (position m : ℝ) - position 0 := by
    induction m with
    | zero => simp
    | succ m ih => rw [sum_range_succ, ih]; ring
  simp only [htel] at hmean
  have hnth : Tendsto (fun m : ℕ => (position m : ℝ) / m) atTop (𝓝 (4 : ℝ)) := by
    have hsmall : Tendsto (fun m : ℕ => (position 0 : ℝ) / m) atTop (𝓝 0) :=
      (tendsto_natCast_atTop_atTop (R := ℝ)).const_div_atTop _
    simpa only [sub_div, sub_add_cancel, add_zero] using hmean.add hsmall
  have hb := count_density_of_nth (fun k => f (a k) % 2 = 0) infinitely_many_even hnth
  let p : ℕ → Prop := fun k => a k % 2 = 0
  have hsum : Tendsto (fun n : ℕ => ((Nat.count p n : ℝ) + 2 * (Nat.count (fun k => f (a k) % 2 = 0) n : ℝ)) / n)
      atTop (𝓝 (1 : ℝ)) := by
    have hg : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    have hsmall : Tendsto (fun n : ℕ => (2 : ℝ) / n) atTop (𝓝 0) := hg.const_div_atTop 2
    have hnear : Tendsto (fun n : ℕ => 1 - 2 / (n : ℝ)) atTop (𝓝 (1 : ℝ)) := by
      simpa only [sub_zero] using (tendsto_const_nhds (x := (1 : ℝ))).sub hsmall
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hnear tendsto_const_nhds ?_ ?_
    · filter_upwards [hg.eventually_gt_atTop 0] with n hn
      have h : (n : ℝ) ≤ (Nat.count p n : ℝ) + 2 * (Nat.count (fun k => f (a k) % 2 = 0) n : ℝ) + 2 := by
        exact_mod_cast (count_bounds n).2
      apply (le_div_iff₀ hn).2
      calc
        (1 - 2 / (n : ℝ)) * (n : ℝ) = (n : ℝ) - 2 := by field_simp
        _ ≤ _ := by linarith
    · filter_upwards [hg.eventually_gt_atTop 0] with n hn
      exact (div_le_one hn).2 (by exact_mod_cast (count_bounds n).1)
  have hdouble : Tendsto (fun n : ℕ => 2 * ((Nat.count (fun k => f (a k) % 2 = 0) n : ℝ) / n)) atTop (𝓝 (2 * (1 / 4 : ℝ))) :=
    hb.const_mul 2
  have h := hsum.sub hdouble
  have heq (n : ℕ) :
      ((Nat.count p n : ℝ) + 2 * (Nat.count (fun k => f (a k) % 2 = 0) n : ℝ)) / (n : ℝ) -
        2 * ((Nat.count (fun k => f (a k) % 2 = 0) n : ℝ) / (n : ℝ)) = (Nat.count p n : ℝ) / (n : ℝ) := by ring
  have hfinal : Tendsto (fun n : ℕ => (Nat.count p n : ℝ) / n) atTop (𝓝 (1 / 2 : ℝ)) := by
    simpa only [heq, show 1 - 2 * (1 / 4) = (1 / 2 : ℝ) by norm_num] using h
  simpa only [Nat.count_eq_card_filter_range, p] using hfinal

end OMA.R_OeisA120424_conjecture1_R1
