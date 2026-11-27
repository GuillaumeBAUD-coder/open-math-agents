import FormalConjectures.ErdosProblems.«860»

-- Problem: Erdős Problem 860 — erdos pomerance upper
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/860.lean:77 (declaration Erdos860.erdos_860.variants.erdos_pomerance_upper)
-- Credit: @senamakel (the owner of the agent is credited as the solver)
-- Proof: Hall marriage theorem; Hall condition by Cauchy-Schwarz double counting of multiples
-- in the interval, plus the Chebyshev bound pi(n) = O(n / log n).

open Finset

namespace E860

lemma card_Ioc_dvd (a b d : ℕ) (hab : a ≤ b) :
    #{x ∈ Ioc a b | d ∣ x} = b / d - a / d := by
  have h1 := Nat.Ioc_filter_dvd_card_eq_div b d
  have h2 := Nat.Ioc_filter_dvd_card_eq_div a d
  have hu : Ioc 0 a ∪ Ioc a b = Ioc 0 b := Ioc_union_Ioc_eq_Ioc (Nat.zero_le _) hab
  have hdisj : Disjoint ({x ∈ Ioc 0 a | d ∣ x}) ({x ∈ Ioc a b | d ∣ x}) := by
    apply Finset.disjoint_filter_filter
    exact Finset.Ioc_disjoint_Ioc_of_le le_rfl
  have : #{x ∈ Ioc 0 b | d ∣ x} = #{x ∈ Ioc 0 a | d ∣ x} + #{x ∈ Ioc a b | d ∣ x} := by
    rw [← card_union_of_disjoint hdisj, ← filter_union, hu]
  omega

/-- multiples of `d` in the open interval `(m, m+L)`. -/
lemma card_Ioo_dvd_le (m L d : ℕ) (hd : 0 < d) :
    (#{x ∈ Ioo m (m + L) | d ∣ x} : ℝ) ≤ L / d + 1 := by
  have hsub : ({x ∈ Ioo m (m + L) | d ∣ x}) ⊆ {x ∈ Ioc m (m + L) | d ∣ x} :=
    filter_subset_filter _ Ioo_subset_Ioc_self
  have h := card_le_card hsub
  rw [card_Ioc_dvd _ _ _ (by omega)] at h
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have k1 := Nat.div_add_mod (m + L) d
  have k2 := Nat.div_add_mod m d
  have k3 := Nat.mod_lt m hd
  have k4 := Nat.mod_lt (m + L) hd
  have hle : m / d ≤ (m + L) / d := Nat.div_le_div_right (by omega)
  have : ((m + L) / d - m / d) * d ≤ L + d := by
    rw [Nat.sub_mul]
    have := Nat.mul_comm d ((m + L) / d)
    have := Nat.mul_comm d (m / d)
    omega
  have hc : ((#{x ∈ Ioo m (m + L) | d ∣ x} : ℕ) : ℝ) * d ≤ L + d := by
    exact_mod_cast (Nat.mul_le_mul_right d h).trans this
  rw [div_add_one hdR.ne', le_div_iff₀ hdR]
  linarith

lemma card_Ioo_dvd_ge (m L d : ℕ) (hd : 0 < d) :
    (L : ℝ) / d - 2 ≤ (#{x ∈ Ioo m (m + L) | d ∣ x} : ℝ) := by
  rcases Nat.eq_zero_or_pos L with rfl | hL
  · simp only [Nat.cast_zero, zero_div]; linarith [(#{x ∈ Ioo m (m + 0) | d ∣ x}).cast_nonneg (α := ℝ)]
  have hIoo : Ioo m (m + L) = Ioc m (m + L - 1) := by
    ext x; simp only [mem_Ioo, mem_Ioc]; omega
  rw [hIoo, card_Ioc_dvd _ _ _ (by omega)]
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have k1 := Nat.div_add_mod (m + L - 1) d
  have k2 := Nat.div_add_mod m d
  have k3 := Nat.mod_lt m hd
  have k4 := Nat.mod_lt (m + L - 1) hd
  have hle : m / d ≤ (m + L - 1) / d := Nat.div_le_div_right (by omega)
  have : L ≤ ((m + L - 1) / d - m / d) * d + 2 * d := by
    rw [Nat.sub_mul]
    have := Nat.mul_comm d ((m + L - 1) / d)
    have := Nat.mul_comm d (m / d)
    omega
  have hc : (L : ℝ) ≤ (((m + L - 1) / d - m / d : ℕ) : ℝ) * d + 2 * d := by exact_mod_cast this
  rw [sub_le_iff_le_add, div_le_iff₀ hdR]
  linarith


lemma final_ineq (s U A B L σ n : ℝ) (hs : 0 < s) (hn : 0 < n) (hσ : s / n ≤ σ)
    (hL1 : 32 * n ≤ L) (hL2 : 16 * n ^ 2 * s ≤ L ^ 2) (hsn : s ≤ 2 * n)
    (hA : L * σ - 2 * s ≤ A) (hB : B ≤ L * σ ^ 2 + s ^ 2 + L * σ)
    (hCS : A ^ 2 ≤ U * B) (hU : 0 ≤ U) : s ≤ U := by
  set X := L * σ with hX
  have hLpos : 0 < L := by linarith
  have hσ0 : 0 < σ := lt_of_lt_of_le (div_pos hs hn) hσ
  have hXs : L * s / n ≤ X := by
    rw [hX, mul_div_assoc]; exact mul_le_mul_of_nonneg_left hσ hLpos.le
  have hX16 : 16 * s ≤ X := by
    refine le_trans ?_ hXs
    rw [le_div_iff₀ hn]; nlinarith
  have hX3 : 16 * s ^ 3 ≤ X ^ 2 := by
    have h1 : (L * s / n) ^ 2 ≤ X ^ 2 := by
      have : 0 ≤ L * s / n := by positivity
      nlinarith
    have h2 : 16 * s ^ 3 ≤ (L * s / n) ^ 2 := by
      rw [div_pow, le_div_iff₀ (by positivity)]; nlinarith
    linarith
  have hsXσ : s * (L * σ ^ 2) ≤ X ^ 2 / 16 := by
    rw [hX]; have : 16 * s ≤ L := by linarith
    have : 0 ≤ σ ^ 2 := sq_nonneg _
    nlinarith
  have hsB : s * B ≤ 3 * X ^ 2 / 16 := by
    have : s * B ≤ s * (L * σ ^ 2 + s ^ 2 + L * σ) := mul_le_mul_of_nonneg_left hB hs.le
    nlinarith
  have hA' : 7 * X / 8 ≤ A := by linarith
  have hXpos : 0 < X := by linarith
  have hA2 : 49 * X ^ 2 / 64 ≤ A ^ 2 := by nlinarith
  have hBpos : 0 < B := by
    by_contra hb; push Not at hb
    nlinarith
  have : s * B ≤ U * B := by nlinarith [sq_nonneg X]
  exact le_of_mul_le_mul_right this hBpos


lemma key {ι : Type*} [DecidableEq ι] (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (n m L : ℕ) (hpn : ∀ i, p i ≤ n) (S : Finset ι)
    (hL1 : 32 * n ≤ L) (hL2 : 16 * n ^ 2 * #S ≤ L ^ 2) :
    #S ≤ #(S.biUnion fun i => {x ∈ Ioo m (m + L) | p i ∣ x}) := by
  set T : ι → Finset ℕ := fun i => {x ∈ Ioo m (m + L) | p i ∣ x} with hT
  set U := S.biUnion T with hU
  rcases S.eq_empty_or_nonempty with hS | hS
  · simp [hS]
  obtain ⟨i0, hi0⟩ := hS
  have hn : 0 < n := lt_of_lt_of_le (hp i0).pos (hpn i0)
  have hpos : ∀ i, (0 : ℝ) < p i := fun i => by exact_mod_cast (hp i).pos
  -- s ≤ n + 1
  have hsn : #S ≤ n + 1 := by
    have : #(S.image p) ≤ #(range (n + 1)) := by
      apply card_le_card
      intro x hx
      obtain ⟨i, -, rfl⟩ := mem_image.1 hx
      exact mem_range.2 (Nat.lt_succ_of_le (hpn i))
    rwa [card_image_of_injective _ hinj, card_range] at this
  set r : ℕ → ℕ := fun a => #{i ∈ S | a ∈ T i} with hr
  have hTU : ∀ i ∈ S, T i ⊆ U := fun i hi => subset_biUnion_of_mem T hi
  -- double counting
  have hA : ∑ i ∈ S, #(T i) = ∑ a ∈ U, r a := by
    have : ∀ i ∈ S, #(T i) = ∑ a ∈ U, if a ∈ T i then 1 else 0 := by
      intro i hi
      rw [← card_filter, filter_mem_eq_inter, inter_eq_right.2 (hTU i hi)]
    rw [sum_congr rfl this, sum_comm]
    refine sum_congr rfl fun a _ => ?_
    simp only [hr, card_filter]
  have hB : ∑ a ∈ U, r a ^ 2 = ∑ i ∈ S, ∑ j ∈ S, #(T i ∩ T j) := by
    have : ∀ i ∈ S, ∀ j ∈ S, #(T i ∩ T j) = ∑ a ∈ U, if a ∈ T i ∩ T j then 1 else 0 := by
      intro i hi j _
      rw [← card_filter, filter_mem_eq_inter, inter_eq_right.2
        (inter_subset_left.trans (hTU i hi))]
    rw [sum_congr rfl fun i hi => sum_congr rfl fun j hj => this i hi j hj]
    conv_rhs => arg 2; ext i; rw [sum_comm]
    rw [sum_comm]
    refine sum_congr rfl fun a _ => ?_
    simp only [hr, card_filter, sq, sum_mul_sum]
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    by_cases h1 : a ∈ T i <;> by_cases h2 : a ∈ T j <;> simp [h1, h2, mem_inter]
  -- real bounds
  set σ : ℝ := ∑ i ∈ S, (1 : ℝ) / p i with hσ
  have hAge : (L : ℝ) * σ - 2 * #S ≤ ∑ i ∈ S, (#(T i) : ℝ) := by
    have : ∀ i ∈ S, (L : ℝ) / p i - 2 ≤ (#(T i) : ℝ) := fun i _ =>
      card_Ioo_dvd_ge m L (p i) (hp i).pos
    calc (L : ℝ) * σ - 2 * #S = ∑ i ∈ S, ((L : ℝ) / p i - 2) := by
          simp only [sum_sub_distrib, hσ, mul_sum, mul_one_div, sum_const, nsmul_eq_mul]; ring
      _ ≤ _ := sum_le_sum this
  have hBle : ∑ i ∈ S, ∑ j ∈ S, (#(T i ∩ T j) : ℝ) ≤
      (L : ℝ) * σ ^ 2 + (#S : ℝ) ^ 2 + L * σ := by
    have hpt : ∀ i ∈ S, ∀ j ∈ S, (#(T i ∩ T j) : ℝ) ≤
        (L : ℝ) * ((1 / p i) * (1 / p j)) + 1 + (if i = j then (L : ℝ) * (1 / p i) else 0) := by
      intro i _ j _
      by_cases hij : i = j
      · subst hij
        simp only [inter_self, if_true]
        have := card_Ioo_dvd_le m L (p i) (hp i).pos
        have : 0 ≤ (L : ℝ) * ((1 / p i) * (1 / p i)) := by
          have := hpos i; positivity
        rw [div_eq_mul_one_div] at *
        linarith
      · simp only [hij, if_false, add_zero]
        have hsub : T i ∩ T j ⊆ {x ∈ Ioo m (m + L) | p i * p j ∣ x} := by
          intro x hx
          rw [mem_inter] at hx
          simp only [hT, mem_filter] at hx ⊢
          refine ⟨hx.1.1, Nat.Coprime.mul_dvd_of_dvd_of_dvd ?_ hx.1.2 hx.2.2⟩
          exact (Nat.coprime_primes (hp i) (hp j)).2 (fun h => hij (hinj h))
        have h1 := card_le_card hsub
        have h2 := card_Ioo_dvd_le m L (p i * p j) (Nat.mul_pos (hp i).pos (hp j).pos)
        have : ((#(T i ∩ T j) : ℕ) : ℝ) ≤ #{x ∈ Ioo m (m + L) | p i * p j ∣ x} := by
          exact_mod_cast h1
        push_cast at h2
        have e : (L : ℝ) / (p i * p j) = L * ((1 / p i) * (1 / p j)) := by
          field_simp
        linarith
    refine le_trans (sum_le_sum fun i hi => sum_le_sum fun j hj => hpt i hi j hj) ?_
    have e1 : ∑ i ∈ S, ∑ j ∈ S, (L : ℝ) * ((1 / p i) * (1 / p j)) = L * σ ^ 2 := by
      rw [hσ, sq, sum_mul_sum, mul_sum]; simp_rw [mul_sum]
    have e2 : ∑ i ∈ S, ∑ j ∈ S, (1 : ℝ) = (#S : ℝ) ^ 2 := by
      simp [sq]
    have e3 : ∑ i ∈ S, ∑ j ∈ S, (if i = j then (L : ℝ) * (1 / p i) else 0) = L * σ := by
      rw [hσ, mul_sum]
      refine sum_congr rfl fun i hi => ?_
      rw [sum_ite_eq, if_pos hi]
    apply le_of_eq
    simp only [sum_add_distrib]
    rw [e1, e2, e3]
  have hAR : (∑ i ∈ S, (#(T i) : ℝ)) = ∑ a ∈ U, (r a : ℝ) := by exact_mod_cast hA
  have hBR : (∑ a ∈ U, (r a : ℝ) ^ 2) = ∑ i ∈ S, ∑ j ∈ S, (#(T i ∩ T j) : ℝ) := by
    exact_mod_cast hB
  have hCS : (∑ a ∈ U, (r a : ℝ)) ^ 2 ≤ #U * ∑ a ∈ U, (r a : ℝ) ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have hσge : (#S : ℝ) / n ≤ σ := by
    have : (#S : ℝ) / n = ∑ i ∈ S, (1 : ℝ) / n := by
      rw [sum_const, nsmul_eq_mul, mul_one_div]
    rw [hσ, this]
    refine sum_le_sum fun i _ => ?_
    exact one_div_le_one_div_of_le (hpos i) (by exact_mod_cast hpn i)
  have hfin := final_ineq (#S : ℝ) (#U : ℝ) (∑ i ∈ S, (#(T i) : ℝ))
    (∑ a ∈ U, (r a : ℝ) ^ 2) L σ n (by exact_mod_cast card_pos.2 ⟨i0, hi0⟩)
    (by exact_mod_cast hn) hσge (by exact_mod_cast hL1) (by exact_mod_cast hL2)
    (by have : (#S : ℝ) ≤ n + 1 := by exact_mod_cast hsn
        have : (1 : ℝ) ≤ n := by exact_mod_cast hn
        linarith)
    hAge (by rw [hBR]; exact hBle) (by rw [hAR]; exact hCS) (Nat.cast_nonneg _)
  exact_mod_cast hfin


lemma h_le_bound (n : ℕ) : Erdos860.h n ≤ 32 * n * (Nat.sqrt (Nat.primeCounting n) + 1) := by
  set L := 32 * n * (Nat.sqrt (Nat.primeCounting n) + 1) with hLdef
  apply Nat.sInf_le
  intro m _
  set p : Fin (Nat.primeCounting n) → ℕ := fun i => Nat.nth Nat.Prime i.val with hpdef
  have hp : ∀ i, (p i).Prime := fun i => Nat.prime_nth_prime _
  have hinj : Function.Injective p :=
    (Nat.nth_injective Nat.infinite_setOfPred_prime).comp Fin.val_injective
  have hpn : ∀ i, p i ≤ n := fun i =>
    Nat.lt_succ_iff.1 (Nat.nth_lt_of_lt_count (n := n + 1) i.isLt)
  have hall : ∀ S : Finset (Fin (Nat.primeCounting n)),
      #S ≤ #(S.biUnion fun i => {x ∈ Ioo m (m + L) | p i ∣ x}) := by
    intro S
    apply key p hp hinj n m L hpn S
    · rw [hLdef]; nlinarith
    · have h1 : #S ≤ Nat.primeCounting n := by
        simpa using card_le_univ S
      have h2 := Nat.lt_succ_sqrt (Nat.primeCounting n)
      have h3 : #S ≤ (Nat.sqrt (Nat.primeCounting n) + 1) ^ 2 := by nlinarith
      rw [hLdef]
      have : 16 * n ^ 2 * #S ≤ 16 * n ^ 2 * (Nat.sqrt (Nat.primeCounting n) + 1) ^ 2 :=
        Nat.mul_le_mul_left _ h3
      nlinarith
  obtain ⟨f, hf, hft⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective _).1 hall
  refine ⟨f, hf, fun i => ?_⟩
  have := hft i
  simp only [mem_filter, mem_Ioo] at this
  exact ⟨this.1.1, this.1.2, this.2⟩


open Filter Asymptotics in
theorem main : (fun n : ℕ ↦ (Erdos860.h n : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 : ℝ) / Real.sqrt (Real.log n) := by
  have hl4 : Real.log 4 + 0.6 ≤ 2 := by
    have : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    have := Real.log_two_lt_d9
    linarith
  have hpi : ∀ᶠ n : ℕ in atTop,
      (Nat.primeCounting n : ℝ) ≤ (Real.log 4 + 0.6) * n / Real.log n := by
    have := tendsto_natCast_atTop_atTop.eventually
      (Chebyshev.eventually_primeCounting_le (ε := 0.6) (by norm_num))
    filter_upwards [this] with n hn
    simpa using hn
  refine IsBigO.of_bound 100 ?_
  filter_upwards [hpi, eventually_ge_atTop 3] with n hn hn3
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn3
  have hlog : 0 < Real.log n := Real.log_pos (by linarith)
  have hlogle : Real.log n ≤ n := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have hπ : (Nat.primeCounting n : ℝ) ≤ 2 * n / Real.log n := by
    refine hn.trans ?_
    gcongr
  have hsq : √(Nat.primeCounting n : ℝ) ≤ √2 * √n / √(Real.log n) := by
    rw [← Real.sqrt_mul (by norm_num), ← Real.sqrt_div (by positivity)]
    exact Real.sqrt_le_sqrt hπ
  have hh : (Erdos860.h n : ℝ) ≤ 32 * n * (√(Nat.primeCounting n : ℝ) + 1) := by
    have := h_le_bound n
    have h2 : ((32 * n * (Nat.sqrt (Nat.primeCounting n) + 1) : ℕ) : ℝ) ≤
        32 * n * (√(Nat.primeCounting n : ℝ) + 1) := by
      push_cast
      have := Real.nat_sqrt_le_real_sqrt (a := Nat.primeCounting n)
      gcongr
    exact (Nat.cast_le.2 this).trans h2
  have hg : (n : ℝ) ^ (3 / 2 : ℝ) = n * √n := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' (by positivity) (by norm_num)]
    norm_num
  have hsl : 0 < √(Real.log n) := Real.sqrt_pos.2 hlog
  have hone : (1 : ℝ) ≤ √n / √(Real.log n) := by
    rw [le_div_iff₀ hsl, one_mul]; exact Real.sqrt_le_sqrt hlogle
  have h2 : √2 ≤ 2 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity), hg]
  have hn0 : (0 : ℝ) ≤ n := by linarith
  calc (Erdos860.h n : ℝ) ≤ 32 * n * (√(Nat.primeCounting n : ℝ) + 1) := hh
    _ ≤ 32 * n * (√2 * √n / √(Real.log n) + √n / √(Real.log n)) := by gcongr
    _ = 32 * (√2 + 1) * (n * √n / √(Real.log n)) := by ring
    _ ≤ 100 * (n * √n / √(Real.log n)) := by
        have : 0 ≤ n * √n / √(Real.log n) := by positivity
        nlinarith

end E860

theorem OMA.solution : type_of% @Erdos860.erdos_860.variants.erdos_pomerance_upper :=
  E860.main
