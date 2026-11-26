import FormalConjectures.ErdosProblems.«882»

-- Problem: Erdős Problem 882
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/882.lean:64 (declaration Erdos882.erdos_882)
-- Credit: @Genbox (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA882

/-- popcount -/
def pc (n : ℕ) : ℕ := n.bitIndices.length

lemma pc_two_mul (n : ℕ) : pc (2 * n) = pc n := by simp [pc]

lemma pc_two_mul_add_one (n : ℕ) : pc (2 * n + 1) = pc n + 1 := by simp [pc]

lemma pc_succ_le : ∀ x : ℕ, pc (x + 1) ≤ pc x + 1 := by
  intro x
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    obtain ⟨y, rfl | rfl⟩ := Nat.even_or_odd' x
    · rw [pc_two_mul_add_one, pc_two_mul]
    · have h : 2 * y + 1 + 1 = 2 * (y + 1) := by ring
      rw [h, pc_two_mul, pc_two_mul_add_one]
      rcases Nat.eq_zero_or_pos y with rfl | hy
      · simp [pc]
      · have := ih y (by omega)
        omega

lemma pc_add_two_pow (t : ℕ) : ∀ x : ℕ, pc (x + 2 ^ t) ≤ pc x + 1 := by
  induction t with
  | zero => intro x; simpa using pc_succ_le x
  | succ s ih =>
    intro x
    obtain ⟨y, rfl | rfl⟩ := Nat.even_or_odd' x
    · have h : 2 * y + 2 ^ (s + 1) = 2 * (y + 2 ^ s) := by ring
      rw [h, pc_two_mul, pc_two_mul]; exact ih y
    · have h : 2 * y + 1 + 2 ^ (s + 1) = 2 * (y + 2 ^ s) + 1 := by ring
      rw [h, pc_two_mul_add_one, pc_two_mul_add_one]; have := ih y; omega

lemma pc_add_list (x : ℕ) (L : List ℕ) : pc (x + (L.map (fun t => 2 ^ t)).sum) ≤ pc x + L.length := by
  induction L generalizing x with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have h1 := ih (x + 2 ^ a)
    have h2 := pc_add_two_pow a x
    rw [← add_assoc]; omega

lemma pc_add (x y : ℕ) : pc (x + y) ≤ pc x + pc y := by
  have h := pc_add_list x y.bitIndices
  rwa [Nat.sum_map_two_pow_bitIndices] at h

lemma pc_sum_finset (s : Finset ℕ) : pc (∑ i ∈ s, 2 ^ i) = s.card := by
  have h := Finset.toFinset_bitIndices_sum_two_pow s
  unfold pc
  conv_rhs => rw [← h]
  rw [List.toFinset_card_of_nodup Nat.bitIndices_nodup]

lemma pc_lt (q : ℕ) (hq : 2 ≤ q) : pc q < q := by
  have hs := Finset.sum_toFinset_bitIndices_two_pow q
  set s := q.bitIndices.toFinset
  have hc : pc q = s.card := by
    unfold pc; rw [List.toFinset_card_of_nodup Nat.bitIndices_nodup]
  rw [hc]
  by_cases h1 : s.card ≤ 1
  · omega
  · have : ∃ i ∈ s, i ≠ 0 := by
      by_contra hne
      simp only [not_exists, not_and, not_not] at hne
      have : s ⊆ {0} := fun i hi => by simp [hne i hi]
      have := Finset.card_le_card this
      simp at this; omega
    obtain ⟨i, hi, hi0⟩ := this
    have hle : ∀ j ∈ s, 1 ≤ 2 ^ j := fun j _ => Nat.one_le_two_pow
    have hsum : ∑ j ∈ s, 1 < ∑ j ∈ s, 2 ^ j := by
      apply Finset.sum_lt_sum hle ⟨i, hi, ?_⟩
      exact Nat.one_lt_two_pow hi0
    simp at hsum; omega

lemma pc_mul_two_pow (q i : ℕ) : pc (q * 2 ^ i) = pc q := by
  unfold pc; rw [mul_comm, Nat.bitIndices_two_pow_mul, List.length_map]

lemma pc_mul_sum (q : ℕ) (s : Finset ℕ) : pc (q * ∑ i ∈ s, 2 ^ i) ≤ pc q * s.card := by
  induction s using Finset.induction_on with
  | empty => simp [pc]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, mul_add, Finset.card_insert_of_notMem ha]
    have := pc_add (q * 2 ^ a) (q * ∑ i ∈ s, 2 ^ i)
    rw [pc_mul_two_pow] at this
    nlinarith

lemma geom_lt (k : ℕ) (I : Finset ℕ) (hI : I ⊆ Finset.range k) : ∑ i ∈ I, 2 ^ i < 2 ^ k := by
  calc ∑ i ∈ I, 2 ^ i ≤ ∑ i ∈ Finset.range k, 2 ^ i := Finset.sum_le_sum_of_subset hI
    _ < 2 ^ k := by
      have := Nat.geomSum_eq (le_refl 2) k
      rw [this]; have : 1 ≤ 2 ^ k := Nat.one_le_two_pow; omega

lemma core (k : ℕ) (I1 I2 : Finset ℕ) (h1 : I1 ⊆ Finset.range k) (h2 : I2 ⊆ Finset.range k)
    (hn1 : I1.Nonempty) (hn2 : I2.Nonempty) (hne : I1 ≠ I2) :
    ¬ (∑ i ∈ I1, 2 ^ i + I1.card * (k * 2 ^ k)) ∣ (∑ i ∈ I2, 2 ^ i + I2.card * (k * 2 ^ k)) := by
  rintro ⟨q, hq⟩
  set E1 := ∑ i ∈ I1, 2 ^ i with hE1
  set E2 := ∑ i ∈ I2, 2 ^ i with hE2
  set j1 := I1.card with hj1
  set j2 := I2.card with hj2
  set T := k * 2 ^ k with hT
  have hE1lt : E1 < 2 ^ k := geom_lt k I1 h1
  have hE2lt : E2 < 2 ^ k := geom_lt k I2 h2
  have hj1pos : 1 ≤ j1 := Finset.card_pos.mpr hn1
  have hj2pos : 1 ≤ j2 := Finset.card_pos.mpr hn2
  have hj1k : j1 ≤ k := by simpa using Finset.card_le_card h1
  have hj2k : j2 ≤ k := by simpa using Finset.card_le_card h2
  have hk : 1 ≤ k := le_trans hj1pos hj1k
  have hTge : 2 ^ k ≤ T := by rw [hT]; nlinarith [Nat.one_le_two_pow (n := k)]
  have heq : E2 + j2 * T = q * E1 + q * j1 * T := by rw [hq]; ring
  rcases lt_trichotomy (q * j1) j2 with hlt | hqe | hgt
  · -- q * j1 < j2
    have hqk : q ≤ k := by
      have : q ≤ q * j1 := Nat.le_mul_of_pos_right q hj1pos
      omega
    have h3 : q * E1 ≤ k * E1 := Nat.mul_le_mul_right E1 hqk
    have h4 : k * E1 < T := by rw [hT]; exact Nat.mul_lt_mul_of_pos_left hE1lt (by omega)
    have h5 : (q * j1 + 1) * T ≤ j2 * T := Nat.mul_le_mul_right T hlt
    nlinarith
  · -- q * j1 = j2
    have hE : E2 = q * E1 := by
      have : q * j1 * T = j2 * T := by rw [hqe]
      omega
    rcases Nat.lt_or_ge q 2 with hq2 | hq2
    · interval_cases q
      · simp at hqe; omega
      · apply hne
        have : E1 = E2 := by rw [hE]; ring
        rw [← Finset.toFinset_bitIndices_sum_two_pow I1, ← Finset.toFinset_bitIndices_sum_two_pow I2]
        rw [← hE1, ← hE2, this]
    · have a1 := pc_sum_finset I2
      have a2 := pc_mul_sum q I1
      have a3 := pc_lt q hq2
      rw [← hE2, hE] at a1
      rw [← hE1] at a2
      have b1 : pc (q * E1) = j2 := a1
      have b2 : pc (q * E1) ≤ pc q * j1 := a2
      have : pc q * j1 < q * j1 := Nat.mul_lt_mul_of_pos_right a3 hj1pos
      omega
  · -- q * j1 > j2
    have h5 : (j2 + 1) * T ≤ q * j1 * T := Nat.mul_le_mul_right T hgt
    nlinarith

lemma pow_bound (k : ℕ) (hk : 4 ≤ k) : (k + 1) * 2 ^ k ≤ 3 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    rw [pow_succ, pow_succ]
    nlinarith [Nat.one_le_two_pow (n := k)]

lemma antichain (k : ℕ) :
    Erdos882.IsSubsetSumAntichain
      ((Finset.range k).image (fun i => 2 ^ i + k * 2 ^ k)) := by
  have hinj : Function.Injective (fun i : ℕ => 2 ^ i + k * 2 ^ k) := by
    intro a b h
    simp only [add_left_inj] at h
    exact Nat.pow_right_injective (le_refl 2) h
  have hsum : ∀ I : Finset ℕ, ∑ x ∈ I.image (fun i => 2 ^ i + k * 2 ^ k), x =
      ∑ i ∈ I, 2 ^ i + I.card * (k * 2 ^ k) := by
    intro I
    rw [Finset.sum_image (fun a _ b _ h => hinj h), Finset.sum_add_distrib]
    simp
  intro S1 hS1 S2 hS2 hn1 hn2 hne
  obtain ⟨I1, hI1, rfl⟩ := Finset.subset_image_iff.mp hS1
  obtain ⟨I2, hI2, rfl⟩ := Finset.subset_image_iff.mp hS2
  rw [hsum, hsum]
  refine core k I1 I2 hI1 hI2 (by simpa using hn1) (by simpa using hn2) ?_
  rintro rfl; exact hne rfl

open Erdos882 in
lemma setBdd (n : ℕ) : BddAbove {k | ∃ A ⊆ Finset.Icc 1 n, IsSubsetSumAntichain A ∧ A.card = k} := by
  refine ⟨n, ?_⟩
  rintro m ⟨B, hB, -, rfl⟩
  simpa using Finset.card_le_card hB

open Erdos882 in
lemma K_spec (n : ℕ) : ∃ A ⊆ Finset.Icc 1 n, IsSubsetSumAntichain A ∧ A.card = maxAntichainCard n := by
  have hne : ({k | ∃ A ⊆ Finset.Icc 1 n, IsSubsetSumAntichain A ∧ A.card = k} : Set ℕ).Nonempty :=
    ⟨0, ∅, by simp, by intro S1 h1 S2 h2 hn1; simp_all [Finset.subset_empty], rfl⟩
  exact Nat.sSup_mem hne (setBdd n)

open Erdos882 in
lemma K_le (n : ℕ) : maxAntichainCard n ≤ n := by
  obtain ⟨A, hA, -, hc⟩ := K_spec n
  rw [← hc]; simpa using Finset.card_le_card hA

open Erdos882 in
lemma K_upper (n : ℕ) : 2 ^ maxAntichainCard n ≤ maxAntichainCard n * n + 1 := by
  obtain ⟨A, hA, hanti, hc⟩ := K_spec n
  rw [← hc]
  have hinj : Set.InjOn (fun S : Finset ℕ => ∑ a ∈ S, a)
      ((A.powerset.filter (fun S => S.Nonempty)) : Set (Finset ℕ)) := by
    intro S1 h1 S2 h2 heq
    simp only [Finset.coe_filter, Finset.mem_powerset, Set.mem_ofPred_eq] at h1 h2
    by_contra hne
    exact hanti S1 h1.1 S2 h2.1 h1.2 h2.2 hne (by simp only at heq; rw [heq])
  have hmaps : ∀ S ∈ A.powerset.filter (fun S => S.Nonempty),
      (fun S : Finset ℕ => ∑ a ∈ S, a) S ∈ Finset.Icc 1 (A.card * n) := by
    intro S hS
    simp only [Finset.mem_filter, Finset.mem_powerset] at hS
    obtain ⟨hSA, hSne⟩ := hS
    simp only [Finset.mem_Icc]
    constructor
    · obtain ⟨x, hx⟩ := hSne
      have hx1 : 1 ≤ x := (Finset.mem_Icc.mp (hA (hSA hx))).1
      exact le_trans hx1 (Finset.single_le_sum (f := fun a : ℕ => a) (fun _ _ => Nat.zero_le _) hx)
    · calc ∑ a ∈ S, a ≤ ∑ a ∈ S, n := Finset.sum_le_sum (fun a ha => (Finset.mem_Icc.mp (hA (hSA ha))).2)
        _ = S.card * n := by simp
        _ ≤ A.card * n := Nat.mul_le_mul_right n (Finset.card_le_card hSA)
  have hcard := Finset.card_le_card_of_injOn _ hmaps hinj
  have hpow : (A.powerset.filter (fun S => S.Nonempty)).card = 2 ^ A.card - 1 := by
    have h1 : A.powerset.filter (fun S => S.Nonempty) = A.powerset.erase ∅ := by
      ext S; simp [Finset.nonempty_iff_ne_empty, and_comm]
    rw [h1, Finset.card_erase_of_mem (Finset.empty_mem_powerset A), Finset.card_powerset]
  rw [hpow] at hcard
  simp at hcard
  have : 1 ≤ 2 ^ A.card := Nat.one_le_two_pow
  omega

open Erdos882 in
lemma K_lower (n m : ℕ) (h : (m + 1) * 2 ^ m ≤ n) : m ≤ maxAntichainCard n := by
  set A := (Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m) with hA
  have hcard : A.card = m := by
    rw [hA, Finset.card_image_of_injective]
    · simp
    · intro a b h
      simp only [add_left_inj] at h
      exact Nat.pow_right_injective (le_refl 2) h
  have hsub : A ⊆ Finset.Icc 1 n := by
    intro x hx
    rw [hA, Finset.mem_image] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    rw [Finset.mem_range] at hi
    have h1 : 2 ^ i ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hi.le
    rw [Finset.mem_Icc]
    constructor
    · have := Nat.one_le_two_pow (n := i); omega
    · nlinarith
  apply le_csSup (setBdd n)
  exact ⟨A, hsub, antichain m, hcard⟩

end OMA882

lemma tendsto_aux (a b : ℝ) :
    Filter.Tendsto (fun x : ℝ => 1 + a * x⁻¹ + b * (Real.log x / x)) Filter.atTop (nhds 1) := by
  have h1 : Filter.Tendsto (fun x : ℝ => x⁻¹) Filter.atTop (nhds 0) := tendsto_inv_atTop_zero
  have h2 : Filter.Tendsto (fun x : ℝ => Real.log x / x) Filter.atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have := ((tendsto_const_nhds (x := (1 : ℝ))).add (h1.const_mul a)).add (h2.const_mul b)
  simpa using this

open Erdos882 in
theorem OMA.solution : type_of% @Erdos882.erdos_882 := by
  set L : ℕ → ℝ := fun n => Real.logb 2 n with hLdef
  have hL : Filter.Tendsto L Filter.atTop Filter.atTop :=
    (Real.tendsto_logb_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hup := (tendsto_aux 2 (Real.log 2)⁻¹).comp hL
  have hlo := (tendsto_aux (-3) (-(Real.log 2)⁻¹)).comp hL
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hup ?_ ?_
  · -- lower bound
    filter_upwards [Filter.eventually_ge_atTop 4] with n hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    set ℓ := Real.logb 2 n with hℓ
    have hℓ2 : 2 ≤ ℓ := by
      rw [hℓ, Real.le_logb_iff_rpow_le (by norm_num) (by linarith)]
      norm_num; exact_mod_cast hn
    set a := Nat.log 2 n with ha
    set b := Nat.log 2 (a + 1) with hb
    have hpa : 2 ^ a ≤ n := Nat.pow_log_le_self 2 (by omega)
    have hna : n < 2 ^ (a + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
    have hpb : 2 ^ b ≤ a + 1 := Nat.pow_log_le_self 2 (by omega)
    have hab : a + 1 < 2 ^ (b + 1) := Nat.lt_pow_succ_log_self (by norm_num) (a + 1)
    have hm : ((a - b - 1) + 1) * 2 ^ (a - b - 1) ≤ n := by
      rcases Nat.lt_or_ge a (b + 1) with h | h
      · have : a - b - 1 = 0 := by omega
        rw [this]; omega
      · have e : 2 ^ (b + 1) * 2 ^ (a - b - 1) = 2 ^ a := by
          rw [← pow_add]; congr 1; omega
        have : (a - b - 1) + 1 ≤ 2 ^ (b + 1) := by omega
        calc ((a - b - 1) + 1) * 2 ^ (a - b - 1) ≤ 2 ^ (b + 1) * 2 ^ (a - b - 1) :=
              Nat.mul_le_mul_right _ this
          _ = 2 ^ a := e
          _ ≤ n := hpa
    have hK := OMA882.K_lower n _ hm
    have hKr : ((a : ℝ) - b - 1) ≤ (maxAntichainCard n : ℝ) := by
      have : ((a - b - 1 : ℕ) : ℝ) ≤ maxAntichainCard n := by exact_mod_cast hK
      have h2 : ((a : ℝ) - b - 1) ≤ ((a - b - 1 : ℕ) : ℝ) := by
        rcases Nat.lt_or_ge a (b + 1) with h | h
        · have : (a : ℝ) < b + 1 := by exact_mod_cast h
          have : (0:ℝ) ≤ ((a - b - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
          linarith
        · rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; simp
      linarith
    have hla : ℓ < a + 1 := by
      rw [hℓ, Real.logb_lt_iff_lt_rpow (by norm_num) (by linarith)]
      have : ((2 : ℝ) ^ ((a : ℝ) + 1)) = ((2 ^ (a + 1) : ℕ) : ℝ) := by
        rw [show ((a : ℝ) + 1) = ((a + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
        push_cast; ring
      rw [this]; exact_mod_cast hna
    have hal : (a : ℝ) ≤ ℓ := by
      rw [hℓ, Real.le_logb_iff_rpow_le (by norm_num) (by linarith), Real.rpow_natCast]
      exact_mod_cast hpa
    have hbl : (b : ℝ) ≤ 1 + Real.logb 2 ℓ := by
      have h1 : (b : ℝ) ≤ Real.logb 2 (a + 1) := by
        rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity), Real.rpow_natCast]
        exact_mod_cast hpb
      have h2 : Real.logb 2 ((a : ℝ) + 1) ≤ Real.logb 2 (2 * ℓ) :=
        Real.logb_le_logb_of_le (by norm_num) (by positivity) (by linarith)
      rw [Real.logb_mul (by norm_num) (by linarith), Real.logb_self_eq_one (by norm_num)] at h2
      linarith
    have hK3 : ℓ - 3 - Real.logb 2 ℓ ≤ (maxAntichainCard n : ℝ) := by linarith
    have hℓpos : 0 < ℓ := by linarith
    show 1 + -3 * ℓ⁻¹ + -(Real.log 2)⁻¹ * (Real.log ℓ / ℓ) ≤ (maxAntichainCard n : ℝ) / ℓ
    rw [le_div_iff₀ hℓpos]
    have e : (1 + -3 * ℓ⁻¹ + -(Real.log 2)⁻¹ * (Real.log ℓ / ℓ)) * ℓ = ℓ - 3 - Real.logb 2 ℓ := by
      rw [Real.logb]; field_simp; ring
    rw [e]; exact hK3
  · filter_upwards [Filter.eventually_ge_atTop 4] with n hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    set ℓ := Real.logb 2 n with hℓ
    have hℓ2 : 2 ≤ ℓ := by
      rw [hℓ, Real.le_logb_iff_rpow_le (by norm_num) (by linarith)]
      norm_num; exact_mod_cast hn
    set K := maxAntichainCard n with hKdef
    have hup := OMA882.K_upper n
    have hKn := OMA882.K_le n
    have h1 : 2 ^ K ≤ (K + 1) * n := by nlinarith
    have h1r : (2 : ℝ) ^ K ≤ ((K : ℝ) + 1) * n := by exact_mod_cast h1
    have hK1 : (K : ℝ) ≤ Real.logb 2 ((K : ℝ) + 1) + ℓ := by
      have := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) h1r
      rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), Real.logb_mul (by positivity)
        (by linarith)] at this
      linarith
    have hKnr : (K : ℝ) ≤ n := by exact_mod_cast hKn
    have hK2 : Real.logb 2 ((K : ℝ) + 1) ≤ 1 + ℓ := by
      have := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity)
        (show (K : ℝ) + 1 ≤ 2 * n by linarith)
      rwa [Real.logb_mul (by norm_num) (by linarith), Real.logb_self_eq_one (by norm_num)] at this
    have hK3 : Real.logb 2 ((K : ℝ) + 1) ≤ 2 + Real.logb 2 ℓ := by
      have := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity)
        (show (K : ℝ) + 1 ≤ 4 * ℓ by linarith)
      rw [Real.logb_mul (by norm_num) (by linarith)] at this
      have h4 : Real.logb 2 (4 : ℝ) = 2 := by
        rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
        norm_num
      linarith
    have hℓpos : 0 < ℓ := by linarith
    show (K : ℝ) / ℓ ≤ 1 + 2 * ℓ⁻¹ + (Real.log 2)⁻¹ * (Real.log ℓ / ℓ)
    rw [div_le_iff₀ hℓpos]
    have e : (1 + 2 * ℓ⁻¹ + (Real.log 2)⁻¹ * (Real.log ℓ / ℓ)) * ℓ = ℓ + 2 + Real.logb 2 ℓ := by
      rw [Real.logb]; field_simp
    rw [e]; linarith
