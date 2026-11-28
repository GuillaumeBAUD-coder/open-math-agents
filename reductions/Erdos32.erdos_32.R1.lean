import FormalConjectures.ErdosProblems.«32»

/-!
Reduction `Erdos32.erdos_32.R1` of Erdős Problem 32 (`o((log N)^2)` additive complement to primes).
Splits the global infinite `o((log N)^2)` complement problem into two symmetric finite-scale
almost-covering problems on doubly-exponential blocks `[2^(2^(j+1)), 2^(2^(j+2)))`:
- `H1`: finite-scale `o(4^j)` almost-covering of EVEN integers in block `j` using shifts `≥ 2^(2^j)`.
- `H2`: finite-scale `o(4^j)` almost-covering of ODD integers in block `j` using shifts `≥ 2^(2^j)`.
- `main`: extracts decaying block witnesses, repairs uncovered elements via `n = 2 + (n - 2)`,
  glues all blocks into a single additive complement `A`, and proves `|A ∩ [1, N]| = o((log N)^2)`
  by doubly-exponential windowing and geometric tail summation.
-/

open Filter Finset Asymptotics

namespace OMA.R_Erdos32_erdos_32_R1

open scoped Classical in
def H1 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop,
    ∃ B : Finset ℕ,
      (∀ a ∈ B, 2 ^ (2 ^ j) ≤ a) ∧
      (B.card : ℝ) ≤ ε * ((2 ^ j : ℕ) : ℝ) ^ 2 ∧
      (((Finset.Ico (2 ^ (2 ^ (j + 1))) (2 ^ (2 ^ (j + 2)))).filter
        (fun n => Even n ∧ ¬ ∃ p, p.Prime ∧ ∃ a ∈ B, n = p + a)).card : ℝ) ≤
        ε * ((2 ^ j : ℕ) : ℝ) ^ 2

open scoped Classical in
def H2 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop,
    ∃ B : Finset ℕ,
      (∀ a ∈ B, 2 ^ (2 ^ j) ≤ a) ∧
      (B.card : ℝ) ≤ ε * ((2 ^ j : ℕ) : ℝ) ^ 2 ∧
      (((Finset.Ico (2 ^ (2 ^ (j + 1))) (2 ^ (2 ^ (j + 2)))).filter
        (fun n => Odd n ∧ ¬ ∃ p, p.Prime ∧ ∃ a ∈ B, n = p + a)).card : ℝ) ≤
        ε * ((2 ^ j : ℕ) : ℝ) ^ 2

lemma strictMono_two_pow_two_pow : StrictMono (fun j : ℕ => 2 ^ (2 ^ j)) := by
  intro i j hij
  exact Nat.pow_lt_pow_right (by decide) (Nat.pow_lt_pow_right (by decide) hij)

lemma window_exists (u : ℕ → ℕ) (hu : StrictMono u) (n : ℕ) (h0 : u 0 ≤ n) :
    ∃ j, u j ≤ n ∧ n < u (j + 1) := by
  classical
  have hex : ∃ k, n < u k := ⟨n + 1, lt_of_lt_of_le (Nat.lt_succ_self n) (hu.id_le (n + 1))⟩
  have hspec := Nat.find_spec hex
  cases he : Nat.find hex with
  | zero =>
    rw [he] at hspec
    omega
  | succ j =>
    refine ⟨j, le_of_not_gt (Nat.find_min hex (by omega)), ?_⟩
    simpa [he] using hspec

lemma geom_sum_four_pow (k : ℕ) :
    ∑ j ∈ Finset.range (k + 1), (((2 ^ j : ℕ) : ℝ) ^ 2) ≤ 2 * (((2 ^ k : ℕ) : ℝ) ^ 2) := by
  induction k with
  | zero =>
    norm_num
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have hpow : (((2 ^ (k + 1) : ℕ) : ℝ) ^ 2) = 4 * (((2 ^ k : ℕ) : ℝ) ^ 2) := by
      push_cast
      ring
    rw [hpow]
    have hnn : (0 : ℝ) ≤ (((2 ^ k : ℕ) : ℝ) ^ 2) := by positivity
    linarith

lemma two_pow_two_pow_succ_ge_add_two (j : ℕ) (hj : 1 ≤ j) :
    2 ^ (2 ^ j) + 2 ≤ 2 ^ (2 ^ (j + 1)) := by
  have h1 : 2 ^ j ≥ 2 := by
    calc 2 ^ j ≥ 2 ^ 1 := Nat.pow_le_pow_right (by decide) hj
      _ = 2 := by norm_num
  have h2 : 2 ^ (2 ^ (j + 1)) = 2 ^ (2 ^ j) * 2 ^ (2 ^ j) := by
    rw [pow_succ, mul_two, pow_add]
  have h3 : 2 ^ (2 ^ j) ≥ 4 := by
    calc 2 ^ (2 ^ j) ≥ 2 ^ 2 := Nat.pow_le_pow_right (by decide) h1
      _ = 4 := by norm_num
  nlinarith

lemma extract_block_seq (P : ℕ → Prop)
    [∀ B : Finset ℕ, DecidablePred (fun n => P n ∧ ¬ ∃ p : ℕ, p.Prime ∧ ∃ a ∈ B, n = p + a)]
    (hP : ∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop,
      ∃ B : Finset ℕ,
        (∀ a ∈ B, 2 ^ (2 ^ j) ≤ a) ∧
        (B.card : ℝ) ≤ ε * ((2 ^ j : ℕ) : ℝ) ^ 2 ∧
        (((Finset.Ico (2 ^ (2 ^ (j + 1))) (2 ^ (2 ^ (j + 2)))).filter
          (fun n => P n ∧ ¬ ∃ p : ℕ, p.Prime ∧ ∃ a ∈ B, n = p + a)).card : ℝ) ≤
          ε * ((2 ^ j : ℕ) : ℝ) ^ 2) :
    ∃ B : ℕ → Finset ℕ,
      (∀ j, ∀ a ∈ B j, 2 ^ (2 ^ j) ≤ a) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop,
        ((B j).card : ℝ) ≤ ε * ((2 ^ j : ℕ) : ℝ) ^ 2 ∧
        (((Finset.Ico (2 ^ (2 ^ (j + 1))) (2 ^ (2 ^ (j + 2)))).filter
          (fun n => P n ∧ ¬ ∃ p : ℕ, p.Prime ∧ ∃ a ∈ B j, n = p + a)).card : ℝ) ≤
          ε * ((2 ^ j : ℕ) : ℝ) ^ 2) := by
  classical
  have hstep : ∀ m : ℕ, ∃ J : ℕ, ∀ j ≥ J,
      ∃ B : Finset ℕ,
        (∀ a ∈ B, 2 ^ (2 ^ j) ≤ a) ∧
        (B.card : ℝ) ≤ (1 / ((m : ℝ) + 1)) * ((2 ^ j : ℕ) : ℝ) ^ 2 ∧
        (((Finset.Ico (2 ^ (2 ^ (j + 1))) (2 ^ (2 ^ (j + 2)))).filter
          (fun n => P n ∧ ¬ ∃ p : ℕ, p.Prime ∧ ∃ a ∈ B, n = p + a)).card : ℝ) ≤
          (1 / ((m : ℝ) + 1)) * ((2 ^ j : ℕ) : ℝ) ^ 2 := by
    intro m
    exact eventually_atTop.mp (hP (1 / ((m : ℝ) + 1)) (by positivity))
  choose J hJ using hstep
  -- Build a strictly increasing threshold sequence t : ℕ → ℕ with J m ≤ t m
  let t : ℕ → ℕ := Nat.rec (J 0) (fun m prev => max (prev + 1) (J (m + 1)))
  have ht_mono : StrictMono t := by
    refine strictMono_nat_of_lt_succ fun m => ?_
    change t m < max (t m + 1) (J (m + 1))
    exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _)
  have hJt : ∀ m, J m ≤ t m := by
    intro m
    cases m with
    | zero => exact le_rfl
    | succ m => exact le_max_right _ _
  -- For each j, pick the largest m with t m ≤ j (if t 0 ≤ j)
  have hchoice : ∀ j : ℕ, ∃ B : Finset ℕ,
      (∀ a ∈ B, 2 ^ (2 ^ j) ≤ a) ∧
      (∀ m : ℕ, t m ≤ j →
        (B.card : ℝ) ≤ (1 / ((m : ℝ) + 1)) * ((2 ^ j : ℕ) : ℝ) ^ 2 ∧
        (((Finset.Ico (2 ^ (2 ^ (j + 1))) (2 ^ (2 ^ (j + 2)))).filter
          (fun n => P n ∧ ¬ ∃ p : ℕ, p.Prime ∧ ∃ a ∈ B, n = p + a)).card : ℝ) ≤
          (1 / ((m : ℝ) + 1)) * ((2 ^ j : ℕ) : ℝ) ^ 2) := by
    intro j
    rcases le_or_gt (t 0) j with hj0 | hj0
    · obtain ⟨m₀, hm₀, hm₀'⟩ := window_exists t ht_mono j hj0
      obtain ⟨B, hlow, hcard, hexc⟩ := hJ m₀ j (le_trans (hJt m₀) hm₀)
      refine ⟨B, hlow, fun m hm => ?_⟩
      have hmm₀ : m ≤ m₀ := by
        by_contra hlt
        push Not at hlt
        have h1 : t (m₀ + 1) ≤ t m := ht_mono.monotone (Nat.succ_le_of_lt hlt)
        omega
      have hinv : (1 : ℝ) / ((m₀ : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) := by
        apply one_div_le_one_div_of_le (by positivity)
        have : (m : ℝ) ≤ (m₀ : ℝ) := by exact_mod_cast hmm₀
        linarith
      have hsq : (0 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) ^ 2 := by positivity
      exact ⟨hcard.trans (mul_le_mul_of_nonneg_right hinv hsq),
        hexc.trans (mul_le_mul_of_nonneg_right hinv hsq)⟩
    · refine ⟨∅, by simp, fun m hm => ?_⟩
      have h0m : t 0 ≤ t m := ht_mono.monotone (Nat.zero_le m)
      omega
  choose B hBlow hBbd using hchoice
  refine ⟨B, hBlow, fun ε hε => ?_⟩
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
  refine eventually_atTop.mpr ⟨t m, fun j hj => ?_⟩
  obtain ⟨h1, h2⟩ := hBbd j m hj
  have hsq : (0 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) ^ 2 := by positivity
  exact ⟨h1.trans (mul_le_mul_of_nonneg_right hm.le hsq),
    h2.trans (mul_le_mul_of_nonneg_right hm.le hsq)⟩

open scoped Classical in
theorem main : H1 → H2 → type_of% @Erdos32.erdos_32 := by
  intro h1 h2
  obtain ⟨B1, hB1low, hB1dec⟩ := extract_block_seq Even h1
  obtain ⟨B2, hB2low, hB2dec⟩ := extract_block_seq Odd h2
  -- Define repair set R j for each block j >= 1
  let E1 (j : ℕ) : Finset ℕ :=
    (Finset.Ico (2 ^ (2 ^ (j + 1))) (2 ^ (2 ^ (j + 2)))).filter
      (fun n => Even n ∧ ¬ ∃ p, p.Prime ∧ ∃ a ∈ B1 j, n = p + a)
  let E2 (j : ℕ) : Finset ℕ :=
    (Finset.Ico (2 ^ (2 ^ (j + 1))) (2 ^ (2 ^ (j + 2)))).filter
      (fun n => Odd n ∧ ¬ ∃ p, p.Prime ∧ ∃ a ∈ B2 j, n = p + a)
  let R (j : ℕ) : Finset ℕ := (E1 j ∪ E2 j).image (fun n => n - 2)
  let C (j : ℕ) : Finset ℕ := if 1 ≤ j then B1 j ∪ B2 j ∪ R j else ∅
  let A : Set ℕ := {a | ∃ j, a ∈ C j}
  have hClow : ∀ j, ∀ a ∈ C j, 2 ^ (2 ^ j) ≤ a := by
    intro j a ha
    by_cases hj : 1 ≤ j
    · simp only [C, hj, if_true, Finset.mem_union] at ha
      rcases ha with (ha1 | ha2) | haR
      · exact hB1low j a ha1
      · exact hB2low j a ha2
      · simp only [R, Finset.mem_image, Finset.mem_union] at haR
        obtain ⟨n, hn, rfl⟩ := haR
        have hnlo : 2 ^ (2 ^ (j + 1)) ≤ n := by
          rcases hn with h | h
          · exact (Finset.mem_Ico.mp (Finset.mem_filter.mp h).1).1
          · exact (Finset.mem_Ico.mp (Finset.mem_filter.mp h).1).1
        have hgap := two_pow_two_pow_succ_ge_add_two j hj
        omega
    · simp [C, hj] at ha
  have hCcard : ∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop,
      ((C j).card : ℝ) ≤ ε * ((2 ^ j : ℕ) : ℝ) ^ 2 := by
    intro ε hε
    have hε4 : 0 < ε / 4 := by linarith
    filter_upwards [hB1dec (ε / 4) hε4, hB2dec (ε / 4) hε4, eventually_ge_atTop 1] with j h1j h2j hj1
    have hcu : (C j).card ≤ (B1 j).card + (B2 j).card + ((E1 j).card + (E2 j).card) := by
      simp only [C, hj1, if_true]
      calc (B1 j ∪ B2 j ∪ R j).card
          ≤ (B1 j ∪ B2 j).card + (R j).card := Finset.card_union_le _ _
        _ ≤ ((B1 j).card + (B2 j).card) + (E1 j ∪ E2 j).card :=
            Nat.add_le_add (Finset.card_union_le _ _) Finset.card_image_le
        _ ≤ (B1 j).card + (B2 j).card + ((E1 j).card + (E2 j).card) :=
            Nat.add_le_add_left (Finset.card_union_le _ _) _
    have hcu' : ((C j).card : ℝ) ≤
        ((B1 j).card : ℝ) + ((B2 j).card : ℝ) + (((E1 j).card : ℝ) + ((E2 j).card : ℝ)) := by
      exact_mod_cast hcu
    have h1a : ((B1 j).card : ℝ) ≤ (ε / 4) * ((2 ^ j : ℕ) : ℝ) ^ 2 := h1j.1
    have h1b : ((E1 j).card : ℝ) ≤ (ε / 4) * ((2 ^ j : ℕ) : ℝ) ^ 2 := h1j.2
    have h2a : ((B2 j).card : ℝ) ≤ (ε / 4) * ((2 ^ j : ℕ) : ℝ) ^ 2 := h2j.1
    have h2b : ((E2 j).card : ℝ) ≤ (ε / 4) * ((2 ^ j : ℕ) : ℝ) ^ 2 := h2j.2
    linarith
  refine ⟨A, ?_, ?_⟩
  · -- Part 1: IsAdditiveComplementToPrimes A
    unfold Erdos32.IsAdditiveComplementToPrimes
    filter_upwards [eventually_ge_atTop (2 ^ (2 ^ 2))] with n hn
    have hu0 : 2 ^ (2 ^ 0) ≤ n := by
      have : 2 ^ (2 ^ 0) ≤ 2 ^ (2 ^ 2) := by norm_num
      omega
    obtain ⟨m, hm1, hm2⟩ := window_exists (fun j => 2 ^ (2 ^ j)) strictMono_two_pow_two_pow n hu0
    have hm_ge2 : 2 ≤ m := by
      by_contra hlt
      push Not at hlt
      have hle : m + 1 ≤ 2 := by omega
      have hpow : 2 ^ (2 ^ (m + 1)) ≤ 2 ^ (2 ^ 2) :=
        strictMono_two_pow_two_pow.monotone hle
      omega
    set j := m - 1 with hjdef
    have hj1 : 1 ≤ j := by omega
    have hj_eq : j + 1 = m := by omega
    have hj_eq2 : j + 2 = m + 1 := by omega
    have hn_mem : n ∈ Finset.Ico (2 ^ (2 ^ (j + 1))) (2 ^ (2 ^ (j + 2))) := by
      rw [Finset.mem_Ico, hj_eq, hj_eq2]
      exact ⟨hm1, hm2⟩
    rcases Nat.even_or_odd n with hev | hodd
    · by_cases hcov : ∃ p, p.Prime ∧ ∃ a ∈ B1 j, n = p + a
      · obtain ⟨p, hp, a, ha, heq⟩ := hcov
        refine ⟨p, hp, a, ⟨j, ?_⟩, heq⟩
        simp only [C, hj1, if_true, Finset.mem_union]
        exact Or.inl (Or.inl ha)
      · have hnE : n ∈ E1 j := Finset.mem_filter.mpr ⟨hn_mem, hev, hcov⟩
        refine ⟨2, Nat.prime_two, n - 2, ⟨j, ?_⟩, by omega⟩
        simp only [C, hj1, if_true, Finset.mem_union]
        right
        exact Finset.mem_image.mpr ⟨n, Finset.mem_union_left _ hnE, rfl⟩
    · by_cases hcov : ∃ p, p.Prime ∧ ∃ a ∈ B2 j, n = p + a
      · obtain ⟨p, hp, a, ha, heq⟩ := hcov
        refine ⟨p, hp, a, ⟨j, ?_⟩, heq⟩
        simp only [C, hj1, if_true, Finset.mem_union]
        exact Or.inl (Or.inr ha)
      · have hnE : n ∈ E2 j := Finset.mem_filter.mpr ⟨hn_mem, hodd, hcov⟩
        refine ⟨2, Nat.prime_two, n - 2, ⟨j, ?_⟩, by omega⟩
        simp only [C, hj1, if_true, Finset.mem_union]
        right
        exact Finset.mem_image.mpr ⟨n, Finset.mem_union_right _ hnE, rfl⟩
  · -- Part 2: |A ∩ [1, N]| =o[atTop] (log N)^2
    rw [Asymptotics.isLittleO_iff]
    intro c hc
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hδ_pos : 0 < c * (Real.log 2) ^ 2 / 4 := by positivity
    obtain ⟨K, hK⟩ := eventually_atTop.mp (hCcard (c * (Real.log 2) ^ 2 / 4) hδ_pos)
    let M : ℝ := ∑ j ∈ Finset.range K, ((C j).card : ℝ)
    have hM_nn : 0 ≤ M := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
    -- Choose N0 large enough that M <= (c / 2) * (log N)^2 and N >= 2^(2^0) = 2
    have htend : Tendsto (fun N : ℕ => (c / 2) * (Real.log (N : ℝ)) ^ 2) atTop atTop := by
      have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
        Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
      have hsq : Tendsto (fun N : ℕ => (Real.log (N : ℝ)) ^ 2) atTop atTop :=
        (tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp hlog
      exact Tendsto.const_mul_atTop (by linarith) hsq
    filter_upwards [htend.eventually_ge_atTop M, eventually_ge_atTop 2] with N hNM hN2
    have h20 : 2 ^ (2 ^ 0) ≤ N := by norm_num; omega
    obtain ⟨k, hk1, hk2⟩ := window_exists (fun j => 2 ^ (2 ^ j)) strictMono_two_pow_two_pow N h20
    have hincl : (Finset.Icc 1 N).filter (· ∈ A) ⊆ (Finset.range (k + 1)).biUnion C := by
      intro a ha
      obtain ⟨hIcc, j, haj⟩ := Finset.mem_filter.mp ha
      refine Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr ?_, haj⟩
      have hlt : 2 ^ (2 ^ j) < 2 ^ (2 ^ (k + 1)) :=
        lt_of_le_of_lt (hClow j a haj) (lt_of_le_of_lt (Finset.mem_Icc.mp hIcc).2 hk2)
      exact strictMono_two_pow_two_pow.lt_iff_lt.mp hlt
    have hcard_le : ((Finset.Icc 1 N).filter (· ∈ A)).card ≤
        ∑ j ∈ Finset.range (k + 1), (C j).card :=
      (Finset.card_le_card hincl).trans Finset.card_biUnion_le
    have hcard_R : (((Finset.Icc 1 N).filter (· ∈ A)).card : ℝ) ≤
        ∑ j ∈ Finset.range (k + 1), ((C j).card : ℝ) := by
      exact_mod_cast hcard_le
    have hsplit : ∑ j ∈ Finset.range (k + 1), ((C j).card : ℝ) ≤
        M + ∑ j ∈ Finset.range (k + 1), (c * (Real.log 2) ^ 2 / 4) * (((2 ^ j : ℕ) : ℝ) ^ 2) := by
      have hterm : ∀ j ∈ Finset.range (k + 1),
          ((C j).card : ℝ) ≤
            (if j < K then ((C j).card : ℝ) else 0) +
            (c * (Real.log 2) ^ 2 / 4) * (((2 ^ j : ℕ) : ℝ) ^ 2) := by
        intro j _
        by_cases hlt : j < K
        · simp only [hlt, if_true]
          have : (0 : ℝ) ≤ (c * (Real.log 2) ^ 2 / 4) * (((2 ^ j : ℕ) : ℝ) ^ 2) := by positivity
          linarith
        · simp only [hlt, if_false, zero_add]
          exact hK j (Nat.le_of_not_lt hlt)
      calc ∑ j ∈ Finset.range (k + 1), ((C j).card : ℝ)
          ≤ ∑ j ∈ Finset.range (k + 1),
              ((if j < K then ((C j).card : ℝ) else 0) +
               (c * (Real.log 2) ^ 2 / 4) * (((2 ^ j : ℕ) : ℝ) ^ 2)) :=
            Finset.sum_le_sum hterm
        _ = (∑ j ∈ Finset.range (k + 1), if j < K then ((C j).card : ℝ) else 0) +
            ∑ j ∈ Finset.range (k + 1), (c * (Real.log 2) ^ 2 / 4) * (((2 ^ j : ℕ) : ℝ) ^ 2) :=
            Finset.sum_add_distrib
        _ ≤ M + ∑ j ∈ Finset.range (k + 1), (c * (Real.log 2) ^ 2 / 4) * (((2 ^ j : ℕ) : ℝ) ^ 2) := by
            gcongr
            rw [← Finset.sum_filter]
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro j hj
              exact Finset.mem_range.mpr (Finset.mem_filter.mp hj).2
            · intro _ _ _; exact Nat.cast_nonneg _
    have hgeom : ∑ j ∈ Finset.range (k + 1),
          (c * (Real.log 2) ^ 2 / 4) * (((2 ^ j : ℕ) : ℝ) ^ 2) ≤
        (c / 2) * (Real.log (N : ℝ)) ^ 2 := by
      rw [← Finset.mul_sum]
      have hg := geom_sum_four_pow k
      have hlog_bd : ((2 ^ k : ℕ) : ℝ) * Real.log 2 ≤ Real.log (N : ℝ) := by
        have h1 : (2 : ℝ) ^ (2 ^ k : ℕ) ≤ (N : ℝ) := by exact_mod_cast hk1
        have h2 := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ (2 ^ k : ℕ)) h1
        simpa [Real.log_pow] using h2
      have hsq_bd : (((2 ^ k : ℕ) : ℝ) ^ 2) * (Real.log 2) ^ 2 ≤ (Real.log (N : ℝ)) ^ 2 := by
        have hnn : 0 ≤ ((2 ^ k : ℕ) : ℝ) * Real.log 2 := by positivity
        have hsq := pow_le_pow_left₀ hnn hlog_bd 2
        simpa [mul_pow] using hsq
      calc (c * (Real.log 2) ^ 2 / 4) * ∑ j ∈ Finset.range (k + 1), (((2 ^ j : ℕ) : ℝ) ^ 2)
          ≤ (c * (Real.log 2) ^ 2 / 4) * (2 * (((2 ^ k : ℕ) : ℝ) ^ 2)) :=
            mul_le_mul_of_nonneg_left hg hδ_pos.le
        _ = (c / 2) * ((((2 ^ k : ℕ) : ℝ) ^ 2) * (Real.log 2) ^ 2) := by ring
        _ ≤ (c / 2) * (Real.log (N : ℝ)) ^ 2 :=
            mul_le_mul_of_nonneg_left hsq_bd (by linarith)
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (sq_nonneg _)]
    linarith

end OMA.R_Erdos32_erdos_32_R1
