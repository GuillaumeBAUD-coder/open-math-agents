import OMAReductions.R_Erdos441_erdos_441_variants_chen_dai_upper_bound_R1
import Mathlib

-- Step Erdos441.erdos_441.variants.chen_dai_upper_bound.R1.H1
-- Credit: @arindale
--
-- The lower bound from Erdős' construction: the set of all integers at most sqrt(N/2)
-- together with the even integers up to sqrt(2N) is admissible and has about sqrt(9N/8)
-- elements.  We exhibit a concrete admissible subset of {1,...,N} and count it.

open Erdos441

namespace OMA441Lower

lemma mul_le_of_two_mul_sq_le_sq_le {N x y : ℕ}
    (hx : 2 * x ^ 2 ≤ N) (hy : y ^ 2 ≤ 2 * N) : x * y ≤ N := by
  nlinarith [sq_nonneg (2 * (x : ℤ) - y)]

lemma two_mul_le_of_two_mul_sq_le {N u v : ℕ}
    (hu : 2 * u ^ 2 ≤ N) (hv : 2 * v ^ 2 ≤ N) : 2 * (u * v) ≤ N := by
  nlinarith [sq_nonneg ((u : ℤ) - v)]

lemma lcm_le_mul {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) : Nat.lcm a b ≤ a * b :=
  Nat.le_of_dvd (Nat.mul_pos (by omega) (by omega)) (Nat.lcm_dvd_mul a b)

lemma construction_lcmBounded (N : ℕ) :
    erdosConstruction N ⊆ Finset.Icc 1 N ∧
      ∀ a ∈ erdosConstruction N, ∀ b ∈ erdosConstruction N, Nat.lcm a b ≤ N := by
  constructor
  · intro a ha
    simp only [erdosConstruction, Finset.mem_filter, Finset.mem_Icc] at ha
    exact Finset.mem_Icc.mpr ⟨ha.1.1, ha.1.2⟩
  · intro a ha b hb
    simp only [erdosConstruction, Finset.mem_filter, Finset.mem_Icc] at ha hb
    obtain ⟨⟨ha1, _haN⟩, haCase⟩ := ha
    obtain ⟨⟨hb1, _hbN⟩, hbCase⟩ := hb
    rcases haCase with haLow | ⟨haEven, haHigh⟩
    · rcases hbCase with hbLow | ⟨_hbEven, hbHigh⟩
      · have hbHigh : b ^ 2 ≤ 2 * N := by omega
        exact (lcm_le_mul ha1 hb1).trans (mul_le_of_two_mul_sq_le_sq_le haLow hbHigh)
      · exact (lcm_le_mul ha1 hb1).trans (mul_le_of_two_mul_sq_le_sq_le haLow hbHigh)
    · rcases hbCase with hbLow | ⟨hbEven, hbHigh⟩
      · rw [Nat.lcm_comm]
        exact (lcm_le_mul hb1 ha1).trans (mul_le_of_two_mul_sq_le_sq_le hbLow haHigh)
      · rcases haEven with ⟨u, rfl⟩
        rcases hbEven with ⟨v, rfl⟩
        have hu : 2 * u ^ 2 ≤ N := by nlinarith
        have hv : 2 * v ^ 2 ≤ N := by nlinarith
        have huPos : 1 ≤ u := by omega
        have hvPos : 1 ≤ v := by omega
        have hdvd : Nat.lcm (2 * u) (2 * v) ∣ 2 * (u * v) := by
          apply Nat.lcm_dvd
          · exact ⟨v, by ring⟩
          · exact ⟨u, by ring⟩
        calc Nat.lcm (2 * u) (2 * v) ≤ 2 * (u * v) :=
            Nat.le_of_dvd (Nat.mul_pos (by norm_num) (Nat.mul_pos huPos hvPos)) hdvd
          _ ≤ N := two_mul_le_of_two_mul_sq_le hu hv

lemma card_le_g {N : ℕ} {A : Finset ℕ}
    (hsub : A ⊆ Finset.Icc 1 N)
    (hlcm : ∀ a ∈ A, ∀ b ∈ A, Nat.lcm a b ≤ N) : A.card ≤ g N := by
  have hmem : A.card ∈ {k | ∃ B : Finset ℕ, B ⊆ Finset.Icc 1 N ∧
      (∀ a ∈ B, ∀ b ∈ B, Nat.lcm a b ≤ N) ∧ B.card = k} :=
    ⟨A, hsub, hlcm, rfl⟩
  have hbdd : BddAbove {k | ∃ B : Finset ℕ, B ⊆ Finset.Icc 1 N ∧
      (∀ a ∈ B, ∀ b ∈ B, Nat.lcm a b ≤ N) ∧ B.card = k} := by
    refine ⟨N, ?_⟩
    rintro k ⟨B, hBsub, _, hBcard⟩
    rw [← hBcard]
    calc B.card ≤ (Finset.Icc 1 N).card := Finset.card_le_card hBsub
      _ = N := by simp
  simpa only [g] using le_csSup hbdd hmem

end OMA441Lower

theorem OMA.solution : OMA.R_Erdos441_erdos_441_variants_chen_dai_upper_bound_R1.H1 := by
  refine ⟨2, ?_⟩
  intro N
  set m : ℕ := Nat.sqrt (N / 2) with hm_def
  set S1 : Finset ℕ := Finset.Icc 1 m with hS1
  set S2 : Finset ℕ := (Finset.Icc (m / 2 + 1) m).image (fun j => 2 * j) with hS2
  set S : Finset ℕ := S1 ∪ S2 with hS
  have hm_sq : m ^ 2 ≤ N / 2 := by
    rw [hm_def]
    exact Nat.sqrt_le' (N / 2)
  have h2div : 2 * (N / 2) ≤ N := by
    have := Nat.div_mul_le_self N 2
    omega
  have h2m2 : 2 * m ^ 2 ≤ N := by
    nlinarith
  have hmN : m ≤ N := by
    have h1 : m ≤ N / 2 := by
      rw [hm_def]
      exact Nat.sqrt_le_self (N / 2)
    have h2 : N / 2 ≤ N := Nat.div_le_self N 2
    omega
  have h2mN : 2 * m ≤ N := by
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · omega
    · have hmle : m ≤ m ^ 2 := by nlinarith
      nlinarith
  have hSsub : S ⊆ erdosConstruction N := by
    intro a ha
    rw [hS, Finset.mem_union] at ha
    rcases ha with ha1 | ha2
    · rw [hS1, Finset.mem_Icc] at ha1
      simp only [erdosConstruction, Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨ha1.1, by omega⟩, Or.inl ?_⟩
      nlinarith [ha1.2, h2m2]
    · rw [hS2, Finset.mem_image] at ha2
      obtain ⟨j, hj, rfl⟩ := ha2
      rw [Finset.mem_Icc] at hj
      simp only [erdosConstruction, Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨by omega, by omega⟩, Or.inr ⟨⟨j, by ring⟩, ?_⟩⟩
      nlinarith [hj.2, h2m2]
  have hS1card : S1.card = m := by
    rw [hS1, Nat.card_Icc]
    omega
  have hinj : Set.InjOn (fun j : ℕ => 2 * j) (↑(Finset.Icc (m / 2 + 1) m) : Set ℕ) := by
    intro j _ k _ h
    exact Nat.mul_left_cancel (by norm_num) h
  have hS2card : S2.card = m - m / 2 := by
    rw [hS2, Finset.card_image_of_injOn hinj, Nat.card_Icc]
    omega
  have hdisj : Disjoint S1 S2 := by
    rw [Finset.disjoint_left]
    intro a ha1 ha2
    rw [hS1, Finset.mem_Icc] at ha1
    rw [hS2, Finset.mem_image] at ha2
    obtain ⟨j, hj, rfl⟩ := ha2
    rw [Finset.mem_Icc] at hj
    omega
  have hScard : S.card = m + (m - m / 2) := by
    rw [hS, Finset.card_union_of_disjoint hdisj, hS1card, hS2card]
  have hSg : S.card ≤ g N := by
    have h1 : S.card ≤ (erdosConstruction N).card := Finset.card_le_card hSsub
    have h2 : (erdosConstruction N).card ≤ g N :=
      OMA441Lower.card_le_g (OMA441Lower.construction_lcmBounded N).1
        (OMA441Lower.construction_lcmBounded N).2
    exact h1.trans h2
  have hm_le_sqrt : (m : ℝ) ≤ Real.sqrt ((N : ℝ) / 2) := by
    have hsq : (m : ℝ) ^ 2 ≤ (N : ℝ) / 2 := by
      have h1 : ((m ^ 2 : ℕ) : ℝ) ≤ ((N / 2 : ℕ) : ℝ) := by
        exact_mod_cast hm_sq
      have h2 : ((N / 2 : ℕ) : ℝ) ≤ (N : ℝ) / 2 := Nat.cast_div_le
      calc (m : ℝ) ^ 2 = ((m ^ 2 : ℕ) : ℝ) := by push_cast; ring
        _ ≤ ((N / 2 : ℕ) : ℝ) := h1
        _ ≤ (N : ℝ) / 2 := h2
    exact (Real.le_sqrt (by positivity) (by positivity)).mpr hsq
  have hsqrt_le_m : Real.sqrt ((N : ℝ) / 2) ≤ (m : ℝ) + 1 := by
    have h1 : N / 2 + 1 ≤ (m + 1) ^ 2 := by
      have := Nat.lt_succ_sqrt' (N / 2)
      rw [← hm_def] at this
      exact Nat.succ_le_of_lt (by simpa [Nat.succ_eq_add_one] using this)
    have h2 : ((N / 2 : ℕ) : ℝ) + 1 ≤ ((m : ℝ) + 1) ^ 2 := by
      have hcast : ((N / 2 + 1 : ℕ) : ℝ) ≤ (((m + 1) ^ 2 : ℕ) : ℝ) := by
        exact_mod_cast h1
      push_cast at hcast
      exact hcast
    have h3 : (N : ℝ) / 2 ≤ ((N / 2 : ℕ) : ℝ) + 1 := by
      have hsplit : 2 * (N / 2) + N % 2 = N := Nat.div_add_mod N 2
      have hmod : (N % 2 : ℕ) ≤ 1 := by
        have := Nat.mod_lt N (by norm_num : 0 < 2)
        omega
      have hcast : (N : ℝ) = 2 * ((N / 2 : ℕ) : ℝ) + ((N % 2 : ℕ) : ℝ) := by
        have h := congrArg (fun x : ℕ => (x : ℝ)) hsplit
        push_cast at h
        linarith
      have hmodR : ((N % 2 : ℕ) : ℝ) ≤ 1 := by exact_mod_cast hmod
      linarith
    have h4 : (N : ℝ) / 2 ≤ ((m : ℝ) + 1) ^ 2 := h3.trans h2
    exact (Real.sqrt_le_iff).mpr ⟨by positivity, h4⟩
  have hcardS : (S.card : ℝ) = 2 * (m : ℝ) - ((m / 2 : ℕ) : ℝ) := by
    have h1 : ((m - m / 2 : ℕ) : ℝ) = (m : ℝ) - ((m / 2 : ℕ) : ℝ) :=
      Nat.cast_sub (Nat.div_le_self m 2)
    rw [hScard]
    push_cast
    rw [h1]
    ring
  have hm2le : ((m / 2 : ℕ) : ℝ) ≤ Real.sqrt ((N : ℝ) / 2) / 2 := by
    have h1 : ((m / 2 : ℕ) : ℝ) ≤ (m : ℝ) / 2 := Nat.cast_div_le
    have h2 : (m : ℝ) / 2 ≤ Real.sqrt ((N : ℝ) / 2) / 2 := by linarith [hm_le_sqrt]
    linarith
  have hmain : Real.sqrt (9 / 8 * (N : ℝ)) - 2 ≤ (S.card : ℝ) := by
    have hsq : Real.sqrt (9 / 8 * (N : ℝ)) = (3 / 2) * Real.sqrt ((N : ℝ) / 2) := by
      have h9 : (9 : ℝ) / 8 * (N : ℝ) = ((3 : ℝ) / 2) ^ 2 * ((N : ℝ) / 2) := by ring
      rw [h9, Real.sqrt_mul (by positivity)]
      rw [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ (3 : ℝ) / 2)]
    rw [hsq, hcardS]
    nlinarith [hm_le_sqrt, hsqrt_le_m, hm2le]
  have hg : (S.card : ℝ) ≤ (g N : ℝ) := by exact_mod_cast hSg
  linarith
