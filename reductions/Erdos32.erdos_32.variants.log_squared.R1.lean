import FormalConjectures.ErdosProblems.«32»

-- Reduction Erdos32.erdos_32.variants.log_squared.R1 of Erdős Problem 32 — log squared
-- Credit: @mucoucah
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
-- H1 / H2: a set A with O((log N)^2) elements up to N which represents all EVEN (resp. ODD)
-- n as p + a (p prime, a in A) except for an exceptional set of size O((log N)^2) up to N.
-- main: glue the two sets and repair every uncovered n via n = 2 + (n - 2).

open Filter Asymptotics

namespace OMA.R_Erdos32_erdos_32_variants_log_squared_R1

open scoped Classical in
def H1 : Prop := ∃ A : Set ℕ, ∃ C : ℝ, ∃ N0 : ℕ, ∀ N ≥ N0,
  (((Finset.Icc 1 N).filter (· ∈ A)).card : ℝ) ≤ C * (Real.log N) ^ 2 ∧
  (((Finset.Icc 1 N).filter (fun n => Even n ∧ ¬ ∃ p, p.Prime ∧ ∃ a ∈ A, n = p + a)).card : ℝ)
    ≤ C * (Real.log N) ^ 2

open scoped Classical in
def H2 : Prop := ∃ A : Set ℕ, ∃ C : ℝ, ∃ N0 : ℕ, ∀ N ≥ N0,
  (((Finset.Icc 1 N).filter (· ∈ A)).card : ℝ) ≤ C * (Real.log N) ^ 2 ∧
  (((Finset.Icc 1 N).filter (fun n => Odd n ∧ ¬ ∃ p, p.Prime ∧ ∃ a ∈ A, n = p + a)).card : ℝ)
    ≤ C * (Real.log N) ^ 2

lemma log_sq_le (N : ℕ) (hN : 2 ≤ N) :
    Real.log ((N + 2 : ℕ) : ℝ) ^ 2 ≤ 4 * Real.log (N : ℝ) ^ 2 := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have h0 : 0 ≤ Real.log ((N + 2 : ℕ) : ℝ) := Real.log_nonneg (by push_cast; linarith)
  have h1 : Real.log ((N + 2 : ℕ) : ℝ) ≤ 2 * Real.log (N : ℝ) := by
    rw [← Real.log_rpow (by linarith)]
    apply Real.log_le_log (by push_cast; linarith)
    push_cast
    rw [show ((N : ℝ) ^ (2 : ℝ)) = (N : ℝ) ^ (2 : ℕ) by norm_cast]
    nlinarith
  nlinarith

open scoped Classical in
lemma card_fix (A1 A2 : Set ℕ) (N : ℕ) :
    (((Finset.Icc 1 N).filter
      (· ∈ {a : ℕ | ¬ ∃ p, p.Prime ∧ ∃ b ∈ A1 ∪ A2, a + 2 = p + b})).card)
    ≤ ((Finset.Icc 1 (N + 2)).filter
        (fun n => Even n ∧ ¬ ∃ p, p.Prime ∧ ∃ a ∈ A1, n = p + a)).card +
      ((Finset.Icc 1 (N + 2)).filter
        (fun n => Odd n ∧ ¬ ∃ p, p.Prime ∧ ∃ a ∈ A2, n = p + a)).card := by
  refine le_trans ?_ (Finset.card_union_le _ _)
  rw [← Finset.card_image_of_injective _ (add_left_injective 2)]
  apply Finset.card_le_card
  intro n hn
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_Icc, Set.mem_setOf_eq] at hn
  obtain ⟨a, ⟨⟨ha1, ha2⟩, hF⟩, rfl⟩ := hn
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Icc]
  rcases Nat.even_or_odd (a + 2) with he | ho
  · left
    refine ⟨⟨by omega, by omega⟩, he, ?_⟩
    rintro ⟨p, hp, b, hb, h⟩
    exact hF ⟨p, hp, b, Or.inl hb, h⟩
  · right
    refine ⟨⟨by omega, by omega⟩, ho, ?_⟩
    rintro ⟨p, hp, b, hb, h⟩
    exact hF ⟨p, hp, b, Or.inr hb, h⟩

lemma card_union3 (A1 A2 F : Set ℕ) (N : ℕ) [DecidablePred (· ∈ A1)] [DecidablePred (· ∈ A2)]
    [DecidablePred (· ∈ F)] [DecidablePred (· ∈ A1 ∪ A2 ∪ F)] :
    ((Finset.Icc 1 N).filter (· ∈ A1 ∪ A2 ∪ F)).card ≤
      ((Finset.Icc 1 N).filter (· ∈ A1)).card + ((Finset.Icc 1 N).filter (· ∈ A2)).card +
      ((Finset.Icc 1 N).filter (· ∈ F)).card := by
  refine le_trans ?_ (le_trans (Finset.card_union_le _ _)
    (Nat.add_le_add_right (Finset.card_union_le _ _) _))
  apply Finset.card_le_card
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_union, Set.mem_union] at hn ⊢
  tauto

open scoped Classical in
theorem main : H1 → H2 → type_of% @Erdos32.erdos_32.variants.log_squared := by
  rintro ⟨A1, C1, M1, h1⟩ ⟨A2, C2, M2, h2⟩
  set F : Set ℕ := {a : ℕ | ¬ ∃ p, p.Prime ∧ ∃ b ∈ A1 ∪ A2, a + 2 = p + b} with hFdef
  refine ⟨A1 ∪ A2 ∪ F, ?_, ?_⟩
  · unfold Erdos32.IsAdditiveComplementToPrimes
    filter_upwards [eventually_ge_atTop 2] with n hn
    by_cases hc : ∃ p, p.Prime ∧ ∃ b ∈ A1 ∪ A2, n = p + b
    · obtain ⟨p, hp, b, hb, h⟩ := hc
      exact ⟨p, hp, b, Or.inl hb, h⟩
    · refine ⟨2, Nat.prime_two, n - 2, Or.inr ?_, by omega⟩
      show ¬ ∃ p, p.Prime ∧ ∃ b ∈ A1 ∪ A2, n - 2 + 2 = p + b
      rwa [Nat.sub_add_cancel hn]
  · refine Asymptotics.IsBigO.of_bound (C1 + C2 + 4 * (C1 + C2)) ?_
    filter_upwards [eventually_ge_atTop (max (max M1 M2) 2)] with N hN
    have hM1 : M1 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
    have hM2 : M2 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
    have h2N : 2 ≤ N := le_trans (le_max_right _ _) hN
    obtain ⟨a1, -⟩ := h1 N hM1
    obtain ⟨a2, -⟩ := h2 N hM2
    obtain ⟨-, e1⟩ := h1 (N + 2) (by omega)
    obtain ⟨-, e2⟩ := h2 (N + 2) (by omega)
    have hl := log_sq_le N h2N
    have hcU := card_union3 A1 A2 F N
    have hcF := card_fix A1 A2 N
    have hcU' : (((Finset.Icc 1 N).filter (· ∈ A1 ∪ A2 ∪ F)).card : ℝ) ≤
        (((Finset.Icc 1 N).filter (· ∈ A1)).card : ℝ) +
        (((Finset.Icc 1 N).filter (· ∈ A2)).card : ℝ) +
        (((Finset.Icc 1 N).filter (· ∈ F)).card : ℝ) := by exact_mod_cast hcU
    have hcF' : (((Finset.Icc 1 N).filter (· ∈ F)).card : ℝ) ≤
        (((Finset.Icc 1 (N + 2)).filter
          (fun n => Even n ∧ ¬ ∃ p, p.Prime ∧ ∃ a ∈ A1, n = p + a)).card : ℝ) +
        (((Finset.Icc 1 (N + 2)).filter
          (fun n => Odd n ∧ ¬ ∃ p, p.Prime ∧ ∃ a ∈ A2, n = p + a)).card : ℝ) := by
      exact_mod_cast hcF
    have hC1 : 0 ≤ C1 := by
      by_contra hneg
      have hlogpos : 0 < Real.log (N : ℝ) :=
        Real.log_pos (by have : (2 : ℝ) ≤ N := by exact_mod_cast h2N
                         linarith)
      have : C1 * Real.log (N : ℝ) ^ 2 < 0 :=
        mul_neg_of_neg_of_pos (by linarith) (by positivity)
      have : (0 : ℝ) ≤ ((Finset.Icc 1 N).filter (· ∈ A1)).card := by positivity
      linarith
    have hC2 : 0 ≤ C2 := by
      by_contra hneg
      have hlogpos : 0 < Real.log (N : ℝ) :=
        Real.log_pos (by have : (2 : ℝ) ≤ N := by exact_mod_cast h2N
                         linarith)
      have : C2 * Real.log (N : ℝ) ^ 2 < 0 :=
        mul_neg_of_neg_of_pos (by linarith) (by positivity)
      have : (0 : ℝ) ≤ ((Finset.Icc 1 N).filter (· ∈ A2)).card := by positivity
      linarith
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      abs_of_nonneg (by positivity)]
    have e1' : C1 * Real.log ((N + 2 : ℕ) : ℝ) ^ 2 ≤ C1 * (4 * Real.log (N : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hl hC1
    have e2' : C2 * Real.log ((N + 2 : ℕ) : ℝ) ^ 2 ≤ C2 * (4 * Real.log (N : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hl hC2
    push_cast at e1 e2 e1' e2'
    have fin := le_trans hcU'
      (show _ ≤ (C1 + C2 + 4 * (C1 + C2)) * Real.log (N : ℝ) ^ 2 by nlinarith)
    convert fin using 3 <;> first | rfl | (ext; simp)

end OMA.R_Erdos32_erdos_32_variants_log_squared_R1
