import FormalConjectures.ErdosProblems.«3»

-- Green and Tao, New bounds for Szemerédi's theorem, III, Section 3.
-- https://arxiv.org/abs/1705.01703
-- Credit: @SubhanAfz

open Asymptotics Filter
open scoped BigOperators

namespace OMA.R_Erdos3_erdos_3_variants_green_tao_R1

private theorem natCast_inj_below {p a b : ℕ} (ha : a < p) (hb : b < p)
    (h : (a : ZMod p) = b) : a = b := by
  simpa [ZMod.val_natCast_of_lt ha, ZMod.val_natCast_of_lt hb] using congrArg ZMod.val h

private theorem increasing_quadruple_forbidden {S : Finset ℕ} {a b c d : ℕ}
    (hS : (S : Set ℕ).IsAPOfLengthFree 4) (ha : a ∈ S) (hb : b ∈ S)
    (hc : c ∈ S) (hd : d ∈ S) (hab : a < b) (h₁ : a + c = b + b)
    (h₂ : b + d = c + c) : False := by
  let step := b - a
  have hstep : 0 < step := by dsimp [step]; omega
  have hpositions : ∀ i : ℕ, i < 4 → a + i * step ∈ S := by
    intro i hi
    interval_cases i
    · simpa using ha
    · convert hb using 1
      dsimp [step]
      omega
    · convert hc using 1
      dsimp [step]
      omega
    · convert hd using 1
      dsimp [step]
      omega
  let e : ℕ ↪ ℕ := ⟨fun i ↦ a + i * step, fun _ _ eqn ↦
    Nat.eq_of_mul_eq_mul_right hstep (Nat.add_left_cancel eqn)⟩
  let T := (Finset.range 4).map e
  have hTS : (T : Set ℕ) ⊆ S := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx
    exact hpositions i (Finset.mem_range.mp hi)
  have hT : (T : Set ℕ).IsAPOfLength 4 := by
    refine ⟨a, step, ?_, ?_⟩
    · change (T : Set ℕ).encard = 4
      rw [Set.encard_coe_eq_coe_finsetCard]
      simp [T]
    · ext x
      simp [T, e]
      rfl
  have impossible := hS (T : Set ℕ) hTS hT
  norm_num at impossible

private theorem no_cyclic_progression {N p : ℕ} {S : Finset ℕ}
    (hp : 2 * N < p) (hS : S ⊆ Finset.Icc 1 N) (hfree : (S : Set ℕ).IsAPOfLengthFree 4)
    {x r : ZMod p} (hr : r ≠ 0)
    (h : x ∈ S.image (Nat.cast : ℕ → ZMod p) ∧
      x + r ∈ S.image (Nat.cast : ℕ → ZMod p) ∧
      x + 2 * r ∈ S.image (Nat.cast : ℕ → ZMod p) ∧
      x + 3 * r ∈ S.image (Nat.cast : ℕ → ZMod p)) : False := by
  obtain ⟨a, ha, he⟩ := Finset.mem_image.mp h.1
  obtain ⟨b, hb, hf⟩ := Finset.mem_image.mp h.2.1
  obtain ⟨c, hc, hg⟩ := Finset.mem_image.mp h.2.2.1
  obtain ⟨d, hd, hh⟩ := Finset.mem_image.mp h.2.2.2
  have haN := (Finset.mem_Icc.mp (hS ha)).2
  have hbN := (Finset.mem_Icc.mp (hS hb)).2
  have hcN := (Finset.mem_Icc.mp (hS hc)).2
  have hdN := (Finset.mem_Icc.mp (hS hd)).2
  -- Each sum of two representatives is below the modulus.
  have h₁ : a + c = b + b := by
    apply natCast_inj_below (by omega) (by omega) (p := p)
    push_cast
    rw [he, hf, hg]
    ring
  have h₂ : b + d = c + c := by
    apply natCast_inj_below (by omega) (by omega) (p := p)
    push_cast
    rw [hf, hg, hh]
    ring
  rcases lt_trichotomy a b with hab | hab | hba
  · exact increasing_quadruple_forbidden hfree ha hb hc hd hab h₁ h₂
  · subst b
    have heq : x + r = x + 0 := hf.symm.trans (he.trans (add_zero x).symm)
    exact hr (add_left_cancel heq)
  · exact increasing_quadruple_forbidden hfree hd hc hb ha (by omega) (by omega) (by omega)

private theorem extremal_witness (N : ℕ) : ∃ S : Finset ℕ,
    S ⊆ Finset.Icc 1 N ∧ (S : Set ℕ).IsAPOfLengthFree 4 ∧ S.card = Erdos3.r 4 N := by
  let sizes : Set ℕ := {Finset.card S | (S) (_ : S ⊆ Finset.Icc 1 N)
    (_ : (S : Set ℕ).IsAPOfLengthFree 4)}
  have h₀ : sizes.Nonempty := by
    refine ⟨0, ∅, Finset.empty_subset _, ?_, rfl⟩
    intro T hT hAP
    have hEmpty : T = ∅ := Set.subset_empty_iff.mp (by simpa using hT)
    subst T
    exact (Set.not_isAPOfLength_empty (by norm_num : (0 : ℕ∞) < 4) hAP).elim
  have hN : BddAbove sizes := by
    refine ⟨N, ?_⟩
    rintro _ ⟨S, hS, _, rfl⟩
    exact (Finset.card_le_card hS).trans_eq (by simp [Nat.card_Icc])
  obtain ⟨S, hS, hfree, hcard⟩ := Nat.sSup_mem h₀ hN
  exact ⟨S, hS, hfree, hcard⟩

/-- The indicator-function case of Green and Tao's quantitative recurrence estimate.
The weights describe the joint distribution of the starting point and common difference. -/
def H1 : Prop :=
  ∃ C B : ℝ, 0 < C ∧ 0 < B ∧
    ∀ (p : ℕ) [Fact p.Prime] (ε : ℝ), 0 < ε → ε ≤ 1 / 10 →
      ∀ A : Finset (ZMod p), ∃ w : ZMod p × ZMod p → ℝ,
        (∀ z, 0 ≤ w z) ∧ (∑ z, w z) = 1 ∧
        ((A.card : ℝ) / p) ^ 4 ≤ C * ε +
          (∑ z, if z.1 ∈ A ∧ z.1 + z.2 ∈ A ∧ z.1 + 2 * z.2 ∈ A ∧
            z.1 + 3 * z.2 ∈ A then w z else 0) ∧
        (∑ z, if z.2 = 0 then w z else 0) ≤ C * Real.exp (ε ^ (-B)) / p

/-- A logarithmic choice of the recurrence parameter bounds both error terms. -/
def H2 : Prop :=
  ∀ C B : ℝ, 0 < C → 0 < B → ∃ c K : ℝ, 0 < c ∧ 0 < K ∧
    ∀ᶠ p : ℕ in atTop, ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / 10 ∧
      C * ε + C * Real.exp (ε ^ (-B)) / p ≤ (K * Real.log p ^ (-c)) ^ 4

theorem main : H1 → H2 → type_of% @Erdos3.erdos_3.variants.green_tao := by
  classical
  rintro ⟨C, B, hC, hB, recurrence⟩ errors
  obtain ⟨c, K, hc, hK, hEventually⟩ := errors C B hC hB
  obtain ⟨M, hM⟩ := eventually_atTop.mp hEventually
  refine ⟨c, hc, Asymptotics.isBigO_iff.mpr ⟨4 * K, ?_⟩⟩
  filter_upwards [eventually_ge_atTop (max 2 M)] with N hN
  have hN₂ : 2 ≤ N := (le_max_left 2 M).trans hN
  obtain ⟨p, hp, hpLower, hpUpper⟩ := Nat.bertrand (2 * N) (by omega)
  let _ : Fact p.Prime := ⟨hp⟩
  obtain ⟨ε, hε, hεsmall, herror⟩ := hM p (by omega)
  obtain ⟨S, hS, hfree, hcard⟩ := extremal_witness N
  let A := S.image (Nat.cast : ℕ → ZMod p)
  have hcardA : A.card = Erdos3.r 4 N := by
    rw [← hcard]
    exact Finset.card_image_of_injOn fun a ha b hb hab ↦ natCast_inj_below
      (lt_of_le_of_lt (Finset.mem_Icc.mp (hS ha)).2 (by omega))
      (lt_of_le_of_lt (Finset.mem_Icc.mp (hS hb)).2 (by omega)) hab
  obtain ⟨w, hw, _, hlower, hupper⟩ := recurrence p ε hε hεsmall A
  have hsum :
      (∑ z, if z.1 ∈ A ∧ z.1 + z.2 ∈ A ∧ z.1 + 2 * z.2 ∈ A ∧
        z.1 + 3 * z.2 ∈ A then w z else 0) ≤ ∑ z, if z.2 = 0 then w z else 0 := by
    apply Finset.sum_le_sum
    intro z _
    by_cases hz : z.2 = 0
    · rw [if_pos hz]
      split_ifs <;> first | exact le_rfl | exact hw z
    · rw [if_neg hz, if_neg (no_cyclic_progression hpLower hS hfree hz)]
  have hpReal : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hNp : (N : ℝ) ≤ p := by exact_mod_cast (show N ≤ p by omega)
  have hlog := Real.log_le_log (by positivity : 0 < (N : ℝ)) hNp
  have hlogp := hlogN.trans_le hlog
  have hpow : ((A.card : ℝ) / p) ^ 4 ≤ (K * Real.log p ^ (-c)) ^ 4 :=
    hlower.trans ((add_le_add (le_refl (C * ε)) (hsum.trans hupper)).trans herror)
  have hcardBound : (A.card : ℝ) ≤ K * Real.log p ^ (-c) * p :=
    (div_le_iff₀ hpReal).mp (le_of_pow_le_pow_left₀ (by norm_num) (by positivity) hpow)
  have hlogBound := Real.rpow_le_rpow_of_nonpos hlogN hlog (neg_nonpos.mpr hc.le)
  have hpBound : (p : ℝ) ≤ 4 * (N : ℝ) := by exact_mod_cast (show p ≤ 4 * N by omega)
  simp only [Real.norm_eq_abs]
  rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity), ← hcardA]
  calc
    (A.card : ℝ) ≤ K * Real.log p ^ (-c) * p := hcardBound
    _ ≤ K * Real.log N ^ (-c) * (4 * (N : ℝ)) := by gcongr
    _ = 4 * K * ((N : ℝ) * Real.log N ^ (-c)) := by ring

end OMA.R_Erdos3_erdos_3_variants_green_tao_R1
