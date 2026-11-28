import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R1_H1_R1_H1_R2
import Mathlib

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Greedy covering by averaging: the |U||S| pairs in U x S spread over 2N shifts, so some shift
-- covers |U||S|/(2N) of the uncovered set U; after q steps at most N (1 - |S|/(2N))^q
-- <= N exp(-q|S|/(2N)) < 1 points remain, so the q shifts cover [1, N].

namespace OMA.SolCover

lemma cover_avg (N : ℕ) (S U : Finset ℕ) (hN : 0 < N) (hS : S ⊆ Finset.Icc 1 N)
    (hU : U ⊆ Finset.Icc 1 N) :
    ∃ s, U.card * S.card ≤ (U.filter (fun x => ∃ b ∈ S, x + N = s + b)).card * (2 * N) := by
  have key : ∀ x ∈ U, S.card ≤
      ((Finset.range (2 * N)).filter (fun s => ∃ b ∈ S, x + N = s + b)).card := by
    intro x hx
    have hx' := Finset.mem_Icc.mp (hU hx)
    apply Finset.card_le_card_of_injOn (fun b => x + N - b)
    · intro b hb
      have hb2 : b ∈ S := by simpa using hb
      have hb' := Finset.mem_Icc.mp (hS hb2)
      simp only [Finset.coe_filter, Finset.mem_coe, Finset.mem_filter, Finset.mem_range,
        Set.mem_setOf_eq]
      exact ⟨by omega, b, hb2, by omega⟩
    · intro b1 hb1 b2 hb2 h
      have h1 := Finset.mem_Icc.mp (hS (by simpa using hb1))
      have h2 := Finset.mem_Icc.mp (hS (by simpa using hb2))
      simp only at h
      omega
  have h1 := Finset.sum_le_sum key
  have h2 : ∑ x ∈ U, ((Finset.range (2 * N)).filter (fun s => ∃ b ∈ S, x + N = s + b)).card
      = ∑ s ∈ Finset.range (2 * N), (U.filter (fun x => ∃ b ∈ S, x + N = s + b)).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have h3 : ∑ _s ∈ Finset.range (2 * N), U.card * S.card ≤
      ∑ s ∈ Finset.range (2 * N), (U.filter (fun x => ∃ b ∈ S, x + N = s + b)).card * (2 * N) := by
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul, ← Finset.sum_mul, ← h2]
    rw [Finset.sum_const, smul_eq_mul] at h1
    calc 2 * N * (U.card * S.card) = (U.card * S.card) * (2 * N) := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ h1
  obtain ⟨s, -, hs⟩ := Finset.exists_le_of_sum_le
    (Finset.nonempty_range_iff.mpr (by omega)) h3
  exact ⟨s, hs⟩

theorem cover_H2 : ∀ (N q : ℕ) (S : Finset ℕ), 0 < N → 0 < q → S ⊆ Finset.Icc 1 N →
    2 * (N : ℝ) * Real.log (N : ℝ) < (q : ℝ) * (S.card : ℝ) →
    ∃ shifts : Fin q → ℕ, ∀ x ∈ Finset.Icc 1 N,
      ∃ t : Fin q, ∃ b ∈ S, x + N = shifts t + b := by
  intro N q S hN hq hS hlog
  have hmN : S.card ≤ N := by
    have := Finset.card_le_card hS
    simpa using this
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hmNr : (S.card : ℝ) ≤ N := by exact_mod_cast hmN
  set c : ℝ := (S.card : ℝ) / (2 * N) with hcdef
  have hc1 : c ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
  have hc0 : 0 ≤ c := by positivity
  have iter : ∀ t : ℕ, ∃ f : ℕ → ℕ,
      ((((Finset.Icc 1 N).filter
        (fun x => ∀ i < t, ¬ ∃ b ∈ S, x + N = f i + b)).card : ℕ) : ℝ) ≤ N * (1 - c) ^ t := by
    intro t
    induction t with
    | zero => exact ⟨fun _ => 0, by simp⟩
    | succ t ih =>
      obtain ⟨f, hf⟩ := ih
      set U := (Finset.Icc 1 N).filter (fun x => ∀ i < t, ¬ ∃ b ∈ S, x + N = f i + b)
        with hU
      obtain ⟨s, hs⟩ := cover_avg N S U hN hS (Finset.filter_subset _ _)
      refine ⟨fun i => if i = t then s else f i, ?_⟩
      refine le_trans (Nat.cast_le.mpr (Finset.card_le_card
        (t := U.filter (fun x => ¬ ∃ b ∈ S, x + N = s + b)) ?_)) ?_
      · intro x hx
        simp only [hU, Finset.mem_filter] at hx ⊢
        refine ⟨⟨hx.1, fun i hi => ?_⟩, ?_⟩
        · have h := hx.2 i (by omega)
          rwa [if_neg (by omega)] at h
        · have h := hx.2 t (by omega)
          rwa [if_pos rfl] at h
      · have hcard := Finset.card_filter_add_card_filter_not (s := U)
          (fun x => ∃ b ∈ S, x + N = s + b)
        have hs' : (U.card : ℝ) * S.card ≤
            (U.filter (fun x => ∃ b ∈ S, x + N = s + b)).card * (2 * N) := by
          exact_mod_cast hs
        have hcr : ((U.filter (fun x => ∃ b ∈ S, x + N = s + b)).card : ℝ) +
            (U.filter (fun x => ¬ ∃ b ∈ S, x + N = s + b)).card = U.card := by
          exact_mod_cast hcard
        have hpc : (U.card : ℝ) * c ≤ (U.filter (fun x => ∃ b ∈ S, x + N = s + b)).card := by
          rw [hcdef, ← mul_div_assoc, div_le_iff₀ (by positivity)]
          exact hs'
        calc ((U.filter (fun x => ¬ ∃ b ∈ S, x + N = s + b)).card : ℝ)
            ≤ U.card * (1 - c) := by linarith
          _ ≤ N * (1 - c) ^ t * (1 - c) := mul_le_mul_of_nonneg_right hf (by linarith)
          _ = N * (1 - c) ^ (t + 1) := by ring
  obtain ⟨f, hf⟩ := iter q
  have hcq : Real.log N < c * q := by
    rw [hcdef, div_mul_eq_mul_div, lt_div_iff₀ (by positivity)]
    linarith
  have hlt : ((((Finset.Icc 1 N).filter
        (fun x => ∀ i < q, ¬ ∃ b ∈ S, x + N = f i + b)).card : ℕ) : ℝ) < 1 := by
    calc _ ≤ N * (1 - c) ^ q := hf
      _ ≤ N * (Real.exp (-c)) ^ q :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith)
            (by linarith [Real.add_one_le_exp (-c)]) q) hNr.le
      _ = N * Real.exp (-(c * q)) := by
          rw [← Real.exp_nat_mul, show ((q:ℝ) * -c) = -(c * q) by ring]
      _ < N * Real.exp (-Real.log N) :=
          mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr (by linarith)) hNr
      _ = 1 := by
          rw [Real.exp_neg, Real.exp_log hNr]
          field_simp
  refine ⟨fun t => f t.val, ?_⟩
  intro x hx
  by_contra hcon
  have hx' : x ∈ (Finset.Icc 1 N).filter
      (fun x => ∀ i < q, ¬ ∃ b ∈ S, x + N = f i + b) := by
    rw [Finset.mem_filter]
    exact ⟨hx, fun i hi hex => hcon ⟨⟨i, hi⟩, hex⟩⟩
  have h1 := Finset.card_pos.mpr ⟨x, hx'⟩
  have h2 : (1:ℝ) ≤ (((Finset.Icc 1 N).filter
      (fun x => ∀ i < q, ¬ ∃ b ∈ S, x + N = f i + b)).card : ℝ) := by
    exact_mod_cast h1
  linarith

end OMA.SolCover

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R1_H1_R1_H1_R2.H2 := by
  unfold OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R1_H1_R1_H1_R2.H2
  exact OMA.SolCover.cover_H2
