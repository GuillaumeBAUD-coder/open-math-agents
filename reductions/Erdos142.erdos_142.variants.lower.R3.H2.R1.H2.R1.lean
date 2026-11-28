import OMAReductions.R_Erdos142_erdos_142_variants_lower_R3_H2_R1
import Mathlib

/-! Split sparse descent into production of a scored polynomial patch and its reset on an interval. The patch is represented by weighted triangular polynomials and a supported Lipschitz function. Based on OpenAI Progressions, 3344da59991e. Thomas Fredrickson with Codex. -/

namespace OMA.R_Erdos142_erdos_142_variants_lower_R3_H2_R1_H2_R1
open Real Filter MvPolynomial
open scoped BigOperators NNReal

/-- Existence of a correlated patch with quantitative rank and length bounds. -/
def H1 : Prop :=
  ∀ k : ℕ, 4 ≤ k → 
  let patch := (fun (d : ℕ) (U : ℝ) (g : ℕ → ℝ) =>
    ∃ (w : Fin d → ℕ) (P : (i : Fin d) → MvPolynomial (Unit ⊕ Fin i.val) ℝ)
      (φ : (Fin d → ℝ) → ℝ) (L : ℝ≥0), Monotone w ∧ (∀ i, 1 ≤ w i ∧ w i ≤ k-2) ∧
      (∀ i, P i ∈ restrictSupport ℝ {m | Finsupp.weight
        (Sum.elim (fun _ => 1) (fun j : Fin i.val => w (j.castLE i.isLt.le))) m ≤ w i}) ∧
      (∀ x, 0 ≤ φ x ∧ φ x ≤ 1) ∧ (∀ x, φ x ≠ 0 → ∀ i, |x i| ≤ 1/4) ∧
      LipschitzWith L φ ∧ (L : ℝ)+1 ≤ exp U ∧ ∀ t, g t = ∑' z : Fin d → ℤ,
        φ (fun i => (z i : ℝ) - aeval
          (Sum.elim (fun _ => (t : ℝ)) (fun j : Fin i.val => (z (j.castLE i.isLt.le) : ℝ))) (P i)))
  ∃ A K B D T : ℝ, 1 < A ∧ 2 ≤ K ∧ 0 < B ∧ 0 < D ∧
  ∀ (N : ℕ) (S : Finset ℕ), 
  let α := (S.card : ℝ) / N
  let p := max 2 (log (2*N/(S.card : ℝ)))
  let t := 1/(4*log K)
  let β := 1-t*log 2/2
  1 < N → S.Nonempty → S ⊆ Finset.Icc 1 N →
  (¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a+i*d ∈ S) → T < p →
  p^β + log 2 ≤ log (log N) → ∃ (d M a q : ℕ) (U : ℝ) (g : ℕ → ℝ), patch d U g ∧ 0 < q ∧
    (∀ i < M, a+q*i < N) ∧ 1 ≤ U ∧ log N-U ≤ log M ∧
    log (d+1 : ℝ) ≤ B*log (2+p) ∧ log U ≤ D*p^(1/4 : ℝ)*log (2+p) ∧
    exp (-U) ≤ 𝔼 i : Fin M, ((if a+q*i.val+1 ∈ S then 1 else 0) -
      A^(2^⌊t*log p⌋₊)/2*α) * g i.val

/-- A single scored patch yields a denser progression-free interval and retains the power reserve. -/
def H2 : Prop :=
  ∀ k : ℕ, 4 ≤ k → 
  let patch := (fun (d : ℕ) (U : ℝ) (g : ℕ → ℝ) =>
    ∃ (w : Fin d → ℕ) (P : (i : Fin d) → MvPolynomial (Unit ⊕ Fin i.val) ℝ)
      (φ : (Fin d → ℝ) → ℝ) (L : ℝ≥0), Monotone w ∧ (∀ i, 1 ≤ w i ∧ w i ≤ k-2) ∧
      (∀ i, P i ∈ restrictSupport ℝ {m | Finsupp.weight
        (Sum.elim (fun _ => 1) (fun j : Fin i.val => w (j.castLE i.isLt.le))) m ≤ w i}) ∧
      (∀ x, 0 ≤ φ x ∧ φ x ≤ 1) ∧ (∀ x, φ x ≠ 0 → ∀ i, |x i| ≤ 1/4) ∧
      LipschitzWith L φ ∧ (L : ℝ)+1 ≤ exp U ∧ ∀ t, g t = ∑' z : Fin d → ℤ,
        φ (fun i => (z i : ℝ) - aeval
          (Sum.elim (fun _ => (t : ℝ)) (fun j : Fin i.val => (z (j.castLE i.isLt.le) : ℝ))) (P i)))
  ∀ A K B D : ℝ, 1 < A → 2 ≤ K → 0 < B → 0 < D →
  ∃ T Cmin : ℝ, ∀ (N : ℕ) (S : Finset ℕ), 
  let α := (S.card : ℝ) / N
  let p := max 2 (log (2*N/(S.card : ℝ)))
  let t := 1/(4*log K)
  let β := 1-t*log 2/2
  1 < N → S.Nonempty → S ⊆ Finset.Icc 1 N →
  (¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a+i*d ∈ S) → T < p →
  ∀ C ≥ Cmin, p^β+C ≤ log (log N) → (∃ (d M a q : ℕ) (U : ℝ) (g : ℕ → ℝ), patch d U g ∧ 0 < q ∧
    (∀ i < M, a+q*i < N) ∧ 1 ≤ U ∧ log N-U ≤ log M ∧
    log (d+1 : ℝ) ≤ B*log (2+p) ∧ log U ≤ D*p^(1/4 : ℝ)*log (2+p) ∧
    exp (-U) ≤ 𝔼 i : Fin M, ((if a+q*i.val+1 ∈ S then 1 else 0) -
      A^(2^⌊t*log p⌋₊)/2*α) * g i.val) →
  ∃ (M : ℕ) (V : Finset ℕ), 1 < M ∧ V.Nonempty ∧ V ⊆ Finset.Icc 1 M ∧
    (¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a+i*d ∈ V) ∧
    let p' := max 2 (log (2*M/(V.card : ℝ)))
    p'+1 ≤ p ∧ p'^β+C ≤ log (log M)

lemma power_reserve {β : ℝ} (hb : 0 ≤ β) (hlt : β < 1) :
    ∃ D : ℝ, ∀ x ≥ 2, 0 ≤ x^β ∧ x^β ≤ x/2+D := by
  have ht := (tendsto_rpow_neg_atTop (sub_pos.mpr hlt)).eventually
    (gt_mem_nhds (show (0:ℝ) < 1/2 by norm_num))
  obtain ⟨L,hL⟩ := eventually_atTop.mp ht
  let B := max 2 L
  have hB : 0 ≤ B := by dsimp [B]; linarith [le_max_left (2:ℝ) L]
  refine ⟨B^β, fun x hx => ⟨rpow_nonneg (by linarith) _, ?_⟩⟩
  by_cases h : x ≤ B
  · linarith only [rpow_le_rpow (by linarith : 0 ≤ x) h hb, hx]
  · have hsmall := hL x ((le_max_right 2 L).trans (le_of_not_ge h))
    have hpos : 0 < x := by linarith
    have he : x ^ (-(1-β)) * x = x^β := by
      conv_lhs => rhs; rw [← rpow_one x]
      rw [← rpow_add hpos]; congr 1; ring
    have := mul_le_mul_of_nonneg_right hsmall.le hpos.le
    rw [he] at this
    linarith only [this, rpow_nonneg hB β]


theorem main : H1 → H2 → OMA.R_Erdos142_erdos_142_variants_lower_R3_H2_R1.H2 := by
  intro hsource hreset k hk
  obtain ⟨A,K,B,D,Ts,hA,hK,hB,hD,source⟩ := hsource k hk
  obtain ⟨Tr,Cr,reset⟩ := hreset k hk A K B D hA hK hB hD
  let β := 1 - 1/(4*log K)*log 2/2
  have hl : 0 < log 2 := log_pos (by norm_num)
  have hKlog : log 2 ≤ log K := log_le_log (by norm_num) hK
  have hKpos : 0 < log K := hl.trans_le hKlog
  have hfrac : 0 < 1/(4*log K)*log 2 := by positivity
  have hupper : 1/(4*log K)*log 2 ≤ 1 := by
    rw [one_div, inv_mul_eq_div]
    exact (div_le_one (by positivity)).mpr (by linarith)
  have hb : 0 ≤ β := by dsimp [β]; linarith
  have hlt : β < 1 := by dsimp [β]; linarith
  obtain ⟨D',hF⟩ := power_reserve hb hlt
  refine ⟨(· ^ β),max Ts Tr,D',max Cr (log 2),hF,?_⟩
  intro p valid C hC N S hv hp hinv
  obtain ⟨hN,hne,hsub,hfree⟩ := hv
  have hseed := source N S hN hne hsub hfree ((le_max_left _ _).trans_lt hp)
    (le_trans (add_le_add_right ((le_max_right _ _).trans hC) _) hinv)
  obtain ⟨M,V,hM,hnV,hsV,hfV,hgain,hnext⟩ :=
    reset N S hN hne hsub hfree ((le_max_right _ _).trans_lt hp) C
      ((le_max_left _ _).trans hC) hinv hseed
  exact ⟨M,V,⟨hM,hnV,hsV,hfV⟩,hnext,hgain⟩

end OMA.R_Erdos142_erdos_142_variants_lower_R3_H2_R1_H2_R1
