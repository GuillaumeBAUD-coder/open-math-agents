import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R1_H1_R1
import Mathlib

/-! Affine density increment for the pointwise bound of Erdős 142.
Thomas Fredrickson (@thomasfredrickson) with Codex. The source and reset
estimates follow OpenAI Progressions at 3344da59991e. The target is the
affine step of Nicholas Wierenga, used in mijuny's pointwise reduction.
The second child retains the actual arithmetic progression and identifies
its reindexed subset of [1,M]. -/

namespace OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R1_H1_R1_H1_R1
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

/-- A single scored patch yields an affine restriction with increased density and sufficient length. -/
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
  ∃ a q M : ℕ, 0 < q ∧ 2 ≤ M ∧
    (∀ i ∈ Finset.Icc 1 M, a+(i-1)*q ∈ Finset.Icc 1 N) ∧
    let V := (Finset.Icc 1 M).filter (fun i => a+(i-1)*q ∈ S)
    let p' := max 2 (log (2*M/(V.card : ℝ)))
    0 < V.card ∧ p'+1 ≤ p ∧ p'^β+C ≤ log (log M)

theorem main : H1 → H2 → OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R1_H1_R1.H1 := by
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
  have hb : 0 < β := by dsimp [β]; linarith
  have hlt : β < 1 := by dsimp [β]; linarith
  refine ⟨β,1,max Ts Tr,max Cr (log 2),hb,hlt,by norm_num,?_⟩
  intro C hC N S hN hs hnon hf p hp hinv
  have hi : p^β+C ≤ log (log N) := by simpa only [one_mul] using hinv
  have cert := source N S hN (Finset.card_pos.mp hnon) hs hf
    ((le_max_left _ _).trans_lt hp)
    ((add_le_add_right ((le_max_right _ _).trans hC) _).trans hi)
  obtain ⟨a,q,m,hq,hm,hinside,hn,hgain,hnext⟩ :=
    reset N S hN (Finset.card_pos.mp hnon) hs hf ((le_max_right _ _).trans_lt hp)
      C ((le_max_left _ _).trans hC) hi cert
  exact ⟨a,q,m,hq,hm,hinside,hn,hgain,by simpa only [one_mul] using hnext⟩

end OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R1_H1_R1_H1_R1
