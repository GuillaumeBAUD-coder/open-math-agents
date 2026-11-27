import FormalConjectures.ErdosProblems.«59»

-- Credit: @marcusbuffett
-- Use sparse containers for copies of the forbidden graph and supersaturation.
-- The complete bipartite lower bound absorbs both quadratic error terms.
open Filter SimpleGraph
open scoped Classical

namespace OMA.R_Erdos59_erdos_59_variants_erdos_frankl_rodl_R1

private lemma count_cover {k n : ℕ} (H : SimpleGraph (Fin k))
    (C : Finset (SimpleGraph (Fin n)))
    (hc : ∀ G : SimpleGraph (Fin n), H.Free G → ∃ T ∈ C, G ≤ T) :
    Erdos59.numFree H n ≤ ∑ T ∈ C, 2 ^ T.edgeFinset.card := by
  classical
  let S : Set (SimpleGraph (Fin n)) := {G | H.Free G}
  change S.ncard ≤ _
  rw [Set.ncard_eq_toFinset_card']
  calc
    S.toFinset.card ≤ (C.biUnion fun T => T.edgeFinset.powerset).card := by
      apply Finset.card_le_card_of_injOn (fun G : SimpleGraph (Fin n) => G.edgeFinset)
      · intro G hG
        obtain ⟨T, hT, hl⟩ := hc G (Set.mem_toFinset.mp hG)
        exact Finset.mem_biUnion.mpr ⟨T, hT, Finset.mem_powerset.mpr (edgeFinset_mono hl)⟩
      · intro G _ G' _ h
        exact edgeFinset_inj.mp h
    _ ≤ _ := by simpa using Finset.card_biUnion_le (s := C) (t := fun T => T.edgeFinset.powerset)

def H1 : Prop :=
  ∀ {k : ℕ} (H : SimpleGraph (Fin k)), ¬ H.IsBipartite →
    ∀ δ > (0 : ℝ), ∀ γ > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
    ∃ C : Finset (SimpleGraph (Fin n)),
      (C.card : ℝ) ≤ (2 : ℝ) ^ (δ * (n : ℝ)^2) ∧
      (∀ T ∈ C, (T.copyCount H : ℝ) ≤ γ * (n : ℝ)^k) ∧
      ∀ G : SimpleGraph (Fin n), H.Free G → ∃ T ∈ C, G ≤ T

def H2 : Prop :=
  ∀ {k : ℕ} (H : SimpleGraph (Fin k)), ¬ H.IsBipartite →
    ∀ δ > (0 : ℝ), ∃ γ > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
    ∀ T : SimpleGraph (Fin n), (T.copyCount H : ℝ) ≤ γ * (n : ℝ)^k →
      (T.edgeFinset.card : ℝ) ≤ extremalNumber n H + δ * (n : ℝ)^2

def H3 : Prop :=
  ∀ {k : ℕ} (H : SimpleGraph (Fin k)), ¬ H.IsBipartite →
    ∀ᶠ n : ℕ in atTop, (n : ℝ)^2 ≤ 8 * extremalNumber n H

theorem main : H1 → H2 → H3 → type_of% @Erdos59.erdos_59.variants.erdos_frankl_rodl := by
  classical
  intro hc hs hd k H hH ε hε
  let δ := ε / 16
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨γ, hγ, hsup⟩ := hs H hH δ hδ
  filter_upwards [hc H hH δ hδ γ hγ, hsup, hd H hH] with n hn hn' hn''
  obtain ⟨C, hcard, hfew, hcover⟩ := hn
  let M : ℝ := extremalNumber n H + δ * (n : ℝ)^2
  have hpow (T : SimpleGraph (Fin n)) (hT : T ∈ C) :
      (2 : ℝ)^T.edgeFinset.card ≤ (2 : ℝ)^M := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (hn' T (hfew T hT))
  calc
    (Erdos59.numFree H n : ℝ) ≤ ∑ T ∈ C, (2 : ℝ)^T.edgeFinset.card := by
      exact_mod_cast count_cover H C hcover
    _ ≤ ∑ _T ∈ C, (2 : ℝ)^M := Finset.sum_le_sum hpow
    _ = C.card * (2 : ℝ)^M := by simp
    _ ≤ (2 : ℝ)^(δ * (n : ℝ)^2) * (2 : ℝ)^M := by gcongr
    _ = (2 : ℝ)^(δ * (n : ℝ)^2 + M) := (Real.rpow_add (by norm_num) _ _).symm
    _ ≤ _ := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      dsimp [M, δ]
      nlinarith [mul_le_mul_of_nonneg_left hn'' hε.le]

end OMA.R_Erdos59_erdos_59_variants_erdos_frankl_rodl_R1

