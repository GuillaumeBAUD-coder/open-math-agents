import OMAReductions.R_Erdos13_erdos_13_variants_general_R1_H1_R1

-- Reduction Erdos13.erdos_13.variants.general.R1.H1.R1.H3.R1 of step Erdos13.erdos_13.variants.general.R1.H1.R1.H3
-- Credit: @jenil-bodhani

namespace OMA.R_Erdos13_erdos_13_variants_general_R1_H1_R1_H3_R1

open Finset

/-- The general bound above an explicit arity cutoff. -/
def H1 : Prop :=
  ∀ r : ℕ, 2^(2^102 : ℕ) ≤ r → ∃ C : ℝ, ∀ (N : ℕ) (A : Finset ℕ),
    A ⊆ Icc 1 N →
    (∀ a ∈ A, ∀ b : Fin r → ℕ, (∀ i, b i ∈ A) → (∀ i, a < b i) → ¬a ∣ ∑ i, b i) →
    (A.card : ℝ) ≤ (N : ℝ)/((r : ℝ)+1)+C

/-- The sparse case at the remaining finitely many arities. -/
def H2 : Prop :=
  ∀ r : ℕ, 3 ≤ r → r < 2^(2^102 : ℕ) → ∃ K : ℕ, ∀ (m : ℕ) (A : Finset ℕ),
    A ⊆ Icc 1 ((r+1)*m) → m+K < A.card →
    (∀ j < m, m-j < (A.filter fun a => (r+1)*j < a).card) →
    2*(Ioc (r*m) ((r+1)*m) ∩ A).card ≤ m →
    (r+1)*(Ioc (r*m) ((r+1)*m) ∩ A).card ≤ 2*m →
    m < (24*r*r*(r+1)+1)*(A.filter (fun a => r*a < (r+1)*m)).card →
    m < (3*r+4)*(A.filter (fun a => 3 ∣ a)).card →
    m < (r+2)*(A.filter (fun a => 2 ∣ a)).card →
    ∃ a ∈ A, ∃ b : Fin r → ℕ, (∀ i, b i ∈ A ∧ a < b i) ∧ a ∣ ∑ i, b i

theorem main : H1 → H2 → OMA.R_Erdos13_erdos_13_variants_general_R1_H1_R1.H3 := by
  intro large small r hr
  by_cases big : 2^(2^102 : ℕ) ≤ r
  · obtain ⟨C,bound⟩ := large r big
    refine ⟨⌈C⌉₊,?_⟩
    intro m A sub excess _ _ _ _ _ _
    by_contra no
    have free (a) (ha : a∈A) (b : Fin r → ℕ) (hb : ∀ i,b i∈A) (hlt : ∀ i,a<b i)
        (dv : a ∣ ∑ i,b i) : False := no ⟨a,ha,b,fun i => ⟨hb i,hlt i⟩,dv⟩
    have h := bound ((r+1)*m) A sub free
    push_cast at h
    have rp : (r:ℝ)+1 ≠ 0 := by positivity
    rw [mul_div_cancel_left₀ _ rp] at h
    have less : (m:ℝ)+(⌈C⌉₊:ℕ)<(A.card:ℝ) := by exact_mod_cast excess
    linarith only [h,less,Nat.le_ceil C]
  · exact small r hr (lt_of_not_ge big)

end OMA.R_Erdos13_erdos_13_variants_general_R1_H1_R1_H3_R1
