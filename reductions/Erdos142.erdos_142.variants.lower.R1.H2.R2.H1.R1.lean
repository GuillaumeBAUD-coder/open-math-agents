import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R2

/-!
# Monochromatic progressions from the quantitative density bound

The target is the van der Waerden statement with (ceil(log N) + 1)^4 colours for every
progression length at least four. It is reduced to two statements.

H1 is the quantitative density bound for sets without long progressions, in the form proved
formally in OpenAI, Quasipolynomial Bounds for Arithmetic Progressions (2026). It is word for
word the hypothesis H1 of reduction R1 of the step lower.R2.H1.R1.H2 (pull request 29901), so a
single proof of that bound closes both branches.

H2 is elementary real analysis: the saving exp(-c (log log N)^(1+eta)) eventually beats the
number of colours.

The theorem main is the pigeonhole principle over the colour classes: each class in [1,N]
has no progression, the classes partition [1,N], and their number times the density bound is
eventually less than N.
-/

namespace OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R2_H1_R1

open Filter

/-- Sets in [1,N] without k-term progressions of positive step have density at most
C exp(-c (log log N)^(1+eta)), for every length at least four. -/
def H1 : Prop :=
  ∀ k : ℕ, 4 ≤ k → ∃ C c η : ℝ, 0 < C ∧ 0 < c ∧ 0 < η ∧
    ∀ (N : ℕ) (S : Finset ℕ), 3 ≤ N → S ⊆ Finset.Icc 1 N →
      (¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ S) →
      (S.card : ℝ) ≤ C * N * Real.exp (-c * (Real.log (Real.log N)) ^ (1 + η))

/-- The saving eventually beats the fourth power of the logarithm. -/
def H2 : Prop :=
  ∀ C c η : ℝ, 0 < C → 0 < c → 0 < η → ∀ᶠ N : ℕ in atTop,
    C * (((⌈Real.log (N : ℝ)⌉₊ + 1) ^ 4 : ℕ) : ℝ) *
      Real.exp (-c * (Real.log (Real.log (N : ℝ))) ^ (1 + η)) < 1

/-- Pigeonhole: if every progression-free subset of [1,N] has at most B elements and
m * B < N, then every colouring with m colours has a monochromatic progression in [1,N]. -/
lemma mono_of_card_bound {k N m : ℕ} {B : ℝ} (hk : 1 ≤ k)
    (hB : ∀ S : Finset ℕ, S ⊆ Finset.Icc 1 N →
      (¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ S) → (S.card : ℝ) ≤ B)
    (hm : (m : ℝ) * B < N) (c : ℕ → Fin m) :
    ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ Finset.Icc 1 N ∧ c (a + i * d) = c a := by
  by_contra hno
  have hcls : ∀ t : Fin m, (((Finset.Icc 1 N).filter (fun x => c x = t)).card : ℝ) ≤ B := by
    intro t
    refine hB _ (Finset.filter_subset _ _) ?_
    rintro ⟨a, d, hd, h⟩
    refine hno ⟨a, d, hd, fun i hi => ?_⟩
    have h0 := h 0 (by omega)
    have hi' := h i hi
    simp only [Finset.mem_filter, zero_mul, add_zero] at h0 hi'
    exact ⟨hi'.1, hi'.2.trans h0.2.symm⟩
  have hsum : ((Finset.Icc 1 N).card : ℝ) =
      ∑ t : Fin m, (((Finset.Icc 1 N).filter (fun x => c x = t)).card : ℝ) := by
    have := Finset.card_eq_sum_card_fiberwise (s := Finset.Icc 1 N) (t := Finset.univ)
      (f := c) (fun x _ => Finset.mem_univ _)
    exact_mod_cast this
  have hle : ((Finset.Icc 1 N).card : ℝ) ≤ (m : ℝ) * B := by
    rw [hsum]
    calc ∑ t : Fin m, (((Finset.Icc 1 N).filter (fun x => c x = t)).card : ℝ)
        ≤ ∑ _t : Fin m, B := Finset.sum_le_sum (fun t _ => hcls t)
      _ = (m : ℝ) * B := by simp
  rw [Nat.card_Icc, Nat.add_sub_cancel] at hle
  linarith

theorem main : H1 → H2 → OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R2.H1 := by
  intro h1 h2 k hk
  obtain ⟨C, c, η, hC, hc, hη, hb⟩ := h1 k hk
  filter_upwards [h2 C c η hC hc hη, eventually_ge_atTop 3] with N hN hN3 col
  refine mono_of_card_bound (by omega) (fun S hS hfree => hb N S hN3 hS hfree) ?_ col
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have := mul_lt_mul_of_pos_right hN hNpos
  nlinarith [this]

end OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R2_H1_R1
