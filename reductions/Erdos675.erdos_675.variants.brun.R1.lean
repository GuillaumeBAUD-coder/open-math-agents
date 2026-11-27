import FormalConjectures.ErdosProblems.«675»

/-!
# A lower sieve bound and a large-modulus estimate for the translation property

For offsets in `[1,N]`, a modulus `b > N` coprime to the dilation `M`
forbids exactly one distinct residue class per offset. The first hypothesis is
a lower bound for the count retaining the small moduli. The second controls
the number of those shifts spoiled by larger moduli along an unbounded sequence.

Erdős cites Brun's method in item 5 of Some unconventional problems in number
theory (1979), https://www.renyi.hu/~p_erdos/1979-22.pdf.
-/

namespace OMA.R_Erdos675_erdos_675_variants_brun_R1

open Asymptotics Filter Finset

open scoped Classical in
/-- A lower sieve bound up to a fixed power of the trial length. -/
def H1 : Prop :=
  ∀ (B : Set ℕ) (A : Finset ℕ) (N M : ℕ),
    B.Pairwise Nat.Coprime →
    A ⊆ Icc 1 N →
    0 < M →
    (∀ b ∈ B, N < b → Nat.Coprime M b) →
    ∃ D : ℕ, 2 ≤ D ∧ ∃ c : ℝ, 0 < c ∧ ∀ᶠ x : ℕ in atTop,
      let y := ⌊(x : ℝ) ^ ((D : ℝ)⁻¹)⌋₊
      let T := (Icc 1 x).filter fun k =>
        ∀ b ∈ B, N < b → b ≤ y → ∀ a ∈ A, ¬b ∣ a + M * k
      let V := ∏ b ∈ Ioc N y with b ∈ B, (1 - (A.card : ℝ) / (b : ℝ))
      c * x * V ≤ (T.card : ℝ)

open scoped Classical in
/-- A large-modulus estimate on arbitrarily long intervals with small reciprocal mass.
One approach is to select record lows of the reciprocal sum at a double exponential scale
minus a small linear term. This bounds the loss of sieve density when the cutoff for a
progression of step `b` decreases from `y` to a fixed power of `x / b`.
Near `b = x`, the estimate for the count of moduli follows by mapping each modulus
to its distinct least prime divisor. -/
def H2 : Prop :=
  ∀ (B : Set ℕ) (A : Finset ℕ) (N M D : ℕ) (c : ℝ),
    B.Pairwise Nat.Coprime →
    A ⊆ Icc 1 N →
    0 < M →
    (∀ b ∈ B, N < b → Nat.Coprime M b) →
    2 ≤ D → 0 < c →
    ((fun x : ℕ ↦ ∑ b ∈ range x with b ∈ B, (1 : ℝ) / (b : ℝ)) =o[atTop]
      fun x : ℕ ↦ Real.log (Real.log (x : ℝ))) →
    ∃ᶠ x : ℕ in atTop,
      let y := ⌊(x : ℝ) ^ ((D : ℝ)⁻¹)⌋₊
      let T := (Icc 1 x).filter fun k =>
        ∀ b ∈ B, N < b → b ≤ y → ∀ a ∈ A, ¬b ∣ a + M * k
      let U := T.filter fun k => ∃ b ∈ B, N < b ∧ y < b ∧ ∃ a ∈ A, b ∣ a + M * k
      let V := ∏ b ∈ Ioc N y with b ∈ B, (1 - (A.card : ℝ) / (b : ℝ))
      (U.card : ℝ) < c * x * V

theorem main : H1 → H2 → type_of% @Erdos675.erdos_675.variants.brun := by
  classical
  intro lower upper B hB hsum n
  let small := (Icc 1 n).filter (· ∈ B)
  let M := ∏ b ∈ small, b
  let A := (Icc 1 n).filter fun a => ∀ b ∈ B, ¬b ∣ a
  have hA : A ⊆ Icc 1 n := filter_subset _ _
  have hM : 0 < M := prod_pos fun b hb => (mem_Icc.mp (mem_filter.mp hb).1).1
  have hcop : ∀ b ∈ B, n < b → Nat.Coprime M b := by
    intro b hb hbn
    apply Nat.coprime_prod_left_iff.mpr
    intro d hd
    obtain ⟨hdn, hdB⟩ := mem_filter.mp hd
    exact hB hdB hb (by have := (mem_Icc.mp hdn).2; omega)
  obtain ⟨D, hD, c, hc, hlower⟩ := lower B A n M hB hA hM hcop
  have hupper := upper B A n M D c hB hA hM hcop hD hc hsum
  obtain ⟨x, hl, hu⟩ := (hlower.and_frequently hupper).exists
  let y := ⌊(x : ℝ) ^ ((D : ℝ)⁻¹)⌋₊
  let T := (Icc 1 x).filter fun k =>
    ∀ b ∈ B, n < b → b ≤ y → ∀ a ∈ A, ¬b ∣ a + M * k
  let U := T.filter fun k => ∃ b ∈ B, n < b ∧ y < b ∧ ∃ a ∈ A, b ∣ a + M * k
  let V := ∏ b ∈ Ioc n y with b ∈ B, (1 - (A.card : ℝ) / (b : ℝ))
  change c * x * V ≤ (T.card : ℝ) at hl
  change (U.card : ℝ) < c * x * V at hu
  have hcard : U.card < T.card := by exact_mod_cast hu.trans_le hl
  obtain ⟨k, hkT, hkU⟩ := exists_mem_notMem_of_card_lt_card hcard
  obtain ⟨hk, hsmall⟩ := mem_filter.mp hkT
  have hpos : 0 < k := (mem_Icc.mp hk).1
  have hdvd {b : ℕ} (hb : b ∈ B) (hb1 : 1 ≤ b) (hbn : b ≤ n) : b ∣ M * k :=
    (dvd_prod_of_mem id (s := small) (mem_filter.mpr ⟨mem_Icc.mpr ⟨hb1, hbn⟩, hb⟩)).trans
      (Nat.dvd_mul_right M k)
  refine ⟨M * k, Nat.mul_pos hM hpos, fun a ha han => ⟨?_, ?_⟩⟩
  · intro h
    have haA : a ∈ A := mem_filter.mpr ⟨mem_Icc.mpr ⟨ha, han⟩, h⟩
    intro b hb hba
    by_cases hb0 : b = 0
    · subst b
      simp only [zero_dvd_iff] at hba
      omega
    by_cases hbn : b ≤ n
    · exact h b hb ((Nat.dvd_add_iff_left (hdvd hb (by omega) hbn)).mpr hba)
    by_cases hby : b ≤ y
    · exact hsmall b hb (by omega) hby a haA hba
    · exact hkU (mem_filter.mpr ⟨hkT, b, hb, by omega, by omega, a, haA, hba⟩)
  · intro h b hb hba
    have hb1 : 1 ≤ b := by
      by_contra! hh
      have : b = 0 := by omega
      simp [this] at hba
      omega
    have hbn := (Nat.le_of_dvd ha hba).trans han
    exact h b hb (dvd_add hba (hdvd hb hb1 hbn))

end OMA.R_Erdos675_erdos_675_variants_brun_R1
