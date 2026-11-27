import FormalConjectures.ErdosProblems.«307»
import Mathlib.Tactic

/-!
# Frame-Rule Reduction for Erdos Problem 307 (coprime variant without 1)

Reduction `Erdos307.erdos_307.variants.coprime_one_notMem.R1` by `@nijv`.
Splits the existence of 1-free pairwise-coprime sets `P, Q` whose reciprocal sums multiply to `1`
into three independent components via the bilinear Frame Rule:
- `H1` (rational cofactor-sum & Leibniz insertion law): expresses `∑ a ∈ A, (a : ℚ)⁻¹` over a common
  product denominator `∏ a ∈ A, a` and gives the cofactor-sum recurrence upon inserting a new member.
- `H2` (automatic coprimality of closing quotients): proves that for any mutually coprime base sets
  `P₀, Q₀` of pairwise-coprime integers `≥ 2`, when `Δ = M * N - M' * N' > 0` divides both
  `M * N' + N ^ 2` and `M' * N + M ^ 2` with quotients `p, q ≥ 2`, those quotients are automatically
  outside `P₀, Q₀` and preserve pairwise coprimality on `insert p P₀` and `insert q Q₀`.
- `H3` (pure natural-number Diophantine frame core): existence of mutually coprime nonempty base sets
  `P₀, Q₀` satisfying the integer divisibility conditions `Δ ∣ (M * N' + N ^ 2)` and
  `Δ ∣ (M' * N + M ^ 2)` with `2 * Δ ≤ M * N' + N ^ 2` and `2 * Δ ≤ M' * N + M ^ 2`
  (necessary and sufficient: erasing any `p ∈ P, q ∈ Q` from a solution recovers `(P₀, Q₀)`).
-/

namespace OMA.R_Erdos307_erdos_307_variants_coprime_one_notMem_R1

open Finset

-- H1: Clearing denominators expresses the rational reciprocal sum as cofactor sum over product,
-- and inserting a fresh positive integer updates the cofactor sum linearly.
def H1 : Prop :=
  ∀ (A : Finset ℕ), (∀ a ∈ A, 0 < a) →
    ((∏ a ∈ A, (a : ℚ)) * (∑ a ∈ A, (a : ℚ)⁻¹) =
      ((∑ a ∈ A, (∏ x ∈ A, x) / a : ℕ) : ℚ)) ∧
    ∀ w : ℕ, 0 < w → w ∉ A →
      (∑ a ∈ insert w A, (∏ x ∈ insert w A, x) / a) =
        w * (∑ a ∈ A, (∏ x ∈ A, x) / a) + ∏ x ∈ A, x

-- H2: Any integer closing quotients p, q >= 2 produced by the Frame Rule automatically avoid P0, Q0
-- and preserve pairwise coprimality on insert p P0 and insert q Q0 without extra gcd hypotheses.
def H2 : Prop :=
  ∀ (P₀ Q₀ : Finset ℕ),
    P₀.Nonempty → Q₀.Nonempty →
    (∀ a ∈ P₀, 2 ≤ a) → (∀ b ∈ Q₀, 2 ≤ b) →
    Set.Pairwise (P₀ : Set ℕ) Nat.Coprime →
    Set.Pairwise (Q₀ : Set ℕ) Nat.Coprime →
    (∀ a ∈ P₀, ∀ b ∈ Q₀, Nat.Coprime a b) →
    let M := ∏ a ∈ P₀, a
    let M' := ∑ a ∈ P₀, M / a
    let N := ∏ b ∈ Q₀, b
    let N' := ∑ b ∈ Q₀, N / b
    M' * N' < M * N →
    2 * (M * N - M' * N') ≤ M * N' + N ^ 2 →
    2 * (M * N - M' * N') ≤ M' * N + M ^ 2 →
    (M * N - M' * N') ∣ (M * N' + N ^ 2) →
    (M * N - M' * N') ∣ (M' * N + M ^ 2) →
    let p := (M * N' + N ^ 2) / (M * N - M' * N')
    let q := (M' * N + M ^ 2) / (M * N - M' * N')
    2 ≤ p ∧ p ∉ P₀ ∧ 2 ≤ q ∧ q ∉ Q₀ ∧
      Set.Pairwise ((insert p P₀ : Finset ℕ) : Set ℕ) Nat.Coprime ∧
      Set.Pairwise ((insert q Q₀ : Finset ℕ) : Set ℕ) Nat.Coprime

-- H3: Lossless pure-integer Diophantine frame existence (equivalent to the full problem by erasing
-- one element from each side of any solution).
def H3 : Prop :=
  ∃ P₀ Q₀ : Finset ℕ,
    P₀.Nonempty ∧ Q₀.Nonempty ∧
    (∀ a ∈ P₀, 2 ≤ a) ∧ (∀ b ∈ Q₀, 2 ≤ b) ∧
    Set.Pairwise (P₀ : Set ℕ) Nat.Coprime ∧
    Set.Pairwise (Q₀ : Set ℕ) Nat.Coprime ∧
    (∀ a ∈ P₀, ∀ b ∈ Q₀, Nat.Coprime a b) ∧
    let M := ∏ a ∈ P₀, a
    let M' := ∑ a ∈ P₀, M / a
    let N := ∏ b ∈ Q₀, b
    let N' := ∑ b ∈ Q₀, N / b
    M' * N' < M * N ∧
    2 * (M * N - M' * N') ≤ M * N' + N ^ 2 ∧
    2 * (M * N - M' * N') ≤ M' * N + M ^ 2 ∧
    (M * N - M' * N') ∣ (M * N' + N ^ 2) ∧
    (M * N - M' * N') ∣ (M' * N + M ^ 2)

lemma frame_cross_eq {M M' N N' Δ p q : ℕ}
    (hlt : M' * N' < M * N)
    (hΔ : Δ = M * N - M' * N')
    (hp : Δ * p = M * N' + N ^ 2)
    (hq : Δ * q = M' * N + M ^ 2) :
    (p * M' + M) = N * q ∧ (q * N' + N) = M * p := by
  have hΔpos : (0 : ℤ) < (Δ : ℤ) := by omega
  have hΔz : (Δ : ℤ) = (M : ℤ) * (N : ℤ) - (M' : ℤ) * (N' : ℤ) := by omega
  have hpz : (Δ : ℤ) * (p : ℤ) = (M : ℤ) * (N' : ℤ) + (N : ℤ) ^ 2 := by exact_mod_cast hp
  have hqz : (Δ : ℤ) * (q : ℤ) = (M' : ℤ) * (N : ℤ) + (M : ℤ) ^ 2 := by exact_mod_cast hq
  have h1z : (Δ : ℤ) * ((p : ℤ) * (M' : ℤ) + (M : ℤ)) = (Δ : ℤ) * ((N : ℤ) * (q : ℤ)) := by
    calc
      (Δ : ℤ) * ((p : ℤ) * (M' : ℤ) + (M : ℤ))
          = ((Δ : ℤ) * (p : ℤ)) * (M' : ℤ) + (Δ : ℤ) * (M : ℤ) := by ring
      _ = ((M : ℤ) * (N' : ℤ) + (N : ℤ) ^ 2) * (M' : ℤ) +
            ((M : ℤ) * (N : ℤ) - (M' : ℤ) * (N' : ℤ)) * (M : ℤ) := by rw [hpz, hΔz]
      _ = (N : ℤ) * ((M' : ℤ) * (N : ℤ) + (M : ℤ) ^ 2) := by ring
      _ = (N : ℤ) * ((Δ : ℤ) * (q : ℤ)) := by rw [← hqz]
      _ = (Δ : ℤ) * ((N : ℤ) * (q : ℤ)) := by ring
  have h2z : (Δ : ℤ) * ((q : ℤ) * (N' : ℤ) + (N : ℤ)) = (Δ : ℤ) * ((M : ℤ) * (p : ℤ)) := by
    calc
      (Δ : ℤ) * ((q : ℤ) * (N' : ℤ) + (N : ℤ))
          = ((Δ : ℤ) * (q : ℤ)) * (N' : ℤ) + (Δ : ℤ) * (N : ℤ) := by ring
      _ = ((M' : ℤ) * (N : ℤ) + (M : ℤ) ^ 2) * (N' : ℤ) +
            ((M : ℤ) * (N : ℤ) - (M' : ℤ) * (N' : ℤ)) * (N : ℤ) := by rw [hqz, hΔz]
      _ = (M : ℤ) * ((M : ℤ) * (N' : ℤ) + (N : ℤ) ^ 2) := by ring
      _ = (M : ℤ) * ((Δ : ℤ) * (p : ℤ)) := by rw [← hpz]
      _ = (Δ : ℤ) * ((M : ℤ) * (p : ℤ)) := by ring
  have hc1 : (p : ℤ) * (M' : ℤ) + (M : ℤ) = (N : ℤ) * (q : ℤ) :=
    mul_left_cancel₀ hΔpos.ne' h1z
  have hc2 : (q : ℤ) * (N' : ℤ) + (N : ℤ) = (M : ℤ) * (p : ℤ) :=
    mul_left_cancel₀ hΔpos.ne' h2z
  exact ⟨by exact_mod_cast hc1, by exact_mod_cast hc2⟩

theorem main : H1 → H2 → H3 → type_of% @Erdos307.erdos_307.variants.coprime_one_notMem := by
  intro h1 h2 h3
  obtain ⟨P₀, Q₀, hP₀ne, hQ₀ne, hP₀2, hQ₀2, hP₀cop, hQ₀cop, hPQcop,
    hMlt, h2p, h2q, hdvdp, hdvdq⟩ := h3
  set M := ∏ a ∈ P₀, a
  set M' := ∑ a ∈ P₀, M / a
  set N := ∏ b ∈ Q₀, b
  set N' := ∑ b ∈ Q₀, N / b
  set Δ := M * N - M' * N' with hΔdef
  set p := (M * N' + N ^ 2) / Δ
  set q := (M' * N + M ^ 2) / Δ
  have h2res :
      2 ≤ p ∧ p ∉ P₀ ∧ 2 ≤ q ∧ q ∉ Q₀ ∧
        Set.Pairwise ((insert p P₀ : Finset ℕ) : Set ℕ) Nat.Coprime ∧
        Set.Pairwise ((insert q Q₀ : Finset ℕ) : Set ℕ) Nat.Coprime :=
    h2 P₀ Q₀ hP₀ne hQ₀ne hP₀2 hQ₀2 hP₀cop hQ₀cop hPQcop hMlt h2p h2q hdvdp hdvdq
  obtain ⟨hp2, hpnot, hq2, hqnot, hPcop, hQcop⟩ := h2res
  refine ⟨insert p P₀, insert q Q₀, ?_, ?_, ?_, ?_, hPcop, hQcop, ?_⟩
  · -- 0 ∉ insert p P₀ ∩ insert q Q₀
    intro h0
    have h0P : 0 ∈ insert p P₀ := (Finset.mem_inter.mp h0).1
    rcases Finset.mem_insert.mp h0P with h0eq | h0mem
    · omega
    · have := hP₀2 0 h0mem; omega
  · -- 1 ∉ insert p P₀ ∪ insert q Q₀
    intro h1mem
    rcases Finset.mem_union.mp h1mem with h1P | h1Q
    · rcases Finset.mem_insert.mp h1P with h1eq | h1in
      · omega
      · have := hP₀2 1 h1in; omega
    · rcases Finset.mem_insert.mp h1Q with h1eq | h1in
      · omega
      · have := hQ₀2 1 h1in; omega
  · -- 1 < #(insert p P₀)
    rw [Finset.card_insert_of_notMem hpnot]
    have hpos : 0 < P₀.card := Finset.card_pos.mpr hP₀ne
    omega
  · -- 1 < #(insert q Q₀)
    rw [Finset.card_insert_of_notMem hqnot]
    have hpos : 0 < Q₀.card := Finset.card_pos.mpr hQ₀ne
    omega
  · -- 1 = (∑ x ∈ insert p P₀, (x : ℚ)⁻¹) * (∑ y ∈ insert q Q₀, (y : ℚ)⁻¹)
    have hPpos : ∀ x ∈ insert p P₀, 0 < x := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hxin
      · omega
      · have := hP₀2 x hxin; omega
    have hQpos : ∀ y ∈ insert q Q₀, 0 < y := by
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hyin
      · omega
      · have := hQ₀2 y hyin; omega
    have hP₀pos : ∀ a ∈ P₀, 0 < a := fun a ha => by have := hP₀2 a ha; omega
    have hQ₀pos : ∀ b ∈ Q₀, 0 < b := fun b hb => by have := hQ₀2 b hb; omega
    have h1P := (h1 (insert p P₀) hPpos).1
    have h1Pins := (h1 P₀ hP₀pos).2 p (by omega) hpnot
    have h1Q := (h1 (insert q Q₀) hQpos).1
    have h1Qins := (h1 Q₀ hQ₀pos).2 q (by omega) hqnot
    have hp_mul : Δ * p = M * N' + N ^ 2 := Nat.mul_div_cancel' hdvdp
    have hq_mul : Δ * q = M' * N + M ^ 2 := Nat.mul_div_cancel' hdvdq
    obtain ⟨hcross1, hcross2⟩ := frame_cross_eq hMlt hΔdef hp_mul hq_mul
    have hprodP_pos : (0 : ℚ) < ∏ x ∈ insert p P₀, (x : ℚ) :=
      Finset.prod_pos fun x hx => Nat.cast_pos.mpr (hPpos x hx)
    have hprodQ_pos : (0 : ℚ) < ∏ y ∈ insert q Q₀, (y : ℚ) :=
      Finset.prod_pos fun y hy => Nat.cast_pos.mpr (hQpos y hy)
    have hprodP_eq : (∏ x ∈ insert p P₀, (x : ℚ)) = (p : ℚ) * (M : ℚ) := by
      rw [Finset.prod_insert hpnot, Nat.cast_prod]
    have hprodQ_eq : (∏ y ∈ insert q Q₀, (y : ℚ)) = (q : ℚ) * (N : ℚ) := by
      rw [Finset.prod_insert hqnot, Nat.cast_prod]
    have hnumP_eq : ((∑ a ∈ insert p P₀, (∏ x ∈ insert p P₀, x) / a : ℕ) : ℚ) =
        ((N * q : ℕ) : ℚ) := by
      rw [h1Pins, hcross1]
    have hnumQ_eq : ((∑ b ∈ insert q Q₀, (∏ y ∈ insert q Q₀, y) / b : ℕ) : ℚ) =
        ((M * p : ℕ) : ℚ) := by
      rw [h1Qins, hcross2]
    have hprod_ne : (∏ x ∈ insert p P₀, (x : ℚ)) * (∏ y ∈ insert q Q₀, (y : ℚ)) ≠ 0 :=
      mul_ne_zero hprodP_pos.ne' hprodQ_pos.ne'
    apply mul_left_cancel₀ hprod_ne
    calc
      (∏ x ∈ insert p P₀, (x : ℚ)) * (∏ y ∈ insert q Q₀, (y : ℚ)) * 1
          = ((p : ℚ) * (M : ℚ)) * ((q : ℚ) * (N : ℚ)) := by rw [mul_one, hprodP_eq, hprodQ_eq]
      _ = ((N * q : ℕ) : ℚ) * ((M * p : ℕ) : ℚ) := by push_cast; ring
      _ = ((∏ x ∈ insert p P₀, (x : ℚ)) * (∑ x ∈ insert p P₀, (x : ℚ)⁻¹)) *
            ((∏ y ∈ insert q Q₀, (y : ℚ)) * (∑ y ∈ insert q Q₀, (y : ℚ)⁻¹)) := by
            rw [h1P, h1Q, hnumP_eq, hnumQ_eq]
      _ = (∏ x ∈ insert p P₀, (x : ℚ)) * (∏ y ∈ insert q Q₀, (y : ℚ)) *
            ((∑ x ∈ insert p P₀, (x : ℚ)⁻¹) * (∑ y ∈ insert q Q₀, (y : ℚ)⁻¹)) := by ring

end OMA.R_Erdos307_erdos_307_variants_coprime_one_notMem_R1
