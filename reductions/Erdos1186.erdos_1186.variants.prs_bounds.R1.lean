import FormalConjectures.ErdosProblems.«1186»
import Mathlib.Topology.Order.LiminfLimsup

/-!
Use the twelve-block coloring for the upper bound and bound the mixed
pairs for the lower bound, as in Theorems 4 and 5 of Parrilo, Robertson,
and Saracino, arXiv:math/0609532. At sizes 1096q every coarse block has
even width. The lower estimate retains the errors of order n.
-/

-- Credit: @dk8827

open Finset Filter Erdos1186
open scoped BigOperators Classical

namespace OMA.R_Erdos1186_erdos_1186_variants_prs_bounds_R1

/-- The finite count for the twelve-block coloring. -/
def H1 : Prop :=
  ∀ q : ℕ, 0 < q →
    let c := fun x : ℕ =>
      let b := (x - 1) / (2 * q)
      b < 28 || (34 ≤ b && b < 62) || (99 ≤ b && b < 158) ||
      (274 ≤ b && b < 390) || (449 ≤ b && b < 486) ||
      (514 ≤ b && b < 520)
    monoCount 3 (1096 * q) c ≤ 64116 * q ^ 2

/-- The mixed-pair inequality from the 128-block certificate. -/
def H2 : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (c : ℕ → Bool),
    let X := ((Icc 1 n ×ˢ Icc 1 n).filter
      (fun p => c p.1 ≠ c p.2 ∧ p.1 + 1 ≤ 2 * p.2 ∧ 2 * p.2 ≤ p.1 + n)).card
    (X : ℝ) ≤ (4469 / 16384 : ℝ) * (n : ℝ) ^ 2 + C * n

/-- Count ordered progressions by their three mixed pairs, and bound
oppositely colored endpoints of equal parity. -/
def H3 : Prop :=
  ∀ (n : ℕ) (c : ℕ → Bool),
    let X := ((Icc 1 n ×ˢ Icc 1 n).filter
      (fun p => c p.1 ≠ c p.2 ∧ p.1 + 1 ≤ 2 * p.2 ∧ 2 * p.2 ≤ p.1 + n)).card
    (n : ℝ) ^ 2 / 2 ≤
      2 * (monoCount 3 n c : ℝ) + n + X + ((n : ℝ) + 1) ^ 2 / 8

private theorem mono_le_sq (n k : ℕ) (c : ℕ → Bool) : monoCount k n c ≤ n ^ 2 := by
  unfold monoCount
  have h := card_filter_le (s := Icc 1 n ×ˢ Icc 1 n)
    (fun p : ℕ × ℕ => p.1 + (k - 1) * p.2 ≤ n ∧ ∀ i < k, c (p.1 + i * p.2) = c p.1)
  simpa only [card_product, Nat.card_Icc, Nat.add_sub_cancel, pow_two] using h

set_option maxHeartbeats 600000 in
theorem main : H1 → H2 → H3 → type_of% @Erdos1186.erdos_1186.variants.prs_bounds := by
  rintro upper ⟨C, hC, mixed⟩ decomp
  let F (n : ℕ) := (minMonoCount 3 n : ℝ) / (n : ℝ) ^ 2
  change (1675 : ℝ) / 32768 ≤ liminf F atTop ∧ liminf F atTop ≤ (117 : ℝ) / 2192
  have hF₀ : IsBoundedUnder (· ≥ ·) atTop F := isBoundedUnder_of_eventually_ge
    (a := 0) (Eventually.of_forall fun n => by dsimp only [F]; positivity)
  have hF₁ : IsBoundedUnder (· ≤ ·) atTop F := by
    apply isBoundedUnder_of_eventually_le (a := 1)
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have h := (minMonoCount_le 3 n (fun _ => true)).trans (mono_le_sq n 3 (fun _ => true))
    have hp : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    apply (div_le_iff₀ (sq_pos_of_pos hp)).2
    norm_num
    exact_mod_cast h
  constructor
  · apply le_of_forall_lt_imp_le_of_dense
    intro x hx
    apply le_liminf_of_le hF₁.isCoboundedUnder_ge
    let d := (1675 : ℝ) / 32768 - x
    have hd : 0 < d := sub_pos.2 hx
    obtain ⟨N, hnN⟩ := exists_nat_gt ((C + 2) / d)
    filter_upwards [eventually_ge_atTop (max N 1)] with n hn
    have hn₀ : 1 ≤ n := (le_max_right _ _).trans hn
    have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn₀
    have hnpos : (0 : ℝ) < n := zero_lt_one.trans_le hnr
    have hne : Set.Nonempty {m : ℕ | ∃ c : ℕ → Bool, monoCount 3 n c = m} :=
      ⟨_, ⟨fun _ => true, rfl⟩⟩
    obtain ⟨c, hc⟩ : ∃ c : ℕ → Bool, monoCount 3 n c = minMonoCount 3 n :=
      csInf_mem hne
    have h1 := mixed n c
    have h2 := decomp n c
    dsimp only at h1 h2
    rw [hc] at h2
    have herror : (n : ℝ) + ((n : ℝ) + 1) ^ 2 / 8 ≤ (n : ℝ) ^ 2 / 8 + 2 * n := by
      nlinarith only [hnr]
    have hD : C + 2 ≤ d * (n : ℝ) := by
      have h := (div_le_iff₀ hd).1 (hnN.le.trans
        (show (N : ℝ) ≤ n by exact_mod_cast ((le_max_left N 1).trans hn)))
      simpa only [mul_comm] using h
    have he := mul_le_mul_of_nonneg_right hD hnpos.le
    apply (le_div_iff₀ (sq_pos_of_pos hnpos)).2
    dsimp only [d] at he
    have hrem := mul_nonneg (sub_nonneg.2 hx.le) (sq_nonneg (n : ℝ))
    nlinarith only [h1, h2, herror, he, hrem]
  · apply liminf_le_of_frequently_le _ hF₀
    rw [frequently_atTop]
    intro N
    let q := max 1 N
    have hq : 0 < q := zero_lt_one.trans_le (le_max_left 1 N)
    refine ⟨1096 * q, ?_, ?_⟩
    · have h := le_max_right 1 N
      dsimp only [q]
      omega
    · let c := fun x : ℕ =>
        let b := (x - 1) / (2 * q)
        b < 28 || (34 ≤ b && b < 62) || (99 ≤ b && b < 158) ||
        (274 ≤ b && b < 390) || (449 ≤ b && b < 486) ||
        (514 ≤ b && b < 520)
      have h := (minMonoCount_le 3 (1096 * q) c).trans (upper q hq)
      have hn : (0 : ℝ) < ((1096 * q : ℕ) : ℝ) := by
        exact_mod_cast Nat.mul_pos (by decide : 0 < 1096) hq
      apply (div_le_iff₀ (sq_pos_of_pos hn)).2
      push_cast
      have h' : (minMonoCount 3 (1096 * q) : ℝ) ≤ 64116 * (q : ℝ) ^ 2 := by exact_mod_cast h
      nlinarith only [h']

end OMA.R_Erdos1186_erdos_1186_variants_prs_bounds_R1
