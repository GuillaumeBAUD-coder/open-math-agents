import FormalConjectures.ErdosProblems.«997»
import Mathlib

/-! Long runs of primes congruent to one force arbitrarily long failures
of uniform distribution for a residual set of real multipliers in (1/8,1/4).
The prime surplus and finite run criterion specialize the Shiu reduction of
@Hennyrick for Erdős 427. -/
namespace OMA.R_Erdos997_erdos_997_variants_irrational_R1

open Set Filter

def H1 : Prop :=
  ∀ q k : ℕ, 0 < q → 0 < k →
    let good : ℕ → Bool := fun i => decide (Nat.nth Nat.Prime i ≡ 1 [MOD q])
    ∃ l r : ℕ,
      (k-1) * (((Finset.Ico l r).filter (fun i => good i = false)).card + 1) <
        ((Finset.Ico l r).filter (fun i => good i = true)).card

def H2 : Prop :=
  ∀ (good : ℕ → Bool) (l r k : ℕ), 1 ≤ k →
    (k-1) * (((Finset.Ico l r).filter (fun i => good i = false)).card + 1) <
      ((Finset.Ico l r).filter (fun i => good i = true)).card →
    ∃ m, l ≤ m ∧ m+k ≤ r ∧ ∀ i ∈ Finset.Ico m (m+k), good i = true

theorem main : H1 → H2 → type_of% @Erdos997.erdos_997.variants.irrational := by
  classical
  intro surplus run
  let p (i : ℕ) := Nat.nth Nat.Prime i
  let U (k : ℕ) : Set ℝ := ⋃ m : ℕ, ⋂ i ∈ Finset.Ioc m (m+k),
    ⋃ z : ℤ, {a : ℝ | |a*((p i : ℝ)-1) - z| < 1/16}
  have ho (k : ℕ) : IsOpen (U k) := by
    exact isOpen_iUnion fun m => isOpen_biInter_finset fun i _ =>
      isOpen_iUnion fun z => isOpen_lt (by fun_prop) continuous_const
  have hd (k : ℕ) : Dense (U k) := by
    apply (Rat.denseRange_cast (𝕜 := ℝ)).mono
    rintro _ ⟨t,rfl⟩
    let good : ℕ → Bool := fun i => decide (p i ≡ 1 [MOD t.den])
    obtain ⟨l,r,he⟩ := surplus t.den (k+1) t.den_pos (by omega)
    obtain ⟨m,_,_,hm⟩ := run good l r (k+1) (by omega) he
    apply mem_iUnion.mpr
    refine ⟨m, mem_iInter₂.mpr fun i hi => ?_⟩
    obtain ⟨hmi,him⟩ := Finset.mem_Ioc.mp hi
    have hc : p i ≡ 1 [MOD t.den] := of_decide_eq_true (hm i (Finset.mem_Ico.mpr ⟨by omega,by omega⟩))
    obtain ⟨v,hv⟩ := hc.symm.dvd
    have hv' : (p i : ℝ) - 1 = t.den * (v : ℝ) := by exact_mod_cast hv
    apply mem_iUnion.mpr
    refine ⟨t.num*v, ?_⟩
    change |(t : ℝ)*((p i : ℝ)-1) - ((t.num*v : ℤ) : ℝ)| < 1/16
    have hden : (t.den : ℝ) ≠ 0 := by exact_mod_cast t.den_nz
    rw [hv', Rat.cast_def, Int.cast_mul, ← mul_assoc, div_mul_cancel₀ _ hden, sub_self, abs_zero]
    norm_num
  have dense := dense_irrational.inter_of_Gδ IsGδ.setOfPred_irrational
    (IsGδ.iInter_of_isOpen ho) (dense_iInter_of_isOpen ho hd)
  obtain ⟨a,⟨ha1,ha2⟩,ha,hu⟩ := dense.inter_open_nonempty
    (Ioo (1/8 : ℝ) (1/4)) isOpen_Ioo (nonempty_Ioo.mpr (by norm_num))
  refine ⟨a,ha,?_⟩
  intro well
  obtain ⟨k,hk⟩ := eventually_atTop.1 (well (1/4) (by norm_num))
  let K := k+1
  have hU : a ∈ U K := mem_iInter.mp hu K
  obtain ⟨m,hm⟩ := mem_iUnion.mp hU
  have hbad (i : ℕ) (hi : i ∈ Finset.Ioc m (m+K)) :
      Int.fract (a*(p i : ℝ)) < 1/2 := by
    obtain ⟨z,hz⟩ := mem_iUnion.mp (mem_iInter₂.mp hm i hi)
    change |a*((p i : ℝ)-1)-z| < 1/16 at hz
    obtain ⟨hz1,hz2⟩ := abs_lt.mp hz
    have h₁ : 0 ≤ a*(p i : ℝ)-z := by linarith
    have h₂ : a*(p i : ℝ)-z < 1/2 := by linarith
    rw [← Int.fract_sub_intCast _ z, Int.fract_eq_self.mpr ⟨h₁,by linarith⟩]
    exact h₂
  have hc : ((Finset.Ioc m (m+K)).filter (fun i => Int.fract (a*(p i : ℝ)) ∈ Ico (1/2 : ℝ) 1)) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro i hi hh
    exact (not_lt_of_ge hh.1) (hbad i hi)
  have hw := hk K (by dsimp [K]; omega) m (1/2) 1 (by norm_num) (by norm_num) le_rfl
  change |((((Finset.Ioc m (m+K)).filter (fun i => Int.fract (a*(p i : ℝ)) ∈ Ico (1/2 : ℝ) 1)).card : ℝ) - (1-1/2)*(K : ℝ))| < 1/4*K at hw
  rw [hc] at hw
  have hK : (0 : ℝ) < K := by dsimp [K]; positivity
  rw [Finset.card_empty, Nat.cast_zero, zero_sub, abs_neg,
    abs_of_nonneg (show 0 ≤ (1-1/2 : ℝ)*(K : ℝ) by positivity)] at hw
  linarith

end OMA.R_Erdos997_erdos_997_variants_irrational_R1
