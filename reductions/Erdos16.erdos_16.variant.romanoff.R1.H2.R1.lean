import OMAReductions.R_Erdos16_erdos_16_variant_romanoff_R1
import Mathlib.NumberTheory.Chebyshev

/-! Expand Romanoff's second moment by the two exponents. Chebyshev's inequality
controls the diagonal. Each off-diagonal pair is bounded by a count of prime
pairs at the prescribed gap. Averaging its odd-prime factor over the exponent
difference gives the remaining factor of the square of the logarithm. -/

namespace OMA.R_Erdos16_erdos_16_variant_romanoff_R1_H2_R1

open Finset

private lemma diagonal : ∃ D : ℝ, ∀ x : ℕ, 2 ≤ x →
    (Nat.log 2 x + 1 : ℕ) * (x.primeCounting : ℝ) ≤ D * x := by
  refine ⟨4 * (Real.log 4 + 1) / Real.log 2, ?_⟩
  intro x hx
  have x2 : (2:ℝ) ≤ x := by exact_mod_cast hx
  have xpos : (0:ℝ) < x := by linarith
  have logtwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have logx : 0 < Real.log (x:ℝ) := Real.log_pos (by linarith)
  have powX : (2:ℝ) ^ Nat.log 2 x ≤ x := by exact_mod_cast Nat.pow_log_le_self 2 (by omega : x ≠ 0)
  have logPow := Real.log_le_log (by positivity : 0 < (2:ℝ)^Nat.log 2 x) powX
  rw [Real.log_pow] at logPow
  have one := Real.log_le_log (by norm_num : (0:ℝ) < 2) x2
  have len : ((Nat.log 2 x + 1 : ℕ):ℝ) * Real.log 2 ≤ 2*Real.log x := by
    push_cast
    nlinarith only [logPow,one]
  have cheb := Chebyshev.pi_le_log4_mul_div (show 1 < (x:ℝ) by linarith)
  rw [Nat.floor_natCast] at cheb
  have rs := Real.log_sqrt xpos.le
  have sl : 0 < Real.log (Real.sqrt (x:ℝ)) := by linarith
  have hd : (x.primeCounting:ℝ)-Real.sqrt x ≤ Real.log 4*x / Real.log (Real.sqrt x) := (sub_le_iff_le_add).mpr cheb
  have cheb' := (le_div_iff₀ sl).mp hd
  have sq := Real.mul_self_sqrt xpos.le
  have sqLe := mul_le_mul_of_nonneg_left (Real.log_le_self (Real.sqrt_nonneg (x:ℝ))) (Real.sqrt_nonneg (x:ℝ))
  have plog : (x.primeCounting:ℝ)*Real.log x ≤ 2*(Real.log 4+1)*x := by
    rw [rs] at cheb' sqLe
    nlinarith only [cheb',sqLe,sq]
  have useLen := mul_le_mul_of_nonneg_right len (show 0 ≤ (x.primeCounting:ℝ) by positivity)
  apply (mul_le_mul_iff_of_pos_right logtwo).mp
  calc
    _ ≤ 4 * (Real.log 4 + 1) * x := by nlinarith only [useLen,plog]
    _ = _ := by field_simp

private lemma square_expand (g : ℕ → ℝ) (m : ℕ) :
    (∑ j ∈ range m, g j)^2 = (∑ j ∈ range m, g j ^ 2) +
      2 * ∑ l ∈ range m, ∑ k ∈ range l, g k * g l := by
  induction m with
  | zero => simp
  | succ m ih =>
    simp only [sum_range_succ, ←sum_mul]
    simp_rw [←sum_mul] at ih
    nlinarith only [ih]


-- A uniform upper-bound sieve for two primes at a power-of-two difference.
def H1 : Prop := ∃ A : ℝ, 0 ≤ A ∧ ∀ x : ℕ, 2 ≤ x →
    let L := Nat.log 2 x + 1
    let W (r : ℕ) : ℝ := ∏ p ∈ (2^r-1 : ℕ).primeFactors, (1 + 1/((p-2 : ℕ):ℝ))
    ∀ k l : ℕ, k < l → l < L →
      (((Finset.range (x+1)).filter (fun p : ℕ => p.Prime ∧ (p+(2^l-2^k)).Prime)).card : ℝ) ≤
        (A*x/(L:ℝ)^2) * W (l-k)

-- Mean value of the odd-prime correction for the numbers 2^r - 1.
def H2 : Prop := ∃ B : ℝ, 0 ≤ B ∧ ∀ L : ℕ, 1 ≤ L →
    let W (r : ℕ) : ℝ := ∏ p ∈ (2^r-1 : ℕ).primeFactors, (1 + 1/((p-2 : ℕ):ℝ))
    ∑ r ∈ Finset.range L, W r ≤ B*L

theorem main : H1 → H2 → OMA.R_Erdos16_erdos_16_variant_romanoff_R1.H2 := by
  rintro ⟨A,hA,sieve⟩ ⟨B,hB,average⟩
  obtain ⟨D,primeBound⟩ := diagonal
  refine ⟨D + 2*A*B, ?_⟩
  intro x hx
  classical
  let L := Nat.log 2 x + 1
  let W (r : ℕ) : ℝ := ∏ p ∈ (2^r-1 : ℕ).primeFactors, (1 + 1/((p-2 : ℕ):ℝ))
  let good (n k : ℕ) : Prop := 1 ≤ k ∧ 2^k < n ∧ (n-2^k).Prime ∧ n-2^k ≠ 2
  let g (n k : ℕ) : ℝ := if good n k then 1 else 0
  let V := range (x+1)
  have l1 : 1 ≤ L := Nat.succ_pos _
  have lp : (0:ℝ) < L := by exact_mod_cast l1
  have wn (r : ℕ) : 0 ≤ W r := prod_nonneg (fun p _ => by positivity)
  have coeff : 0 ≤ A*x/(L:ℝ)^2 := by positivity
  have row (n : ℕ) (hn : n ∈ V) :
      (((range n).filter (good n)).card : ℝ) = ∑ k ∈ range L, g n k := by
    have nx : n ≤ x := by simpa [V, Nat.lt_succ_iff] using hn
    have e : (range n).filter (good n) = (range L).filter (good n) := by
      ext k
      simp only [mem_filter, mem_range]
      constructor
      · rintro ⟨_,h⟩
        exact ⟨Nat.lt_succ_of_le (Nat.le_log_of_pow_le (by decide : 1<2) (h.2.1.le.trans nx)), h⟩
      · rintro ⟨_,h⟩
        exact ⟨k.lt_two_pow_self.trans h.2.1, h⟩
    rw [e]
    exact (sum_boole (R:=ℝ) (good n) (range L)).symm
  have single (k : ℕ) : ∑ n ∈ V, (g n k)^2 ≤ (x.primeCounting:ℝ) := by
    have eq (n : ℕ) : (g n k)^2 = if good n k then (1:ℝ) else 0 := by
      by_cases h : good n k <;> simp [g,h]
    simp_rw [eq]
    rw [sum_boole, ←Nat.primesLE_card_eq_primeCounting]
    exact_mod_cast (card_le_card_of_injOn (fun n : ℕ => n-2^k) (by
      intro n hn
      obtain ⟨hv,hg⟩ := mem_filter.mp hn
      have nx : n ≤ x := by simpa [V, Nat.lt_succ_iff] using hv
      exact Nat.mem_primesLE.mpr ⟨Nat.le_trans (Nat.sub_le _ _) nx,hg.2.2.1⟩) (by
      intro n hn m hm he
      have h₁ : 2^k < n := (mem_filter.mp hn).2.2.1
      have h₂ : 2^k < m := (mem_filter.mp hm).2.2.1
      dsimp at he
      omega) : ((V.filter (fun n => good n k)).card) ≤ x.primesLE.card)
  have pair (l k : ℕ) (hl : l < L) (hk : k < l) :
      ∑ n ∈ V, g n k * g n l ≤ A*x/(L:ℝ)^2 * W (l-k) := by
    have eq (n : ℕ) : g n k * g n l = if good n k ∧ good n l then (1:ℝ) else 0 := by
      by_cases h : good n k <;> by_cases h' : good n l <;> simp [g,h,h']
    simp_rw [eq]
    rw [sum_boole]
    apply le_trans _ (sieve x hx k l hk hl)
    apply Nat.cast_le.mpr
    apply card_le_card_of_injOn (fun n : ℕ => n-2^l)
    · intro n hn
      obtain ⟨hv,low,high⟩ := mem_filter.mp hn
      have nx : n ≤ x := by simpa [V, Nat.lt_succ_iff] using hv
      have pw : 2^k ≤ 2^l := Nat.pow_le_pow_right (by decide) hk.le
      have lo : 2^l < n := high.2.1
      have e : n-2^l+(2^l-2^k) = n-2^k := by omega
      exact mem_filter.mpr ⟨mem_range.mpr ((Nat.sub_le n (2^l)).trans_lt (Nat.lt_succ_of_le nx)),high.2.2.1, e ▸ low.2.2.1⟩
    · intro n hn m hm he
      have a : 2^l < n := (mem_filter.mp hn).2.2.2.1
      have b : 2^l < m := (mem_filter.mp hm).2.2.2.1
      dsimp at he
      omega
  have singleSum : (∑ k ∈ range L, ∑ n ∈ V, (g n k)^2) ≤ D*x := by
    calc
      _ ≤ ∑ _ ∈ range L, (x.primeCounting:ℝ) := sum_le_sum (fun k _ => single k)
      _ = (L:ℝ)*x.primeCounting := by simp
      _ ≤ _ := primeBound x hx
  have partialSum (l : ℕ) (hl : l < L) : ∑ k ∈ range l, W (l-k) ≤ B*L := by
    rw [←sum_range_reflect (fun k => W (l-k)) l]
    have e : (∑ j ∈ range l, W (l-(l-1-j))) = ∑ j ∈ range l, W (j+1) := by
      apply sum_congr rfl
      intro j hj
      have := mem_range.mp hj
      congr 1 <;> omega
    rw [e]
    have small : (∑ j ∈ range l, W (j+1)) ≤ ∑ j ∈ range (l+1), W j := by
      rw [sum_range_succ']; linarith only [wn 0]
    exact small.trans ((sum_le_sum_of_subset_of_nonneg (range_mono hl) (fun r _ _ => wn r)).trans (average L l1))
  have pairSum : (∑ l ∈ range L, ∑ k ∈ range l, ∑ n ∈ V, g n k * g n l) ≤ A*B*x := by
    calc
      _ ≤ ∑ l ∈ range L, ∑ k ∈ range l, (A*x/(L:ℝ)^2)*W (l-k) :=
        sum_le_sum fun l hl => sum_le_sum fun k hk => pair l k (mem_range.mp hl) (mem_range.mp hk)
      _ ≤ ∑ _ ∈ range L, (A*x/(L:ℝ)^2)*(B*L) := by
        apply sum_le_sum
        intro l hl
        rw [←mul_sum]
        exact mul_le_mul_of_nonneg_left (partialSum l (mem_range.mp hl)) coeff
      _ = _ := by simp; field_simp
  change (∑ n ∈ V, (((range n).filter (good n)).card : ℝ)^2) ≤ _
  calc
    _ = ∑ n ∈ V, ((∑ k ∈ range L, (g n k)^2) +
        2*∑ l ∈ range L, ∑ k ∈ range l, g n k*g n l) := by
      apply sum_congr rfl
      intro n hn
      rw [row n hn,square_expand]
    _ = (∑ k ∈ range L, ∑ n ∈ V, (g n k)^2) +
        2*(∑ l ∈ range L, ∑ k ∈ range l, ∑ n ∈ V, g n k*g n l) := by
      rw [sum_add_distrib, ←mul_sum, sum_comm (s:=V) (t:=range L),
        sum_comm (s:=V) (t:=range L)]
      congr 2
      apply sum_congr rfl
      intro l _
      rw [sum_comm]
    _ ≤ _ := by linarith only [singleSum,pairSum]

end OMA.R_Erdos16_erdos_16_variant_romanoff_R1_H2_R1
