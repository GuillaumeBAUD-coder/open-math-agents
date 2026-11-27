import OMAReductions.R_Erdos297_erdos_297_variants_general_R1_H3_R1_H2_R1
import Mathlib

/-! Starting from an initial harmonic segment, expand the positive remaining
fraction greedily. The numerator decreases and the denominators increase. -/
open Finset

namespace IntegerEgypt297

private lemma greedy (a b L : ℕ) (hb : 0 < b) (hab : a ≤ b) (hL : a*L < b) :
    ∃ S : Finset ℕ, (∀ n ∈ S, L < n) ∧ (∑ n ∈ S, (1:ℚ)/n) = (a:ℚ)/b := by
  induction a using Nat.strong_induction_on generalizing b L with
  | h a ih =>
    rcases a.eq_zero_or_pos with rfl|ha
    · exact ⟨∅,by simp,by simp⟩
    let k := (b-1)/a+1
    have low : b ≤ a*k := by
      have H := Nat.lt_mul_div_succ (b-1) ha
      dsimp [k]; omega
    have high : a*k < b+a := by
      have H := Nat.div_mul_le_self (b-1) a
      dsimp [k]; rw [Nat.mul_add,Nat.mul_one,Nat.mul_comm a]; omega
    have hk : 0 < k := Nat.succ_pos _
    have kL : L < k := by
      apply Nat.lt_of_mul_lt_mul_left (a := a)
      exact hL.trans_le low
    let r := a*k-b
    have hr : r < a := by dsimp [r]; omega
    have hbk : 0 < b*k := Nat.mul_pos hb hk
    have rb : r < b := hr.trans_le hab
    have hl' : r*k < b*k := Nat.mul_lt_mul_of_pos_right rb hk
    have rbk : r ≤ b*k := rb.le.trans (Nat.le_mul_of_pos_right b hk)
    obtain ⟨S,hS,eq⟩ := ih r hr (b*k) k hbk rbk hl'
    refine ⟨insert k S,?_,?_⟩
    · intro n hn
      rcases mem_insert.mp hn with rfl|hs
      · exact kL
      · exact kL.trans (hS _ hs)
    · rw [sum_insert (fun hkS => (lt_irrefl k) (hS k hkS)),eq]
      dsimp [r]
      push_cast [Nat.cast_sub low]
      field_simp
      ring

lemma integers (j : ℕ) (hj : 0 < j) :
    ∃ S : Finset ℕ, (∀ n ∈ S, 0 < n) ∧ (∑ n ∈ S, (1:ℚ)/n) = j := by
  have existsH : ∃ n : ℕ, (j:ℚ) ≤ harmonic n := by
    obtain ⟨n,hn⟩ := exists_nat_gt (Real.exp j)
    have he : Real.exp (j:ℝ) ≤ ((n+1:ℕ):ℝ) := by push_cast; linarith only [hn]
    have hh := (Real.log_le_log (Real.exp_pos _) he).trans (log_add_one_le_harmonic n)
    rw [Real.log_exp] at hh
    exact ⟨n,by exact_mod_cast hh⟩
  let t := Nat.find existsH
  have ht : (j:ℚ) ≤ harmonic t := Nat.find_spec existsH
  have tn : t ≠ 0 := by rintro h; rw [h,harmonic_zero] at ht; exact (not_le_of_gt (by exact_mod_cast hj : (0:ℚ) < j)) ht
  obtain ⟨n,hn⟩ := Nat.exists_eq_succ_of_ne_zero tn
  have below : harmonic n < (j:ℚ) := lt_of_not_ge (Nat.find_min existsH (by change n<t; omega))
  rw [hn,harmonic_succ] at ht
  let r := (j:ℚ)-harmonic n
  have rp : 0 < r := sub_pos.mpr below
  have rle : r ≤ 1/((n:ℚ)+1) := by dsimp [r]; simpa [one_div] using (by linarith only [ht] : (j:ℚ)-harmonic n ≤ (↑(n+1))⁻¹)
  let a := r.num.toNat
  let b := r.den
  have bp : 0 < b := r.den_pos
  have br : 0 < (b:ℚ) := by exact_mod_cast bp
  have repr : (a:ℚ)/b = r := by
    have hnum : 0 ≤ r.num := Rat.num_nonneg.mpr rp.le
    dsimp [a,b]; rw [← Int.cast_natCast, Int.toNat_of_nonneg hnum, Rat.num_div_den]
  have ab : a ≤ b := by
    have hr1 : r ≤ 1 := rle.trans ((div_le_iff₀ (by positivity)).mpr (by simp))
    rw [←repr,div_le_iff₀ br] at hr1
    exact_mod_cast (by simpa using hr1 : (a:ℚ) ≤ b)
  have hnt : a*n < b := by
    have hR := (le_div_iff₀ (by positivity : 0 < (n:ℚ)+1)).mp rle
    rw [← repr] at hR
    field_simp at hR
    have ap : 0 < (a:ℚ) := by rw [←repr] at rp; exact (div_pos_iff_of_pos_right br).mp rp
    exact_mod_cast (by linarith only [hR,ap] : (a:ℚ)*n < b)
  obtain ⟨S,large,sum⟩ := greedy a b n bp ab hnt
  let T := Icc 1 n
  have disj : Disjoint T S := Finset.disjoint_left.mpr fun k hk hS =>
    (not_lt_of_ge (mem_Icc.mp hk).2) (large k hS)
  refine ⟨T ∪ S,?_,?_⟩
  · intro k hk
    rcases mem_union.mp hk with t|s
    · exact (mem_Icc.mp t).1
    · exact (Nat.zero_le n).trans_lt (large k s)
  · rw [sum_union disj,sum,repr]
    change (∑ i ∈ Icc 1 n, (1:ℚ)/i)+((j:ℚ)-harmonic n) = j
    simp [one_div, ← harmonic_eq_sum_Icc]

end IntegerEgypt297

theorem OMA.solution : OMA.R_Erdos297_erdos_297_variants_general_R1_H3_R1_H2_R1.H2 := IntegerEgypt297.integers
