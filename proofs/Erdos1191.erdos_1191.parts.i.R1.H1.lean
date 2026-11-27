import OMAReductions.R_Erdos1191_erdos_1191_parts_i_R1
import Mathlib.Algebra.Order.Chebyshev

/-! A finite form of Erdős's bound for Sidon counting functions. Count signed differences
within blocks of width (2^R), then bound the normalized dyadic prefix counts by
the sum of the squared block counts. -/

-- Credit: @dk8827

open Finset
open scoped BigOperators

namespace OMA.SidonDyadic

private theorem block_energy (N : ℕ) (S : Finset ℕ) (hN : 0 < N)
    (hpos : ∀ x ∈ S, 0 < x) (hsid : IsSidon (↑S : Set ℕ)) :
    (∑ j ∈ range N, ((S.filter (fun x => (x - 1) / N = j)).card : ℝ) ^ 2) ≤
      7 * N := by
  classical
  let block (j : ℕ) := S.filter fun x => (x - 1) / N = j
  let pairs (j : ℕ) := (block j).offDiag
  have pairwise : (↑(range N) : Set ℕ).PairwiseDisjoint pairs := by
    intro i _ j _ hij
    apply Finset.disjoint_left.2
    intro p hi hj
    have hi' := (mem_filter.1 (mem_offDiag.1 hi).1).2
    have hj' := (mem_filter.1 (mem_offDiag.1 hj).1).2
    exact hij (hi'.symm.trans hj')
  let P := (range N).biUnion pairs
  have member {p : ℕ × ℕ} (hp : p ∈ P) :
      p.1 ∈ S ∧ p.2 ∈ S ∧ p.1 ≠ p.2 ∧ (p.1 - 1) / N = (p.2 - 1) / N := by
    obtain ⟨j, _, hj⟩ := mem_biUnion.1 hp
    obtain ⟨h₁, h₂, hne⟩ := mem_offDiag.1 hj
    obtain ⟨h₁S, h₁j⟩ := mem_filter.1 h₁
    obtain ⟨h₂S, h₂j⟩ := mem_filter.1 h₂
    exact ⟨h₁S, h₂S, hne, h₁j.trans h₂j.symm⟩
  let diff (p : ℕ × ℕ) : ℤ := (p.1 : ℤ) - p.2
  have bound : P.card ≤ (Icc (-(N : ℤ)) (N : ℤ)).card := by
    apply card_le_card_of_injOn diff
    · intro p hp
      change p ∈ P at hp
      obtain ⟨ha, hb, _, he⟩ := member hp
      have ha' := hpos _ ha
      have hb' := hpos _ hb
      have hma := Nat.mod_lt (p.1 - 1) hN
      have hmb := Nat.mod_lt (p.2 - 1) hN
      have hda := Nat.mod_add_div (p.1 - 1) N
      have hdb := Nat.mod_add_div (p.2 - 1) N
      rw [he] at hda
      simp only [coe_Icc, Set.mem_Icc, diff]
      omega
    · intro p hp q hq he
      change p ∈ P at hp
      change q ∈ P at hq
      obtain ⟨hpa, hpb, hne, _⟩ := member hp
      obtain ⟨hqa, hqb, _, _⟩ := member hq
      change (p.1 : ℤ) - p.2 = (q.1 : ℤ) - q.2 at he
      rcases hsid p.1 hpa q.1 hqa q.2 hqb p.2 hpb (by omega) with h | h
      · exact Prod.ext h.1 h.2.symm
      · exact (hne h.1).elim
  rw [Int.card_Icc] at bound
  have hP : P.card ≤ 2 * N + 1 := by omega
  have hsum : (∑ j ∈ range N, (pairs j).card) ≤ 2 * N + 1 := by
    rw [← card_biUnion pairwise]
    exact hP
  have hterm (j : ℕ) : (block j).card ^ 2 ≤ 1 + 2 * (pairs j).card := by
    let m := (block j).card
    have hm : m ≤ m * m := by
      cases m with
      | zero => simp
      | succ m => exact Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
    change m ^ 2 ≤ 1 + 2 * (block j).offDiag.card
    rw [offDiag_card]
    change m ^ 2 ≤ 1 + 2 * (m * m - m)
    have heq := Nat.sub_add_cancel hm
    nlinarith [sq_nonneg ((m : ℤ) - 1)]
  have hnat : (∑ j ∈ range N, (block j).card ^ 2) ≤ 7 * N := by
    calc
      _ ≤ ∑ j ∈ range N, (1 + 2 * (pairs j).card) := sum_le_sum (fun j _ => hterm j)
      _ = N + 2 * ∑ j ∈ range N, (pairs j).card := by
        simp [sum_add_distrib, mul_sum]
      _ ≤ _ := by omega
  exact_mod_cast hnat

private theorem dyadic_prefix_energy (a : ℕ → ℝ) (k : ℕ) :
    (∑ j ∈ range k, (∑ i ∈ range (2 ^ j), a i) ^ 2 / (2 : ℝ) ^ j) +
        4 * ((∑ i ∈ range (2 ^ k), a i) ^ 2 / (2 : ℝ) ^ k) ≤
      6 * ∑ i ∈ range (2 ^ k), a i ^ 2 := by
  induction k with
  | zero => simpa using (by nlinarith [sq_nonneg (a 0)] : 4 * a 0 ^ 2 ≤ 6 * a 0 ^ 2)
  | succ k ih =>
    have hpow : (2 : ℕ) ^ k ≤ 2 ^ (k + 1) := by
      rw [pow_succ]
      omega
    let p := ∑ i ∈ range (2 ^ k), a i
    let B := Ico (2 ^ k) (2 ^ (k + 1)) (α := ℕ)
    let b := ∑ i ∈ B, a i
    have hprefix : (∑ i ∈ range (2 ^ (k + 1)), a i) = p + b :=
      (sum_range_add_sum_Ico a hpow).symm
    have henergy : (∑ i ∈ range (2 ^ (k + 1)), a i ^ 2) =
        (∑ i ∈ range (2 ^ k), a i ^ 2) + ∑ i ∈ B, a i ^ 2 :=
      (sum_range_add_sum_Ico (fun i => a i ^ 2) hpow).symm
    have hcard : (B.card : ℝ) = 2 ^ k := by
      have hcard' : B.card = 2 ^ k := by
        simp only [B, Nat.card_Ico, pow_succ]
        omega
      exact_mod_cast hcard'
    have hCauchy : b ^ 2 ≤ (2 : ℝ) ^ k * ∑ i ∈ B, a i ^ 2 := by
      simpa only [b, hcard] using (sq_sum_le_card_mul_sum_sq (s := B) (f := a))
    have hquad : 2 * (p + b) ^ 2 ≤ 3 * p ^ 2 + 6 * b ^ 2 := by
      nlinarith [sq_nonneg (p - 2 * b)]
    have hd : (0 : ℝ) < 2 ^ k := by positivity
    have hstep : 4 * ((p + b) ^ 2 / (2 : ℝ) ^ (k + 1)) ≤
        3 * (p ^ 2 / (2 : ℝ) ^ k) + 6 * ∑ i ∈ B, a i ^ 2 := by
      rw [pow_succ]
      calc
        _ = (2 * (p + b) ^ 2) / (2 : ℝ) ^ k := by ring
        _ ≤ _ := (div_le_iff₀ hd).2 (by
          calc
            _ ≤ 3 * p ^ 2 + 6 * b ^ 2 := hquad
            _ ≤ _ := by
              rw [add_mul, mul_assoc, div_mul_cancel₀ _ hd.ne']
              linarith)
    rw [sum_range_succ, hprefix, henergy]
    change (_ + p ^ 2 / (2 : ℝ) ^ k) + _ ≤ _
    change _ + 4 * (p ^ 2 / (2 : ℝ) ^ k) ≤ _ at ih
    linarith

end OMA.SidonDyadic

set_option maxHeartbeats 950000 in
theorem OMA.solution : OMA.R_Erdos1191_erdos_1191_parts_i_R1.H1 := by
  classical
  intro R S hR hS hsid
  let N : ℕ := 2 ^ R
  have hN : 0 < N := by positivity
  have hpos (x : ℕ) (hx : x ∈ S) : 0 < x := (hS hx).1
  let a : ℕ → ℝ := fun i => (S.filter (fun x => (x - 1) / N = i)).card
  have henergy : (∑ j ∈ range N, a j ^ 2) ≤ 7 * N :=
    OMA.SidonDyadic.block_energy N S hN hpos hsid
  have hcount (k : ℕ) : (∑ i ∈ range (2 ^ k), a i) =
      ((S.filter (· ≤ 2 ^ (R + k))).card : ℝ) := by
    have eqfilter : (S.filter (fun x => (x - 1) / N ∈ range (2 ^ k))) =
        S.filter (· ≤ 2 ^ (R + k)) := by
      ext x
      simp only [mem_filter, mem_range]
      refine and_congr_right fun hx => ?_
      rw [Nat.div_lt_iff_lt_mul hN, pow_add]
      change x - 1 < 2 ^ k * 2 ^ R ↔ x ≤ 2 ^ R * 2 ^ k
      rw [mul_comm (2 ^ k) (2 ^ R)]
      have := hpos x hx
      omega
    have hcard := sum_card_fiberwise_eq_card_filter S (range (2 ^ k)) (fun x => (x - 1) / N)
    rw [eqfilter] at hcard
    unfold a
    rw [← Nat.cast_sum, hcard]
  let U (k : ℕ) : ℝ := (∑ i ∈ range (2 ^ k), a i) ^ 2 / (2 : ℝ) ^ k
  have hU (j : ℕ) : 0 ≤ U j := by
    exact div_nonneg (sq_nonneg _) (pow_nonneg (by norm_num) _)
  have hupper : (∑ j ∈ range (R + 1), U j) ≤ 42 * N := by
    have h := OMA.SidonDyadic.dyadic_prefix_energy a R
    change (∑ j ∈ range R, U j) + 4 * U R ≤ 6 * ∑ i ∈ range N, a i ^ 2 at h
    rw [sum_range_succ]
    linarith only [h, henergy, hU R]
  by_contra h
  have hlarge (j : ℕ) (hj : j ∈ range (R + 1)) : 256 * (N : ℝ) < R * U j := by
    have hjR : j ≤ R := by simpa using hj
    have hbad : 512 * 2 ^ (R + j) <
        (S.filter (· ≤ 2 ^ (R + j))).card ^ 2 * (R + j) :=
      lt_of_not_ge (fun hg => h ⟨R + j, ⟨by omega, by omega⟩, hg⟩)
    have hbad' : 512 * (2 : ℝ) ^ (R + j) <
        ((S.filter (· ≤ 2 ^ (R + j))).card : ℝ) ^ 2 * ((R : ℝ) + j) := by
      exact_mod_cast hbad
    have hd : (0 : ℝ) < 2 ^ j := by positivity
    have hmul : U j * (2 : ℝ) ^ j =
        ((S.filter (· ≤ 2 ^ (R + j))).card : ℝ) ^ 2 := by
      change (_ ^ 2 / (2 : ℝ) ^ j) * (2 : ℝ) ^ j = _
      rw [div_mul_cancel₀ _ hd.ne', hcount]
    have hnreal : (N : ℝ) = 2 ^ R := by exact_mod_cast (rfl : N = 2 ^ R)
    rw [pow_add, ← hnreal, ← hmul] at hbad'
    have hjreal : (j : ℝ) ≤ R := by exact_mod_cast hjR
    have hdenom : U j * ((R : ℝ) + j) ≤ 2 * (R * U j) := by
      nlinarith only [mul_le_mul_of_nonneg_left hjreal (hU j)]
    have hcancel : 512 * (N : ℝ) < U j * (R + j) := by
      apply (mul_lt_mul_iff_left₀ hd).1
      calc
        _ = 512 * ((N : ℝ) * (2 : ℝ) ^ j) := by ring
        _ < _ := hbad'
        _ = _ := by ring
    linarith only [hcancel, hdenom]
  have hlower : (∑ _j ∈ range (R + 1), 256 * (N : ℝ)) ≤
      ∑ j ∈ range (R + 1), (R : ℝ) * U j :=
    sum_le_sum fun j hj => (hlarge j hj).le
  rw [← mul_sum (range (R + 1)) U (R : ℝ)] at hlower
  simp only [sum_const, card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one] at hlower
  have hRreal : (0 : ℝ) ≤ R := by positivity
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  nlinarith only [hlower, hNreal, mul_le_mul_of_nonneg_left hupper hRreal,
    mul_nonneg hRreal hNreal.le]
