import FormalConjectures.ErdosProblems.«366»
import Mathlib

/-! The two endpoints can be expressed as products of a cube, a fourth power,
and a fifth power. A finite arithmetic certificate excludes all first endpoints
up to 100000. The residual witness is a polynomial equation in positive integers. -/

open Finset

namespace OMA.R_Erdos366_erdos_366_variants_weaker_R2

def H1 : Prop :=
  ∃ a b c d e f : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧ 0 < e ∧ 0 < f ∧
    100000 < a^3*b^4*c^5 ∧ a^3*b^4*c^5 + 1 = d^3*e^4*f^5

def H2 : Prop :=
  ∀ a b c : ℕ, 0 < a → 0 < b → 0 < c → Nat.Full 3 (a^3*b^4*c^5)

section Proof

/-- Separate prime exponents by their residues modulo three. -/
private theorem cube_full_factors {n : ℕ} (hn : 0 < n) (hf : Nat.Full 3 n) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ n = a^3*b^4*c^5 := by
  let e := n.factorization
  let A (p : ℕ) := p ^ (e p / 3 - if e p % 3 = 0 then 0 else 1)
  let B (p : ℕ) := if e p % 3 = 1 then p else 1
  let C (p : ℕ) := if e p % 3 = 2 then p else 1
  let P := n.primeFactors
  have hp (p : ℕ) (h : p ∈ P) := (Nat.mem_primeFactors.mp h).1
  have hpos (p : ℕ) (h : p ∈ P) := (hp p h).pos
  have hA : 0 < ∏ p ∈ P, A p := Finset.prod_pos (fun p h => pow_pos (hpos p h) _)
  have hB : 0 < ∏ p ∈ P, B p := Finset.prod_pos (fun p h => by dsimp [B]; split; exact hpos p h; decide)
  have hC : 0 < ∏ p ∈ P, C p := Finset.prod_pos (fun p h => by dsimp [C]; split; exact hpos p h; decide)
  refine ⟨∏ p ∈ P,A p,∏ p ∈ P,B p,∏ p ∈ P,C p,hA,hB,hC,?_⟩
  rw [← prod_pow,← prod_pow,← prod_pow,← prod_mul_distrib,← prod_mul_distrib]
  conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hn.ne']
  change (∏ p ∈ P,p ^ e p) = _
  apply prod_congr rfl
  intro p hpP
  have he : 3 ≤ e p := ((hp p hpP).pow_dvd_iff_le_factorization hn.ne').mp (hf p hpP)
  have hnorm (j : ℕ) (hj : j < 3) (h : e p % 3 = j) :
      e p = (e p/3 - if j=0 then 0 else 1)*3 +
        (if j=1 then 4 else 0) + (if j=2 then 5 else 0) := by
    interval_cases j <;> simp_all <;> omega
  have hmod : e p % 3 < 3 := Nat.mod_lt _ (by norm_num)
  by_cases hz : e p % 3 = 0
  · have h : (e p/3)*3 = e p := by omega
    simp [A,B,C,hz,← pow_mul,h]
  by_cases ho : e p % 3 = 1
  · simp [A,B,C,hz,ho,show e p % 3 ≠ 2 by omega,← pow_mul,← pow_add]
    congr 1
    have h := hnorm _ (by norm_num) ho
    simp at h
    omega
  have ht : e p % 3 = 2 := by omega
  simp [A,B,C,hz,ho,ht,← pow_mul,← pow_add]
  congr 1
  have h := hnorm _ (by norm_num) ht
  simp at h
  omega

private def power_table : List ℕ :=
  (List.range 10).flatMap fun c =>
    (List.range 17).flatMap fun b =>
      (List.range 46).filterMap fun a =>
        let v := (a+1)^3*(b+1)^4*(c+1)^5
        if v ≤ 100001 then some v else none

private theorem table_contains {n : ℕ} (hn : 0 < n) (hb : n ≤ 100001) (h : Nat.Full 3 n) :
    n ∈ power_table := by
  obtain ⟨a,b,c,ha,hb',hc,he⟩ := cube_full_factors hn h
  have h1 : a^3 ≤ n := by
    rw [he]
    have hC : 0 < c^5 := pow_pos hc _
    have hB : 0 < b^4 := pow_pos hb' _
    exact (Nat.le_mul_of_pos_right _ hB).trans (Nat.le_mul_of_pos_right _ hC)
  have h2 : b^4 ≤ n := by
    rw [he,mul_comm (a^3)]
    exact (Nat.le_mul_of_pos_right _ (pow_pos ha _)).trans (Nat.le_mul_of_pos_right _ (pow_pos hc _))
  have h3 : c^5 ≤ n := by
    rw [he,mul_comm]
    exact Nat.le_mul_of_pos_right _ (mul_pos (pow_pos ha _) (pow_pos hb' _))
  have haR : a ≤ 46 := by
    by_contra! h
    have hh : 47^3 ≤ a^3 := Nat.pow_le_pow_left h 3
    omega
  have hbR : b ≤ 17 := by
    by_contra! h
    have hh : 18^4 ≤ b^4 := Nat.pow_le_pow_left h 4
    omega
  have hcR : c ≤ 10 := by
    by_contra! h
    have hh : 11^5 ≤ c^5 := Nat.pow_le_pow_left h 5
    omega
  unfold power_table
  apply List.mem_flatMap.mpr
  refine ⟨c-1,List.mem_range.mpr (by omega),?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨b-1,List.mem_range.mpr (by omega),?_⟩
  apply List.mem_filterMap.mpr
  refine ⟨a-1,List.mem_range.mpr (by omega),?_⟩
  simp only [Nat.sub_add_cancel (show 1 ≤ a by omega),Nat.sub_add_cancel (show 1 ≤ b by omega),
    Nat.sub_add_cancel (show 1 ≤ c by omega),← he,if_pos hb]

private def explicit_table : List ℕ :=
  [1, 8, 27, 64, 125, 216, 343, 512, 729, 1000, 1331, 1728,
   2197, 2744, 3375, 4096, 4913, 5832, 6859, 8000, 9261, 10648, 12167, 13824,
   15625, 17576, 19683, 21952, 24389, 27000, 29791, 32768, 35937, 39304, 42875, 46656,
   50653, 54872, 59319, 64000, 68921, 74088, 79507, 85184, 91125, 97336, 16, 128,
   432, 1024, 2000, 3456, 5488, 8192, 11664, 16000, 21296, 27648, 35152, 43904,
   54000, 65536, 78608, 93312, 81, 648, 2187, 5184, 10125, 17496, 27783, 41472,
   59049, 81000, 256, 2048, 6912, 16384, 32000, 55296, 87808, 625, 5000, 16875,
   40000, 78125, 1296, 10368, 34992, 82944, 2401, 19208, 64827, 4096, 32768, 6561,
   52488, 10000, 80000, 14641, 20736, 28561, 38416, 50625, 65536, 83521, 32, 256,
   864, 2048, 4000, 6912, 10976, 16384, 23328, 32000, 42592, 55296, 70304, 87808,
   512, 4096, 13824, 32768, 64000, 2592, 20736, 69984, 8192, 65536, 20000, 41472,
   76832, 243, 1944, 6561, 15552, 30375, 52488, 83349, 3888, 31104, 19683, 62208,
   1024, 8192, 27648, 65536, 16384, 82944, 3125, 25000, 84375, 50000, 7776, 62208,
   16807, 32768, 59049, 100000]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem table_eq : power_table = explicit_table := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem no_adjacent_in_table : ∀ n ∈ explicit_table, n+1 ∉ explicit_table := by
  decide +kernel

private theorem no_small_pair :
    ¬ ∃ n : ℕ, 0 < n ∧ n ≤ 100000 ∧ Nat.Full 3 n ∧ Nat.Full 3 (n+1) := by
  rintro ⟨n,hn,hB,h,h'⟩
  have ha := table_contains hn (by omega) h
  have hb := table_contains (by omega) (by omega) h'
  rw [table_eq] at ha hb
  exact no_adjacent_in_table n ha hb


/-- Every potential pair gives a witness for the residual arithmetic equation. -/
theorem specialized_witness :
    (∃ n : ℕ, 0 < n ∧ Nat.Full 3 n ∧ Nat.Full 3 (n+1)) → H1 := by
  rintro ⟨n,hn,h,h'⟩
  have hN : 100000 < n := by
    by_contra! hle
    exact no_small_pair ⟨n,hn,hle,h,h'⟩
  obtain ⟨a,b,c,ha,hb,hc,he⟩ := cube_full_factors hn h
  obtain ⟨d,e,f,hd,he',hf,heq⟩ := cube_full_factors (by omega) h'
  exact ⟨a,b,c,d,e,f,ha,hb,hc,hd,he',hf,he ▸ hN,he ▸ heq⟩

theorem main : H1 → H2 → type_of% @Erdos366.erdos_366.variants.weaker := by
  rintro ⟨a,b,c,d,e,f,ha,hb,hc,hd,he,hf,hbound,hEq⟩ hfull
  refine ⟨a^3*b^4*c^5,by omega,hfull a b c ha hb hc,?_⟩
  rw [hEq]
  exact hfull d e f hd he hf

end Proof

end OMA.R_Erdos366_erdos_366_variants_weaker_R2
