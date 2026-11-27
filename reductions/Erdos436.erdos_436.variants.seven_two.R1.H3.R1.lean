import OMAReductions.R_Erdos436_erdos_436_variants_seven_two_R1
import Mathlib

/-! The case vector in Table II of Brillhart, Lehmer and Lehmer prescribes
characters on primes. The power character multiplies along factorizations,
and the finite-field criterion detects seventh powers from its kernel. -/
namespace OMA.R_Erdos436_erdos_436_variants_seven_two_R1_H3_R1
open Erdos436 Finset

def H1 : Prop :=
  let w (q : ℕ) : ℕ := if q ∈ ([3,41] : List ℕ) then 0 else
    if q ∈ ([79,137,197,233,269,277,463,467,797,1709,2647,2903,15791] : List ℕ) then 2 else 1
  ∀ B : ℕ, ∃ p > B, p.Prime ∧ 7 ∣ p-1 ∧
    ∃ u : ZMod p, IsPrimitiveRoot u 7 ∧ ∀ q : ℕ, q.Prime → q ≤ 1649375 →
      (q : ZMod p)^((p-1)/7) = u^(w q)

def H2 : Prop := ∀ (p : ℕ), p.Prime → 7 ∣ p-1 → ∀ a : ZMod p, a ≠ 0 →
  ((∃ x : ZMod p, x^7=a) ↔ a^((p-1)/7)=1)

lemma character {p k : ℕ} (u : ZMod p) (w : ℕ → ℕ) (n : ℕ) (hn : 0<n)
    (h : ∀ q ∈ n.primeFactors, (q : ZMod p)^((p-1)/k) = u^(w q)) :
    (n : ZMod p)^((p-1)/k) = u^(∑ q ∈ n.primeFactors, n.factorization q*w q) := by
  have np : (n : ZMod p) = ∏ q ∈ n.primeFactors,(q : ZMod p)^(n.factorization q) := by
    simpa only [Nat.cast_prod,Nat.cast_pow] using congrArg (fun a : ℕ => (a : ZMod p)) (Nat.prod_primeFactors_pow_factorization hn.ne')
  rw [np,← Finset.prod_pow,← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_congr rfl
  intro q hq
  rw [← pow_mul,Nat.mul_comm,pow_mul,h _ hq,← pow_mul,Nat.mul_comm]

theorem main : H1 → H2 → OMA.R_Erdos436_erdos_436_variants_seven_two_R1.H3 := by
  intro realize criterion B
  let w (q : ℕ) : ℕ := if q ∈ ([3,41] : List ℕ) then 0 else
    if q ∈ ([79,137,197,233,269,277,463,467,797,1709,2647,2903,15791] : List ℕ) then 2 else 1
  obtain ⟨p,hpB,hp,hk,u,hu,h⟩ := realize (max B 1649375)
  refine ⟨p,by omega,hp,fun n hn hN => ?_⟩
  have hnz : (n : ZMod p) ≠ 0 := by
    intro he
    have := Nat.le_of_dvd hn ((ZMod.natCast_eq_zero_iff _ _).mp he)
    omega
  have he := character (k := 7) u w n hn fun q hq => h q (Nat.prime_of_mem_primeFactors hq)
    ((Nat.le_of_mem_primeFactors hq).trans hN)
  have hw (p : ℕ) : (w p : ZMod 7) = (if p ∈ ([3,41] : List ℕ) then 0 else
    if p ∈ ([79,137,197,233,269,277,463,467,797,1709,2647,2903,15791] : List ℕ) then 2 else 1) := by
    unfold w; split_ifs <;> norm_num
  rw [IsPowerResidue,and_iff_right hnz,criterion p hp hk _ hnz,he,hu.pow_eq_one_iff_dvd,
    ← ZMod.natCast_eq_zero_iff]
  simp only [Nat.cast_sum,Nat.cast_mul,hw]

end OMA.R_Erdos436_erdos_436_variants_seven_two_R1_H3_R1
