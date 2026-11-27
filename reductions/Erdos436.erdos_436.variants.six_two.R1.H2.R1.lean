import OMAReductions.R_Erdos436_erdos_436_variants_six_two_R1
import Mathlib

/-! Lehmer, Lehmer and Mills, Pairs of consecutive power residues, Canadian J. Math. 15
(1963), 172–177. Negating the case vector of their formula (13) yields nonnegative
weights zero, one and two. The finite extremality test and the prime character
prescription are independent. The multiplicative calculation below extends the
character prescription on primes to composite integers. -/
namespace OMA.R_Erdos436_erdos_436_variants_six_two_R1_H2_R1
open Erdos436

def H1 : Prop :=
  let w (p : ℕ) : ℕ := if p ∈ ([3,43,61] : List ℕ) then 0 else
    if p ∈ ([71,101,331,733,1423,4877,5413,6043] : List ℕ) then 2 else 1
  ∀ n : ℕ, 1 ≤ n → n < 202124 →
    (n.primeFactorsList.map w).sum % 6 ≠ 0 ∨ ((n+1).primeFactorsList.map w).sum % 6 ≠ 0

def H2 : Prop :=
  let w (p : ℕ) : ℕ := if p ∈ ([3,43,61] : List ℕ) then 0 else
    if p ∈ ([71,101,331,733,1423,4877,5413,6043] : List ℕ) then 2 else 1
  ∀ B : ℕ, ∃ p > B, p.Prime ∧ 6 ∣ p-1 ∧
    ∃ u : ZMod p, IsPrimitiveRoot u 6 ∧
      ∀ q : ℕ, q.Prime → q ≤ 202124 → (q : ZMod p)^((p-1)/6) = u^(w q)

lemma char_prod {p k : ℕ} (u : ZMod p) (w : ℕ → ℕ) (l : List ℕ)
    (h : ∀ q ∈ l, (q : ZMod p)^((p-1)/k) = u^(w q)) :
    (l.prod : ZMod p)^((p-1)/k) = u^(l.map w).sum := by
  induction l with
  | nil => simp
  | cons q qs ih =>
    simp only [List.prod_cons,Nat.cast_mul,mul_pow,List.map_cons,List.sum_cons,pow_add]
    rw [h q (by simp),ih (fun a ha => h _ (by simp [ha]))]

lemma zero_weight {p k M : ℕ} (hp : p.Prime) (hk : k ∣ p-1)
    {u : ZMod p} (hu : IsPrimitiveRoot u k) (w : ℕ → ℕ)
    (h : ∀ q : ℕ, q.Prime → q ≤ M → (q : ZMod p)^((p-1)/k) = u^(w q))
    {n : ℕ} (hn : 0 < n) (hle : n ≤ M) (hr : IsPowerResidue k p n) (hk0 : 0 < k) :
    (n.primeFactorsList.map w).sum % k = 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  have he := char_prod u w n.primeFactorsList fun q hq => h q
    (Nat.prime_of_mem_primeFactorsList hq) ((Nat.le_of_dvd hn (Nat.dvd_of_mem_primeFactorsList hq)).trans hle)
  rw [Nat.prod_primeFactorsList hn.ne'] at he
  obtain ⟨hne,x,hx⟩ := hr
  have xne : x ≠ 0 := by rintro rfl; simp [hk0.ne'] at hx; exact hne hx.symm
  apply Nat.mod_eq_zero_of_dvd
  apply hu.dvd_of_pow_eq_one
  rw [← he,← hx,← pow_mul,Nat.mul_div_cancel' hk]
  exact ZMod.pow_card_sub_one_eq_one xne

theorem main : H1 → H2 → OMA.R_Erdos436_erdos_436_variants_six_two_R1.H2 := by
  intro check realize B
  obtain ⟨p,hpB,hp,hk,u,hu,hchar⟩ := realize B
  refine ⟨p,hpB,hp,?_⟩
  apply le_iInf₂
  rintro n ⟨hn,allpow⟩
  suffices 202124 ≤ n by exact_mod_cast this
  by_contra! lt
  have a := zero_weight hp hk hu _ hchar hn lt.le (by simpa using allpow 0 (by decide)) (by decide)
  have b := zero_weight hp hk hu _ hchar (show 0 < n+1 by omega) (by omega) (allpow 1 (by decide)) (by decide)
  rcases check n hn lt with h|h
  · exact h a
  · exact h b

end OMA.R_Erdos436_erdos_436_variants_six_two_R1_H2_R1
