import OMAStatements.S_oeis_a055231

-- Problem: A055231, a(nm) = a(n) a(m) / (gcd(n, a(m)) gcd(m, a(n))) for the powerfree part a.
-- Credit: @ShoQo
-- Proof: v_p(a(n)) = [v_p(n) = 1]; compare p-adic valuations of both sides prime by prime,
-- with a case split on e = v_p(n) and f = v_p(m).

open OMA.S_oeis_a055231

namespace OMA_A055231_Proof

lemma a_ne_zero (n : ℕ) : a n ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun _ hp =>
    (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).ne_zero

lemma factorization_a (n p : ℕ) :
    (a n).factorization p = if n.factorization p = 1 then 1 else 0 := by
  unfold a
  rw [Nat.factorization_prod fun x hx =>
    (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hx).1).ne_zero,
    Finsupp.finsetSum_apply]
  rw [Finset.sum_congr rfl fun x hx => by
    rw [(Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hx).1).factorization,
      Finsupp.single_apply]]
  rw [Finset.sum_ite_eq']
  have : p ∈ n.primeFactors.filter (fun p => n.factorization p = 1) ↔ n.factorization p = 1 := by
    rw [Finset.mem_filter, ← Nat.support_factorization, Finsupp.mem_support_iff]
    constructor
    · exact fun h => h.2
    · intro h; exact ⟨by omega, h⟩
  simp only [this]

end OMA_A055231_Proof

open OMA_A055231_Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a055231.main := by
  intro n m hn hm
  have hg1 : Nat.gcd n (a m) ≠ 0 := Nat.gcd_ne_zero_left hn.ne'
  have hg2 : Nat.gcd m (a n) ≠ 0 := Nat.gcd_ne_zero_left hm.ne'
  symm
  refine Nat.div_eq_of_eq_mul_left (Nat.pos_of_ne_zero (mul_ne_zero hg1 hg2)) ?_
  refine Nat.eq_of_factorization_eq (mul_ne_zero (a_ne_zero n) (a_ne_zero m))
    (mul_ne_zero (a_ne_zero _) (mul_ne_zero hg1 hg2)) fun p => ?_
  rw [Nat.factorization_mul (a_ne_zero n) (a_ne_zero m),
    Nat.factorization_mul (a_ne_zero _) (mul_ne_zero hg1 hg2),
    Nat.factorization_mul hg1 hg2,
    Nat.factorization_gcd hn.ne' (a_ne_zero m), Nat.factorization_gcd hm.ne' (a_ne_zero n)]
  simp only [Finsupp.add_apply, Finsupp.inf_apply, factorization_a,
    Nat.factorization_mul hn.ne' hm.ne']
  -- compare p-adic valuations case by case on e = v_p(n), f = v_p(m)
  split_ifs <;> simp_all <;> omega

