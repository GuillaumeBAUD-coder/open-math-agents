import OMAStatements.S_oeis_a046385
import Mathlib

-- A sparse palindromic prime copies each seed into five disjoint decimal blocks.
-- In particular the missing counts 14, 17, and 21 all occur.
namespace PalindromeWitness

lemma fast_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : a^n = npowBinRec n a := by
  induction n with
  | zero => rw [pow_zero,npowBinRec_zero]
  | succ n ih => rw [pow_succ,npowBinRec_succ,ih]

lemma factor_mem {q : ℕ} (hq : q.Prime) (fs : List ℕ) (good : ∀ r ∈ fs, r.Prime)
    (divides : q ∣ fs.prod) : q ∈ fs := by
  induction fs with
  | nil => simp at divides; exact (hq.ne_one divides).elim
  | cons r fs ih =>
    rcases hq.dvd_mul.mp divides with h | h
    · have eq := (Nat.prime_dvd_prime_iff_eq hq (good r List.mem_cons_self)).mp h
      simp [eq]
    · exact List.mem_cons_of_mem r (ih (fun s hs => good s (List.mem_cons_of_mem r hs)) h)

lemma lucas_list (p a : ℕ) (factors : List ℕ) (fac : factors.prod = p-1)
    (primes : ∀ q ∈ factors, q.Prime)
    (unit : npowBinRec (p-1) (a : ZMod p) = 1)
    (orders : ∀ q ∈ factors, npowBinRec ((p-1)/q) (a : ZMod p) ≠ 1) : p.Prime := by
  apply lucas_primality p (a : ZMod p) (by rwa [fast_pow])
  intro q hq hdiv
  rw [← fac] at hdiv
  have mem := factor_mem hq factors primes hdiv
  rw [fast_pow]
  exact orders q mem

private lemma prime_195353 : Nat.Prime 195353 := by
  apply lucas_list 195353 3 [2, 2, 2, 24419] (by decide +kernel)
  · intro q h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl | rfl | rfl | rfl
    all_goals first | norm_num1
  · decide +kernel
  · intro q h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl | rfl | rfl | rfl <;> decide +kernel

private lemma prime_20316713 : Nat.Prime 20316713 := by
  apply lucas_list 20316713 5 [2, 2, 2, 13, 195353] (by decide +kernel)
  · intro q h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl
    all_goals first | exact prime_195353 | norm_num1
  · decide +kernel
  · intro q h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl <;> decide +kernel

private lemma prime_5030702572783 : Nat.Prime 5030702572783 := by
  apply lucas_list 5030702572783 3 [2, 3, 41269, 20316713] (by decide +kernel)
  · intro q h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl | rfl | rfl | rfl
    all_goals first | exact prime_20316713 | norm_num1
  · decide +kernel
  · intro q h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl | rfl | rfl | rfl <;> decide +kernel

private lemma prime_3454901 : Nat.Prime 3454901 := by
  apply lucas_list 3454901 2 [2, 2, 5, 5, 34549] (by decide +kernel)
  · intro q h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl
    all_goals first | norm_num1
  · decide +kernel
  · intro q h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl <;> decide +kernel

private lemma prime_428143 : Nat.Prime 428143 := by
  apply lucas_list 428143 3 [2, 3, 11, 13, 499] (by decide +kernel)
  · intro q h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl
    all_goals first | norm_num1
  · decide +kernel
  · intro q h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl <;> decide +kernel

private lemma prime_6850289 : Nat.Prime 6850289 := by
  apply lucas_list 6850289 3 [2, 2, 2, 2, 428143] (by decide +kernel)
  · intro q h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl
    all_goals first | exact prime_428143 | norm_num1
  · decide +kernel
  · intro q h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl <;> decide +kernel

private lemma prime_9514162267188379 : Nat.Prime 9514162267188379 := by
  apply lucas_list 9514162267188379 2 [2, 3, 67, 3454901, 6850289] (by decide +kernel)
  · intro q h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl
    all_goals first | exact prime_3454901 | exact prime_6850289 | norm_num1
  · decide +kernel
  · intro q h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl <;> decide +kernel

private lemma prime_10000000000001000000000100000000010000000000001 : Nat.Prime 10000000000001000000000100000000010000000000001 := by
  apply lucas_list 10000000000001000000000100000000010000000000001 6 [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 17, 1229, 5030702572783, 9514162267188379] (by decide +kernel)
  · intro q h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact prime_5030702572783 | exact prime_9514162267188379 | norm_num1
  · decide +kernel
  · intro q h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel


private lemma copy_seed (n seed : ℕ)
    (hseed : seed ≠ 0) (count : seed.primeFactorsList.length = n)
    (pal : (Nat.digits 10 (seed*10000000000001000000000100000000010000000000001)).Palindrome)
    (small : ∀ r ∈ seed.primeFactorsList, (Nat.digits 10 r).Palindrome) :
    seed*10000000000001000000000100000000010000000000001 ∈ OMA.S_oeis_a046385.palindromesWithFactorCount (n+1) := by
  have prime := prime_10000000000001000000000100000000010000000000001
  have perm := Nat.perm_primeFactorsList_mul hseed prime.ne_zero
  rw [Nat.primeFactorsList_prime prime] at perm
  refine ⟨Nat.mul_pos (Nat.pos_of_ne_zero hseed) prime.pos,pal,?_,?_⟩
  · simpa only [List.length_append,List.length_singleton,count] using perm.length_eq
  · intro r hr
    have m := perm.mem_iff.mp hr
    rw [List.mem_append,List.mem_singleton] at m
    rcases m with h | rfl
    · exact small r h
    · exact List.Palindrome.of_reverse_eq (by decide +kernel)

open OMA.S_oeis_a046385

lemma witness_14 : 29777920000002977792000297779200029777920000002977792 ∈ palindromesWithFactorCount 14 := by
  apply copy_seed 13 2977792 (by decide) (by decide +kernel)
  · exact List.Palindrome.of_reverse_eq (by decide +kernel)
  · intro r h
    have test : (2977792 : ℕ).primeFactorsList.all (fun t => decide ((Nat.digits 10 t).reverse = Nat.digits 10 t)) = true := by decide +kernel
    exact List.Palindrome.of_reverse_eq (of_decide_eq_true (List.all_eq_true.mp test r h))

lemma witness_17 : 409559040000040955904004095590400409559040000040955904 ∈ palindromesWithFactorCount 17 := by
  apply copy_seed 16 40955904 (by decide) (by decide +kernel)
  · exact List.Palindrome.of_reverse_eq (by decide +kernel)
  · intro r h
    have test : (40955904 : ℕ).primeFactorsList.all (fun t => decide ((Nat.digits 10 t).reverse = Nat.digits 10 t)) = true := by decide +kernel
    exact List.Palindrome.of_reverse_eq (of_decide_eq_true (List.all_eq_true.mp test r h))

lemma witness_21 : 6777077760000677707776067770777606777077760000677707776 ∈ palindromesWithFactorCount 21 := by
  apply copy_seed 20 677707776 (by decide) (by decide +kernel)
  · exact List.Palindrome.of_reverse_eq (by decide +kernel)
  · intro r h
    have test : (677707776 : ℕ).primeFactorsList.all (fun t => decide ((Nat.digits 10 t).reverse = Nat.digits 10 t)) = true := by decide +kernel
    exact List.Palindrome.of_reverse_eq (of_decide_eq_true (List.all_eq_true.mp test r h))

end PalindromeWitness

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a046385.main) := by
  intro h
  let s := OMA.S_oeis_a046385.palindromesWithFactorCount 17
  have nonempty : s.Nonempty := ⟨409559040000040955904004095590400409559040000040955904,PalindromeWitness.witness_17⟩
  have least : IsLeast s (sInf s) := ⟨Nat.sInf_mem nonempty,fun _ hm => Nat.sInf_le hm⟩
  have bad := (h 17 (sInf s)).mp least
  simp [OMA.S_oeis_a046385.knownTerms] at bad
