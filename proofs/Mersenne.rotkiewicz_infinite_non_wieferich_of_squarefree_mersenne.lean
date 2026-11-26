import FormalConjectures.Wikipedia.Mersenne
import Mathlib.NumberTheory.Multiplicity

/-! A Wieferich prime dividing a Mersenne number divides it twice, by lifting
the exponent. Thus every squarefree Mersenne number is a product of distinct
non-Wieferich primes. -/

namespace OMA.MersenneProof

lemma not_wieferich {n p : ℕ} (hs : Squarefree (mersenne n)) (hp : p.Prime)
    (hd : p ∣ mersenne n) : ¬ IsWieferichPrime p := by
  intro hw
  have hne : p ≠ 2 := by
    rintro rfl
    exact (by decide : ¬ IsWieferichPrime 2) hw
  have hodd := hp.odd_of_ne_two hne
  have hnd : ¬ p ∣ 2 ^ n := fun h => hne
    ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
  have hpred : ¬ p ∣ p-1 := Nat.not_dvd_of_pos_of_lt (by have := hp.two_le; omega) (by have := hp.pos; omega)
  have lift := Nat.emultiplicity_pow_sub_pow hp hodd (y := 1) (x := 2^n) hd hnd (p-1)
  rw [one_pow, emultiplicity_eq_zero.mpr hpred, add_zero] at lift
  have raised := (hw.pow_modEq (by decide : 2 ≠ 0)).pow n
  rw [one_pow, ← pow_mul, Nat.mul_comm (p-1) n, pow_mul] at raised
  have hsquare : p^2 ∣ (2^n)^(p-1) - 1 := raised.symm.dvd'
  rw [pow_dvd_iff_le_emultiplicity, lift, ← pow_dvd_iff_le_emultiplicity] at hsquare
  exact (Nat.squarefree_iff_prime_squarefree.mp hs p hp) (by simpa [pow_two, mersenne] using hsquare)

end OMA.MersenneProof

theorem OMA.solution : type_of% @Mersenne.rotkiewicz_infinite_non_wieferich_of_squarefree_mersenne := by
  classical
  intro hinf hfin
  let T := hfin.toFinset
  let B := ∏ p ∈ T, p
  have hB : 0 < B := by
    apply Finset.prod_pos
    intro p hp
    have h := hfin.mem_toFinset.mp hp
    exact h.1.pos
  obtain ⟨n,hs,hn⟩ := hinf.exists_gt B
  have incl : (mersenne n).primeFactors ⊆ T := by
    intro p hp
    obtain ⟨hprime,hd,_⟩ := Nat.mem_primeFactors.mp hp
    exact hfin.mem_toFinset.mpr ⟨hprime, OMA.MersenneProof.not_wieferich hs hprime hd⟩
  have hdiv := Finset.prod_dvd_prod_of_subset _ _ (fun p : ℕ => p) incl
  rw [Nat.prod_primeFactors_of_squarefree hs] at hdiv
  have hle := Nat.le_of_dvd hB hdiv
  have hpow := Nat.lt_two_pow_self (n := n)
  unfold mersenne at hle
  omega
