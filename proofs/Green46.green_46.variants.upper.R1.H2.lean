import OMAReductions.R_Green46_green_46_variants_upper_R1
import Mathlib

/-! Adapted from HJ van Veen, 30k30/scholia, Erdos687, commit
b072c89c3edac06521868e32cc15b2bc91bd8533, used under Apache-2.0.
The covering residues here are natural numbers, so the CRT solution
can be used before passing to the integral interval. -/

theorem OMA.solution : OMA.R_Green46_green_46_variants_upper_R1.H2 := by
  rintro x y ⟨a, cover⟩
  have nonzero : ∀ p ∈ Nat.primesLE x, id p ≠ 0 :=
    fun p hp => (Nat.prime_of_mem_primesLE hp).ne_zero
  have pairwise : Set.Pairwise (Nat.primesLE x : Set ℕ) (fun p q => (id p).Coprime (id q)) := by
    intro p hp q hq hpq
    exact (Nat.coprime_primes (Nat.prime_of_mem_primesLE hp)
      (Nat.prime_of_mem_primesLE hq)).2 hpq
  obtain ⟨A, hA⟩ := Nat.chineseRemainderOfFinset a id (Nat.primesLE x) nonzero pairwise
  refine ⟨1 - (A : ℤ), ?_⟩
  intro i hi hcop
  obtain ⟨p,hpx,hp,hcong⟩ := cover (i+1) (Finset.mem_Icc.mpr ⟨by omega,by omega⟩)
  have hAp : A ≡ a p [MOD p] := hA p (Nat.mem_primesLE.mpr ⟨hpx,hp⟩)
  have he : (A : ℤ) ≡ ((i+1 : ℕ) : ℤ) [ZMOD p] :=
    Int.natCast_modEq_iff.mpr (hAp.trans hcong.symm)
  have hd : (p : ℤ) ∣ 1 - (A : ℤ) + i := by
    convert he.dvd using 1 <;> push_cast <;> ring
  exact hp.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hcop
    (Int.natCast_dvd.mp hd) (hp.dvd_primorial_iff.mpr hpx))
