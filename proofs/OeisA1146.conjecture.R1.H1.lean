import OMAReductions.R_OeisA1146_conjecture_R1

/-! Classification of powers of two in Hasler's conjecture. Lean formalization by @Deldor14. -/

open OMA.Hasler

theorem OMA.solution : OMA.R_OeisA1146_conjecture_R1.H1 := by
  intro m
  constructor
  · intro h
    change (2^m)^4-1 ∣ 2^(2^m)-1 at h
    rw [← pow_mul, mersenneIff] at h
    have hd := (dvd_mul_right m 4).trans h
    obtain ⟨t,_,ht⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
    refine ⟨t,?_,ht⟩
    by_contra hlt
    have : t=0 ∨ t=1 := by omega
    rcases this with rfl|rfl <;> norm_num at ht <;> subst m <;> norm_num at h
  · rintro ⟨t,ht,rfl⟩
    exact OeisA1146.divisibility_fact t ht
