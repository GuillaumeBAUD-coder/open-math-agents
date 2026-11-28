import OMAReductions.R_Grimm_grimm_conjecture_R1

/-! Distinct prime powers in a family whose common divisors are controlled. -/

namespace A227864

/-- If a positive integer does not divide M, one of its prime exponents
exceeds the corresponding exponent in M. -/
theorem prime_power_missing {n M : ℕ} (hn : 0 < n) (hM : 0 < M) (missing : ¬ n ∣ M) :
    ∃ q, q.Prime ∧ q ∣ n ∧ ¬ q^(n.factorization q) ∣ M := by
  have no : ¬ ∀ q, n.factorization q ≤ M.factorization q :=
    fun h => missing ((Nat.factorization_le_iff_dvd hn.ne' hM.ne').mp h)
  obtain ⟨q,bad⟩ := not_forall.mp no
  have prime : q.Prime := by
    by_contra other
    simp [Nat.factorization_eq_zero_of_not_prime n other] at bad
  have once : q^1 ∣ n := (prime.pow_dvd_iff_le_factorization hn.ne').mpr (by omega)
  exact ⟨q,prime,by simpa using once,fun h => bad ((prime.pow_dvd_iff_le_factorization hM.ne').mp h)⟩

/-- If all pairwise common divisors at i divide Mᵢ < nᵢ, each nᵢ has
a different prime whose full power there divides no other member. -/
theorem exclusive_prime_factors {ι : Type*} (n M : ι → ℕ)
    (pos : ∀ i, 0 < M i) (big : ∀ i, M i < n i)
    (common : ∀ i j, i ≠ j → (n i).gcd (n j) ∣ M i) :
    ∃ f : ι → ℕ, Function.Injective f ∧ ∀ i, (f i).Prime ∧ f i ∣ n i ∧
      ∀ j, i ≠ j → ¬ (f i)^((n i).factorization (f i)) ∣ n j := by
  classical
  choose f prime div missing using fun i =>
    prime_power_missing ((pos i).trans (big i)) (pos i) (Nat.not_dvd_of_pos_of_lt (pos i) (big i))
  have alone (i j : ι) (ne : i ≠ j) (h : (f i)^((n i).factorization (f i)) ∣ n j) : False :=
    missing i ((Nat.dvd_gcd (Nat.ordProj_dvd (n i) (f i)) h).trans (common i j ne))
  refine ⟨f,?_,fun i => ⟨prime i,div i,alone i⟩⟩
  intro i j eq
  by_contra ne
  rcases le_total ((n i).factorization (f i)) ((n j).factorization (f i)) with le|le
  · exact alone i j ne ((pow_dvd_pow (f i) le).trans (Nat.ordProj_dvd (n j) (f i)))
  · apply alone j i (Ne.symm ne)
    rw [←eq]
    exact (pow_dvd_pow (f i) le).trans (Nat.ordProj_dvd (n i) (f i))

end A227864


/-! A distinct prime divisor at each position of a sufficiently short interval. -/

namespace GrimmInterval

/-- The starting point can be any integer above lcm(1,...,k-1). -/
theorem consecutive_factors (n k : ℕ) (large : Nat.lcmUpto (k-1) < n) :
    ∃ f : Fin k ↪ ℕ, ∀ i, (f i).Prime ∧ f i ∣ n+i := by
  let L := Nat.lcmUpto (k-1)
  have forward (i j : Fin k) (lt : i.val < j.val) : (n+i.val).gcd (n+j.val) ∣ L := by
    have both := Nat.dvd_sub (Nat.gcd_dvd_right (n+i.val) (n+j.val)) (Nat.gcd_dvd_left ..)
    rw [show n+j.val-(n+i.val)=j.val-i.val by omega] at both
    apply both.trans
    exact Finset.dvd_lcm (f:=id) (Finset.mem_Icc.mpr ⟨by omega,by have := j.isLt; omega⟩)
  have pair (i j : Fin k) (ne : i ≠ j) : (n+i.val).gcd (n+j.val) ∣ L := by
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne ne) with h|h
    · exact forward i j h
    · rw [Nat.gcd_comm]; exact forward j i h
  obtain ⟨f,inj,hf⟩ := A227864.exclusive_prime_factors (fun i : Fin k => n+i.val) (fun _ => L)
    (fun _ => Nat.lcmUpto_pos _) (fun i => large.trans_le (Nat.le_add_right ..)) pair
  exact ⟨⟨f,inj⟩,fun i => ⟨(hf i).1,(hf i).2.1⟩⟩

/-- The site's first step of Grimm's conjecture. -/
theorem three (n k : ℕ) (_hn : 1 ≤ n) (hk : 1 ≤ k) (limit : k ≤ 3)
    (composite : ∀ i : Fin k, (n+i).Composite) :
    ∃ f : Fin k ↪ ℕ, ∀ i, (f i).Prime ∧ f i ∣ n+i := by
  have comp : n.Composite := by simpa using composite ⟨0,hk⟩
  have gt : 2 < n := by
    have n2 := comp.1
    have ne : n ≠ 2 := fun eq => comp.2 (eq ▸ Nat.prime_two)
    omega
  apply consecutive_factors
  have bound : Nat.lcmUpto (k-1) ≤ 2 := by interval_cases k <;> decide +kernel
  omega

end GrimmInterval

theorem OMA.solution : OMA.R_Grimm_grimm_conjecture_R1.H1 := GrimmInterval.three
