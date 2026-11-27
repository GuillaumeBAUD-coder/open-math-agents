import FormalConjectures.ErdosProblems.«983»

-- Problem: Erdős Problem 983 — i
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/983.lean:86 (declaration Erdos983.erdos_983.parts.i)
-- Credit: @OrangeHeadz (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-!
Proof outline (the construction described in the upstream docstring).

* `pomerance`: there are arbitrarily large `c` with `p_{c-i} * p_{c+i} < p_c ^ 2` for all
  `1 ≤ i ≤ c` (primes indexed from zero).  Take `c` to be the last maximiser of
  `log p_n - ε n`; the maximum exists because `p_n` grows polynomially (Chebyshev).
* `path_lower`: a path of `m + 1` distinct primes whose adjacent products are at most `n` gives a
  set `A` of `π n + 1` integers (the edge products together with all primes up to `n` that are
  not interior vertices) on which every set of at most `m` primes has no more smooth elements
  than its own size, so `f (π n + 1) n ≥ m + 1`.
* For `n = p_c ^ 2 - 1` the path `p_{2c}, p_0, p_{2c-1}, p_1, …, p_c` gives
  `f (π n + 1) n ≥ 2 c + 1 = 2 π (√n) + 1`, so the difference is negative infinitely often.
-/

namespace OMA983

open Finset

/-- `π n` is admissible in the definition of `f`, so the defining set is nonempty. -/
theorem mem_set (k n : ℕ) (hk : Nat.primeCounting n < k) :
    ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 n → A.card = k →
      ∃ S : Finset ℕ, S.card = Nat.primeCounting n ∧ (∀ p ∈ S, p.Prime) ∧
        Nat.primeCounting n < Erdos983.numSmooth A S := by
  intro A hA hAk
  refine ⟨(Finset.range (n + 1)).filter Nat.Prime, ?_, ?_, ?_⟩
  · simp [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
  · exact fun p hp => (Finset.mem_filter.mp hp).2
  · have hAll : A.filter (fun a => ∀ p ∈ a.primeFactors,
        p ∈ (Finset.range (n + 1)).filter Nat.Prime) = A := by
      refine Finset.filter_true_of_mem fun a ha p hp => ?_
      have ha' := Finset.mem_Icc.mp (hA ha)
      have hp' := Nat.mem_primeFactors.mp hp
      have hpa : p ≤ a := Nat.le_of_dvd (by omega) hp'.2.1
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hp'.1⟩
    rw [Erdos983.numSmooth, hAll, hAk]
    exact hk

/-- A set `A` on which every small set of primes has few smooth elements bounds `f` below. -/
theorem f_ge (k n R : ℕ) (hk : Nat.primeCounting n < k) (A : Finset ℕ)
    (hA : A ⊆ Finset.Icc 1 n) (hAk : A.card = k)
    (hbad : ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) → S.card < R →
      Erdos983.numSmooth A S ≤ S.card) : R ≤ Erdos983.f k n := by
  have hne : {r : ℕ | ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 n → A.card = k →
      ∃ S : Finset ℕ, S.card = r ∧ (∀ p ∈ S, p.Prime) ∧ r < Erdos983.numSmooth A S}.Nonempty :=
    ⟨Nat.primeCounting n, mem_set k n hk⟩
  have hmem : Erdos983.f k n ∈ {r : ℕ | ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 n → A.card = k →
      ∃ S : Finset ℕ, S.card = r ∧ (∀ p ∈ S, p.Prime) ∧ r < Erdos983.numSmooth A S} :=
    Nat.sInf_mem hne
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨S, hS, hprime, hgt⟩ := hmem A hA hAk
  have := hbad S hprime (by rw [hS]; exact hlt)
  omega

/-- The path construction: a path of `m + 1` distinct primes whose adjacent products are `≤ n`
forces `f (π n + 1) n ≥ m + 1`. -/
theorem path_lower (n m : ℕ) (v : ℕ → ℕ) (hm : 1 ≤ m)
    (hprime : ∀ j, j ≤ m → (v j).Prime)
    (hinj : ∀ i j, i ≤ m → j ≤ m → v i = v j → i = j)
    (hedge : ∀ j, j < m → v j * v (j + 1) ≤ n) :
    m + 1 ≤ Erdos983.f (Nat.primeCounting n + 1) n := by
  classical
  -- the pieces of the set
  set E : Finset ℕ := (Finset.range m).image (fun j => v j * v (j + 1)) with hE
  set I : Finset ℕ := (Finset.Ico 1 m).image v with hI
  set Pn : Finset ℕ := (Finset.range (n + 1)).filter Nat.Prime with hPn
  set Q : Finset ℕ := Pn \ I with hQ
  have hPncard : Pn.card = Nat.primeCounting n := by
    simp [hPn, Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
  -- edges are injective
  have hEinj : Set.InjOn (fun j => v j * v (j + 1)) (Finset.range m : Set ℕ) := by
    intro i hi j hj hij
    have hi' : i < m := Finset.mem_range.mp (Finset.mem_coe.mp hi)
    have hj' : j < m := Finset.mem_range.mp (Finset.mem_coe.mp hj)
    simp only at hij
    have pi0 := hprime i (by omega)
    have pi1 := hprime (i + 1) (by omega)
    have pj0 := hprime j (by omega)
    have pj1 := hprime (j + 1) (by omega)
    have d0 : v i ∣ v j * v (j + 1) := ⟨v (i + 1), hij.symm⟩
    have d1 : v (i + 1) ∣ v j * v (j + 1) := ⟨v i, by rw [← hij]; ring⟩
    have c0 : i = j ∨ i = j + 1 := by
      rcases pi0.dvd_mul.mp d0 with h | h
      · exact Or.inl (hinj i j (by omega) (by omega) ((Nat.prime_dvd_prime_iff_eq pi0 pj0).mp h))
      · exact Or.inr (hinj i (j + 1) (by omega) (by omega)
          ((Nat.prime_dvd_prime_iff_eq pi0 pj1).mp h))
    have c1 : i + 1 = j ∨ i + 1 = j + 1 := by
      rcases pi1.dvd_mul.mp d1 with h | h
      · exact Or.inl (hinj (i + 1) j (by omega) (by omega)
          ((Nat.prime_dvd_prime_iff_eq pi1 pj0).mp h))
      · exact Or.inr (hinj (i + 1) (j + 1) (by omega) (by omega)
          ((Nat.prime_dvd_prime_iff_eq pi1 pj1).mp h))
    omega
  have hEcard : E.card = m := by
    rw [hE, Finset.card_image_of_injOn hEinj, Finset.card_range]
  have hIcard : I.card ≤ m - 1 := by
    have := Finset.card_image_le (s := Finset.Ico 1 m) (f := v)
    rw [Nat.card_Ico] at this
    exact this
  have hQcard : Nat.primeCounting n - (m - 1) ≤ Q.card := by
    have h1 := Finset.le_card_sdiff I Pn
    rw [hPncard] at h1
    have h2 : Q.card = (Pn \ I).card := by rw [hQ]
    omega
  have hEQ : Disjoint E Q := by
    rw [Finset.disjoint_left]
    intro a haE haQ
    rw [hE, Finset.mem_image] at haE
    obtain ⟨j, hj, rfl⟩ := haE
    have hj' := Finset.mem_range.mp hj
    have hp : (v j * v (j + 1)).Prime := by
      rw [hQ, Finset.mem_sdiff, hPn, Finset.mem_filter] at haQ
      exact haQ.1.2
    exact Nat.not_prime_mul (hprime j (by omega)).one_lt.ne'
      (hprime (j + 1) (by omega)).one_lt.ne' hp
  -- the big set
  have hbig : Nat.primeCounting n + 1 ≤ (E ∪ Q).card := by
    rw [Finset.card_union_of_disjoint hEQ, hEcard]
    omega
  have hsub0 : E ∪ Q ⊆ Finset.Icc 1 n := by
    intro a ha
    rw [Finset.mem_union] at ha
    rw [Finset.mem_Icc]
    rcases ha with ha | ha
    · rw [hE, Finset.mem_image] at ha
      obtain ⟨j, hj, rfl⟩ := ha
      have hj' := Finset.mem_range.mp hj
      have p0 := (hprime j (by omega)).pos
      have p1 := (hprime (j + 1) (by omega)).pos
      exact ⟨Nat.mul_pos p0 p1, hedge j hj'⟩
    · rw [hQ, Finset.mem_sdiff, hPn, Finset.mem_filter, Finset.mem_range] at ha
      have := ha.1.2.pos
      omega
  obtain ⟨A, hAsub, hAcard⟩ := Finset.exists_subset_card_eq hbig
  apply f_ge (Nat.primeCounting n + 1) n (m + 1) (by omega) A (hAsub.trans hsub0) hAcard
  intro S hSprime hScard
  -- some path vertex is missing from `S`
  obtain ⟨t, htm, htS⟩ : ∃ t, t ≤ m ∧ v t ∉ S := by
    by_contra hcon
    push Not at hcon
    have hsub : (Finset.range (m + 1)).image v ⊆ S := by
      intro a ha
      rw [Finset.mem_image] at ha
      obtain ⟨j, hj, rfl⟩ := ha
      exact hcon j (by have := Finset.mem_range.mp hj; omega)
    have hcard : ((Finset.range (m + 1)).image v).card = m + 1 := by
      rw [Finset.card_image_of_injOn, Finset.card_range]
      intro i hi j hj hij
      have hi' := Finset.mem_range.mp (Finset.mem_coe.mp hi)
      have hj' := Finset.mem_range.mp (Finset.mem_coe.mp hj)
      exact hinj i j (by omega) (by omega) hij
    have := Finset.card_le_card hsub
    omega
  -- smooth edge indices
  set J : Finset ℕ := (Finset.range m).filter (fun j => v j ∈ S ∧ v (j + 1) ∈ S) with hJ
  set h : ℕ → ℕ := fun j => if j < t then v (j + 1) else v j with hh
  have hJmem : ∀ j, j ∈ J → j < m ∧ v j ∈ S ∧ v (j + 1) ∈ S ∧ j ≠ t ∧ j + 1 ≠ t := by
    intro j hj
    rw [hJ, Finset.mem_filter, Finset.mem_range] at hj
    refine ⟨hj.1, hj.2.1, hj.2.2, ?_, ?_⟩
    · intro e; rw [e] at hj; exact htS hj.2.1
    · intro e; rw [e] at hj; exact htS hj.2.2
  have hhinj : Set.InjOn h (J : Set ℕ) := by
    intro i hi j hj hij
    obtain ⟨hi1, -, -, hi4, hi5⟩ := hJmem i (Finset.mem_coe.mp hi)
    obtain ⟨hj1, -, -, hj4, hj5⟩ := hJmem j (Finset.mem_coe.mp hj)
    simp only [hh] at hij
    by_cases c1 : i < t <;> by_cases c2 : j < t
    · rw [if_pos c1, if_pos c2] at hij
      have := hinj (i + 1) (j + 1) (by omega) (by omega) hij
      omega
    · rw [if_pos c1, if_neg c2] at hij
      have := hinj (i + 1) j (by omega) (by omega) hij
      omega
    · rw [if_neg c1, if_pos c2] at hij
      have := hinj i (j + 1) (by omega) (by omega) hij
      omega
    · rw [if_neg c1, if_neg c2] at hij
      exact hinj i j (by omega) (by omega) hij
  -- the images are interior vertices lying in `S`
  have hhS : J.image h ⊆ S := by
    intro a ha
    rw [Finset.mem_image] at ha
    obtain ⟨j, hj, rfl⟩ := ha
    obtain ⟨-, h2, h3, -, -⟩ := hJmem j hj
    simp only [hh]
    by_cases c : j < t
    · rw [if_pos c]; exact h3
    · rw [if_neg c]; exact h2
  have hhI : J.image h ⊆ I := by
    intro a ha
    rw [Finset.mem_image] at ha
    obtain ⟨j, hj, rfl⟩ := ha
    obtain ⟨h1, -, -, h4, h5⟩ := hJmem j hj
    simp only [hh]
    rw [hI, Finset.mem_image]
    by_cases c : j < t
    · rw [if_pos c]
      exact ⟨j + 1, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, rfl⟩
    · rw [if_neg c]
      exact ⟨j, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, rfl⟩
  have hdisj : Disjoint (S ∩ Q) (J.image h) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    have h1 := hhI hb
    rw [Finset.mem_inter, hQ, Finset.mem_sdiff] at ha
    exact ha.2.2 h1
  have hcount : (S ∩ Q).card + J.card ≤ S.card := by
    have e1 : (J.image h).card = J.card := Finset.card_image_of_injOn hhinj
    have e2 := Finset.card_union_of_disjoint hdisj
    have e3 : (S ∩ Q) ∪ J.image h ⊆ S :=
      Finset.union_subset Finset.inter_subset_left hhS
    have e4 := Finset.card_le_card e3
    omega
  -- count the smooth elements
  have hsmooth : (E ∪ Q).filter (fun a => ∀ p ∈ a.primeFactors, p ∈ S) ⊆
      J.image (fun j => v j * v (j + 1)) ∪ (S ∩ Q) := by
    intro a ha
    rw [Finset.mem_filter, Finset.mem_union] at ha
    obtain ⟨ha1, ha2⟩ := ha
    rw [Finset.mem_union]
    rcases ha1 with ha1 | ha1
    · left
      rw [hE, Finset.mem_image] at ha1
      obtain ⟨j, hj, rfl⟩ := ha1
      have hj' := Finset.mem_range.mp hj
      have p0 := hprime j (by omega)
      have p1 := hprime (j + 1) (by omega)
      rw [Finset.mem_image]
      refine ⟨j, ?_, rfl⟩
      rw [hJ, Finset.mem_filter]
      refine ⟨hj, ha2 _ ?_, ha2 _ ?_⟩
      · exact Nat.mem_primeFactors.mpr ⟨p0, Dvd.intro _ rfl,
          Nat.mul_ne_zero p0.ne_zero p1.ne_zero⟩
      · exact Nat.mem_primeFactors.mpr ⟨p1, Dvd.intro_left _ rfl,
          Nat.mul_ne_zero p0.ne_zero p1.ne_zero⟩
    · right
      rw [Finset.mem_inter]
      refine ⟨?_, ha1⟩
      have hap : a.Prime := by
        rw [hQ, Finset.mem_sdiff, hPn, Finset.mem_filter] at ha1
        exact ha1.1.2
      exact ha2 a (Nat.mem_primeFactors.mpr ⟨hap, dvd_refl a, hap.ne_zero⟩)
  have hA0 : Erdos983.numSmooth (E ∪ Q) S ≤ S.card := by
    rw [Erdos983.numSmooth]
    have e1 := Finset.card_le_card hsmooth
    have e2 := Finset.card_union_le (J.image (fun j => v j * v (j + 1))) (S ∩ Q)
    have e3 := Finset.card_image_le (s := J) (f := fun j => v j * v (j + 1))
    omega
  have hAle : Erdos983.numSmooth A S ≤ Erdos983.numSmooth (E ∪ Q) S := by
    rw [Erdos983.numSmooth, Erdos983.numSmooth]
    exact Finset.card_le_card (Finset.filter_subset_filter _ hAsub)
  omega

/-- `π (p_n) = n + 1` for the `n`-th prime (zero indexed). -/
theorem pi_nth (n : ℕ) : Nat.primeCounting (Nat.nth Nat.Prime n) = n + 1 := by
  rw [Nat.primeCounting, Nat.primeCounting', Nat.count_succ, if_pos (Nat.prime_nth_prime n)]
  have := Nat.primeCounting'_nth_eq n
  rw [Nat.primeCounting'] at this
  rw [this]

theorem log_le_two_sqrt (x : ℝ) (hx : 0 < x) : Real.log x ≤ 2 * Real.sqrt x := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have h1 : Real.log (Real.sqrt x) ≤ Real.sqrt x - 1 := Real.log_le_sub_one_of_pos hs
  have h2 : Real.log (Real.sqrt x) = Real.log x / 2 := Real.log_sqrt hx.le
  linarith

/-- A polynomial bound for the `n`-th prime, from Chebyshev's lower bound for `π`. -/
theorem nth_prime_le (n : ℕ) : (Nat.nth Nat.Prime n : ℝ) ≤ 17 * ((n : ℝ) + 2) ^ 2 := by
  set p : ℕ := Nat.nth Nat.Prime n with hp
  have hp2 : 2 ≤ p := by
    have := Nat.add_two_le_nth_prime n
    omega
  have hp2r : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
  have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos (by linarith)
  have hpi := Chebyshev.pi_ge p
  rw [pi_nth n] at hpi
  rw [div_le_iff₀ hlogp] at hpi
  push_cast at hpi
  have hL : (0.69 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hlog1 : Real.log (p : ℝ) ≤ Real.log ((p : ℝ) + 1) :=
    Real.log_le_log (by linarith) (by linarith)
  have hlog2 : Real.log ((p : ℝ) + 1) ≤ 2 * Real.sqrt ((p : ℝ) + 1) :=
    log_le_two_sqrt _ (by linarith)
  set s : ℝ := Real.sqrt ((p : ℝ) + 1) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = (p : ℝ) + 1 := Real.sq_sqrt (by linarith)
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  -- p * log 2 ≤ 2 * (n + 2) * s
  have h1 : (p : ℝ) * Real.log 2 ≤ 2 * ((n : ℝ) + 2) * s := by
    have h2 : ((n : ℝ) + 1) * Real.log (p : ℝ) ≤ ((n : ℝ) + 1) * (2 * s) :=
      mul_le_mul_of_nonneg_left (hlog1.trans hlog2) (by linarith)
    nlinarith
  -- hence 0.69 * p ≤ 2 * (n + 2) * s
  have h3 : 0.69 * (p : ℝ) ≤ 2 * ((n : ℝ) + 2) * s := by
    have : 0.69 * (p : ℝ) ≤ (p : ℝ) * Real.log 2 := by nlinarith
    linarith
  -- square
  have h4 : (0.69 * (p : ℝ)) ^ 2 ≤ (2 * ((n : ℝ) + 2) * s) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h3 2
  have h5 : (2 * ((n : ℝ) + 2) * s) ^ 2 = 4 * ((n : ℝ) + 2) ^ 2 * ((p : ℝ) + 1) := by
    rw [← hs2]; ring
  rw [h5] at h4
  by_contra hcon
  rw [not_le] at hcon
  have hm : 0 < ((n : ℝ) + 2) ^ 2 := by positivity
  -- 4 (n+2)^2 (p+1) < (4/17) p (p+1) ≤ (6/17) p^2 < 0.4761 p^2
  have h6 : 4 * ((n : ℝ) + 2) ^ 2 * ((p : ℝ) + 1) ≤ 4 / 17 * (p : ℝ) * ((p : ℝ) + 1) := by
    have : 4 * ((n : ℝ) + 2) ^ 2 ≤ 4 / 17 * (p : ℝ) := by linarith
    exact mul_le_mul_of_nonneg_right this (by linarith)
  nlinarith

/-- `log p_n` is eventually below `ε n + log 2`. -/
theorem log_nth_lt (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℕ, ∀ n : ℕ, M < n →
      Real.log (Nat.nth Nat.Prime n : ℝ) < ε * (n : ℝ) + Real.log 2 := by
  obtain ⟨M1, hM1⟩ := exists_nat_gt (32 / ε)
  obtain ⟨M2, hM2⟩ := exists_nat_gt (128 / ε ^ 2)
  refine ⟨M1 + M2 + 2, ?_⟩
  intro n hn
  have hnr : ((M1 : ℝ) + (M2 : ℝ) + 2) < (n : ℝ) := by exact_mod_cast hn
  have hM1' : (0 : ℝ) ≤ (M1 : ℝ) := Nat.cast_nonneg _
  have hM2' : (0 : ℝ) ≤ (M2 : ℝ) := Nat.cast_nonneg _
  have hn1 : 32 / ε < (n : ℝ) := by linarith
  have hn2 : 128 / ε ^ 2 < (n : ℝ) := by linarith
  have hn3 : (2 : ℝ) < (n : ℝ) := by linarith
  have e1 : 32 < ε * (n : ℝ) := by
    rw [div_lt_iff₀ hε] at hn1
    linarith
  have e2 : 128 < ε ^ 2 * (n : ℝ) := by
    rw [div_lt_iff₀ (by positivity)] at hn2
    linarith
  have hp2 : (2 : ℝ) ≤ (Nat.nth Nat.Prime n : ℝ) := by
    have := Nat.add_two_le_nth_prime n
    have h : 2 ≤ Nat.nth Nat.Prime n := by omega
    exact_mod_cast h
  have h1 : Real.log (Nat.nth Nat.Prime n : ℝ) ≤ Real.log (17 * ((n : ℝ) + 2) ^ 2) :=
    Real.log_le_log (by linarith) (nth_prime_le n)
  have h2 : Real.log (17 * ((n : ℝ) + 2) ^ 2) =
      Real.log 17 + 2 * Real.log ((n : ℝ) + 2) := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    push_cast
    ring
  have h3 : Real.log 17 ≤ 16 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 17 by norm_num)
    linarith
  have h4 : Real.log ((n : ℝ) + 2) ≤ 2 * Real.sqrt ((n : ℝ) + 2) :=
    log_le_two_sqrt _ (by linarith)
  have h5 : Real.sqrt ((n : ℝ) + 2) ≤ ε * (n : ℝ) / 8 := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    have : (ε * (n : ℝ) / 8) ^ 2 = ε ^ 2 * (n : ℝ) * (n : ℝ) / 64 := by ring
    rw [this]
    nlinarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  linarith

/-- Pomerance's lemma: there are arbitrarily large `c` with
`p_{c-i} * p_{c+i} < p_c ^ 2` for all `1 ≤ i ≤ c`. -/
theorem pomerance (B : ℕ) : ∃ c : ℕ, B ≤ c ∧ 1 ≤ c ∧
    ∀ i : ℕ, 1 ≤ i → i ≤ c →
      Nat.nth Nat.Prime (c - i) * Nat.nth Nat.Prime (c + i) < Nat.nth Nat.Prime c ^ 2 := by
  classical
  have hmono : StrictMono (Nat.nth Nat.Prime) := Nat.nth_strictMono Nat.infinite_setOfPred_prime
  have hpos : ∀ n, (0 : ℝ) < (Nat.nth Nat.Prime n : ℝ) := by
    intro n
    have := Nat.add_two_le_nth_prime n
    have h : 0 < Nat.nth Nat.Prime n := by omega
    exact_mod_cast h
  set a : ℕ → ℝ := fun n => Real.log (Nat.nth Nat.Prime n : ℝ) with ha
  have hamono : StrictMono a := by
    intro x y hxy
    exact Real.log_lt_log (hpos x) (by exact_mod_cast hmono hxy)
  -- choose ε
  set B' : ℕ := B + 1 with hB'
  set δ : ℝ := a B' - a (B' - 1) with hδ
  have hδpos : 0 < δ := by
    have : a (B' - 1) < a B' := hamono (by omega)
    linarith
  set ε : ℝ := δ / ((B' : ℝ) + 1) with hε
  have hB'r : (0 : ℝ) ≤ (B' : ℝ) := Nat.cast_nonneg _
  have hεpos : 0 < ε := div_pos hδpos (by linarith)
  have hεB : ε * ((B' : ℝ) + 1) = δ := by
    rw [hε]; field_simp
  obtain ⟨M, hM⟩ := log_nth_lt ε hεpos
  set g : ℕ → ℝ := fun n => a n - ε * (n : ℝ) with hg
  have hg0 : g 0 = Real.log 2 := by
    simp only [hg, ha, Nat.nth_prime_zero_eq_two]
    norm_num
  have hlarge : ∀ n, M < n → g n < g 0 := by
    intro n hn
    have := hM n hn
    rw [hg0]
    simp only [hg, ha]
    linarith
  set N : ℕ := max M B' with hN
  set R : Finset ℕ := Finset.range (N + 1) with hR
  set Smax : Finset ℕ := R.filter (fun n => ∀ k ∈ R, g k ≤ g n) with hSmax
  have hSne : Smax.Nonempty := by
    obtain ⟨x, hx, hxmax⟩ := Finset.exists_max_image R g ⟨0, Finset.mem_range.mpr (by omega)⟩
    exact ⟨x, Finset.mem_filter.mpr ⟨hx, hxmax⟩⟩
  set c : ℕ := Smax.max' hSne with hc
  have hcmem : c ∈ Smax := Finset.max'_mem Smax hSne
  have hcR : c ∈ R := (Finset.mem_filter.mp hcmem).1
  have hcmax : ∀ k ∈ R, g k ≤ g c := (Finset.mem_filter.mp hcmem).2
  have h0R : 0 ∈ R := Finset.mem_range.mpr (by omega)
  have hall : ∀ k, g k ≤ g c := by
    intro k
    by_cases hk : k ∈ R
    · exact hcmax k hk
    · have hk' : M < k := by
        rw [hR, Finset.mem_range] at hk
        have : M ≤ N := le_max_left _ _
        omega
      exact (hlarge k hk').le.trans (hcmax 0 h0R)
  have hstrict : ∀ k, c < k → g k < g c := by
    intro k hk
    by_cases hkR : k ∈ R
    · by_contra hcon
      rw [not_lt] at hcon
      have hkS : k ∈ Smax := by
        rw [hSmax, Finset.mem_filter]
        exact ⟨hkR, fun j hj => (hcmax j hj).trans hcon⟩
      have := Finset.le_max' Smax k hkS
      omega
    · have hk' : M < k := by
        rw [hR, Finset.mem_range] at hkR
        have : M ≤ N := le_max_left _ _
        omega
      exact lt_of_lt_of_le (hlarge k hk') (hcmax 0 h0R)
  -- c ≥ B'
  have hcB : B' ≤ c := by
    by_contra hcon
    rw [not_le] at hcon
    have h1 := hall B'
    have h2 : a c ≤ a (B' - 1) := hamono.monotone (by omega)
    have h3 : (c : ℝ) + 1 ≤ (B' : ℝ) := by exact_mod_cast hcon
    have hcr : (0 : ℝ) ≤ (c : ℝ) := Nat.cast_nonneg _
    simp only [hg] at h1
    nlinarith
  refine ⟨c, by omega, by omega, ?_⟩
  intro i hi hic
  have h1 := hstrict (c + i) (by omega)
  have h2 := hall (c - i)
  simp only [hg] at h1 h2
  have e1 : ((c + i : ℕ) : ℝ) = (c : ℝ) + (i : ℝ) := by push_cast; ring
  have e2 : ((c - i : ℕ) : ℝ) = (c : ℝ) - (i : ℝ) := by
    rw [Nat.cast_sub hic]
  rw [e1] at h1
  rw [e2] at h2
  have h3 : a (c - i) + a (c + i) < 2 * a c := by nlinarith
  simp only [ha] at h3
  rw [← Real.log_mul (hpos _).ne' (hpos _).ne'] at h3
  have h4 : 2 * Real.log (Nat.nth Nat.Prime c : ℝ) = Real.log ((Nat.nth Nat.Prime c : ℝ) ^ 2) := by
    rw [Real.log_pow]; push_cast; ring
  rw [h4] at h3
  have h5 := (Real.log_lt_log_iff (mul_pos (hpos _) (hpos _)) (pow_pos (hpos c) 2)).mp h3
  exact_mod_cast h5

/-- The alternating path `p_{2c}, p_0, p_{2c-1}, p_1, …, p_c`. -/
theorem big_n (c : ℕ) (hc : 1 ≤ c)
    (hpom : ∀ i : ℕ, 1 ≤ i → i ≤ c →
      Nat.nth Nat.Prime (c - i) * Nat.nth Nat.Prime (c + i) < Nat.nth Nat.Prime c ^ 2) :
    2 * c + 1 ≤ Erdos983.f (Nat.primeCounting (Nat.nth Nat.Prime c ^ 2 - 1) + 1)
      (Nat.nth Nat.Prime c ^ 2 - 1) := by
  have hmono : StrictMono (Nat.nth Nat.Prime) := Nat.nth_strictMono Nat.infinite_setOfPred_prime
  apply path_lower (Nat.nth Nat.Prime c ^ 2 - 1) (2 * c)
    (fun j => if j % 2 = 0 then Nat.nth Nat.Prime (2 * c - j / 2) else Nat.nth Nat.Prime (j / 2))
    (by omega)
  · intro j _
    by_cases h : j % 2 = 0
    · simp only [if_pos h]; exact Nat.prime_nth_prime _
    · simp only [if_neg h]; exact Nat.prime_nth_prime _
  · intro i j hi hj hij
    by_cases h1 : i % 2 = 0 <;> by_cases h2 : j % 2 = 0
    · simp only [if_pos h1, if_pos h2] at hij
      have := hmono.injective hij
      omega
    · simp only [if_pos h1, if_neg h2] at hij
      have := hmono.injective hij
      omega
    · simp only [if_neg h1, if_pos h2] at hij
      have := hmono.injective hij
      omega
    · simp only [if_neg h1, if_neg h2] at hij
      have := hmono.injective hij
      omega
  · intro j hj
    have hlt : (if j % 2 = 0 then Nat.nth Nat.Prime (2 * c - j / 2) else Nat.nth Nat.Prime (j / 2)) *
        (if (j + 1) % 2 = 0 then Nat.nth Nat.Prime (2 * c - (j + 1) / 2)
          else Nat.nth Nat.Prime ((j + 1) / 2)) < Nat.nth Nat.Prime c ^ 2 := by
      by_cases h : j % 2 = 0
      · have h' : ¬ (j + 1) % 2 = 0 := by omega
        rw [if_pos h, if_neg h']
        have e0 : (j + 1) / 2 = j / 2 := by omega
        have hp := hpom (c - j / 2) (by omega) (by omega)
        have e1 : c - (c - j / 2) = j / 2 := by omega
        have e2 : c + (c - j / 2) = 2 * c - j / 2 := by omega
        rw [e1, e2] at hp
        rw [e0, Nat.mul_comm]
        exact hp
      · have h' : (j + 1) % 2 = 0 := by omega
        rw [if_neg h, if_pos h']
        have hp := hpom (c - j / 2) (by omega) (by omega)
        have e1 : c - (c - j / 2) = j / 2 := by omega
        have e2 : c + (c - j / 2) = 2 * c - j / 2 := by omega
        rw [e1, e2] at hp
        have hle : Nat.nth Nat.Prime (2 * c - (j + 1) / 2) ≤ Nat.nth Nat.Prime (2 * c - j / 2) :=
          hmono.monotone (by omega)
        exact lt_of_le_of_lt (Nat.mul_le_mul_left _ hle) hp
    have hpos : 0 < Nat.nth Nat.Prime c ^ 2 := by
      have := (Nat.prime_nth_prime c).pos
      positivity
    exact Nat.le_sub_one_of_lt hlt

end OMA983

open Filter in
theorem OMA.solution : type_of% @Erdos983.erdos_983.parts.i := by
  intro h
  have h0 := (Filter.tendsto_atTop.mp h) 0
  rw [Filter.eventually_atTop] at h0
  obtain ⟨n0, hn0⟩ := h0
  obtain ⟨c, hcB, hc1, hpom⟩ := OMA983.pomerance n0
  have hbig := OMA983.big_n c hc1 hpom
  have hp2 : c + 2 ≤ Nat.nth Nat.Prime c := Nat.add_two_le_nth_prime c
  obtain ⟨q, hq⟩ : ∃ q, Nat.nth Nat.Prime c = q + 1 := ⟨Nat.nth Nat.Prime c - 1, by omega⟩
  have hn : Nat.nth Nat.Prime c ^ 2 - 1 = q ^ 2 + 2 * q := by
    rw [hq]
    have : (q + 1) ^ 2 = q ^ 2 + 2 * q + 1 := by ring
    omega
  have hsqrt : Nat.sqrt (Nat.nth Nat.Prime c ^ 2 - 1) = q := by
    symm
    rw [Nat.eq_sqrt', hn]
    constructor
    · omega
    · have : (q + 1) ^ 2 = q ^ 2 + 2 * q + 1 := by ring
      omega
  have hpi : Nat.primeCounting q = c := by
    have h1 : q = Nat.nth Nat.Prime c - 1 := by omega
    rw [h1, Nat.primeCounting_sub_one, Nat.primeCounting'_nth_eq]
  have hge : n0 ≤ Nat.nth Nat.Prime c ^ 2 - 1 := by
    rw [hn]
    have : q ≤ q ^ 2 := Nat.le_self_pow (by norm_num) q
    omega
  have hfin := hn0 _ hge
  rw [hsqrt, hpi] at hfin
  have hbig' : ((2 * c + 1 : ℕ) : ℤ) ≤
      (Erdos983.f (Nat.primeCounting (Nat.nth Nat.Prime c ^ 2 - 1) + 1)
        (Nat.nth Nat.Prime c ^ 2 - 1) : ℤ) := by
    exact_mod_cast hbig
  push_cast at hbig'
  omega
