import FormalConjectures.ErdosProblems.«32»

/-!
# A strict lower bound for complements to the primes

Choose residue classes to exclude translates of the primes. The Chinese remainder theorem
combines the exclusions, and a bound on the reciprocal sum over smooth numbers controls the
number of additional primes needed.
-/

open Filter Finset Real
open scoped BigOperators Function Classical

namespace OMA32

private lemma exists_residue (S : Finset ℕ) {p : ℕ} (hp : 0 < p) :
    ∃ r : ℕ, ((S.filter fun a => a % p ≠ r).card : ℝ) ≤
      (S.card : ℝ) * (1 - (p : ℝ)⁻¹) := by
  classical
  have hs := Finset.card_eq_sum_card_fiberwise
    (s := S) (t := range p) (f := fun a => a % p)
    (fun a _ => mem_range.mpr (Nat.mod_lt a hp))
  have hsum : (∑ r ∈ range p, ((S.filter fun a => a % p = r).card : ℝ)) =
      (S.card : ℝ) := by
    exact_mod_cast hs.symm
  have hpp : (0 : ℝ) < p := by exact_mod_cast hp
  obtain ⟨r, hr, hlarge⟩ : ∃ r ∈ range p,
      (S.card : ℝ) / p ≤ ((S.filter fun a => a % p = r).card : ℝ) := by
    by_contra! h
    have hlt := Finset.sum_lt_sum_of_nonempty (nonempty_range_iff.mpr hp.ne') h
    rw [hsum, sum_const, card_range, nsmul_eq_mul, mul_div_cancel₀ _ hpp.ne'] at hlt
    exact (lt_irrefl _ hlt)
  refine ⟨r, ?_⟩
  have hcard := Finset.card_filter_add_card_filter_not
    (s := S) (p := fun a => a % p = r)
  have hcard' : ((S.filter fun a => a % p = r).card : ℝ) +
      ((S.filter fun a => a % p ≠ r).card : ℝ) = (S.card : ℝ) := by
    exact_mod_cast hcard
  rw [mul_sub, mul_one, ← div_eq_mul_inv]
  linarith

/-- Choose the residues for the small primes one at a time. -/
private lemma exists_residues (P S : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    ∃ r : ℕ → ℕ,
      ((S.filter fun a => ∀ p ∈ P, a % p ≠ r p).card : ℝ) ≤
        (S.card : ℝ) * ∏ p ∈ P, (1 - (p : ℝ)⁻¹) := by
  classical
  induction P using Finset.induction_on generalizing S with
  | empty => simp
  | @insert p P hp ih =>
    have hp' := hP p (mem_insert_self _ _)
    obtain ⟨b, hb⟩ := exists_residue S hp'.pos
    obtain ⟨r, hr⟩ := ih (S.filter fun a => a % p ≠ b)
      (fun q hq => hP q (mem_insert_of_mem hq))
    refine ⟨Function.update r p b, ?_⟩
    have he : (S.filter fun a => ∀ q ∈ insert p P,
        a % q ≠ Function.update r p b q) =
        (S.filter fun a => a % p ≠ b).filter (fun a => ∀ q ∈ P, a % q ≠ r q) := by
      ext a
      have hne : ∀ q ∈ P, q ≠ p := fun q hq e => hp (e ▸ hq)
      simp only [mem_filter, Finset.forall_mem_insert, Function.update_self, and_assoc]
      exact and_congr_right fun _ => and_congr_right fun _ =>
        forall₂_congr fun q hq => by rw [Function.update_of_ne (hne q hq)]
    rw [he, prod_insert hp, ← mul_assoc]
    refine hr.trans (mul_le_mul_of_nonneg_right hb ?_)
    exact prod_nonneg fun q hq => sub_nonneg.mpr
      (inv_le_one_of_one_le₀ (by exact_mod_cast (hP q (mem_insert_of_mem hq)).one_le))

/-- Extend the small-prime congruences with a separate prime for each survivor. -/
private lemma exists_covering_congruences (P Q S : Finset ℕ)
    (hprime : ∀ p ∈ P ∪ Q, p.Prime) (hdisj : Disjoint P Q)
    (hQ : (S.card : ℝ) * (∏ p ∈ P, (1 - (p : ℝ)⁻¹)) ≤ Q.card) :
    ∃ T ⊆ Q, (T.card : ℝ) ≤ (S.card : ℝ) * (∏ p ∈ P, (1 - (p : ℝ)⁻¹)) ∧
      ∃ b : ℕ, b < (∏ p ∈ P ∪ T, p) ∧
      ∀ a ∈ S, ∃ p ∈ P ∪ T, b ≡ a [MOD p] := by
  classical
  obtain ⟨r, hr⟩ := exists_residues P S (fun p hp => hprime p (mem_union_left _ hp))
  let U := S.filter (fun a => ∀ p ∈ P, a % p ≠ r p)
  have hU : U.card ≤ Q.card := by exact_mod_cast hr.trans hQ
  obtain ⟨T, hT, hcard⟩ := exists_subset_card_eq hU
  let e : T ≃ U := Finset.equivOfCardEq hcard
  let residues (p : ℕ) : ℕ := if hp : p ∈ T then (e ⟨p, hp⟩ : ℕ) else r p
  have hP' : ∀ p ∈ P ∪ T, p.Prime :=
    fun p hp => hprime p (union_subset_union_right hT hp)
  have hne : ∀ p ∈ P ∪ T, p ≠ 0 := fun p hp => (hP' p hp).ne_zero
  have hcop : Set.Pairwise (↑(P ∪ T) : Set ℕ) (Nat.Coprime on id) :=
    fun p hp q hq hpq => (Nat.coprime_primes (hP' p hp) (hP' q hq)).mpr hpq
  let b := Nat.chineseRemainderOfFinset residues id (P ∪ T) hne hcop
  refine ⟨T, hT, by simpa only [hcard] using hr, b, ?_, ?_⟩
  · exact Nat.chineseRemainderOfFinset_lt_prod residues id hne hcop
  · intro a ha
    by_cases hau : a ∈ U
    · let p := e.symm ⟨a, hau⟩
      have hp : (p : ℕ) ∈ P ∪ T := mem_union_right _ p.property
      have hs := b.property p hp
      refine ⟨p, hp, ?_⟩
      simpa [residues, p] using hs
    · have hex : ∃ p ∈ P, a % p = r p := by simpa [U, ha] using hau
      obtain ⟨p, hp, he⟩ := hex
      have hpT : p ∉ T := fun ht => (Finset.disjoint_left.mp hdisj hp (hT ht))
      have hpu := mem_union_left T hp
      refine ⟨p, hpu, ?_⟩
      have hs := b.property p hpu
      simpa [residues, hpT, Nat.ModEq, ← he, Nat.mod_mod] using hs

/-- The progression contains more terms than possible exceptions. -/
private lemma exists_uncovered (S P : Finset ℕ) {B N b : ℕ}
    (hprime : ∀ p ∈ P, p.Prime) (hb : b < ∏ p ∈ P, p)
    (hcover : ∀ a ∈ S, ∃ p ∈ P, b ≡ a [MOD p])
    (hsize : (B + S.card + 1) * (∏ p ∈ P, p) ≤ N) :
    ∃ n ∈ Icc B N, ∀ a ∈ S, ∀ p : ℕ, p.Prime → n ≠ p + a := by
  classical
  let M := ∏ p ∈ P, p
  have hM : 0 < M := Finset.prod_pos fun p hp => (hprime p hp).pos
  choose q hq hqa using hcover
  let f (a : ℕ) := if ha : a ∈ S then q a ha + a else 0
  let C := (range (S.card + 1)).image (fun j => b + (B + j) * M)
  have hcard : C.card = S.card + 1 := by
    rw [Finset.card_image_of_injective, card_range]
    intro i j hij
    exact Nat.add_left_cancel (Nat.eq_of_mul_eq_mul_right hM (Nat.add_left_cancel hij))
  have hnot : ¬ C ⊆ S.image f := by
    intro hc
    have h := (card_le_card hc).trans (card_image_le (s := S) (f := f))
    omega
  obtain ⟨n, hn, hnf⟩ := Finset.not_subset.mp hnot
  obtain ⟨j, hj, rfl⟩ := mem_image.mp hn
  have hj' := mem_range.mp hj
  refine ⟨b + (B + j) * M, mem_Icc.mpr ⟨?_, ?_⟩, ?_⟩
  · have h := Nat.mul_le_mul_left (B + j) (Nat.one_le_iff_ne_zero.mpr hM.ne')
    simp only [Nat.mul_one] at h
    omega
  · have h := Nat.mul_le_mul_right M (show B + j + 1 ≤ B + S.card + 1 by omega)
    rw [Nat.add_mul, Nat.one_mul] at h
    change (B + S.card + 1) * M ≤ N at hsize
    omega
  · intro a ha p hp hn
    have hd : q a ha ∣ M := Finset.dvd_prod_of_mem (fun p : ℕ => p) (hq a ha)
    have hm : b + (B + j) * M ≡ b [MOD q a ha] :=
      (Nat.add_mul_modulus_modEq_iff.mpr (Nat.ModEq.refl b)).of_dvd hd
    have hmod := hm.trans (hqa a ha)
    rw [hn, Nat.add_comm p a, Nat.add_modEq_left_iff] at hmod
    have heq := (Nat.dvd_prime hp).mp hmod
    rcases heq with h | rfl
    · exact (hprime _ (hq a ha)).ne_one h
    · apply hnf
      exact mem_image.mpr ⟨a, ha, by simpa [f, ha] using hn.symm⟩

private noncomputable def survivorFactor (y : ℕ) : ℝ :=
  ∏ p ∈ Nat.primesLE y, (1 - (p : ℝ)⁻¹)

private lemma survivorFactor_pos (y : ℕ) : 0 < survivorFactor y := by
  apply prod_pos
  intro p hp
  have hp' : (1 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_lt
  exact sub_pos.mpr (inv_lt_one_of_one_lt₀ hp')

private lemma log_modulus_bound {y z : ℕ} {T : Finset ℕ}
    (hT : T ⊆ Nat.primesLE z \ Nat.primesLE y) :
    Real.log ((∏ p ∈ Nat.primesLE y ∪ T, p : ℕ) : ℝ) ≤
      Real.log 4 * y + (T.card : ℝ) * Real.log z := by
  have hdisj : Disjoint (Nat.primesLE y) T :=
    Finset.disjoint_left.mpr fun p hp ht => (mem_sdiff.mp (hT ht)).2 hp
  have hprime : ∀ p ∈ Nat.primesLE y ∪ T, p.Prime := by
    intro p hp
    rcases mem_union.mp hp with hp | hp
    · exact Nat.prime_of_mem_primesLE hp
    · exact Nat.prime_of_mem_primesLE (mem_sdiff.mp (hT hp)).1
  rw [Nat.cast_prod, Real.log_prod (fun p hp => by exact_mod_cast (hprime p hp).ne_zero),
    sum_union hdisj, ← Chebyshev.theta_eq_sum_primesLE_log]
  refine add_le_add (Chebyshev.theta_le_log4_mul_x (by positivity)) ?_
  rw [← nsmul_eq_mul, ← sum_const]
  exact sum_le_sum fun p hp => Real.log_le_log
    (by exact_mod_cast (hprime p (mem_union_right _ hp)).pos)
    (by exact_mod_cast (Nat.mem_primesLE.mp (mem_sdiff.mp (hT hp)).1).1)

-- These factorial estimates come from the local OMALib.Mertens development.
/- `log n!` as a sum over the primes `≤ n` (Legendre). -/
private lemma log_factorial_eq_sum_primesLE (n : ℕ) :
    Real.log (n.factorial : ℝ) =
      ∑ p ∈ Nat.primesLE n, ((n.factorial).factorization p : ℝ) * Real.log p := by
  rw [Real.log_nat_eq_sum_factorization, Finsupp.sum]
  apply Finset.sum_subset
  · intro p hp
    rw [Nat.support_factorization] at hp
    rw [Nat.mem_primesLE]
    have hpp := Nat.prime_of_mem_primeFactors hp
    exact ⟨(hpp.dvd_factorial).mp (Nat.dvd_of_mem_primeFactors hp), hpp⟩
  · intro p _ hp
    rw [Finsupp.notMem_support_iff] at hp
    simp [hp]

/- `⌊n/p⌋ ≤ v_p(n!)`. -/
private lemma div_le_factorization_factorial {p : ℕ} (hp : p.Prime) (n : ℕ) :
    n / p ≤ (n.factorial).factorization p := by
  rw [Nat.factorization_factorial hp (b := n + 1) (Nat.lt_succ_of_le (Nat.log_le_self p n))]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have h1 : 1 ∈ Finset.Ico 1 (n + 1) := by
      rw [Finset.mem_Ico]; omega
    have := Finset.single_le_sum (f := fun i => n / p ^ i) (fun i _ => Nat.zero_le _) h1
    simpa using this

/- Mertens' first theorem, upper bound, explicit constant `log 4`. -/
private theorem mertens_first_upper_explicit (n : ℕ) (hn : 1 ≤ n) :
    ∑ p ∈ Nat.primesLE n, Real.log p / p ≤ Real.log n + Real.log 4 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : Real.log (n.factorial : ℝ) ≤ n * Real.log n := by
    rw [← Real.log_pow]
    apply Real.log_le_log
    · exact_mod_cast Nat.factorial_pos n
    · exact_mod_cast Nat.factorial_le_pow n
  have h2 : ∑ p ∈ Nat.primesLE n, ((n : ℝ) / p - 1) * Real.log p
      ≤ Real.log (n.factorial : ℝ) := by
    rw [log_factorial_eq_sum_primesLE]
    apply Finset.sum_le_sum
    intro p hp
    have hpp := Nat.prime_of_mem_primesLE hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_le)
    apply mul_le_mul_of_nonneg_right _ hlog
    have h3 : ((n / p : ℕ) : ℝ) ≤ ((n.factorial).factorization p : ℝ) := by
      exact_mod_cast div_le_factorization_factorial hpp n
    have h4 : (n : ℝ) < ((n / p : ℕ) : ℝ) * p + p := by
      exact_mod_cast Nat.lt_div_mul_add hpp.pos
    have h5 : (n : ℝ) / p < ((n / p : ℕ) : ℝ) + 1 := by
      rw [div_lt_iff₀ hp0]; linarith
    linarith
  have h6 : ∑ p ∈ Nat.primesLE n, ((n : ℝ) / p - 1) * Real.log p
      = n * ∑ p ∈ Nat.primesLE n, Real.log p / p - ∑ p ∈ Nat.primesLE n, Real.log p := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p _
    ring
  have h7 : ∑ p ∈ Nat.primesLE n, Real.log p ≤ Real.log 4 * n := by
    rw [← Chebyshev.theta_eq_sum_primesLE_log]
    exact Chebyshev.theta_le_log4_mul_x (by positivity)
  have h8 : n * ∑ p ∈ Nat.primesLE n, Real.log p / p ≤ n * (Real.log n + Real.log 4) := by
    linarith
  exact le_of_mul_le_mul_left h8 hn0

private lemma mertens_log_succ_le (x : ℝ) (hx : 0 < x) : Real.log (x + 1) ≤ Real.log x + 1 / x := by
  have h := Real.log_le_sub_one_of_pos (show 0 < (x + 1) / x by positivity)
  rw [Real.log_div (by positivity) (by positivity)] at h
  have h' : (x + 1) / x - 1 = 1 / x := by field_simp; ring
  linarith

private lemma mertens_tail_step (x : ℝ) (hx : 1 < x) :
    Real.log x / (x * (x - 1)) + (Real.log (x + 1) + 1) / x ≤ (Real.log x + 1) / (x - 1) := by
  have hx0 : 0 < x := by linarith
  have hx1 : 0 < x - 1 := by linarith
  have h1 : Real.log (x + 1) - Real.log x ≤ 1 / x := by
    have := mertens_log_succ_le x hx0; linarith
  have h2 : (x - 1) * (Real.log (x + 1) - Real.log x) ≤ (x - 1) * (1 / x) :=
    mul_le_mul_of_nonneg_left h1 hx1.le
  have h3 : (x - 1) * (1 / x) ≤ 1 := by
    rw [mul_one_div, div_le_one hx0]; linarith
  have key : (Real.log x + 1) / (x - 1) - Real.log x / (x * (x - 1))
      - (Real.log (x + 1) + 1) / x
      = (1 - (x - 1) * (Real.log (x + 1) - Real.log x)) / (x * (x - 1)) := by
    field_simp
    ring
  have h4 : 0 ≤ (1 - (x - 1) * (Real.log (x + 1) - Real.log x)) / (x * (x - 1)) := by
    apply div_nonneg
    · linarith
    · positivity
  linarith

/- `∑_{m=2}^{n+1} log m / (m (m-1)) ≤ log 2 + 1` (telescoping majorant). -/
private lemma mertens_tail_bound (n : ℕ) :
    ∑ m ∈ Finset.Icc 2 (n + 1), Real.log (m : ℝ) / ((m : ℝ) * ((m : ℝ) - 1))
      + (Real.log ((n : ℝ) + 2) + 1) / ((n : ℝ) + 1) ≤ Real.log 2 + 1 := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have h := mertens_tail_step ((k : ℝ) + 2) (by have : (0:ℝ) ≤ k := Nat.cast_nonneg k; linarith)
    have e0 : ((k + 1 + 1 : ℕ) : ℝ) = (k : ℝ) + 2 := by push_cast; ring
    have e1 : (k : ℝ) + 2 - 1 = k + 1 := by ring
    have e2 : ((k + 1 : ℕ) : ℝ) + 2 = (k : ℝ) + 2 + 1 := by push_cast; ring
    have e3 : ((k + 1 : ℕ) : ℝ) + 1 = (k : ℝ) + 2 := by push_cast; ring
    rw [e0, e2, e3]
    rw [e1] at h ⊢
    linarith

/- Mertens' first theorem, lower bound, explicit constant `2 + log 2`. -/
private theorem mertens_first_lower_explicit (n : ℕ) (hn : 1 ≤ n) :
    Real.log n - (2 + Real.log 2) ≤ ∑ p ∈ Nat.primesLE n, Real.log p / p := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : n * Real.log n - n ≤ Real.log (n.factorial : ℝ) := by
    have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
    have h := Real.pow_div_factorial_le_exp (x := (n : ℝ)) hn0.le n
    rw [div_le_iff₀ hf] at h
    have h' := Real.log_le_log (by positivity) h
    rw [Real.log_pow, Real.log_mul (Real.exp_pos _).ne' hf.ne', Real.log_exp] at h'
    linarith
  have h2 : Real.log (n.factorial : ℝ)
      ≤ ∑ p ∈ Nat.primesLE n, (n : ℝ) / ((p : ℝ) - 1) * Real.log p := by
    rw [log_factorial_eq_sum_primesLE]
    apply Finset.sum_le_sum
    intro p hp
    have hpp := Nat.prime_of_mem_primesLE hp
    have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_le)
    apply mul_le_mul_of_nonneg_right _ hlog
    have h3 : ((n.factorial).factorization p : ℝ) ≤ ((n / (p - 1) : ℕ) : ℝ) := by
      exact_mod_cast Nat.factorization_factorial_le_div_pred hpp n
    have h4 : ((n / (p - 1) : ℕ) : ℝ) ≤ (n : ℝ) / ((p - 1 : ℕ) : ℝ) := Nat.cast_div_le
    rw [Nat.cast_sub hpp.one_le, Nat.cast_one] at h4
    linarith
  have h5 : ∑ p ∈ Nat.primesLE n, (n : ℝ) / ((p : ℝ) - 1) * Real.log p
      = n * ∑ p ∈ Nat.primesLE n, Real.log p / p
        + n * ∑ p ∈ Nat.primesLE n, Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    have hpp := Nat.prime_of_mem_primesLE hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by
      have : (1 : ℝ) < p := by exact_mod_cast hpp.one_lt
      linarith
    field_simp
    ring
  have h6 : ∑ p ∈ Nat.primesLE n, Real.log p / ((p : ℝ) * ((p : ℝ) - 1))
      ≤ Real.log 2 + 1 := by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have hsub : Nat.primesLE (k + 1) ⊆ Finset.Icc 2 (k + 1) := by
      rw [Nat.primesLE_eq_filter_Icc_two]; exact Finset.filter_subset _ _
    have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (f := fun m : ℕ => Real.log (m : ℝ) / ((m : ℝ) * ((m : ℝ) - 1))) (fun m hm _ => by
        rw [Finset.mem_Icc] at hm
        have h2m : (2 : ℝ) ≤ m := by exact_mod_cast hm.1
        apply div_nonneg (Real.log_nonneg (by linarith))
        apply mul_nonneg <;> linarith)
    have hb := mertens_tail_bound k
    have hpos : 0 ≤ (Real.log ((k : ℝ) + 2) + 1) / ((k : ℝ) + 1) := by
      have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      apply div_nonneg
      · have := Real.log_nonneg (show (1 : ℝ) ≤ (k : ℝ) + 2 by linarith)
        linarith
      · linarith
    linarith
  have h7 : n * (Real.log n - (2 + Real.log 2))
      ≤ n * ∑ p ∈ Nat.primesLE n, Real.log p / p := by
    have := mul_le_mul_of_nonneg_left h6 hn0.le
    nlinarith
  exact le_of_mul_le_mul_left h7 hn0

private lemma sum_inv_le_survivorFactor_inv {y : ℕ} {D : Finset ℕ}
    (hD : ∀ n ∈ D, n ∈ Nat.factoredNumbers (Nat.primesLE y)) :
    (∑ n ∈ D, (n : ℝ)⁻¹) ≤ (survivorFactor y)⁻¹ := by
  let f : ℕ →* ℝ :=
    { toFun := fun n => (n : ℝ)⁻¹
      map_one' := by simp
      map_mul' := by intro a b; push_cast; exact mul_inv _ _ }
  have hf {p : ℕ} (hp : p.Prime) : ‖f p‖ < 1 := by
    dsimp [f]
    rw [abs_of_nonneg (by positivity)]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  have hs := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
    (f := f) hf (Nat.primesLE y)).2
  have he : (Nat.primesLE y).filter Nat.Prime = Nat.primesLE y :=
    filter_eq_self.mpr fun p hp => Nat.prime_of_mem_primesLE hp
  rw [he] at hs
  let e : D ↪ Nat.factoredNumbers (Nat.primesLE y) :=
    ⟨fun n => ⟨n, hD n n.property⟩, fun _ _ h => Subtype.ext (congrArg (fun v : Nat.factoredNumbers (Nat.primesLE y) => v.val) h)⟩
  have hb := sum_le_hasSum (D.attach.map e) (fun n _ => show 0 ≤ (n.val : ℝ)⁻¹ by positivity) hs
  rw [Finset.sum_map] at hb
  change (∑ n ∈ D.attach, ((n : ℕ) : ℝ)⁻¹) ≤ (∏ p ∈ Nat.primesLE y, (1 - (p : ℝ)⁻¹)⁻¹) at hb
  rw [Finset.sum_attach D (fun n : ℕ => (n : ℝ)⁻¹)] at hb
  simpa only [survivorFactor, Finset.prod_inv_distrib] using hb

private lemma factored_of_le {n y : ℕ} (hn : 0 < n) (hny : n ≤ y) :
    n ∈ Nat.factoredNumbers (Nat.primesLE y) := by
  rw [Nat.mem_factoredNumbers_iff_forall_le]
  exact ⟨hn.ne', fun p hp hprime _ => Nat.mem_primesLE.mpr ⟨hp.trans hny, hprime⟩⟩

private lemma sum_harmonic_and_tail {m : ℕ} (hm : 1 < m) :
    ((harmonic (m ^ 4) : ℚ) : ℝ) +
      (∑ p ∈ Nat.primesLE (m ^ 4) \ Nat.primesLE (m ^ 3), (p : ℝ)⁻¹) *
        (∑ n ∈ Icc (m + 1) (m ^ 2), (n : ℝ)⁻¹) ≤ (survivorFactor (m ^ 4))⁻¹ := by
  let P := Nat.primesLE (m ^ 4) \ Nat.primesLE (m ^ 3)
  let J := Icc (m + 1) (m ^ 2)
  let L := Icc 1 (m ^ 4)
  let f : ℕ × ℕ → ℕ := fun x => x.1 * x.2
  let T := (P ×ˢ J).image f
  have h23 : m ^ 2 ≤ m ^ 3 := Nat.pow_le_pow_right (by omega) (by decide)
  have h24 : m ^ 2 ≤ m ^ 4 := Nat.pow_le_pow_right (by omega) (by decide)
  have hp (p : ℕ) (hp : p ∈ P) : m ^ 3 < p ∧ p ≤ m ^ 4 ∧ p.Prime := by
    obtain ⟨hp₁, hp₂⟩ := mem_sdiff.mp hp
    obtain ⟨hle, hpp⟩ := Nat.mem_primesLE.mp hp₁
    exact ⟨lt_of_not_ge (fun h => hp₂ (Nat.mem_primesLE.mpr ⟨h, hpp⟩)), hle, hpp⟩
  have hf : Set.InjOn f (P ×ˢ J : Finset (ℕ × ℕ)) := by
    rintro ⟨p, n⟩ ha ⟨q, k⟩ hb hab
    obtain ⟨hap, han⟩ := mem_product.mp ha
    obtain ⟨hbq, hbk⟩ := mem_product.mp hb
    have hn := (mem_Icc.mp han).1
    have hk := (mem_Icc.mp hbk).2
    change p * n = q * k at hab
    have hpd : p ∣ q * k := hab ▸ dvd_mul_right p n
    have hpq : p = q := by
      rcases ((hp p hap).2.2.dvd_mul.mp hpd) with h | h
      · exact ((Nat.dvd_prime (hp q hbq).2.2).mp h).resolve_left (hp p hap).2.2.ne_one
      · have hkpos := (mem_Icc.mp hbk).1
        have := Nat.le_of_dvd (by omega : 0 < k) h
        have := (hp p hap).1
        omega
    subst q
    congr
    exact Nat.eq_of_mul_eq_mul_left (hp p hap).2.2.pos hab
  have hd : Disjoint L T := by
    refine Finset.disjoint_left.mpr ?_
    intro a ha hb
    obtain ⟨⟨p, n⟩, hx, rfl⟩ := mem_image.mp hb
    obtain ⟨hxp, hxn⟩ := mem_product.mp hx
    have hmp : m ^ 4 = m ^ 3 * m := by ring
    have hlt : m ^ 4 < p * n := by
      rw [hmp]
      exact Nat.mul_lt_mul_of_lt_of_le (hp p hxp).1
        (by have := (mem_Icc.mp hxn).1; omega) (show 0 < n by have := (mem_Icc.mp hxn).1; omega)
    exact (not_lt_of_ge (mem_Icc.mp ha).2) hlt
  have hfact (n : ℕ) (hn : n ∈ L ∪ T) : n ∈ Nat.factoredNumbers (Nat.primesLE (m ^ 4)) := by
    rcases mem_union.mp hn with hl | ht
    · exact factored_of_le (mem_Icc.mp hl).1 (mem_Icc.mp hl).2
    · obtain ⟨⟨p, k⟩, hx, rfl⟩ := mem_image.mp ht
      obtain ⟨hxp, hxk⟩ := mem_product.mp hx
      exact Nat.mul_mem_factoredNumbers
        (factored_of_le (hp p hxp).2.2.pos (hp p hxp).2.1)
        (factored_of_le (by have := (mem_Icc.mp hxk).1; omega) ((mem_Icc.mp hxk).2.trans h24))
  have hb := sum_inv_le_survivorFactor_inv hfact
  rw [sum_union hd, sum_image hf] at hb
  simpa only [L, T, P, J, f, harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
    Rat.cast_natCast, Nat.cast_mul, mul_inv, Finset.sum_product, ← Finset.mul_sum,
    ← Finset.sum_mul] using hb

private lemma survivorFactor_pow_four :
    ∀ᶠ m : ℕ in atTop, (4 + 1 / 16 : ℝ) * Real.log m ≤ (survivorFactor (m ^ 4))⁻¹ := by
  have hlogt : Tendsto (fun m : ℕ => Real.log (m : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (2 : ℕ),
    hlogt.eventually_ge_atTop (8 * (2 + Real.log 2 + Real.log 4)),
    hlogt.eventually_ge_atTop 2] with m hm hml hm2
  have hmpos : 0 < m := by omega
  have h34 : m ^ 3 ≤ m ^ 4 := Nat.pow_le_pow_right (by omega) (by decide)
  have h12 : m ≤ m ^ 2 := by nlinarith
  let P := Nat.primesLE (m ^ 4) \ Nat.primesLE (m ^ 3)
  have hlog (k : ℕ) : Real.log ((m ^ k : ℕ) : ℝ) = k * Real.log m := by
    rw [Nat.cast_pow, Real.log_pow]
  have hs := sum_sdiff (f := fun p : ℕ => Real.log p / (p : ℝ)) (Nat.primesLE_mono h34)
  have ha := mertens_first_lower_explicit (m ^ 4) (Nat.one_le_iff_ne_zero.mpr (by positivity))
  have hb := mertens_first_upper_explicit (m ^ 3) (Nat.one_le_iff_ne_zero.mpr (by positivity))
  rw [hlog] at ha hb
  norm_num at ha hb
  have hP : (1 / 8 : ℝ) ≤ ∑ p ∈ P, (p : ℝ)⁻¹ := by
    have hsmall : Real.log m - (2 + Real.log 2 + Real.log 4) ≤
        ∑ p ∈ P, Real.log p / (p : ℝ) := by
      change (∑ p ∈ P, _) + _ = _ at hs
      linarith
    have hlarge : (∑ p ∈ P, Real.log p / (p : ℝ)) ≤
        (4 * Real.log m) * ∑ p ∈ P, (p : ℝ)⁻¹ := by
      rw [mul_sum]
      refine sum_le_sum fun p hp => ?_
      have hp' := Nat.mem_primesLE.mp (mem_sdiff.mp hp).1
      have hlog' := Real.log_le_log
        (show (0 : ℝ) < p by exact_mod_cast hp'.2.pos)
        (show (p : ℝ) ≤ (m ^ 4 : ℕ) by exact_mod_cast hp'.1)
      rw [hlog] at hlog'
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hlog') (by positivity)
    have hprod : (4 * Real.log m) * (1 / 8 : ℝ) ≤
        (4 * Real.log m) * ∑ p ∈ P, (p : ℝ)⁻¹ := by linarith
    exact le_of_mul_le_mul_left hprod (by linarith)
  have hh (k : ℕ) : Real.log ((m ^ k : ℕ) : ℝ) ≤ (harmonic (m ^ k) : ℝ) := by
    refine (Real.log_le_log (by positivity) ?_).trans (log_add_one_le_harmonic _)
    exact_mod_cast Nat.le_succ (m ^ k)
  have hJ : Real.log m / 2 ≤ ∑ n ∈ Icc (m + 1) (m ^ 2), (n : ℝ)⁻¹ := by
    have he : Icc (m + 1) (m ^ 2) = Icc 1 (m ^ 2) \ Icc 1 m := by
      ext n
      simp only [Finset.mem_sdiff, mem_Icc]
      omega
    rw [he]
    have he' := sum_sdiff (f := fun n : ℕ => (n : ℝ)⁻¹)
      (Icc_subset_Icc_right h12 : Icc 1 m ⊆ Icc 1 (m ^ 2))
    have h₁ := hh 2
    have h₂ := harmonic_le_one_add_log m
    rw [hlog] at h₁
    norm_num at h₁
    simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] at h₁ h₂
    linarith
  have htail := mul_le_mul hP hJ (by linarith) (by linarith)
  have hh4 := hh 4
  rw [hlog] at hh4
  norm_num at hh4
  have hbound := sum_harmonic_and_tail (m := m) (by omega)
  change _ + (∑ p ∈ P, _) * _ ≤ _ at hbound
  linarith

private lemma lower_bound_of_parameters (c : ℝ) (hc : 1 < c)
    (hparams : ∀ B : ℕ, ∀ᶠ N : ℕ in atTop, 1 < N ∧
      ∃ y z : ℕ, 1 ≤ z ∧
        (c * Real.log N + 1) * survivorFactor y ≤
          ((Nat.primesLE z \ Nat.primesLE y).card : ℝ) ∧
        Real.log (B + c * Real.log N + 2) + Real.log 4 * y +
          (c * Real.log N + 1) * survivorFactor y * Real.log z ≤ Real.log N) :
    ∀ A : Set ℕ, Erdos32.IsAdditiveComplementToPrimes A →
      (1 : EReal) < liminf (fun N : ℕ =>
        (((Icc 1 N).filter (· ∈ A)).card / Real.log N : EReal)) atTop := by
  classical
  intro A hA
  obtain ⟨B, hB⟩ := Filter.eventually_atTop.mp hA
  have hlow : ∀ᶠ N : ℕ in atTop, (c : EReal) ≤
      (((Icc 1 N).filter (· ∈ A)).card / Real.log N : EReal) := by
    filter_upwards [hparams B] with N hN
    obtain ⟨hN, y, z, hz, hQ, hmodulus⟩ := hN
    let S := (Icc 0 N).filter (· ∈ A)
    let S' := (Icc 1 N).filter (· ∈ A)
    have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
    change (c : EReal) ≤ ((S'.card : EReal) / (Real.log N : EReal))
    rw [← EReal.coe_natCast, ← EReal.coe_div, EReal.coe_le_coe_iff, le_div_iff₀ hlog]
    by_contra! hsmall
    have hsub : S ⊆ insert 0 S' := by
      intro a ha
      simp only [S, mem_filter, mem_Icc] at ha
      by_cases ha0 : a = 0
      · exact mem_insert.mpr (Or.inl ha0)
      · exact mem_insert_of_mem (mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, ha.1.2⟩, ha.2⟩)
    have hcard : (S.card : ℝ) ≤ c * Real.log N + 1 := by
      have ht := (card_le_card hsub).trans (card_insert_le 0 S')
      have ht' : (S.card : ℝ) ≤ (S'.card : ℝ) + 1 := by exact_mod_cast ht
      linarith
    let P := Nat.primesLE y
    let Q := Nat.primesLE z \ P
    have hpq : ∀ p ∈ P ∪ Q, p.Prime := by
      intro p hp
      rcases mem_union.mp hp with hp | hp
      · exact Nat.prime_of_mem_primesLE hp
      · exact Nat.prime_of_mem_primesLE (mem_sdiff.mp hp).1
    have hdisj : Disjoint P Q :=
      Finset.disjoint_left.mpr fun p hp hq => (mem_sdiff.mp hq).2 hp
    have hSQ : (S.card : ℝ) * survivorFactor y ≤ Q.card :=
      (mul_le_mul_of_nonneg_right hcard (survivorFactor_pos y).le).trans hQ
    obtain ⟨T, hT, hTc, b, hb, hbcover⟩ := exists_covering_congruences P Q S hpq hdisj hSQ
    have hprime : ∀ p ∈ P ∪ T, p.Prime :=
      fun p hp => hpq p (union_subset_union_right hT hp)
    have hsize : (B + S.card + 1) * (∏ p ∈ P ∪ T, p) ≤ N := by
      have hm : 0 < ∏ p ∈ P ∪ T, p := prod_pos fun p hp => (hprime p hp).pos
      have hL : Real.log ((B + S.card + 1 : ℕ) : ℝ) ≤
            Real.log (B + c * Real.log N + 2) := by
        apply Real.log_le_log (by positivity)
        push_cast
        linarith
      have hTbound : (T.card : ℝ) * Real.log z ≤
          (c * Real.log N + 1) * survivorFactor y * Real.log z := by
        refine mul_le_mul_of_nonneg_right (hTc.trans ?_) (Real.log_nonneg (by exact_mod_cast hz))
        exact mul_le_mul_of_nonneg_right hcard (survivorFactor_pos y).le
      have hM := (log_modulus_bound hT).trans
        (add_le_add_right hTbound (Real.log 4 * y))
      have h : Real.log ((B + S.card + 1 : ℕ) : ℝ) +
          Real.log ((∏ p ∈ P ∪ T, p : ℕ) : ℝ) ≤ Real.log N :=
        (add_le_add hL hM).trans (by linarith only [hmodulus])
      rw [← Real.log_mul (by positivity) (by exact_mod_cast hm.ne')] at h
      have h' := (Real.log_le_log_iff (by positivity) (by positivity)).mp h
      exact_mod_cast h'
    obtain ⟨n, hn, havoid⟩ := exists_uncovered S (P ∪ T) hprime hb hbcover hsize
    obtain ⟨p, hp, a, ha, he⟩ := hB n (mem_Icc.mp hn).1
    exact havoid a (mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, by have := (mem_Icc.mp hn).2; omega⟩, ha⟩)
      p hp he
  exact (EReal.coe_lt_coe_iff.mpr hc).trans_le
    (Filter.le_liminf_of_le (by isBoundedDefault) hlow)

private lemma eventually_log_affine_le {a b d : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hd : 0 < d) :
    ∀ᶠ x : ℝ in atTop, Real.log (a * x + b) ≤ d * x := by
  have hsum : 0 < a + b := by linarith
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    eventually_ge_atTop (Real.log (a + b) / (d / 2)),
    Real.isLittleO_log_id_atTop.bound (show 0 < d / 2 by positivity)] with x hx hxc hlog
  have hx0 : 0 < x := by linarith
  have hbc : b ≤ b * x := by simpa using mul_le_mul_of_nonneg_left hx hb
  have h := Real.log_le_log (show 0 < a * x + b by positivity)
    (show a * x + b ≤ (a + b) * x by linarith)
  rw [Real.log_mul hsum.ne' hx0.ne'] at h
  have hcon := (div_le_iff₀ (show 0 < d / 2 by positivity)).mp hxc
  change ‖Real.log x‖ ≤ d / 2 * ‖x‖ at hlog
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hx), abs_of_pos hx0] at hlog
  linarith

private lemma eventually_prime_supply {b : ℝ} (hb : 1 < b) :
    ∀ᶠ x : ℝ in atTop, 3 * x ≤
      ((Nat.primesLE ⌊x ^ b⌋₊).card : ℝ) := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hb0 : 0 < b := by linarith
  have ht := tendsto_rpow_atTop hb0
  have hh : ∀ᶠ x : ℝ in atTop, Real.log (x ^ b + 2) ≤ Real.log 2 / 4 * (x ^ b) := by
    simpa using ht.eventually
      (eventually_log_affine_le (a := 1) (b := 2) (d := Real.log 2 / 4)
        (by norm_num) (by norm_num) (by positivity))
  have hj := (isLittleO_log_rpow_atTop (show 0 < b - 1 by linarith)).bound
    (show 0 < Real.log 2 / (6 * b) by positivity)
  filter_upwards [eventually_gt_atTop (1 : ℝ), ht.eventually_ge_atTop 4, hh, hj]
    with x hx hpow hlog hsmall
  have hx0 : 0 < x := by linarith
  have hpow' : 1 < x ^ b := by linarith
  have hCheb := Chebyshev.pi_ge' hpow'
  rw [← Nat.primesLE_card_eq_primeCounting] at hCheb
  refine le_trans ?_ hCheb
  rw [le_div_iff₀ (Real.log_pos hpow')]
  have hlin : Real.log 2 ≤ Real.log 2 / 4 * x ^ b := by nlinarith
  have hhalf : Real.log 2 / 2 * x ^ b ≤ (x ^ b - 1) * Real.log 2 - Real.log (x ^ b + 2) := by
    linarith only [hlin, hlog]
  refine le_trans ?_ hhalf
  change ‖Real.log x‖ ≤ (Real.log 2 / (6 * b)) * ‖x ^ (b - 1)‖ at hsmall
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.log_pos hx),
    abs_of_pos (Real.rpow_pos_of_pos hx0 _)] at hsmall
  have hs := (le_div_iff₀ (show 0 < 6 * b by positivity)).mp
    (show Real.log x ≤ (Real.log 2 * x ^ (b - 1)) / (6 * b) by
      simpa only [div_mul_eq_mul_div] using hsmall)
  have hs' := mul_le_mul_of_nonneg_right hs hx0.le
  have he : x ^ (b - 1) * x = x ^ b := calc
    _ = x ^ (b - 1) * x ^ (1 : ℝ) := by rw [Real.rpow_one]
    _ = x ^ b := by rw [← Real.rpow_add hx0, sub_add_cancel]
  rw [Real.log_rpow hx0]
  calc
    3 * x * (b * Real.log x) = (Real.log x * (6 * b) * x) / 2 := by ring
    _ ≤ (Real.log 2 * x ^ (b - 1) * x) / 2 := by linarith only [hs']
    _ = Real.log 2 / 2 * x ^ b := by rw [mul_assoc, he]; ring

private lemma eventually_parameters (B : ℕ) :
    ∀ᶠ x : ℝ in atTop, ∃ y z : ℕ, 1 ≤ z ∧
      ((1001 / 1000 : ℝ) * x + 1) * survivorFactor y ≤
        ((Nat.primesLE z \ Nat.primesLE y).card : ℝ) ∧
      Real.log (B + (1001 / 1000 : ℝ) * x + 2) + Real.log 4 * y +
        ((1001 / 1000 : ℝ) * x + 1) * survivorFactor y * Real.log z ≤ x := by
  let a : ℝ := 255 / 1024
  let b : ℝ := 257 / 256
  have ha : 0 < a := by norm_num [a]
  have hb : 1 < b := by norm_num [b]
  have hB : ∀ᶠ x : ℝ in atTop, Real.log (B + (1001 / 1000 : ℝ) * x + 2) ≤ (1 / 1000 : ℝ) * x := by
    filter_upwards [eventually_log_affine_le (a := 1001 / 1000) (b := (B : ℝ) + 2)
      (d := 1 / 1000) (by norm_num) (by positivity) (by norm_num)] with x hx
    convert hx using 2
    ring
  have ht := tendsto_rpow_atTop ha
  have hu := tendsto_rpow_atTop (show 0 < 1 - 4 * a by norm_num [a])
  have hv := tendsto_rpow_atTop (show 0 < b by linarith)
  filter_upwards [eventually_ge_atTop (1000 : ℝ), ht.eventually_ge_atTop 2,
    hv.eventually_ge_atTop 1, hu.eventually_ge_atTop (1000 * Real.log 4), hB,
    Real.tendsto_log_atTop.eventually_ge_atTop (10000 * (Real.log 2 + 1)),
    (tendsto_nat_floor_atTop.comp ht).eventually survivorFactor_pow_four,
    eventually_prime_supply hb] with x hx hxa hxb hux hBlog hloglarge hF hQ
  let m : ℕ := ⌊x ^ a⌋₊
  let y : ℕ := m ^ 4
  let z : ℕ := ⌊x ^ b⌋₊
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hxlog : 0 < Real.log x := Real.log_pos (by linarith)
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hm : x ^ a / 2 ≤ (m : ℝ) := by
    have hh := Nat.lt_floor_add_one (x ^ a)
    change x ^ a < (m : ℝ) + 1 at hh
    linarith
  have hm' : (m : ℝ) ≤ x ^ a := Nat.floor_le (by positivity)
  have hy : (y : ℝ) ≤ x ^ (4 * a) := by
    rw [mul_comm, show (4 : ℝ) = (4 : ℕ) by norm_num, Real.rpow_mul_natCast hx0.le]
    exact_mod_cast (pow_le_pow_left₀ (Nat.cast_nonneg m) hm' 4)
  have hyx : (y : ℝ) ≤ x :=
    hy.trans (by
      nth_rw 2 [← Real.rpow_one x]
      exact Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num [a]))
  have hz : 1 ≤ z := Nat.le_floor (by exact_mod_cast hxb)
  have hz' : (z : ℝ) ≤ x ^ b := Nat.floor_le (by positivity)
  have hzlog : Real.log (z : ℝ) ≤ b * Real.log x := by
    rw [← Real.log_rpow hx0]
    apply Real.log_le_log _ hz'
    exact_mod_cast (show 0 < z by omega)
  have h2m := Real.log_le_log (show 0 < x ^ a / 2 by positivity) hm
  rw [Real.log_div (by positivity) (by norm_num), Real.log_rpow hx0] at h2m
  change (4 + 1 / 16 : ℝ) * Real.log m ≤ (survivorFactor y)⁻¹ at hF
  have hd : (101 / 100 : ℝ) * Real.log x ≤ (survivorFactor y)⁻¹ := by
    apply le_trans _ hF
    dsimp [a] at h2m
    linarith only [h2m, hloglarge, h2]
  have hdpos : 0 < (101 / 100 : ℝ) * Real.log x := by positivity
  have hfactor := (le_inv_comm₀ hdpos (survivorFactor_pos y)).mp hd
  have hlog1 : (1 : ℝ) ≤ (101 / 100 : ℝ) * Real.log x := by linarith
  have hfactor1 := hfactor.trans (inv_le_one_of_one_le₀ hlog1)
  have hcx : (1001 / 1000 : ℝ) * x + 1 ≤ (1002 / 1000 : ℝ) * x := by linarith
  have hcardy : ((Nat.primesLE y).card : ℝ) ≤ x := by
    have hc : (Nat.primesLE y).card ≤ y := by
      simpa using (card_le_card (show Nat.primesLE y ⊆ Icc 1 y from fun p hp =>
        mem_Icc.mpr ⟨(Nat.prime_of_mem_primesLE hp).one_le, (Nat.mem_primesLE.mp hp).1⟩))
    exact (show ((Nat.primesLE y).card : ℝ) ≤ y by exact_mod_cast hc).trans hyx
  change 3 * x ≤ ((Nat.primesLE z).card : ℝ) at hQ
  have hcards : ((Nat.primesLE z).card : ℝ) ≤
      ((Nat.primesLE z \ Nat.primesLE y).card : ℝ) + ((Nat.primesLE y).card : ℝ) := by
    exact_mod_cast (Finset.card_le_card_sdiff_add_card (s := Nat.primesLE z) (t := Nat.primesLE y))
  have hycost : Real.log 4 * (y : ℝ) ≤ (1 / 1000 : ℝ) * x := by
    have h := mul_le_mul_of_nonneg_right hux (Real.rpow_nonneg hx0.le (4 * a))
    rw [mul_assoc, ← Real.rpow_add hx0, show 1 - 4 * a + 4 * a = 1 by ring, Real.rpow_one] at h
    have hy' := mul_le_mul_of_nonneg_left hy h4.le
    linarith only [h, hy']
  have hratio : survivorFactor y * Real.log z ≤ b / (101 / 100 : ℝ) := by
    have hzlog0 : 0 ≤ Real.log (z : ℝ) := Real.log_nonneg (by exact_mod_cast hz)
    calc
      _ ≤ ((101 / 100 : ℝ) * Real.log x)⁻¹ * (b * Real.log x) := by gcongr
      _ = _ := by field_simp
  have hcost : ((1001 / 1000 : ℝ) * x + 1) * survivorFactor y * Real.log z ≤
      (998 / 1000 : ℝ) * x := by
    rw [mul_assoc]
    calc
      _ ≤ ((1002 / 1000 : ℝ) * x) * (b / (101 / 100 : ℝ)) := by
        gcongr
        exact mul_nonneg (survivorFactor_pos y).le (Real.log_nonneg (by exact_mod_cast hz))
      _ ≤ _ := by dsimp [b]; linarith
  refine ⟨y, z, hz, ?_, by linarith only [hBlog, hycost, hcost]⟩
  have hf : ((1001 / 1000 : ℝ) * x + 1) * survivorFactor y ≤
      ((1001 / 1000 : ℝ) * x + 1) * 1 :=
    mul_le_mul_of_nonneg_left hfactor1 (by positivity)
  linarith only [hf, hcx, hcards, hcardy, hQ, hx]

private lemma strict_liminf :
    ∀ A : Set ℕ, Erdos32.IsAdditiveComplementToPrimes A →
      (1 : EReal) < liminf (fun N : ℕ =>
        (((Icc 1 N).filter (· ∈ A)).card / Real.log N : EReal)) atTop := by
  apply lower_bound_of_parameters (1001 / 1000) (by norm_num)
  intro B
  have ht : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (2 : ℕ), ht.eventually (eventually_parameters B)] with N hN h
  exact ⟨by omega, h⟩

end OMA32

theorem OMA.solution : type_of% @Erdos32.erdos_32.variants.liminf_gt_one := by
  exact OMA32.strict_liminf

