import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1

-- Reduction Erdos1052.erdos_1052.R1.H2.R1.H1.R1
-- Credit: @adammcarter
-- Splits step H1 of Erdos1052.erdos_1052.R1.H2.R1 (the 2-adic valuation is bounded over the
-- unitary perfect numbers whose set S of repeated odd primes is not admissible) by the shape of
-- S, with the cases proved in rounds 3 and 4 built in.  Proving the three H proves the step.
--
-- Notation: n unitary perfect, a = padicValNat 2 n, a REPEATED odd prime is an odd prime p with
-- p^2 | n, e = the exponent of the repeated prime (n.factorization z).  Admissible is as in the
-- parent file.  S is never empty here: the empty set is admissible.  For S = {z} admissibility
-- is exactly 128 <= z, 4 <= z and (z + 1) / (z - 3) <= 2101/2097, i.e. z >= 2100; main proves the
-- direction it needs (z >= 2100 makes {z} admissible), so a lone repeated prime z here is < 2100.
-- e is an ODD MULTIPLE of d when e mod 2d = d; then z^d + 1 divides z^e + 1.
--
-- PROVED BELOW, no hypothesis needed (from rounds 3 and 4, the lemmas of this file):
--   S = {3}: if 2 <= e <= 40 then n = 90 or e is 5, 7, 11, 13 or 19 (three_exponent_cases_forty),
--     and e is never an odd multiple of any d in
--     D3 = 6, 8, 9, 10, 12, 14, 15, 16, 17, 20, 21, 22, 23, 25, 26, 28, 29, 31, 32, 33, 34, 35,
--          37, 38, 39 (three_exponent_residues).
--   S = {z}, z = 2 mod 3, e odd: e = 1 mod 6 (odd_exponent_mod_six).
--   S = {5}: 2 <= e <= 40 gives e = 2 or 4, and e is never an odd multiple of any d in
--     D5 = 5, 6, 7, 8, 10, 12, 13, 14, 16, 19, 20, 22, 26, 28, 29, 31, 32, 34, 37, 38.
--   S = {7}: e >= 41, and e is never an odd multiple of any d in
--     D7 = 2, 3, 4, 5, 7, 8, 11, 13, 16, 17, 19, 23, 29, 31, 32, 37.
-- Method: the forced primes of z^d + 1 give some odd prime two sources in the balance equation,
-- or a weight (path product) bound below 2; primes above 5 * 10^7 are certified by the Lucas
-- test.  The case n = 90 (a = 1) is absorbed into the bound of main.
--
-- H1 (OPEN): S = {3} with e in {5, 7, 11, 13, 19} or e >= 41, e no odd multiple of any d in D3.
--    Contains no known unitary perfect number (90 has e = 2).
-- H2 (OPEN): S = {z} with 5 <= z < 2100, with the restrictions above for e.  Contains Wall's
--    number 2^18 * 3 * 5^4 * 7 * 11 * 13 * 19 * 37 * 79 * 109 * 157 * 313 (z = 5, e = 4).
-- H3 (OPEN): at least two repeated odd primes and S not admissible (as in the parent).

namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1

-- H1: the 2-adic valuation is bounded over the unitary perfect numbers whose only repeated odd
-- prime is 3, where the exponent e of 3 is 5, 7, 11, 13, 19 or at least 41, and e is not an
-- odd multiple of any d in D3 (the list in the header).
def H1 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 3) →
    (n.factorization 3 = 5 ∨ n.factorization 3 = 7 ∨ n.factorization 3 = 11 ∨
      n.factorization 3 = 13 ∨ n.factorization 3 = 19 ∨ 41 ≤ n.factorization 3) →
    (∀ d ∈ ({6, 8, 9, 10, 12, 14, 15, 16, 17, 20, 21, 22, 23, 25, 26, 28, 29, 31, 32, 33, 34, 35, 37, 38, 39} : Finset ℕ), n.factorization 3 % (2 * d) ≠ d) →
    padicValNat 2 n ≤ A

-- H2: the 2-adic valuation is bounded over the unitary perfect numbers with exactly one repeated
-- odd prime z, 5 ≤ z < 2100, whose exponent e satisfies the proved restrictions: e = 1 mod 6
-- when z = 2 mod 3 and e is odd; for z = 5, e is 2, 4 or at least 41 and not an odd multiple of
-- any d in D5; for z = 7, e is at least 41 and not an odd multiple of any d in D7.
def H2 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n → ∀ z : ℕ, z.Prime → 5 ≤ z → z < 2100 →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = z) →
    (z % 3 = 2 → Odd (n.factorization z) → n.factorization z % 6 = 1) →
    (z = 5 → (n.factorization 5 = 2 ∨ n.factorization 5 = 4 ∨ 41 ≤ n.factorization 5) ∧
      ∀ d ∈ ({5, 6, 7, 8, 10, 12, 13, 14, 16, 19, 20, 22, 26, 28, 29, 31, 32, 34, 37, 38} : Finset ℕ),
        n.factorization 5 % (2 * d) ≠ d) →
    (z = 7 → 41 ≤ n.factorization 7 ∧
      ∀ d ∈ ({2, 3, 4, 5, 7, 8, 11, 13, 16, 17, 19, 23, 29, 31, 32, 37} : Finset ℕ),
        n.factorization 7 % (2 * d) ≠ d) →
    padicValNat 2 n ≤ A

-- H3: the 2-adic valuation is bounded over the unitary perfect numbers with at least two repeated
-- odd primes whose set S of repeated odd primes is not admissible.
def H3 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    ∀ S : Finset ℕ, (∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n) → 2 ≤ S.card →
    ¬ ((∀ z ∈ S, 128 ≤ z ∧ S.card + 3 ≤ z) ∧
      ∏ z ∈ S, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (S.card : ℚ))) ≤ 2101 / 2097) →
    padicValNat 2 n ≤ A

-- Lemmas repeated from the round-4 file Erdos1052OpenCore4.lean (only those used below).

theorem mem_udiv {n d : ℕ} :
    d ∈ Finset.filter (fun d => Nat.Coprime d (n / d)) n.divisors ↔ d ∣ n ∧ n ≠ 0 ∧ d.Coprime (n / d) := by
  simp [and_assoc]

theorem self_mem_udiv {n : ℕ} (hn : n ≠ 0) :
    n ∈ Finset.filter (fun d => Nat.Coprime d (n / d)) n.divisors := by
  rw [mem_udiv, Nat.div_self (Nat.pos_of_ne_zero hn)]
  exact ⟨dvd_rfl, hn, Nat.coprime_one_right n⟩

theorem proper_eq_erase (n : ℕ) :
    Erdos1052.properUnitaryDivisors n = (Finset.filter (fun d => Nat.Coprime d (n / d)) n.divisors).erase n := by
  ext d
  simp only [Erdos1052.properUnitaryDivisors, Finset.mem_filter, Finset.mem_Ico, Finset.mem_erase,
    Nat.mem_divisors]
  constructor
  · rintro ⟨⟨h1, h2⟩, hd, hc⟩
    exact ⟨h2.ne, ⟨hd, by omega⟩, hc⟩
  · rintro ⟨hne, ⟨hd, hn⟩, hc⟩
    have hd0 : d ≠ 0 := by rintro rfl; exact hn (zero_dvd_iff.mp hd)
    exact ⟨⟨Nat.pos_of_ne_zero hd0,
      lt_of_le_of_ne (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd) hne⟩, hd, hc⟩

theorem sum_udiv_eq_sum_proper_add {n : ℕ} (hn : n ≠ 0) :
    ∑ d ∈ Finset.filter (fun d => Nat.Coprime d (n / d)) n.divisors, d =
      (∑ i ∈ Erdos1052.properUnitaryDivisors n, i) + n := by
  rw [proper_eq_erase, Finset.sum_erase_add _ _ (self_mem_udiv hn)]

theorem sum_udiv_of_isUnitaryPerfect {n : ℕ} (h : Erdos1052.IsUnitaryPerfect n) :
    0 < n ∧ ∑ d ∈ Finset.filter (fun d => Nat.Coprime d (n / d)) n.divisors, d = 2 * n := by
  obtain ⟨hs, hpos⟩ := h
  refine ⟨hpos, ?_⟩
  rw [sum_udiv_eq_sum_proper_add hpos.ne', hs]
  ring

theorem factorization_of_mem_udiv {n d : ℕ}
    (h : d ∈ Finset.filter (fun d => Nat.Coprime d (n / d)) n.divisors) (p : ℕ) :
    d.factorization p = if p ∈ d.primeFactors then n.factorization p else 0 := by
  obtain ⟨hd, hn, hc⟩ := mem_udiv.mp h
  have hd0 : d ≠ 0 := by rintro rfl; exact hn (zero_dvd_iff.mp hd)
  have hq : n / d ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd) (Nat.pos_of_ne_zero hd0)).ne'
  have hmul : n = d * (n / d) := (Nat.mul_div_cancel' hd).symm
  split_ifs with hp
  · have hpp := Nat.prime_of_mem_primeFactors hp
    have hpd := Nat.dvd_of_mem_primeFactors hp
    have hnd : ¬ p ∣ n / d := by
      intro h'
      have := Nat.dvd_gcd hpd h'
      rw [hc.gcd_eq_one] at this
      exact hpp.not_dvd_one this
    conv_rhs => rw [hmul]
    rw [Nat.factorization_mul hd0 hq, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hnd, add_zero]
  · by_contra h'
    exact hp (Nat.support_factorization d ▸ Finsupp.mem_support_iff.mpr h')

theorem ppart_ne_zero {n : ℕ} {S : Finset ℕ} (hS : S ⊆ n.primeFactors) :
    ∏ p ∈ S, p ^ n.factorization p ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun _p hp =>
    pow_ne_zero _ (Nat.prime_of_mem_primeFactors (hS hp)).ne_zero

theorem factorization_ppart {n : ℕ} {S : Finset ℕ} (hS : S ⊆ n.primeFactors) (q : ℕ) :
    (∏ p ∈ S, p ^ n.factorization p).factorization q = if q ∈ S then n.factorization q else 0 := by
  rw [Nat.factorization_prod (fun p hp =>
    pow_ne_zero _ (Nat.prime_of_mem_primeFactors (hS hp)).ne_zero), Finsupp.finsetSum_apply]
  rw [Finset.sum_congr rfl (fun p hp => by
    rw [(Nat.prime_of_mem_primeFactors (hS hp)).factorization_pow, Finsupp.single_apply])]
  exact Finset.sum_ite_eq' S q _

theorem primeFactors_ppart {n : ℕ} {S : Finset ℕ} (hS : S ⊆ n.primeFactors) :
    (∏ p ∈ S, p ^ n.factorization p).primeFactors = S := by
  ext q
  rw [← Nat.support_factorization, Finsupp.mem_support_iff, factorization_ppart hS]
  split_ifs with h
  · simp only [h, iff_true]
    exact Finsupp.mem_support_iff.mp (by rw [Nat.support_factorization]; exact hS h)
  · simp [h]

theorem ppart_mem_udiv {n : ℕ} (hn : n ≠ 0) {S : Finset ℕ} (hS : S ⊆ n.primeFactors) :
    (∏ p ∈ S, p ^ n.factorization p) ∈ Finset.filter (fun d => Nat.Coprime d (n / d)) n.divisors := by
  have h0 := ppart_ne_zero hS
  have hdvd : (∏ p ∈ S, p ^ n.factorization p) ∣ n := by
    rw [← Nat.factorization_le_iff_dvd h0 hn]
    intro q
    rw [factorization_ppart hS]
    split_ifs <;> simp
  refine mem_udiv.mpr ⟨hdvd, hn, Nat.coprime_of_dvd fun p hp h1 h2 => ?_⟩
  have hq : n / (∏ p ∈ S, p ^ n.factorization p) ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd) (Nat.pos_of_ne_zero h0)).ne'
  have e1 := (hp.dvd_iff_one_le_factorization h0).mp h1
  have e2 := (hp.dvd_iff_one_le_factorization hq).mp h2
  rw [factorization_ppart hS] at e1
  rw [Nat.factorization_div hdvd, Finsupp.tsub_apply, factorization_ppart hS] at e2
  split_ifs at e1 e2 <;> omega

theorem eq_ppart_of_mem_udiv {n d : ℕ}
    (h : d ∈ Finset.filter (fun d => Nat.Coprime d (n / d)) n.divisors) :
    d = ∏ p ∈ d.primeFactors, p ^ n.factorization p := by
  obtain ⟨hd, hn, -⟩ := mem_udiv.mp h
  have hd0 : d ≠ 0 := by rintro rfl; exact hn (zero_dvd_iff.mp hd)
  have hsub := Nat.primeFactors_mono hd hn
  exact Nat.eq_of_factorization_eq hd0 (ppart_ne_zero hsub) fun q => by
    rw [factorization_of_mem_udiv h, factorization_ppart hsub]

theorem sum_udiv_eq_prod {n : ℕ} (hn : n ≠ 0) :
    ∑ d ∈ Finset.filter (fun d => Nat.Coprime d (n / d)) n.divisors, d =
      ∏ p ∈ n.primeFactors, (1 + p ^ n.factorization p) := by
  rw [Finset.prod_one_add]
  exact Finset.sum_nbij' (fun d => d.primeFactors) (fun S => ∏ p ∈ S, p ^ n.factorization p)
    (fun d hd => Finset.mem_powerset.mpr (Nat.primeFactors_mono (mem_udiv.mp hd).1 hn))
    (fun S hS => ppart_mem_udiv hn (Finset.mem_powerset.mp hS))
    (fun d hd => (eq_ppart_of_mem_udiv hd).symm)
    (fun S hS => primeFactors_ppart (Finset.mem_powerset.mp hS))
    (fun d hd => eq_ppart_of_mem_udiv hd)

theorem prod_primeFactors_pow_self {n : ℕ} (hn : n ≠ 0) :
    ∏ p ∈ n.primeFactors, p ^ n.factorization p = n :=
  (eq_ppart_of_mem_udiv (self_mem_udiv hn)).symm

theorem prod_eq_two_mul {n : ℕ} (h : Erdos1052.IsUnitaryPerfect n) :
    ∏ p ∈ n.primeFactors, (1 + p ^ n.factorization p) = 2 * n := by
  obtain ⟨hpos, hs⟩ := sum_udiv_of_isUnitaryPerfect h
  rw [← sum_udiv_eq_prod hpos.ne']
  exact hs

theorem B_step {c p : ℕ} (hc : 2 ≤ c) (hp : 2 * c ≤ p + 1) :
    (1 + 1 / (c : ℚ)) * (((p : ℚ) + 1) / ((p : ℚ) - 1)) ≤ ((c : ℚ) + 1) / ((c : ℚ) - 1) := by
  have hc' : (2 : ℚ) ≤ c := by exact_mod_cast hc
  have hp' : 2 * (c : ℚ) ≤ p + 1 := by exact_mod_cast hp
  have h1 : (0 : ℚ) < c - 1 := by linarith
  have h2 : (0 : ℚ) < (p : ℚ) - 1 := by linarith
  have h3 : (0 : ℚ) < c := by linarith
  have e : (1 + 1 / (c : ℚ)) = ((c : ℚ) + 1) / c := by field_simp
  rw [e, div_mul_div_comm, div_le_div_iff₀ (mul_pos h3 h2) h1]
  nlinarith [mul_nonneg (by linarith : (0 : ℚ) ≤ (c : ℚ) + 1) (by linarith : (0 : ℚ) ≤ (p : ℚ) + 1 - 2 * c)]

theorem B_anti {a b : ℕ} (ha : 2 ≤ a) (hab : a ≤ b) :
    ((b : ℚ) + 1) / ((b : ℚ) - 1) ≤ ((a : ℚ) + 1) / ((a : ℚ) - 1) := by
  have ha' : (2 : ℚ) ≤ a := by exact_mod_cast ha
  have hab' : (a : ℚ) ≤ b := by exact_mod_cast hab
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

theorem one_add_le_B {p : ℕ} (hp : 2 ≤ p) :
    1 + 1 / (p : ℚ) ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
  have hp' : (2 : ℚ) ≤ p := by exact_mod_cast hp
  have e : (1 + 1 / (p : ℚ)) = ((p : ℚ) + 1) / p := by field_simp
  rw [e, div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

theorem path_bound (g : ℕ → ℕ) (β : ℕ → ℚ) : ∀ (n : ℕ) (P : Finset ℕ), P.card = n →
    (∀ p ∈ P, 0 < p) →
    (∀ p ∈ P, g p ∈ P → g p < p) →
    (∀ p ∈ P, ∀ p' ∈ P, g p ∈ P → g p = g p' → p = p') →
    (∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p) →
    (∀ p ∈ P, g p ∈ P → (1 + 1 / ((g p : ℕ) : ℚ)) * β p ≤ β (g p)) →
    ∏ p ∈ P, (1 + 1 / (p : ℚ)) ≤ ∏ q ∈ P.filter (fun q => g q ∉ P), β q := by
  intro n
  induction n with
  | zero =>
    intro P hP _ _ _ _ _
    rw [Finset.card_eq_zero.mp hP]
    simp
  | succ n ih =>
    intro P hcard hpos hlt hinj hβ hstep
    have hne : P.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨q, hqP, hqmin⟩ : ∃ q ∈ P, ∀ p ∈ P, q ≤ p :=
      ⟨P.min' hne, Finset.min'_mem P hne, fun p hp => Finset.min'_le P p hp⟩
    have hgq : g q ∉ P := fun h => absurd (hqmin _ h) (not_le.mpr (hlt q hqP h))
    have hβpos : ∀ p ∈ P, 0 < β p := fun p hp => by
      have h0 : (0 : ℚ) ≤ 1 / (p : ℚ) := by positivity
      linarith [hβ p hp]
    have hmem : ∀ x, x ∈ P.erase q → x ∈ P := fun x hx => Finset.mem_of_mem_erase hx
    have ih' := ih (P.erase q) (by rw [Finset.card_erase_of_mem hqP, hcard]; rfl)
      (fun p hp => hpos p (hmem p hp))
      (fun p hp hg => hlt p (hmem p hp) (hmem _ hg))
      (fun p hp p' hp' hg he => hinj p (hmem p hp) p' (hmem p' hp') (hmem _ hg) he)
      (fun p hp => hβ p (hmem p hp))
      (fun p hp hg => hstep p (hmem p hp) (hmem _ hg))
    have hqL : q ∈ P.filter (fun q => g q ∉ P) := Finset.mem_filter.mpr ⟨hqP, hgq⟩
    have hrest0 : 0 ≤ ∏ x ∈ (P.filter (fun q => g q ∉ P)).erase q, β x :=
      Finset.prod_nonneg fun x hx =>
        (hβpos x (Finset.mem_filter.mp (Finset.mem_of_mem_erase hx)).1).le
    have hq0 : (0 : ℚ) ≤ 1 + 1 / (q : ℚ) := by positivity
    have key : (1 + 1 / (q : ℚ)) * ∏ x ∈ (P.erase q).filter (fun x => g x ∉ P.erase q), β x ≤
        β q * ∏ x ∈ (P.filter (fun q => g q ∉ P)).erase q, β x := by
      by_cases hpar : ∃ p ∈ P, g p = q
      · obtain ⟨p, hpP, hpq⟩ := hpar
        have hpne : p ≠ q := by
          intro h
          have := hlt p hpP (hpq ▸ hqP)
          omega
        have hset : (P.erase q).filter (fun x => g x ∉ P.erase q) =
            insert p ((P.filter (fun q => g q ∉ P)).erase q) := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_insert, not_and]
          constructor
          · rintro ⟨⟨hxq, hxP⟩, hx⟩
            by_cases hgx : g x = q
            · left
              exact (hinj p hpP x hxP (hpq ▸ hqP) (hpq.trans hgx.symm)).symm
            · right
              exact ⟨hxq, hxP, fun h => hx hgx h⟩
          · rintro (rfl | ⟨hxq, hxP, hx⟩)
            · exact ⟨⟨hpne, hpP⟩, fun h => absurd hpq h⟩
            · exact ⟨⟨hxq, hxP⟩, fun _ h => hx h⟩
        have hnotin : p ∉ (P.filter (fun q => g q ∉ P)).erase q := by
          intro h
          exact (Finset.mem_filter.mp (Finset.mem_of_mem_erase h)).2 (hpq ▸ hqP)
        rw [hset, Finset.prod_insert hnotin, ← mul_assoc]
        refine mul_le_mul_of_nonneg_right ?_ hrest0
        have := hstep p hpP (hpq ▸ hqP)
        rwa [hpq] at this
      · have hset : (P.erase q).filter (fun x => g x ∉ P.erase q) =
            (P.filter (fun q => g q ∉ P)).erase q := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_erase, not_and]
          constructor
          · rintro ⟨⟨hxq, hxP⟩, hx⟩
            exact ⟨hxq, hxP, fun h => hx (fun hgx => hpar ⟨x, hxP, hgx⟩) h⟩
          · rintro ⟨hxq, hxP, hx⟩
            exact ⟨⟨hxq, hxP⟩, fun _ h => hx h⟩
        rw [hset]
        exact mul_le_mul_of_nonneg_right (hβ q hqP) hrest0
    calc ∏ p ∈ P, (1 + 1 / (p : ℚ))
        = (1 + 1 / (q : ℚ)) * ∏ p ∈ P.erase q, (1 + 1 / (p : ℚ)) :=
          (Finset.mul_prod_erase P (fun p : ℕ => (1 + 1 / (p : ℚ))) hqP).symm
      _ ≤ (1 + 1 / (q : ℚ)) * ∏ x ∈ (P.erase q).filter (fun x => g x ∉ P.erase q), β x :=
          mul_le_mul_of_nonneg_left ih' hq0
      _ ≤ β q * ∏ x ∈ (P.filter (fun q => g q ∉ P)).erase q, β x := key
      _ = ∏ q ∈ P.filter (fun q => g q ∉ P), β q := Finset.mul_prod_erase _ β hqL

theorem tail_bound : ∀ (n : ℕ) (Q : Finset ℕ) (a : ℕ), Q.card = n → 4 ≤ a → (∀ q ∈ Q, a ≤ q) →
    (∀ q ∈ Q, ∀ q' ∈ Q, q < q' → 2 * q + 1 ≤ q') →
    ∏ q ∈ Q, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ ((a : ℚ) + 1) / ((a : ℚ) - 3) := by
  intro n
  induction n with
  | zero =>
    intro Q a hQ ha _ _
    have ha' : (4 : ℚ) ≤ a := by exact_mod_cast ha
    rw [Finset.card_eq_zero.mp hQ, Finset.prod_empty, le_div_iff₀ (by linarith)]
    linarith
  | succ n ih =>
    intro Q a hcard ha hge hdbl
    have hne : Q.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨q, hqQ, hqmin⟩ : ∃ q ∈ Q, ∀ p ∈ Q, q ≤ p :=
      ⟨Q.min' hne, Finset.min'_mem Q hne, fun p hp => Finset.min'_le Q p hp⟩
    have haq : a ≤ q := hge q hqQ
    have ih' := ih (Q.erase q) (2 * q + 1) (by rw [Finset.card_erase_of_mem hqQ, hcard]; rfl)
      (by omega)
      (fun x hx => hdbl q hqQ x (Finset.mem_of_mem_erase hx)
        (lt_of_le_of_ne (hqmin x (Finset.mem_of_mem_erase hx)) (Finset.ne_of_mem_erase hx).symm))
      (fun x hx y hy => hdbl x (Finset.mem_of_mem_erase hx) y (Finset.mem_of_mem_erase hy))
    have ha' : (4 : ℚ) ≤ a := by exact_mod_cast ha
    have haq' : (a : ℚ) ≤ q := by exact_mod_cast haq
    have hB0 : (0 : ℚ) ≤ ((q : ℚ) + 1) / ((q : ℚ) - 1) := div_nonneg (by linarith) (by linarith)
    rw [← Finset.mul_prod_erase Q _ hqQ]
    calc ((q : ℚ) + 1) / ((q : ℚ) - 1) * ∏ x ∈ Q.erase q, (((x : ℚ) + 1) / ((x : ℚ) - 1))
        ≤ ((q : ℚ) + 1) / ((q : ℚ) - 1) * ((((2 * q + 1 : ℕ) : ℚ) + 1) / (((2 * q + 1 : ℕ) : ℚ) - 3)) :=
          mul_le_mul_of_nonneg_left ih' hB0
      _ ≤ ((q : ℚ) + 1) / ((q : ℚ) - 3) := by
          push_cast
          rw [div_mul_div_comm, div_le_div_iff₀ (by nlinarith) (by linarith)]
          nlinarith
      _ ≤ ((a : ℚ) + 1) / ((a : ℚ) - 3) := by
          rw [div_le_div_iff₀ (by linarith) (by linarith)]
          nlinarith

theorem mersenne_small {q k : ℕ} (hq : q.Prime) (hk : q + 1 = 2 ^ k) (hlt : q < 8191) :
    q = 3 ∨ q = 7 ∨ q = 31 ∨ q = 127 := by
  have hk13 : k < 13 := by
    by_contra h
    have : 2 ^ 13 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  interval_cases k <;> simp at hk <;> subst hk <;> first | omega | (norm_num at hq)

theorem two_mul_le {c p : ℕ} (hc : c.Prime) (hc2 : c ≠ 2) (hp : p.Prime) (hp2 : p ≠ 2)
    (hd : c ∣ p + 1) : 2 * c ≤ p + 1 := by
  have h2 : 2 ∣ p + 1 := by
    rcases hp.eq_two_or_odd with h | h
    · exact absurd h hp2
    · omega
  have hcop : Nat.Coprime 2 c := (Nat.coprime_primes Nat.prime_two hc).mpr (Ne.symm hc2)
  exact Nat.le_of_dvd (by omega) (Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop h2 hd)

theorem exists_child (N : Finset ℕ) : ∃ g : ℕ → ℕ, ∀ p : ℕ, g p ∣ p + 1 ∧
    (g p = 1 → ∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ p + 1 → c ∈ N) ∧
    (g p ≠ 1 → (g p).Prime ∧ g p ≠ 2 ∧ g p ∉ N) ∧
    (∀ c : ℕ, c.Prime → c ≠ 2 → c ∉ N → c ∣ p + 1 → g p ≤ c) := by
  have key : ∀ p : ℕ, ∃ x : ℕ, x ∣ p + 1 ∧
      (x = 1 → ∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ p + 1 → c ∈ N) ∧
      (x ≠ 1 → x.Prime ∧ x ≠ 2 ∧ x ∉ N) ∧
      (∀ c : ℕ, c.Prime → c ≠ 2 → c ∉ N → c ∣ p + 1 → x ≤ c) := by
    intro p
    by_cases h : ∃ c : ℕ, c.Prime ∧ c ≠ 2 ∧ c ∉ N ∧ c ∣ p + 1
    · classical
      refine ⟨Nat.find h, (Nat.find_spec h).2.2.2, fun h1 => ?_,
        fun _ => ⟨(Nat.find_spec h).1, (Nat.find_spec h).2.1, (Nat.find_spec h).2.2.1⟩,
        fun c hc hc2 hcN hcd => Nat.find_min' h ⟨hc, hc2, hcN, hcd⟩⟩
      exact absurd (h1 ▸ (Nat.find_spec h).1) Nat.not_prime_one
    · refine ⟨1, one_dvd _, fun _ c hc hc2 hcd => ?_, fun h1 => absurd rfl h1,
        fun c hc hc2 hcN hcd => absurd ⟨c, hc, hc2, hcN, hcd⟩ h⟩
      by_contra hcN
      exact h ⟨c, hc, hc2, hcN, hcd⟩
  exact ⟨fun p => (key p).choose, fun p => (key p).choose_spec⟩

theorem geom_bound {z c v : ℕ} (hz : c + 1 ≤ z) : ∀ (n : ℕ) (T : Finset ℕ) (i : ℕ), T.card = n →
    c + 2 ≤ v * z ^ i → (∀ j ∈ T, i ≤ j) →
    ∏ j ∈ T, (((v : ℚ) * (z : ℚ) ^ j) / ((v : ℚ) * (z : ℚ) ^ j - (c : ℚ))) ≤
      ((v : ℚ) * (z : ℚ) ^ i) / ((v : ℚ) * (z : ℚ) ^ i - ((c : ℚ) + 1)) := by
  have hc0 : (0 : ℚ) ≤ c := Nat.cast_nonneg c
  have hzq : (c : ℚ) + 1 ≤ z := by exact_mod_cast hz
  have hz1 : (1 : ℚ) ≤ z := by linarith
  have hv0 : (0 : ℚ) ≤ v := Nat.cast_nonneg v
  intro n
  induction n with
  | zero =>
    intro T i hT hi _
    have hY : (c : ℚ) + 2 ≤ (v : ℚ) * (z : ℚ) ^ i := by exact_mod_cast hi
    rw [Finset.card_eq_zero.mp hT, Finset.prod_empty, le_div_iff₀ (by linarith)]
    linarith
  | succ n ih =>
    intro T i hcard hi hge
    have hne : T.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨j0, hj0T, hj0min⟩ : ∃ q ∈ T, ∀ p ∈ T, q ≤ p :=
      ⟨T.min' hne, Finset.min'_mem T hne, fun p hp => Finset.min'_le T p hp⟩
    have hij0 : i ≤ j0 := hge j0 hj0T
    have hzpos : 0 < z := by omega
    have hi' : c + 2 ≤ v * z ^ (j0 + 1) :=
      hi.trans (Nat.mul_le_mul_left v (Nat.pow_le_pow_right hzpos (by omega)))
    have ih' := ih (T.erase j0) (j0 + 1) (by rw [Finset.card_erase_of_mem hj0T, hcard]; rfl)
      hi'
      (fun x hx => by
        have h1 := hj0min x (Finset.mem_of_mem_erase hx)
        have h2 := Finset.ne_of_mem_erase hx
        omega)
    have hY : (c : ℚ) + 2 ≤ (v : ℚ) * (z : ℚ) ^ i := by exact_mod_cast hi
    have hYX : (v : ℚ) * (z : ℚ) ^ i ≤ (v : ℚ) * (z : ℚ) ^ j0 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hz1 hij0) hv0
    have e : (v : ℚ) * (z : ℚ) ^ (j0 + 1) = (v : ℚ) * (z : ℚ) ^ j0 * z := by ring
    rw [← Finset.mul_prod_erase T _ hj0T]
    rw [e] at ih'
    generalize (v : ℚ) * (z : ℚ) ^ j0 = X at ih' hYX ⊢
    generalize (v : ℚ) * (z : ℚ) ^ i = Y at hY hYX ⊢
    have hX0 : (0 : ℚ) ≤ X := by linarith
    have hB0 : (0 : ℚ) ≤ X / (X - c) := div_nonneg hX0 (by linarith)
    have hXz : X ≤ X * z := by nlinarith
    calc X / (X - c) * ∏ x ∈ T.erase j0, ((v : ℚ) * (z : ℚ) ^ x / ((v : ℚ) * (z : ℚ) ^ x - c))
        ≤ X / (X - c) * (X * z / (X * z - (c + 1))) := mul_le_mul_of_nonneg_left ih' hB0
      _ ≤ X / (X - (c + 1)) := by
          rw [div_mul_div_comm, div_le_div_iff₀ (mul_pos (by linarith) (by linarith)) (by linarith)]
          nlinarith [mul_nonneg (mul_nonneg hX0 hX0) (by linarith : (0 : ℚ) ≤ (z : ℚ) - c - 1),
            mul_nonneg hX0 (mul_nonneg hc0 (by linarith : (0 : ℚ) ≤ (c : ℚ) + 1))]
      _ ≤ Y / (Y - (c + 1)) := by
          rw [div_le_div_iff₀ (by linarith) (by linarith)]
          nlinarith [mul_le_mul_of_nonneg_left hYX (by linarith : (0 : ℚ) ≤ (c : ℚ) + 1)]

theorem fiber_bound {u : ℕ} (hu : 3 ≤ u) (Q : Finset ℕ)
    (hQ : ∀ q ∈ Q, ∃ k, 1 ≤ k ∧ q + 1 = 2 ^ k * u) :
    ∏ q ∈ Q, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ (u : ℚ) / ((u : ℚ) - 2) := by
  obtain ⟨a, ha⟩ : ∃ a, a + 1 = 2 * u := ⟨2 * u - 1, by omega⟩
  have htb := tail_bound Q.card Q a rfl (by omega)
    (fun q hq => by
      obtain ⟨k, hk, he⟩ := hQ q hq
      have h2k : 2 ≤ 2 ^ k := by
        have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hk
        simpa using this
      have : 2 * u ≤ 2 ^ k * u := Nat.mul_le_mul_right _ h2k
      omega)
    (fun q hq q' hq' hlt => by
      obtain ⟨k, hk, he⟩ := hQ q hq
      obtain ⟨k', hk', he'⟩ := hQ q' hq'
      have hkk : k < k' := by
        by_contra hcon
        have : 2 ^ k' ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
        have : 2 ^ k' * u ≤ 2 ^ k * u := Nat.mul_le_mul_right _ this
        omega
      have : 2 ^ (k + 1) ≤ 2 ^ k' := Nat.pow_le_pow_right (by norm_num) (by omega)
      have : 2 ^ (k + 1) * u ≤ 2 ^ k' * u := Nat.mul_le_mul_right _ this
      rw [pow_succ] at this
      linarith)
  refine htb.trans ?_
  have haq : (a : ℚ) + 1 = 2 * (u : ℚ) := by exact_mod_cast ha
  have huq : (3 : ℚ) ≤ (u : ℚ) := by exact_mod_cast hu
  have e : (a : ℚ) = 2 * (u : ℚ) - 1 := by linarith
  rw [e, div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

theorem mersenne_bound (β : ℕ → ℚ) (L : Finset ℕ) (hLp : ∀ q ∈ L, q.Prime)
    (hLm : ∀ q ∈ L, ∃ k, q + 1 = 2 ^ k)
    (hLβ : ∀ q ∈ L, 0 < β q ∧ β q ≤ ((q : ℚ) + 1) / ((q : ℚ) - 1))
    (h1 : 1 ≤ β 3 ∧ 1 ≤ β 7 ∧ 1 ≤ β 31 ∧ 1 ≤ β 127) :
    ∏ q ∈ L, β q ≤ (β 3 * β 7 * β 31 * β 127) * (2048 / 2047) := by
  have hsplit := Finset.prod_filter_mul_prod_filter_not L (fun q => q < 8191) β
  have hsmall : ∏ q ∈ L.filter (fun q => q < 8191), β q ≤ β 3 * β 7 * β 31 * β 127 := by
    have hsub : L.filter (fun q => q < 8191) ⊆ ({3, 7, 31, 127} : Finset ℕ) := by
      intro q hq
      obtain ⟨hqL, hlt⟩ := Finset.mem_filter.mp hq
      obtain ⟨k, hk⟩ := hLm q hqL
      have := mersenne_small (hLp q hqL) hk hlt
      simp only [Finset.mem_insert, Finset.mem_singleton]
      exact this
    have h := Finset.prod_le_prod_of_subset_of_one_le (f := β) hsub
      (fun i hi => (hLβ i (Finset.mem_filter.mp hi).1).1.le) (fun i hi _ => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl | rfl | rfl
      · exact h1.1
      · exact h1.2.1
      · exact h1.2.2.1
      · exact h1.2.2.2)
    have e : ∏ q ∈ ({3, 7, 31, 127} : Finset ℕ), β q = β 3 * β 7 * β 31 * β 127 := by
      rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide),
        Finset.prod_insert (by decide), Finset.prod_singleton]
      ring
    rwa [e] at h
  have htail : ∏ q ∈ L.filter (fun q => ¬ q < 8191), β q ≤ 2048 / 2047 := by
    have hmemT : ∀ q ∈ L.filter (fun q => ¬ q < 8191), q ∈ L ∧ 8191 ≤ q := fun q hq => by
      obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hq
      exact ⟨h1, by omega⟩
    have hle : ∏ q ∈ L.filter (fun q => ¬ q < 8191), β q ≤
        ∏ q ∈ L.filter (fun q => ¬ q < 8191), (((q : ℚ) + 1) / ((q : ℚ) - 1)) :=
      Finset.prod_le_prod (fun q hq => (hLβ q (hmemT q hq).1).1.le)
        (fun q hq => (hLβ q (hmemT q hq).1).2)
    have htb := tail_bound _ _ 8191 rfl (by norm_num) (fun q hq => (hmemT q hq).2)
      (fun q hq q' hq' hlt => by
        obtain ⟨k, hk⟩ := hLm q (hmemT q hq).1
        obtain ⟨k', hk'⟩ := hLm q' (hmemT q' hq').1
        have hkk : k < k' := by
          by_contra hcon
          have : 2 ^ k' ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
          omega
        have : 2 ^ (k + 1) ≤ 2 ^ k' := Nat.pow_le_pow_right (by norm_num) (by omega)
        rw [pow_succ] at this
        omega)
    refine hle.trans (htb.trans ?_)
    norm_num
  rw [← hsplit]
  refine mul_le_mul hsmall htail ?_ ?_
  · exact Finset.prod_nonneg fun q hq => (hLβ q (Finset.mem_filter.mp hq).1).1.le
  · obtain ⟨a, b, c, d⟩ := h1
    have h3 : (0 : ℚ) ≤ β 3 := by linarith
    have h7 : (0 : ℚ) ≤ β 7 := by linarith
    have h31 : (0 : ℚ) ≤ β 31 := by linarith
    have h127 : (0 : ℚ) ≤ β 127 := by linarith
    positivity

theorem S_mem {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    {c : ℕ} (hc : c.Prime) (hc2 : c ≠ 2) (hcz : c ∉ N)
    (hd : c ∣ (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1)) : c ∈ P := by
  rw [E] at hd
  rcases (Nat.Prime.dvd_mul hc).mp hd with h | h
  · rcases (Nat.Prime.dvd_mul hc).mp h with h | h
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hc Nat.prime_two).mp (hc.dvd_of_dvd_pow h)) hc2
    · exact absurd (hK c hc h) hcz
  · obtain ⟨p, hp, hcp⟩ := (Prime.dvd_finsetProd_iff hc.prime _).mp h
    rwa [(Nat.prime_dvd_prime_iff_eq hc (hP p hp).1).mp hcp]

theorem S_sq {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    {c : ℕ} (hc : c.Prime) (hc2 : c ≠ 2) (hcz : c ∉ N) :
    ¬ c * c ∣ (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) := by
  intro hd
  have hcP : c ∈ P := S_mem hP hK E hc hc2 hcz ((dvd_mul_right c c).trans hd)
  rw [E, ← Finset.mul_prod_erase P (fun p => p) hcP, mul_left_comm] at hd
  have h1 : c ∣ 2 ^ (m + 1) * K * ∏ p ∈ P.erase c, p := Nat.dvd_of_mul_dvd_mul_left hc.pos hd
  rcases (Nat.Prime.dvd_mul hc).mp h1 with h | h
  · rcases (Nat.Prime.dvd_mul hc).mp h with h | h
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hc Nat.prime_two).mp (hc.dvd_of_dvd_pow h)) hc2
    · exact absurd (hK c hc h) hcz
  · obtain ⟨p, hp, hcp⟩ := (Prime.dvd_finsetProd_iff hc.prime _).mp h
    have := (Nat.prime_dvd_prime_iff_eq hc (hP p (Finset.mem_of_mem_erase hp)).1).mp hcp
    exact (Finset.ne_of_mem_erase hp) this.symm

theorem facts {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p) :
    (∀ c : ℕ, c.Prime → c ≠ 2 → c ∉ N → ∀ p ∈ P, c ∣ p + 1 → c ∈ P) ∧
    (∀ c : ℕ, c.Prime → c ≠ 2 → c ∉ N → c ∣ 2 ^ m + 1 → c ∈ P) ∧
    (∀ c : ℕ, c.Prime → c ≠ 2 → c ∉ N → ∀ p ∈ P, ∀ p' ∈ P, c ∣ p + 1 → c ∣ p' + 1 → p = p') ∧
    (∀ c : ℕ, c.Prime → c ≠ 2 → c ∉ N → c ∣ 2 ^ m + 1 → ∀ p ∈ P, ¬ c ∣ p + 1) ∧
    (∀ c : ℕ, c.Prime → c ≠ 2 → c ∉ N → ¬ c * c ∣ 2 ^ m + 1) ∧
    (∀ c : ℕ, c.Prime → c ≠ 2 → c ∉ N → ∀ p ∈ P, ¬ c * c ∣ p + 1) ∧
    (∀ c : ℕ, c.Prime → c ≠ 2 → c ∉ N → c ∣ K' → c ∈ P) ∧
    (∀ c : ℕ, c.Prime → c ≠ 2 → c ∉ N → c ∣ K' → ∀ p ∈ P, ¬ c ∣ p + 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c hc hc2 hcz p hp hd
    exact S_mem hP hK E hc hc2 hcz
      ((hd.trans (Finset.dvd_prod_of_mem (fun p => p + 1) hp)).mul_left _)
  · intro c hc hc2 hcz hd
    exact S_mem hP hK E hc hc2 hcz ((hd.mul_right _).mul_right _)
  · intro c hc hc2 hcz p hp p' hp' hd hd'
    by_contra hne
    apply S_sq hP hK E hc hc2 hcz
    have hsub : ({p, p'} : Finset ℕ) ⊆ P := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hp
      · rw [Finset.mem_singleton.mp hx]; exact hp'
    have h1 : (p + 1) * (p' + 1) ∣ ∏ x ∈ P, (x + 1) := by
      have := Finset.prod_dvd_prod_of_subset _ _ (fun x => x + 1) hsub
      rwa [Finset.prod_pair hne] at this
    exact ((mul_dvd_mul hd hd').trans h1).mul_left _
  · intro c hc hc2 hcz hd p hp hd'
    apply S_sq hP hK E hc hc2 hcz
    have h := (mul_dvd_mul hd (hd'.trans (Finset.dvd_prod_of_mem (fun p => p + 1) hp))).mul_left K'
    have e : K' * ((2 ^ m + 1) * ∏ p ∈ P, (p + 1)) = (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) := by ring
    rwa [e] at h
  · intro c hc hc2 hcz hd
    exact S_sq hP hK E hc hc2 hcz ((hd.mul_right _).mul_right _)
  · intro c hc hc2 hcz p hp hd
    exact S_sq hP hK E hc hc2 hcz
      ((hd.trans (Finset.dvd_prod_of_mem (fun p => p + 1) hp)).mul_left _)
  · intro c hc hc2 hcz hd
    exact S_mem hP hK E hc hc2 hcz ((hd.mul_left _).mul_right _)
  · intro c hc hc2 hcz hd p hp hd'
    apply S_sq hP hK E hc hc2 hcz
    have h := (mul_dvd_mul hd (hd'.trans (Finset.dvd_prod_of_mem (fun p => p + 1) hp))).mul_left
      (2 ^ m + 1)
    rwa [← mul_assoc] at h

theorem exists_prime_mod3 : ∀ N : ℕ, N % 3 = 2 → ∃ p, p.Prime ∧ p ∣ N ∧ p % 3 = 2 := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro hN
    have hN1 : N ≠ 1 := by omega
    have hq := Nat.minFac_prime hN1
    have hqd := Nat.minFac_dvd N
    have h3 : N.minFac % 3 ≠ 0 := by
      intro h
      have : 3 ∣ N := (Nat.dvd_of_mod_eq_zero h).trans hqd
      omega
    by_cases h2 : N.minFac % 3 = 2
    · exact ⟨_, hq, hqd, h2⟩
    · have h1 : N.minFac % 3 = 1 := by omega
      obtain ⟨k, hk⟩ := hqd
      have hk2 : k % 3 = 2 := by
        have : (N.minFac * k) % 3 = 2 := by rw [← hk]; exact hN
        rw [Nat.mul_mod, h1] at this
        omega
      have hklt : k < N := by
        have := hq.two_le
        have hk0 : 0 < k := by omega
        calc k < N.minFac * k := by nlinarith
          _ = N := hk.symm
      obtain ⟨p, hp, hpd, hp2⟩ := ih k hklt hk2
      exact ⟨p, hp, hpd.trans (Dvd.intro_left _ hk.symm), hp2⟩

theorem not_dvd_fourth_5 (x : ℕ) : ¬ 5 ∣ x ^ 4 + 1 := by
  intro h
  have h' := (ZMod.natCast_eq_zero_iff (x ^ 4 + 1) 5).mpr h
  push_cast at h'
  exact (by decide : ∀ y : ZMod 5, y ^ 4 + 1 ≠ 0) _ h'

theorem kernel_balance {n : ℕ} {N : Finset ℕ} (h : Erdos1052.IsUnitaryPerfect n) (h2 : 2 ∣ n)
    (hs : ∀ r ∈ n.primeFactors, r ≠ 2 → r ∉ N → n.factorization r = 1) :
    (2 ^ n.factorization 2 + 1) *
        (∏ z ∈ (n.primeFactors.erase 2).filter (fun r => r ∈ N), (1 + z ^ n.factorization z)) *
        ∏ p ∈ (n.primeFactors.erase 2).filter (fun r => ¬ r ∈ N), (p + 1) =
      2 ^ (n.factorization 2 + 1) *
        (∏ z ∈ (n.primeFactors.erase 2).filter (fun r => r ∈ N), z ^ n.factorization z) *
        ∏ p ∈ (n.primeFactors.erase 2).filter (fun r => ¬ r ∈ N), p := by
  have hn0 : n ≠ 0 := h.2.ne'
  have hprod := prod_eq_two_mul h
  have hself := prod_primeFactors_pow_self hn0
  have h2mem : 2 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_two, h2, hn0⟩
  rw [← Finset.mul_prod_erase _ _ h2mem,
    ← Finset.prod_filter_mul_prod_filter_not (n.primeFactors.erase 2) (fun r => r ∈ N)] at hprod hself
  have hPs : ∀ p ∈ (n.primeFactors.erase 2).filter (fun r => ¬ r ∈ N), n.factorization p = 1 :=
    fun p hp => by
      obtain ⟨h1, hpN⟩ := Finset.mem_filter.mp hp
      exact hs p (Finset.mem_of_mem_erase h1) (Finset.ne_of_mem_erase h1) hpN
  have e1 : ∏ p ∈ (n.primeFactors.erase 2).filter (fun r => ¬ r ∈ N), (1 + p ^ n.factorization p) =
      ∏ p ∈ (n.primeFactors.erase 2).filter (fun r => ¬ r ∈ N), (p + 1) :=
    Finset.prod_congr rfl fun p hp => by rw [hPs p hp, pow_one, add_comm]
  have e2 : ∏ p ∈ (n.primeFactors.erase 2).filter (fun r => ¬ r ∈ N), p ^ n.factorization p =
      ∏ p ∈ (n.primeFactors.erase 2).filter (fun r => ¬ r ∈ N), p :=
    Finset.prod_congr rfl fun p hp => by rw [hPs p hp, pow_one]
  rw [e1] at hprod
  rw [e2] at hself
  rw [pow_succ]
  linarith

theorem mod_four_of_dvd_one_add_pow_even {l p e : ℕ} (hl : l.Prime) (hl2 : l ≠ 2)
    (he : Even e) (hd : l ∣ 1 + p ^ e) : l % 4 = 1 := by
  have : Fact l.Prime := ⟨hl⟩
  obtain ⟨j, rfl⟩ := he
  have h3 : l % 4 ≠ 3 := by
    apply ZMod.exists_sq_eq_neg_one_iff.mp
    refine ⟨(p : ZMod l) ^ j, ?_⟩
    have h0 : ((1 + p ^ (j + j) : ℕ) : ZMod l) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hd
    push_cast at h0
    linear_combination (-1 : ZMod l) * h0
  have hodd := Nat.odd_iff.mp (hl.odd_of_ne_two hl2)
  omega

theorem master_gen {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N) (hK0 : 0 < K)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    (β : ℕ → ℚ)
    (hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1))
    (h4 : ∀ p ∈ P, ∀ c ∈ P, c ∣ p + 1 →
        (∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ N → c' ∣ p + 1 → c ≤ c') →
        β c ≠ ((c : ℚ) + 1) / ((c : ℚ) - 1) → (1 + 1 / (c : ℚ)) * β p ≤ β c) :
    ∃ L : Finset ℕ, L ⊆ P ∧ (∀ q ∈ L, ∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c ∈ N) ∧
      (2 : ℚ) ≤ (1 + 1 / (2 : ℚ) ^ m) * ((K' : ℚ) / K) * ∏ q ∈ L, β q := by
  obtain ⟨S1, -, S2, -, -, -, -, -⟩ := facts hP hK E
  obtain ⟨g, hg⟩ := exists_child N
  have hpos : ∀ p ∈ P, 0 < p := fun p hp => (hP p hp).1.pos
  have hg1 : ∀ p ∈ P, g p ∈ P → g p ≠ 1 := fun p _ h h1 => by
    have := (hP _ h).1
    rw [h1] at this
    exact Nat.not_prime_one this
  have hgP : ∀ p ∈ P, g p ≠ 1 → g p ∈ P := fun p hp h =>
    S1 _ ((hg p).2.2.1 h).1 ((hg p).2.2.1 h).2.1 ((hg p).2.2.1 h).2.2 p hp (hg p).1
  have hpath := path_bound g β P.card P rfl hpos
    (fun p hp h => by
      have hc := (hg p).2.2.1 (hg1 p hp h)
      have := two_mul_le hc.1 hc.2.1 (hP p hp).1 (hP p hp).2 (hg p).1
      have := hc.1.two_le
      omega)
    (fun p hp p' hp' h he => by
      have hc := (hg p).2.2.1 (hg1 p hp h)
      exact S2 _ hc.1 hc.2.1 hc.2.2 p hp p' hp' (hg p).1 (he ▸ (hg p').1))
    (fun p hp => (hB p hp).1)
    (fun p hp h => by
      have hc := (hg p).2.2.1 (hg1 p hp h)
      by_cases hsp : β (g p) = (((g p : ℕ) : ℚ) + 1) / (((g p : ℕ) : ℚ) - 1)
      · rw [hsp]
        have h0 : (0 : ℚ) ≤ 1 + 1 / ((g p : ℕ) : ℚ) := by positivity
        exact (mul_le_mul_of_nonneg_left (hB p hp).2 h0).trans
          (B_step hc.1.two_le (two_mul_le hc.1 hc.2.1 (hP p hp).1 (hP p hp).2 (hg p).1))
      · exact h4 p hp (g p) h (hg p).1 (hg p).2.2.2 hsp)
  have hleaf : ∀ q ∈ P.filter (fun q => g q ∉ P),
      ∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c ∈ N := fun q hq => by
    obtain ⟨hqP, hgq⟩ := Finset.mem_filter.mp hq
    by_cases h : g q = 1
    · exact (hg q).2.1 h
    · exact absurd (hgP q hqP h) hgq
  have hKq : (0 : ℚ) < K := by exact_mod_cast hK0
  have hEq : (1 + 1 / (2 : ℚ) ^ m) * ((K' : ℚ) / K) * ∏ p ∈ P, (1 + 1 / (p : ℚ)) = 2 := by
    have hY : (0 : ℚ) < ∏ p ∈ P, (p : ℚ) :=
      Finset.prod_pos fun p hp => by exact_mod_cast hpos p hp
    have hcast : ((2 : ℚ) ^ m + 1) * K' * ∏ p ∈ P, ((p : ℚ) + 1) =
        2 ^ (m + 1) * K * ∏ p ∈ P, (p : ℚ) := by
      have h := congrArg (Nat.cast : ℕ → ℚ) E
      push_cast at h
      exact h
    have e : ∏ p ∈ P, (1 + 1 / (p : ℚ)) = (∏ p ∈ P, ((p : ℚ) + 1)) / ∏ p ∈ P, (p : ℚ) := by
      rw [← Finset.prod_div_distrib]
      refine Finset.prod_congr rfl fun p hp => ?_
      have : (0 : ℚ) < p := by exact_mod_cast hpos p hp
      field_simp
    have h2 : (0 : ℚ) < (2 : ℚ) ^ m := by positivity
    rw [e]
    field_simp
    rw [pow_succ] at hcast
    linarith
  refine ⟨P.filter (fun q => g q ∉ P), Finset.filter_subset _ _, hleaf, ?_⟩
  have hfac : (0 : ℚ) ≤ (1 + 1 / (2 : ℚ) ^ m) * ((K' : ℚ) / K) :=
    mul_nonneg (by positivity) (div_nonneg (Nat.cast_nonneg _) hKq.le)
  calc (2 : ℚ) = (1 + 1 / (2 : ℚ) ^ m) * ((K' : ℚ) / K) * ∏ p ∈ P, (1 + 1 / (p : ℚ)) := hEq.symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hpath hfac

theorem two_pow_of_no_odd_prime {M : ℕ} (h : ∀ c : ℕ, c.Prime → c ≠ 2 → ¬ c ∣ M) :
    ∃ k, M = 2 ^ k := by
  rcases Nat.eq_two_pow_or_exists_odd_prime_and_dvd M with hk | ⟨p, hp, hpd, hodd⟩
  · exact hk
  · refine absurd hpd (h p hp ?_)
    rintro rfl
    exact absurd hodd (by decide)

theorem two_pow_mul_pow_of_odd_primes_eq {M z : ℕ} (hM : M ≠ 0)
    (h : ∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ M → c = z) : ∃ k j, M = 2 ^ k * z ^ j := by
  have hmul := Nat.ordProj_mul_ordCompl_eq_self M 2
  have hu0 : M / 2 ^ M.factorization 2 ≠ 0 := (Nat.ordCompl_pos 2 hM).ne'
  have hodd : ¬ 2 ∣ M / 2 ^ M.factorization 2 := Nat.not_dvd_ordCompl Nat.prime_two hM
  have hu := Nat.eq_prime_pow_of_unique_prime_dvd (p := z) hu0 (fun {d} hd hdd =>
    h d hd (fun h2 => hodd (h2 ▸ hdd)) (hdd.trans (Nat.ordCompl_dvd M 2)))
  exact ⟨M.factorization 2, _, by rw [← hu]; exact hmul.symm⟩

theorem three_dvd_two_pow_add_one {m : ℕ} (hm : m % 2 = 1) : 3 ∣ 2 ^ m + 1 := by
  have h := Odd.nat_add_dvd_pow_add_pow 2 1 (Nat.odd_iff.mpr hm)
  rwa [one_pow] at h

theorem five_dvd_two_pow_add_one {m : ℕ} (hm : m % 4 = 2) : 5 ∣ 2 ^ m + 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = 2 * k := ⟨m / 2, by omega⟩
  have h := Odd.nat_add_dvd_pow_add_pow 4 1 (n := k) (Nat.odd_iff.mpr (by omega))
  rw [one_pow] at h
  rw [pow_mul]
  exact h

theorem core_e2 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (hm : 1 ≤ m)
    (E : (2 ^ m + 1) * 10 * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 9 * ∏ p ∈ P, p) :
    m = 1 ∧ P = {5} := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 9 → c ∈ ({3} : Finset ℕ) := fun c hc hd => by
    have h9 : (9 : ℕ) = 3 ^ 2 := by norm_num
    rw [h9] at hd
    exact Finset.mem_singleton.mpr ((Nat.prime_dvd_prime_iff_eq hc Nat.prime_three).mp
      (hc.dvd_of_dvd_pow hd))
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have hn3 : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  have h5P : 5 ∈ P := S7 5 (by norm_num) (by norm_num) (hn3 (by norm_num)) (by norm_num)
  have h5no : ∀ p ∈ P, ¬ 5 ∣ p + 1 := S8 5 (by norm_num) (by norm_num) (hn3 (by norm_num)) (by norm_num)
  have h5top : ¬ 5 ∣ 2 ^ m + 1 := fun h => by
    apply S_sq hP hK E (c := 5) (by norm_num) (by norm_num) (hn3 (by norm_num))
    have : 5 * 5 ∣ (2 ^ m + 1) * 10 := mul_dvd_mul h (by norm_num)
    exact this.mul_right _
  -- the 3-adic budget: 27 does not divide the left side
  have h27 : ¬ 27 ∣ (2 ^ m + 1) * 10 * ∏ p ∈ P, (p + 1) := by
    rw [E]
    intro h
    have e : 2 ^ (m + 1) * 9 * ∏ p ∈ P, p = 9 * (2 ^ (m + 1) * ∏ p ∈ P, p) := by ring
    rw [e] at h
    have h3 : 3 ∣ 2 ^ (m + 1) * ∏ p ∈ P, p :=
      Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 9) (by simpa using h)
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h3 with h | h
    · have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
        (Nat.prime_three.dvd_of_dvd_pow h)
      omega
    · obtain ⟨p, hp, h3p⟩ := (Prime.dvd_finsetProd_iff Nat.prime_three.prime _).mp h
      rw [(Nat.prime_dvd_prime_iff_eq Nat.prime_three (hP p hp).1).mp h3p] at h3P
      exact h3P hp
  have hbud : ∀ (d : ℕ) (S : Finset ℕ), S ⊆ P → 27 ∣ d * 10 * ∏ p ∈ S, (p + 1) → d ∣ 2 ^ m + 1 → False :=
    fun d S hS h hd => h27 (h.trans (mul_dvd_mul (mul_dvd_mul_right hd 10)
      (Finset.prod_dvd_prod_of_subset _ _ (fun p => p + 1) hS)))
  have b1 : ¬ 9 ∣ 2 ^ m + 1 := fun h => by
    refine hbud 9 {5} (Finset.singleton_subset_iff.mpr h5P) ?_ h
    rw [Finset.prod_singleton]
    norm_num
  have b2 : 3 ∣ 2 ^ m + 1 → ∀ p ∈ P, p ≠ 5 → ¬ 3 ∣ p + 1 := fun h p hp hp5 h3 => by
    have hS : ({5, p} : Finset ℕ) ⊆ P := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact h5P
      · rw [Finset.mem_singleton.mp hx]; exact hp
    refine hbud 3 {5, p} hS ?_ h
    rw [Finset.prod_pair (Ne.symm hp5)]
    obtain ⟨t, ht⟩ := h3
    rw [ht]
    exact ⟨20 * t, by ring⟩
  have b3 : ∀ p ∈ P, ∀ p' ∈ P, p ≠ 5 → p' ≠ 5 → 3 ∣ p + 1 → 3 ∣ p' + 1 → p = p' :=
    fun p hp p' hp' hp5 hp5' h3 h3' => by
      by_contra hne
      have hS : ({5, p, p'} : Finset ℕ) ⊆ P := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl
        · exact h5P
        · exact hp
        · exact hp'
      refine hbud 1 {5, p, p'} hS ?_ (one_dvd _)
      rw [Finset.prod_insert (by simp [Ne.symm hp5, Ne.symm hp5']), Finset.prod_pair hne]
      obtain ⟨t, ht⟩ := h3
      obtain ⟨t', ht'⟩ := h3'
      rw [ht, ht']
      exact ⟨20 * t * t', by ring⟩
  have b4 : ∀ p ∈ P, p ≠ 5 → ¬ 9 ∣ p + 1 := fun p hp hp5 h9 => by
    have hS : ({5, p} : Finset ℕ) ⊆ P := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact h5P
      · rw [Finset.mem_singleton.mp hx]; exact hp
    refine hbud 1 {5, p} hS ?_ (one_dvd _)
    rw [Finset.prod_pair (Ne.symm hp5)]
    obtain ⟨t, ht⟩ := h9
    rw [ht]
    exact ⟨20 * t, by ring⟩
  -- m at least 5 is impossible
  have hbig : ¬ 5 ≤ m := by
    intro hm5
    have h42 : m % 4 ≠ 2 := fun h => h5top (five_dvd_two_pow_add_one h)
    -- the only leaf with 3 ∣ q + 1 is 5
    have hu : ∀ q ∈ P, (∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c ∈ ({3} : Finset ℕ)) →
        3 ∣ q + 1 → q = 5 := by
      intro q hq hleaf h3
      by_contra hq5
      rcases Nat.lt_or_ge (m % 2) 1 with hpar | hpar
      · -- 4 ∣ m
        have h40 : m % 4 = 0 := by omega
        have hmod : (2 ^ m + 1) % 3 = 2 := by
          obtain ⟨k, rfl⟩ : ∃ k, m = 2 * k := ⟨m / 2, by omega⟩
          rw [pow_mul, Nat.add_mod, Nat.pow_mod]
          norm_num
        obtain ⟨r, hr, hrd, hr3⟩ := exists_prime_mod3 _ hmod
        have hr2 : r ≠ 2 := by
          rintro rfl
          have h1 : 2 ∣ 1 := (Nat.dvd_add_right (dvd_pow_self 2 (by omega : m ≠ 0))).mp hrd
          omega
        have hrP : r ∈ P := S2 r hr hr2 (hn3 (by omega)) hrd
        have hr5 : r ≠ 5 := by
          rintro rfl
          exact h5top hrd
        have hr4 : r % 4 = 1 := mod_four_of_dvd_one_add_pow_even (p := 2) (e := m) hr hr2
          (Nat.even_iff.mpr (by omega)) (by rw [add_comm]; exact hrd)
        have hqr : q = r := b3 q hq r hrP hq5 hr5 h3 (by omega)
        subst hqr
        have h9 := b4 q hq hq5
        -- q + 1 = 6 * u with u > 1 odd and prime to 3: u has a prime factor outside {2, 3}
        obtain ⟨u, hu⟩ : ∃ u, q + 1 = 6 * u := ⟨(q + 1) / 6, by omega⟩
        have hu1 : u ≠ 1 := by omega
        have hc := Nat.minFac_prime hu1
        have hcd : u.minFac ∣ q + 1 := (Nat.minFac_dvd u).trans (Dvd.intro_left 6 hu.symm)
        have hc2 : u.minFac ≠ 2 := fun h2 => by
          have : 2 ∣ u := h2 ▸ Nat.minFac_dvd u
          omega
        have hc3 : u.minFac ≠ 3 := fun h3' => by
          have : 3 ∣ u := h3' ▸ Nat.minFac_dvd u
          omega
        exact hc3 (Finset.mem_singleton.mp (hleaf _ hc hc2 hcd))
      · exact b2 (three_dvd_two_pow_add_one (by omega)) q hq hq5 h3
    let β : ℕ → ℚ := fun p => if p = 5 then 6 / 5 else if p = 3 then 1 else
      ((p : ℚ) + 1) / ((p : ℚ) - 1)
    have hβ5 : β 5 = 6 / 5 := by simp [β]
    have hβB : ∀ p : ℕ, p ≠ 5 → p ≠ 3 → β p = ((p : ℚ) + 1) / ((p : ℚ) - 1) := fun p h5 h3 => by
      simp [β, h5, h3]
    have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
      intro p hp
      by_cases h5 : p = 5
      · subst h5
        rw [hβ5]
        norm_num
      · have h3 : p ≠ 3 := fun h => h3P (h ▸ hp)
        rw [hβB p h5 h3]
        exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
    obtain ⟨L, hLP, hLleaf, hmain⟩ := master_gen (N := {3}) hP hK (by norm_num) E β hB
      (fun p hp c hc hcd _ hne => by
        by_cases h5 : c = 5
        · subst h5
          exact absurd hcd (h5no p hp)
        · exact absurd (hβB c h5 (fun h => h3P (h ▸ hc))) hne)
    have hβpos : ∀ q ∈ L, 0 < β q := fun q hq => by
      have h0 : (0 : ℚ) ≤ 1 / (q : ℚ) := by positivity
      linarith [(hB q (hLP hq)).1]
    have hsplit := Finset.prod_filter_mul_prod_filter_not L (fun q => 3 ∣ q + 1) β
    have h3leaves : ∏ q ∈ L.filter (fun q => 3 ∣ q + 1), β q ≤ 6 / 5 := by
      have hsub : L.filter (fun q => 3 ∣ q + 1) ⊆ ({5} : Finset ℕ) := by
        intro q hq
        obtain ⟨hqL, h3⟩ := Finset.mem_filter.mp hq
        exact Finset.mem_singleton.mpr (hu q (hLP hqL) (hLleaf q hqL) h3)
      have h := Finset.prod_le_prod_of_subset_of_one_le (f := β) hsub
        (fun i hi => (hβpos i (Finset.mem_filter.mp hi).1).le) (fun i hi _ => by
          rw [Finset.mem_singleton.mp hi, hβ5]
          norm_num)
      rwa [Finset.prod_singleton, hβ5] at h
    have hmers : ∏ q ∈ L.filter (fun q => ¬ 3 ∣ q + 1), β q ≤
        (β 3 * β 7 * β 31 * β 127) * (2048 / 2047) := by
      refine mersenne_bound β _ (fun q hq => (hP q (hLP (Finset.mem_filter.mp hq).1)).1)
        (fun q hq => ?_)
        (fun q hq => ⟨hβpos q (Finset.mem_filter.mp hq).1,
          (hB q (hLP (Finset.mem_filter.mp hq).1)).2⟩) ?_
      · obtain ⟨hqL, h3⟩ := Finset.mem_filter.mp hq
        refine two_pow_of_no_odd_prime (fun c hc hc2 hcd => ?_)
        rw [Finset.mem_singleton.mp (hLleaf q hqL c hc hc2 hcd)] at hcd
        exact h3 hcd
      · simp only [β]
        norm_num
    have hvals : (β 3 * β 7 * β 31 * β 127) * (2048 / 2047) =
        1 * (8 / 6) * (32 / 30) * (128 / 126) * (2048 / 2047) := by
      simp only [β]
      norm_num
    rw [hvals] at hmers
    have hprod : ∏ q ∈ L, β q ≤ 6 / 5 * (1 * (8 / 6) * (32 / 30) * (128 / 126) * (2048 / 2047)) := by
      rw [← hsplit]
      exact mul_le_mul h3leaves hmers
        (Finset.prod_nonneg fun q hq => (hβpos q (Finset.mem_filter.mp hq).1).le) (by norm_num)
    have hT : 1 + 1 / (2 : ℚ) ^ m ≤ 33 / 32 := by
      have h2 : (2 : ℚ) ^ 5 ≤ (2 : ℚ) ^ m := pow_le_pow_right₀ (by norm_num) hm5
      have : 1 / (2 : ℚ) ^ m ≤ 1 / (2 : ℚ) ^ 5 := one_div_le_one_div_of_le (by positivity) h2
      norm_num at this ⊢
      linarith
    have hfin : (2 : ℚ) ≤ 33 / 32 * (((10 : ℕ) : ℚ) / ((9 : ℕ) : ℚ)) *
        (6 / 5 * (1 * (8 / 6) * (32 / 30) * (128 / 126) * (2048 / 2047))) :=
      hmain.trans (mul_le_mul (mul_le_mul_of_nonneg_right hT (by norm_num)) hprod
        (Finset.prod_nonneg fun q hq => (hβpos q hq).le) (by norm_num))
    norm_num at hfin
  have hm4 : m ≤ 4 := by omega
  interval_cases m
  · -- m = 1
    refine ⟨rfl, ?_⟩
    have E' : (2 ^ 1 + 1) * 10 * ((5 + 1) * ∏ p ∈ P.erase 5, (p + 1)) =
        2 ^ (1 + 1) * 9 * (5 * ∏ p ∈ P.erase 5, p) := by
      rw [Finset.mul_prod_erase P (fun p => p + 1) h5P, Finset.mul_prod_erase P (fun p => p) h5P]
      exact E
    have E'' : ∏ p ∈ P.erase 5, (p + 1) = ∏ p ∈ P.erase 5, p := by
      norm_num at E'
      omega
    have hemp : P.erase 5 = ∅ := by
      by_contra hne
      have hlt := Finset.prod_lt_prod_of_nonempty (s := P.erase 5) (f := fun p => p)
        (g := fun p => p + 1)
        (fun p hp => (hP p (Finset.mem_of_mem_erase hp)).1.pos) (fun p _ => Nat.lt_succ_self p)
        (Finset.nonempty_iff_ne_empty.mpr hne)
      omega
    rw [← Finset.insert_erase h5P, hemp]
    rfl
  · exact absurd (by norm_num : 5 ∣ 2 ^ 2 + 1) h5top
  · exact absurd (by norm_num : 9 ∣ 2 ^ 3 + 1) b1
  · have h17 : 17 ∈ P := S2 17 (by norm_num) (by norm_num) (hn3 (by norm_num)) (by norm_num)
    exact absurd (by norm_num : 9 ∣ 17 + 1) (b4 17 h17 (by norm_num))

theorem two_dvd_of_isUnitaryPerfect {n : ℕ} (h : Erdos1052.IsUnitaryPerfect n) : 2 ∣ n := by
  have hn0 : n ≠ 0 := h.2.ne'
  have hprod := prod_eq_two_mul h
  by_contra h2
  have hev : ∀ p ∈ n.primeFactors, 2 ∣ 1 + p ^ n.factorization p := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hp2 : p ≠ 2 := fun e => h2 (e ▸ Nat.dvd_of_mem_primeFactors hp)
    have hpo : Odd p := hpp.odd_of_ne_two hp2
    have := (hpo.pow (n := n.factorization p)).add_one
    rw [add_comm]
    exact even_iff_two_dvd.mp this
  have h2k : 2 ^ n.primeFactors.card ∣ 2 * n := by
    rw [← hprod, ← Finset.prod_const]
    exact Finset.prod_dvd_prod_of_dvd _ _ hev
  have hcard : n.primeFactors.card ≤ 1 := by
    by_contra hc
    have h4 : 2 ^ 2 ∣ 2 * n := (pow_dvd_pow 2 (by omega)).trans h2k
    norm_num at h4
    omega
  rcases Nat.lt_or_ge n.primeFactors.card 1 with hc | hc
  · have h0 : n.primeFactors = ∅ := Finset.card_eq_zero.mp (by omega)
    have hself := prod_primeFactors_pow_self hn0
    rw [h0, Finset.prod_empty] at hprod hself
    omega
  · obtain ⟨p, hp⟩ := Finset.card_eq_one.mp (by omega : n.primeFactors.card = 1)
    have hself := prod_primeFactors_pow_self hn0
    rw [hp, Finset.prod_singleton] at hprod hself
    have h1 : n = 1 := by omega
    rw [h1] at hp
    simp at hp

theorem B_nonneg {q : ℕ} (hq : 1 ≤ q) : (0 : ℚ) ≤ ((q : ℚ) + 1) / ((q : ℚ) - 1) := by
  have : (1 : ℚ) ≤ q := by exact_mod_cast hq
  exact div_nonneg (by linarith) (by linarith)

theorem zleaf_bound {z : ℕ} (hz : 4 ≤ z) (i : ℕ) (hi : 1 ≤ i) (L : Finset ℕ)
    (hL : ∀ q ∈ L, ∃ k j, 1 ≤ k ∧ i ≤ j ∧ q + 1 = 2 ^ k * z ^ j) :
    ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ ((z : ℚ) ^ i) / ((z : ℚ) ^ i - 3) := by
  choose! K J hKJ using hL
  have hzi : ∀ j, i ≤ j → 4 ≤ z ^ j := fun j hj => by
    calc 4 ≤ z := hz
      _ = z ^ 1 := (pow_one z).symm
      _ ≤ z ^ j := Nat.pow_le_pow_right (by omega) (by omega)
  rw [← Finset.prod_fiberwise_of_maps_to (g := J) (t := L.image J)
    (fun x hx => Finset.mem_image_of_mem _ hx)]
  have hfib : ∀ j ∈ L.image J, ∏ q ∈ L.filter (fun q => J q = j),
      (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ ((z : ℚ) ^ j) / ((z : ℚ) ^ j - 2) := by
    intro j hj
    obtain ⟨q0, hq0, rfl⟩ := Finset.mem_image.mp hj
    have h3 : 3 ≤ z ^ (J q0) := by have := hzi _ (hKJ q0 hq0).2.1; omega
    have h := fiber_bound h3 (L.filter (fun q => J q = J q0)) (fun q hq => by
      obtain ⟨hqL, hJ⟩ := Finset.mem_filter.mp hq
      exact ⟨K q, (hKJ q hqL).1, by rw [← hJ]; exact (hKJ q hqL).2.2⟩)
    push_cast at h
    exact h
  refine (Finset.prod_le_prod (fun j _ => Finset.prod_nonneg fun q hq => ?_) hfib).trans ?_
  · obtain ⟨hk, hj, he⟩ := hKJ q (Finset.mem_filter.mp hq).1
    have h1 : 2 ^ 1 ≤ 2 ^ K q := Nat.pow_le_pow_right (by norm_num) hk
    have h2 : 1 ≤ z ^ J q := Nat.one_le_pow _ _ (by omega)
    have h3 := Nat.mul_le_mul h1 h2
    exact B_nonneg (by omega)
  · have hg := geom_bound (z := z) (c := 2) (v := 1) (by omega) (L.image J).card (L.image J) i rfl
      (by have := hzi i le_rfl; omega)
      (fun j hj => by
        obtain ⟨q0, hq0, rfl⟩ := Finset.mem_image.mp hj
        exact (hKJ q0 hq0).2.1)
    simp only [Nat.cast_one, one_mul, Nat.cast_ofNat] at hg
    norm_num at hg ⊢
    exact hg

theorem filter_mem_singleton {n z : ℕ} (hz : z ∈ n.primeFactors) (hz2 : z ≠ 2) :
    (n.primeFactors.erase 2).filter (fun r => r ∈ ({z} : Finset ℕ)) = {z} := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_singleton]
  constructor
  · rintro ⟨-, rfl⟩
    rfl
  · rintro rfl
    exact ⟨⟨hz2, hz⟩, rfl⟩

theorem eq_ninety_of_three_sq {n : ℕ} (h : Erdos1052.IsUnitaryPerfect n)
    (h3 : n.factorization 3 = 2)
    (hs : ∀ r ∈ n.primeFactors, r ≠ 2 → r ≠ 3 → n.factorization r = 1) : n = 90 := by
  have hn0 : n ≠ 0 := h.2.ne'
  have h2 := two_dvd_of_isUnitaryPerfect h
  have hm : 1 ≤ n.factorization 2 := Nat.prime_two.factorization_pos_of_dvd hn0 h2
  have h3pf : 3 ∈ n.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Nat.prime_three, Nat.dvd_of_factorization_pos (by omega), hn0⟩
  have h2pf : 2 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_two, h2, hn0⟩
  have hs' : ∀ r ∈ n.primeFactors, r ≠ 2 → r ∉ ({3} : Finset ℕ) → n.factorization r = 1 :=
    fun r hr hr2 hrN => hs r hr hr2 (fun e => hrN (Finset.mem_singleton.mpr e))
  have E := kernel_balance (N := {3}) h h2 hs'
  rw [filter_mem_singleton h3pf (by norm_num), Finset.prod_singleton, Finset.prod_singleton, h3] at E
  have hP : ∀ p ∈ (n.primeFactors.erase 2).filter (fun r => ¬ r ∈ ({3} : Finset ℕ)),
      p.Prime ∧ p ≠ 2 := fun p hp => by
    have h1 := (Finset.mem_filter.mp hp).1
    exact ⟨Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase h1), Finset.ne_of_mem_erase h1⟩
  have h3P : 3 ∉ (n.primeFactors.erase 2).filter (fun r => ¬ r ∈ ({3} : Finset ℕ)) :=
    fun hmem => (Finset.mem_filter.mp hmem).2 (Finset.mem_singleton_self 3)
  obtain ⟨hm1, hP5⟩ := core_e2 hP h3P hm (by norm_num at E ⊢; exact E)
  have hself := prod_primeFactors_pow_self hn0
  rw [← Finset.mul_prod_erase _ _ h2pf,
    ← Finset.prod_filter_mul_prod_filter_not (n.primeFactors.erase 2)
      (fun r => r ∈ ({3} : Finset ℕ)),
    filter_mem_singleton h3pf (by norm_num), hP5, Finset.prod_singleton, Finset.prod_singleton,
    h3, hm1] at hself
  have h5pf : 5 ∈ n.primeFactors := by
    have : 5 ∈ (n.primeFactors.erase 2).filter (fun r => ¬ r ∈ ({3} : Finset ℕ)) := by
      rw [hP5]
      exact Finset.mem_singleton_self 5
    exact Finset.mem_of_mem_erase (Finset.mem_filter.mp this).1
  rw [hs 5 h5pf (by norm_num) (by norm_num)] at hself
  omega

theorem prod_le_pow_of_card {S : Finset ℕ} {β : ℕ → ℚ} {c : ℚ} (hc : 1 ≤ c)
    (h : ∀ q ∈ S, 0 ≤ β q ∧ β q ≤ c) {k : ℕ} (hk : S.card ≤ k) : ∏ q ∈ S, β q ≤ c ^ k := by
  calc ∏ q ∈ S, β q ≤ ∏ _q ∈ S, c := Finset.prod_le_prod (fun q hq => (h q hq).1) (fun q hq => (h q hq).2)
    _ = c ^ S.card := Finset.prod_const c
    _ ≤ c ^ k := pow_le_pow_right₀ hc hk

theorem budget3 {m : ℕ} {Q : Finset ℕ} (hbud : ¬ 81 ∣ (2 ^ m + 1) * ∏ p ∈ Q, (p + 1)) :
    (2 ^ m + 1).factorization 3 + ∑ p ∈ Q, (p + 1).factorization 3 ≤ 3 := by
  have h1 : (2 ^ m + 1) ≠ 0 := by positivity
  have h2 : ∏ p ∈ Q, (p + 1) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun p _ => by omega)
  have h81 : (81 : ℕ) = 3 ^ 4 := by norm_num
  rw [h81, Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three (mul_ne_zero h1 h2),
    Nat.factorization_mul h1 h2, Finsupp.add_apply,
    Nat.factorization_prod (fun p _ => by omega), Finsupp.finsetSum_apply] at hbud
  omega

theorem one_le_fact3 {x : ℕ} (hx : x ≠ 0) (h : 3 ∣ x) : 1 ≤ x.factorization 3 :=
  Nat.prime_three.factorization_pos_of_dvd hx h

theorem two_le_fact3 {x : ℕ} (hx : x ≠ 0) (h : 9 ∣ x) : 2 ≤ x.factorization 3 := by
  have h9 : (9 : ℕ) = 3 ^ 2 := by norm_num
  rw [h9] at h
  exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hx).mp h

theorem leaf3_size {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (h3 : 3 ∣ q + 1) :
    q % 6 = 5 := by
  rcases hq.eq_two_or_odd with h | h
  · exact absurd h hq2
  · omega

theorem leaf3_bound_two {L : Finset ℕ} {β : ℕ → ℚ}
    (hL : ∀ q ∈ L, q.Prime ∧ q ≠ 2 ∧ 3 ∣ q + 1)
    (hsum : ∑ q ∈ L, (q + 1).factorization 3 ≤ 2)
    (hβ : ∀ q ∈ L, 0 < β q ∧ β q ≤ ((q : ℚ) + 1) / ((q : ℚ) - 1))
    (hβ5 : β 5 ≤ 4 / 3) (hβ11 : β 11 ≤ 8 / 7) : ∏ q ∈ L, β q ≤ 32 / 21 := by
  have hval : ∀ q ∈ L, 1 ≤ (q + 1).factorization 3 := fun q hq =>
    one_le_fact3 (by omega) (hL q hq).2.2
  have hcardle : ∀ S : Finset ℕ, S ⊆ L → S.card ≤ ∑ q ∈ S, (q + 1).factorization 3 := fun S hS => by
    have := Finset.card_nsmul_le_sum S (fun q => (q + 1).factorization 3) 1
      (fun q hq => hval q (hS hq))
    simpa using this
  have h87 : ∀ q ∈ L, q ≠ 5 → 0 ≤ β q ∧ β q ≤ 8 / 7 := fun q hq hq5 => by
    obtain ⟨hqp, hq2, hq3⟩ := hL q hq
    have h6 := leaf3_size hqp hq2 hq3
    refine ⟨(hβ q hq).1.le, ?_⟩
    by_cases h11 : q = 11
    · rw [h11]; exact hβ11
    · have h17 : 17 ≤ q := by omega
      refine (hβ q hq).2.trans ((B_anti (by norm_num) h17).trans ?_)
      norm_num
  by_cases h5 : 5 ∈ L
  · have hsum' : ∑ q ∈ L.erase 5, (q + 1).factorization 3 ≤ 1 := by
      have := Finset.add_sum_erase L (fun q => (q + 1).factorization 3) h5
      have h1 := hval 5 h5
      omega
    have hc : (L.erase 5).card ≤ 1 := (hcardle _ (Finset.erase_subset _ _)).trans hsum'
    have hp := prod_le_pow_of_card (c := 8 / 7) (by norm_num)
      (fun q hq => h87 q (Finset.mem_of_mem_erase hq) (Finset.ne_of_mem_erase hq)) hc
    rw [← Finset.mul_prod_erase L β h5]
    calc β 5 * ∏ q ∈ L.erase 5, β q ≤ 4 / 3 * (8 / 7) ^ 1 :=
          mul_le_mul hβ5 hp (Finset.prod_nonneg fun q hq =>
            (hβ q (Finset.mem_of_mem_erase hq)).1.le) (by norm_num)
      _ = 32 / 21 := by norm_num
  · have hc : L.card ≤ 2 := (hcardle L (Finset.Subset.refl _)).trans hsum
    have hp := prod_le_pow_of_card (c := 8 / 7) (by norm_num)
      (fun q hq => h87 q hq (fun e => h5 (e ▸ hq))) hc
    refine hp.trans ?_
    norm_num

theorem leaf3_bound {m : ℕ} {Q L : Finset ℕ} {β : ℕ → ℚ} (hm : 1 ≤ m)
    (hLQ : L ⊆ Q)
    (hL : ∀ q ∈ L, q.Prime ∧ q ≠ 2 ∧ 3 ∣ q + 1)
    (hLform : ∀ q ∈ L, ∃ k j, q + 1 = 2 ^ k * 3 ^ j)
    (hbud : ¬ 81 ∣ (2 ^ m + 1) * ∏ p ∈ Q, (p + 1))
    (hr : ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ 2 ^ m + 1 → r % 3 = 2 → r ∈ Q)
    (hβ : ∀ q ∈ L, 0 < β q ∧ β q ≤ ((q : ℚ) + 1) / ((q : ℚ) - 1))
    (hβ5 : β 5 ≤ 4 / 3) (hβ5' : 5 ∣ 2 ^ m + 1 → β 5 ≤ 6 / 5) (hβ11 : β 11 ≤ 8 / 7) :
    ∏ q ∈ L, β q ≤ 32 / 21 := by
  have hB := budget3 hbud
  have hsub : ∀ S : Finset ℕ, S ⊆ Q →
      ∑ q ∈ S, (q + 1).factorization 3 ≤ ∑ q ∈ Q, (q + 1).factorization 3 :=
    fun S hS => Finset.sum_le_sum_of_subset hS
  have hval : ∀ q ∈ L, 1 ≤ (q + 1).factorization 3 := fun q hq =>
    one_le_fact3 (by omega) (hL q hq).2.2
  have hcardle : ∀ S : Finset ℕ, S ⊆ L → S.card ≤ ∑ q ∈ S, (q + 1).factorization 3 := fun S hS => by
    have := Finset.card_nsmul_le_sum S (fun q => (q + 1).factorization 3) 1
      (fun q hq => hval q (hS hq))
    simpa using this
  have hnn : ∀ S : Finset ℕ, S ⊆ L → (0 : ℚ) ≤ ∏ q ∈ S, β q := fun S hS =>
    Finset.prod_nonneg fun q hq => (hβ q (hS hq)).1.le
  have hsize : ∀ q ∈ L, q % 6 = 5 := fun q hq => leaf3_size (hL q hq).1 (hL q hq).2.1 (hL q hq).2.2
  rcases Nat.lt_or_ge (m % 2) 1 with hpar | hpar
  · rcases Nat.lt_or_ge (m % 4) 1 with h4 | h4
    · -- 4 ∣ m
      have hmod : (2 ^ m + 1) % 3 = 2 := by
        obtain ⟨k, rfl⟩ : ∃ k, m = 2 * k := ⟨m / 2, by omega⟩
        rw [pow_mul, Nat.add_mod, Nat.pow_mod]
        norm_num
      obtain ⟨r, hrp, hrd, hr3⟩ := exists_prime_mod3 _ hmod
      have hr2 : r ≠ 2 := by
        rintro rfl
        have h1 : 2 ∣ 1 := (Nat.dvd_add_right (dvd_pow_self 2 (by omega : m ≠ 0))).mp hrd
        omega
      have hrQ : r ∈ Q := hr r hrp hr2 hrd hr3
      have hr5 : r ≠ 5 := by
        rintro rfl
        obtain ⟨k, rfl⟩ : ∃ k, m = k * 4 := ⟨m / 4, by omega⟩
        rw [pow_mul] at hrd
        exact not_dvd_fourth_5 _ hrd
      have hr4 : r % 4 = 1 := mod_four_of_dvd_one_add_pow_even (p := 2) (e := m) hrp hr2
        (Nat.even_iff.mpr (by omega)) (by rw [add_comm]; exact hrd)
      have hrv : 1 ≤ (r + 1).factorization 3 := one_le_fact3 (by omega) (by omega)
      by_cases hrL : r ∈ L
      · -- r is a leaf: r + 1 = 2 * 3^j with j ≥ 2
        obtain ⟨k, j, hkj⟩ := hLform r hrL
        have hk1 : k = 1 := by
          rcases Nat.lt_or_ge k 1 with hk | hk
          · have hk0 : k = 0 := by omega
            rw [hk0, pow_zero, one_mul] at hkj
            have : (3 ^ j) % 2 = 1 := by simp [Nat.pow_mod]
            omega
          · rcases Nat.lt_or_ge k 2 with hk' | hk'
            · omega
            · have : 2 ^ 2 ∣ 2 ^ k := pow_dvd_pow 2 hk'
              have : 4 ∣ r + 1 := by
                rw [hkj]
                exact Dvd.dvd.mul_right (by simpa using this) _
              omega
        rw [hk1, pow_one] at hkj
        have hj2 : 2 ≤ j := by
          by_contra hj
          have hj' : j = 0 ∨ j = 1 := by omega
          rcases hj' with rfl | rfl
          · have h1 := hrp.one_lt
            omega
          · omega
        have h9 : 9 ∣ r + 1 := by
          rw [hkj]
          have : 3 ^ 2 ∣ 3 ^ j := pow_dvd_pow 3 hj2
          exact Dvd.dvd.mul_left (by simpa using this) _
        have hrv2 : 2 ≤ (r + 1).factorization 3 := two_le_fact3 (by omega) h9
        have h17 : 17 ≤ r := by omega
        have hsum' : ∑ q ∈ L.erase r, (q + 1).factorization 3 ≤ 1 := by
          have h1 := Finset.add_sum_erase L (fun q => (q + 1).factorization 3) hrL
          have h2 := hsub L hLQ
          omega
        have hc : (L.erase r).card ≤ 1 := (hcardle _ (Finset.erase_subset _ _)).trans hsum'
        have hp := prod_le_pow_of_card (c := 4 / 3) (by norm_num)
          (fun q hq => by
            have hqL := Finset.mem_of_mem_erase hq
            refine ⟨(hβ q hqL).1.le, ?_⟩
            by_cases h5 : q = 5
            · rw [h5]; exact hβ5
            · have h11 : 11 ≤ q := by have := hsize q hqL; omega
              refine (hβ q hqL).2.trans ((B_anti (by norm_num) h11).trans ?_)
              norm_num) hc
        have hβr : β r ≤ 9 / 8 := by
          refine (hβ r hrL).2.trans ((B_anti (by norm_num) h17).trans ?_)
          norm_num
        rw [← Finset.mul_prod_erase L β hrL]
        calc β r * ∏ q ∈ L.erase r, β q ≤ 9 / 8 * (4 / 3) ^ 1 :=
              mul_le_mul hβr hp (hnn _ (Finset.erase_subset _ _)) (by norm_num)
          _ ≤ 32 / 21 := by norm_num
      · -- r is not a leaf but uses one unit of the budget
        have hins : insert r L ⊆ Q := Finset.insert_subset hrQ hLQ
        have h1 := hsub _ hins
        rw [Finset.sum_insert hrL] at h1
        exact leaf3_bound_two hL (by omega) hβ hβ5 hβ11
    · -- m ≡ 2 mod 4: 5 divides 2^m + 1
      have h5d : 5 ∣ 2 ^ m + 1 := five_dvd_two_pow_add_one (by omega)
      have h5Q : 5 ∈ Q := hr 5 (by norm_num) (by norm_num) h5d (by norm_num)
      have hβ5'' := hβ5' h5d
      have h5v : 1 ≤ (5 + 1).factorization 3 := one_le_fact3 (by norm_num) (by norm_num)
      have hins : insert 5 (L.erase 5) ⊆ Q :=
        Finset.insert_subset h5Q ((Finset.erase_subset _ _).trans hLQ)
      have h1 := hsub _ hins
      rw [Finset.sum_insert (Finset.notMem_erase 5 L)] at h1
      have hsum5 : ∑ q ∈ L.erase 5, (q + 1).factorization 3 ≤ 2 := by omega
      have hL5 : ∏ q ∈ L, β q ≤ 6 / 5 * ∏ q ∈ L.erase 5, β q := by
        by_cases h5 : 5 ∈ L
        · rw [← Finset.mul_prod_erase L β h5]
          exact mul_le_mul_of_nonneg_right hβ5'' (hnn _ (Finset.erase_subset _ _))
        · rw [Finset.erase_eq_of_notMem h5]
          have := hnn L (Finset.Subset.refl _)
          linarith
      have hmemE : ∀ q ∈ L.erase 5, q ∈ L ∧ 11 ≤ q := fun q hq => by
        have hqL := Finset.mem_of_mem_erase hq
        have := hsize q hqL
        have := Finset.ne_of_mem_erase hq
        exact ⟨hqL, by omega⟩
      have hrest : ∏ q ∈ L.erase 5, β q ≤ 81 / 64 := by
        by_cases h11 : 11 ∈ L.erase 5
        · have h11v : 1 ≤ (11 + 1).factorization 3 := one_le_fact3 (by norm_num) (by norm_num)
          have hsum' : ∑ q ∈ (L.erase 5).erase 11, (q + 1).factorization 3 ≤ 1 := by
            have h1 := Finset.add_sum_erase (L.erase 5) (fun q => (q + 1).factorization 3) h11
            omega
          have hc : ((L.erase 5).erase 11).card ≤ 1 :=
            (hcardle _ ((Finset.erase_subset _ _).trans (Finset.erase_subset _ _))).trans hsum'
          have hp := prod_le_pow_of_card (c := 12 / 11) (by norm_num)
            (fun q hq => by
              have hq5 := Finset.mem_of_mem_erase hq
              obtain ⟨hqL, hq11⟩ := hmemE q hq5
              have hne := Finset.ne_of_mem_erase hq
              refine ⟨(hβ q hqL).1.le, ?_⟩
              have h17 : q ≠ 17 := by
                rintro rfl
                have h2 : 2 ≤ (17 + 1).factorization 3 := two_le_fact3 (by norm_num) (by norm_num)
                have h3 := Finset.single_le_sum (f := fun q => (q + 1).factorization 3)
                  (fun i _ => Nat.zero_le _) hq
                omega
              have h23 : 23 ≤ q := by have := hsize q hqL; omega
              refine (hβ q hqL).2.trans ((B_anti (by norm_num) h23).trans ?_)
              norm_num) hc
          rw [← Finset.mul_prod_erase (L.erase 5) β h11]
          calc β 11 * ∏ q ∈ (L.erase 5).erase 11, β q ≤ 8 / 7 * (12 / 11) ^ 1 :=
                mul_le_mul hβ11 hp (hnn _ ((Finset.erase_subset _ _).trans
                  (Finset.erase_subset _ _))) (by norm_num)
            _ ≤ 81 / 64 := by norm_num
        · have hc : (L.erase 5).card ≤ 2 := (hcardle _ (Finset.erase_subset _ _)).trans hsum5
          have hp := prod_le_pow_of_card (c := 9 / 8) (by norm_num)
            (fun q hq => by
              obtain ⟨hqL, hq11⟩ := hmemE q hq
              refine ⟨(hβ q hqL).1.le, ?_⟩
              have h17 : 17 ≤ q := by
                have := hsize q hqL
                have : q ≠ 11 := fun e => h11 (e ▸ hq)
                omega
              refine (hβ q hqL).2.trans ((B_anti (by norm_num) h17).trans ?_)
              norm_num) hc
          refine hp.trans ?_
          norm_num
      refine hL5.trans ?_
      calc (6 / 5 : ℚ) * ∏ q ∈ L.erase 5, β q ≤ 6 / 5 * (81 / 64) :=
            mul_le_mul_of_nonneg_left hrest (by norm_num)
        _ ≤ 32 / 21 := by norm_num
  · -- m odd: 3 divides 2^m + 1
    have h3d : 3 ∣ 2 ^ m + 1 := three_dvd_two_pow_add_one (by omega)
    have h3v : 1 ≤ (2 ^ m + 1).factorization 3 := one_le_fact3 (by positivity) h3d
    have h1 := hsub L hLQ
    exact leaf3_bound_two hL (by omega) hβ hβ5 hβ11

theorem not_two_pow_dvd {m K K' : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hK2 : ¬ 2 ∣ K)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p) :
    ¬ 2 ^ (m + 2) ∣ (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) := by
  rw [E]
  intro h
  have e : 2 ^ (m + 2) = 2 ^ (m + 1) * 2 := pow_succ 2 (m + 1)
  rw [e, mul_assoc] at h
  have h2 : 2 ∣ K * ∏ p ∈ P, p := Nat.dvd_of_mul_dvd_mul_left (by positivity) h
  rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h2 with h | h
  · exact hK2 h
  · obtain ⟨p, hp, h2p⟩ := (Prime.dvd_finsetProd_iff Nat.prime_two.prime _).mp h
    exact (hP p hp).2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two (hP p hp).1).mp h2p).symm

theorem three_not_dvd_rhs {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P) :
    ¬ 3 ∣ 2 ^ (m + 1) * ∏ p ∈ P, p := by
  intro h3
  rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h3 with h | h
  · have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h)
    omega
  · obtain ⟨p, hp, h3p⟩ := (Prime.dvd_finsetProd_iff Nat.prime_three.prime _).mp h
    rw [(Nat.prime_dvd_prime_iff_eq Nat.prime_three (hP p hp).1).mp h3p] at h3P
    exact h3P hp

theorem core_e34 {m K K' : ℕ} {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ ({3} : Finset ℕ)) (hK0 : 0 < K)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p) (hm : 6 ≤ m)
    (hQ : ∀ q ∈ P, (∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c ∈ ({3} : Finset ℕ)) → q ∈ Q)
    (hbud : ¬ 81 ∣ (2 ^ m + 1) * ∏ p ∈ Q, (p + 1))
    (hrQ : ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ 2 ^ m + 1 → r % 3 = 2 → r ∈ Q)
    (b7 b41 : ℚ) (h7w : 8 / 7 ≤ b7 ∧ b7 ≤ 4 / 3) (h41w : 42 / 41 ≤ b41 ∧ b41 ≤ 42 / 40)
    (h7par : ∀ p ∈ P, 7 ∣ p + 1 → p = 41 ∧ 8 / 7 * b41 ≤ b7)
    (h41par : b41 = 42 / 40 ∨ ∀ p ∈ P, ¬ 41 ∣ p + 1)
    (hκ : (K' : ℚ) / K * b7 ≤ 32 / 27) : False := by
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have hn3 : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  let β : ℕ → ℚ := fun p => if p = 5 then (if 5 ∣ 2 ^ m + 1 then 6 / 5 else 4 / 3) else
    if p = 7 then b7 else if p = 11 then 8 / 7 else if p = 41 then b41 else if p = 3 then 1 else
      ((p : ℚ) + 1) / ((p : ℚ) - 1)
  have hβ5 : β 5 = if 5 ∣ 2 ^ m + 1 then 6 / 5 else 4 / 3 := by simp [β]
  have hβ7 : β 7 = b7 := by simp [β]
  have hβ11 : β 11 = 8 / 7 := by simp [β]
  have hβ41 : β 41 = b41 := by simp [β]
  have hβ3 : β 3 = 1 := by simp [β]
  have hβB : ∀ p : ℕ, p ≠ 5 → p ≠ 7 → p ≠ 11 → p ≠ 41 → p ≠ 3 →
      β p = ((p : ℚ) + 1) / ((p : ℚ) - 1) := fun p h5 h7 h11 h41 h3 => by
    simp [β, h5, h7, h11, h41, h3]
  have hβ5le : β 5 ≤ 4 / 3 := by
    rw [hβ5]
    split_ifs <;> norm_num
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases h5 : p = 5
    · subst h5
      rw [hβ5]
      split_ifs <;> norm_num
    by_cases h7 : p = 7
    · subst h7
      rw [hβ7]
      constructor <;> norm_num <;> linarith [h7w.1, h7w.2]
    by_cases h11 : p = 11
    · subst h11
      rw [hβ11]
      norm_num
    by_cases h41 : p = 41
    · subst h41
      rw [hβ41]
      constructor <;> norm_num <;> linarith [h41w.1, h41w.2]
    · have h3 : p ≠ 3 := fun h => h3P (h ▸ hp)
      rw [hβB p h5 h7 h11 h41 h3]
      exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  obtain ⟨L, hLP, hLleaf, hmain⟩ := master_gen (N := {3}) hP hK hK0 E β hB
    (fun p hp c hc hcd _ hne => by
      have hpp := (hP p hp).1
      have hpodd : p % 2 = 1 := by
        rcases hpp.eq_two_or_odd with h | h
        · exact absurd h (hP p hp).2
        · exact h
      by_cases h5 : c = 5
      · subst h5
        rw [hβ5]
        by_cases h5d : 5 ∣ 2 ^ m + 1
        · exact absurd hcd (S4 5 (by norm_num) (by norm_num) (hn3 (by norm_num)) h5d p hp)
        · rw [if_neg h5d]
          have h19 : 19 ≤ p := by
            have h9 : p ≠ 9 := by
              rintro rfl
              norm_num at hpp
            omega
          have := (hB p hp).2.trans (B_anti (by norm_num) h19)
          norm_num at this ⊢
          linarith
      by_cases h7 : c = 7
      · subst h7
        obtain ⟨hp41, hw⟩ := h7par p hp hcd
        rw [hβ7, hp41, hβ41]
        norm_num at hw ⊢
        linarith
      by_cases h11 : c = 11
      · subst h11
        rw [hβ11]
        have h43 : 43 ≤ p := by
          have h21 : p ≠ 21 := by
            rintro rfl
            norm_num at hpp
          omega
        have := (hB p hp).2.trans (B_anti (by norm_num) h43)
        norm_num at this ⊢
        linarith
      by_cases h41 : c = 41
      · subst h41
        rcases h41par with hb | hno
        · exact absurd (by rw [hβ41, hb]; norm_num) hne
        · exact absurd hcd (hno p hp)
      · exact absurd (hβB c h5 h7 h11 h41 (fun h => h3P (h ▸ hc))) hne)
  have hβpos : ∀ q ∈ L, 0 < β q := fun q hq => by
    have h0 : (0 : ℚ) ≤ 1 / (q : ℚ) := by positivity
    linarith [(hB q (hLP hq)).1]
  have hsplit := Finset.prod_filter_mul_prod_filter_not L (fun q => 3 ∣ q + 1) β
  have h3leaves : ∏ q ∈ L.filter (fun q => 3 ∣ q + 1), β q ≤ 32 / 21 := by
    refine leaf3_bound (m := m) (Q := Q) (by omega) (fun q hq => ?_) (fun q hq => ?_)
      (fun q hq => ?_) hbud hrQ (fun q hq => ?_) hβ5le (fun h5d => ?_) (le_of_eq hβ11)
    · have hqL := (Finset.mem_filter.mp hq).1
      exact hQ q (hLP hqL) (hLleaf q hqL)
    · have hqL := (Finset.mem_filter.mp hq).1
      exact ⟨(hP q (hLP hqL)).1, (hP q (hLP hqL)).2, (Finset.mem_filter.mp hq).2⟩
    · have hqL := (Finset.mem_filter.mp hq).1
      exact two_pow_mul_pow_of_odd_primes_eq (by omega)
        (fun c hc hc2 hcd => Finset.mem_singleton.mp (hLleaf q hqL c hc hc2 hcd))
    · have hqL := (Finset.mem_filter.mp hq).1
      exact ⟨hβpos q hqL, (hB q (hLP hqL)).2⟩
    · rw [hβ5, if_pos h5d]
  have hmers : ∏ q ∈ L.filter (fun q => ¬ 3 ∣ q + 1), β q ≤
      (β 3 * β 7 * β 31 * β 127) * (2048 / 2047) := by
    refine mersenne_bound β _ (fun q hq => (hP q (hLP (Finset.mem_filter.mp hq).1)).1)
      (fun q hq => ?_)
      (fun q hq => ⟨hβpos q (Finset.mem_filter.mp hq).1,
        (hB q (hLP (Finset.mem_filter.mp hq).1)).2⟩) ?_
    · obtain ⟨hqL, h3⟩ := Finset.mem_filter.mp hq
      refine two_pow_of_no_odd_prime (fun c hc hc2 hcd => ?_)
      rw [Finset.mem_singleton.mp (hLleaf q hqL c hc hc2 hcd)] at hcd
      exact h3 hcd
    · rw [hβ3, hβ7, hβB 31 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
        hβB 127 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
      refine ⟨le_refl _, by linarith [h7w.1], by norm_num, by norm_num⟩
  have hvals : (β 3 * β 7 * β 31 * β 127) * (2048 / 2047) =
      b7 * ((32 / 30) * (128 / 126) * (2048 / 2047)) := by
    rw [hβ3, hβ7, hβB 31 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
      hβB 127 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
    norm_num
    ring
  rw [hvals] at hmers
  have hb70 : (0 : ℚ) ≤ b7 := by linarith [h7w.1]
  have hKq : (0 : ℚ) < K := by exact_mod_cast hK0
  have hKr0 : (0 : ℚ) ≤ (K' : ℚ) / K := div_nonneg (Nat.cast_nonneg _) hKq.le
  have hprod : ∏ q ∈ L, β q ≤ 32 / 21 * (b7 * ((32 / 30) * (128 / 126) * (2048 / 2047))) := by
    rw [← hsplit]
    exact mul_le_mul h3leaves hmers
      (Finset.prod_nonneg fun q hq => (hβpos q (Finset.mem_filter.mp hq).1).le) (by norm_num)
  have hT : 1 + 1 / (2 : ℚ) ^ m ≤ 65 / 64 := by
    have h2 : (2 : ℚ) ^ 6 ≤ (2 : ℚ) ^ m := pow_le_pow_right₀ (by norm_num) hm
    have : 1 / (2 : ℚ) ^ m ≤ 1 / (2 : ℚ) ^ 6 := one_div_le_one_div_of_le (by positivity) h2
    norm_num at this ⊢
    linarith
  have hfin : (2 : ℚ) ≤ 65 / 64 * (32 / 21 * ((32 / 30) * (128 / 126) * (2048 / 2047)) * (32 / 27)) := by
    calc (2 : ℚ) ≤ (1 + 1 / (2 : ℚ) ^ m) * ((K' : ℚ) / K) * ∏ q ∈ L, β q := hmain
      _ ≤ (1 + 1 / (2 : ℚ) ^ m) * ((K' : ℚ) / K) *
          (32 / 21 * (b7 * ((32 / 30) * (128 / 126) * (2048 / 2047)))) :=
          mul_le_mul_of_nonneg_left hprod (mul_nonneg (by positivity) hKr0)
      _ = (1 + 1 / (2 : ℚ) ^ m) * (32 / 21 * ((32 / 30) * (128 / 126) * (2048 / 2047)) *
          ((K' : ℚ) / K * b7)) := by ring
      _ ≤ 65 / 64 * (32 / 21 * ((32 / 30) * (128 / 126) * (2048 / 2047)) * (32 / 27)) :=
          mul_le_mul hT (mul_le_mul_of_nonneg_left hκ (by norm_num))
            (mul_nonneg (by norm_num) (mul_nonneg hKr0 hb70)) (by norm_num)
  norm_num at hfin

theorem core_e3 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (hm : 1 ≤ m)
    (E : (2 ^ m + 1) * 28 * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 27 * ∏ p ∈ P, p) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 27 → c ∈ ({3} : Finset ℕ) := fun c hc hd => by
    have h27 : (27 : ℕ) = 3 ^ 3 := by norm_num
    rw [h27] at hd
    exact Finset.mem_singleton.mpr ((Nat.prime_dvd_prime_iff_eq hc Nat.prime_three).mp
      (hc.dvd_of_dvd_pow hd))
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have hn3 : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  have h7P : 7 ∈ P := S7 7 (by norm_num) (by norm_num) (hn3 (by norm_num)) (by norm_num)
  have h7no : ∀ p ∈ P, ¬ 7 ∣ p + 1 := S8 7 (by norm_num) (by norm_num) (hn3 (by norm_num)) (by norm_num)
  have h2adic := not_two_pow_dvd hP (by norm_num : ¬ 2 ∣ 27) E
  have hsubdvd : ∀ S : Finset ℕ, S ⊆ P → (2 ^ m + 1) * 28 * ∏ p ∈ S, (p + 1) ∣
      (2 ^ m + 1) * 28 * ∏ p ∈ P, (p + 1) := fun S hS =>
    mul_dvd_mul_left _ (Finset.prod_dvd_prod_of_subset _ _ (fun p => p + 1) hS)
  have hbud : ¬ 81 ∣ (2 ^ m + 1) * ∏ p ∈ P, (p + 1) := by
    intro h
    have h' : 81 ∣ (2 ^ m + 1) * 28 * ∏ p ∈ P, (p + 1) := by
      have e : (2 ^ m + 1) * 28 * ∏ p ∈ P, (p + 1) = 28 * ((2 ^ m + 1) * ∏ p ∈ P, (p + 1)) := by ring
      rw [e]
      exact h.mul_left 28
    rw [E] at h'
    have e : 2 ^ (m + 1) * 27 * ∏ p ∈ P, p = 27 * (2 ^ (m + 1) * ∏ p ∈ P, p) := by ring
    rw [e] at h'
    exact three_not_dvd_rhs hP h3P
      (Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 27) (by simpa using h'))
  rcases Nat.lt_or_ge m 6 with hsmall | hm6
  · -- m ≤ 5: the 2-adic budget
    have h4 : 4 ≤ m := by
      by_contra hlt
      apply h2adic
      refine Dvd.dvd.trans ?_ (hsubdvd {7} (Finset.singleton_subset_iff.mpr h7P))
      rw [Finset.prod_singleton]
      have : 2 ^ (m + 2) ∣ 2 ^ 5 := pow_dvd_pow 2 (by omega)
      exact this.trans ⟨(2 ^ m + 1) * 7, by ring⟩
    have hm45 : m = 4 ∨ m = 5 := by omega
    rcases hm45 with rfl | rfl
    · have h17 : 17 ∈ P := S2 17 (by norm_num) (by norm_num) (hn3 (by norm_num)) (by norm_num)
      apply h2adic
      have hS : ({7, 17} : Finset ℕ) ⊆ P := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact h7P
        · exact h17
      refine Dvd.dvd.trans ?_ (hsubdvd {7, 17} hS)
      rw [Finset.prod_pair (by norm_num)]
      norm_num
    · have h11 : 11 ∈ P := S2 11 (by norm_num) (by norm_num) (hn3 (by norm_num)) (by norm_num)
      apply h2adic
      have hS : ({7, 11} : Finset ℕ) ⊆ P := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact h7P
        · exact h11
      refine Dvd.dvd.trans ?_ (hsubdvd {7, 11} hS)
      rw [Finset.prod_pair (by norm_num)]
      norm_num
  · refine core_e34 (Q := P) hP h3P hK (by norm_num) E hm6 (fun q hq _ => hq) hbud
      (fun r hr hr2 hrd hr3 => S2 r hr hr2 (hn3 (by omega)) hrd)
      (8 / 7) (42 / 40) (by norm_num) (by norm_num)
      (fun p hp h7 => absurd h7 (h7no p hp)) (Or.inl rfl) ?_
    norm_num

theorem core_e4 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (hm : 1 ≤ m)
    (E : (2 ^ m + 1) * 82 * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 81 * ∏ p ∈ P, p) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 81 → c ∈ ({3} : Finset ℕ) := fun c hc hd => by
    have h81 : (81 : ℕ) = 3 ^ 4 := by norm_num
    rw [h81] at hd
    exact Finset.mem_singleton.mpr ((Nat.prime_dvd_prime_iff_eq hc Nat.prime_three).mp
      (hc.dvd_of_dvd_pow hd))
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have hn3 : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  have h41P : 41 ∈ P := S7 41 (by norm_num) (by norm_num) (hn3 (by norm_num)) (by norm_num)
  have h41no : ∀ p ∈ P, ¬ 41 ∣ p + 1 :=
    S8 41 (by norm_num) (by norm_num) (hn3 (by norm_num)) (by norm_num)
  have h7P : 7 ∈ P := S1 7 (by norm_num) (by norm_num) (hn3 (by norm_num)) 41 h41P (by norm_num)
  have h7par : ∀ p ∈ P, 7 ∣ p + 1 → p = 41 := fun p hp h7 =>
    S3 7 (by norm_num) (by norm_num) (hn3 (by norm_num)) p hp 41 h41P h7 (by norm_num)
  have h41top : ¬ 41 ∣ 2 ^ m + 1 := fun h => by
    apply S_sq hP hK E (c := 41) (by norm_num) (by norm_num) (hn3 (by norm_num))
    have : 41 * 41 ∣ (2 ^ m + 1) * 82 := mul_dvd_mul h (by norm_num)
    exact this.mul_right _
  have h2adic := not_two_pow_dvd hP (by norm_num : ¬ 2 ∣ 81) E
  have hsubdvd : ∀ S : Finset ℕ, S ⊆ P → (2 ^ m + 1) * 82 * ∏ p ∈ S, (p + 1) ∣
      (2 ^ m + 1) * 82 * ∏ p ∈ P, (p + 1) := fun S hS =>
    mul_dvd_mul_left _ (Finset.prod_dvd_prod_of_subset _ _ (fun p => p + 1) hS)
  have hbud : ¬ 81 ∣ (2 ^ m + 1) * ∏ p ∈ P.erase 41, (p + 1) := by
    intro h
    have h' : 81 * 3 ∣ (2 ^ m + 1) * 82 * ∏ p ∈ P, (p + 1) := by
      rw [← Finset.mul_prod_erase P (fun p => p + 1) h41P]
      have e : (2 ^ m + 1) * 82 * ((41 + 1) * ∏ p ∈ P.erase 41, (p + 1)) =
          ((2 ^ m + 1) * ∏ p ∈ P.erase 41, (p + 1)) * (3 * 1148) := by ring
      rw [e]
      exact mul_dvd_mul h (Dvd.intro _ rfl)
    rw [E] at h'
    have e : 2 ^ (m + 1) * 81 * ∏ p ∈ P, p = 81 * (2 ^ (m + 1) * ∏ p ∈ P, p) := by ring
    rw [e] at h'
    exact three_not_dvd_rhs hP h3P (Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 81) h')
  have hS741 : ({7, 41} : Finset ℕ) ⊆ P := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact h7P
    · exact h41P
  rcases Nat.lt_or_ge m 6 with hsmall | hm6
  · have h4 : 4 ≤ m := by
      by_contra hlt
      apply h2adic
      refine Dvd.dvd.trans ?_ (hsubdvd {7, 41} hS741)
      rw [Finset.prod_pair (by norm_num)]
      have : 2 ^ (m + 2) ∣ 2 ^ 5 := pow_dvd_pow 2 (by omega)
      exact this.trans ⟨(2 ^ m + 1) * 861, by ring⟩
    have hm45 : m = 4 ∨ m = 5 := by omega
    rcases hm45 with rfl | rfl
    · have h17 : 17 ∈ P := S2 17 (by norm_num) (by norm_num) (hn3 (by norm_num)) (by norm_num)
      apply h2adic
      have hS : ({7, 41, 17} : Finset ℕ) ⊆ P := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl
        · exact h7P
        · exact h41P
        · exact h17
      refine Dvd.dvd.trans ?_ (hsubdvd {7, 41, 17} hS)
      rw [Finset.prod_insert (by norm_num), Finset.prod_pair (by norm_num)]
      norm_num
    · have h11 : 11 ∈ P := S2 11 (by norm_num) (by norm_num) (hn3 (by norm_num)) (by norm_num)
      apply h2adic
      have hS : ({7, 41, 11} : Finset ℕ) ⊆ P := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl
        · exact h7P
        · exact h41P
        · exact h11
      refine Dvd.dvd.trans ?_ (hsubdvd {7, 41, 11} hS)
      rw [Finset.prod_insert (by norm_num), Finset.prod_pair (by norm_num)]
      norm_num
  · refine core_e34 (Q := P.erase 41) hP h3P hK (by norm_num) E hm6 (fun q hq hleaf => ?_) hbud
      (fun r hr hr2 hrd hr3 => ?_)
      (48 / 41) (42 / 41) (by norm_num) (by norm_num)
      (fun p hp h7 => ⟨h7par p hp h7, by norm_num⟩) (Or.inr h41no) ?_
    · refine Finset.mem_erase.mpr ⟨?_, hq⟩
      rintro rfl
      have := Finset.mem_singleton.mp (hleaf 7 (by norm_num) (by norm_num) (by norm_num))
      omega
    · refine Finset.mem_erase.mpr ⟨?_, S2 r hr hr2 (hn3 (by omega)) hrd⟩
      rintro rfl
      exact h41top hrd
    · norm_num

theorem eq_ninety_of_three_pow_le_four {n : ℕ} (h : Erdos1052.IsUnitaryPerfect n)
    (h3lo : 2 ≤ n.factorization 3) (h3hi : n.factorization 3 ≤ 4)
    (hs : ∀ r ∈ n.primeFactors, r ≠ 2 → r ≠ 3 → n.factorization r = 1) : n = 90 := by
  have hn0 : n ≠ 0 := h.2.ne'
  have h2 := two_dvd_of_isUnitaryPerfect h
  have hm : 1 ≤ n.factorization 2 := Nat.prime_two.factorization_pos_of_dvd hn0 h2
  have h3pf : 3 ∈ n.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Nat.prime_three, Nat.dvd_of_factorization_pos (by omega), hn0⟩
  have hs' : ∀ r ∈ n.primeFactors, r ≠ 2 → r ∉ ({3} : Finset ℕ) → n.factorization r = 1 :=
    fun r hr hr2 hrN => hs r hr hr2 (fun e => hrN (Finset.mem_singleton.mpr e))
  have E := kernel_balance (N := {3}) h h2 hs'
  rw [filter_mem_singleton h3pf (by norm_num), Finset.prod_singleton, Finset.prod_singleton] at E
  have hP : ∀ p ∈ (n.primeFactors.erase 2).filter (fun r => ¬ r ∈ ({3} : Finset ℕ)),
      p.Prime ∧ p ≠ 2 := fun p hp => by
    have h1 := (Finset.mem_filter.mp hp).1
    exact ⟨Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase h1), Finset.ne_of_mem_erase h1⟩
  have h3P : 3 ∉ (n.primeFactors.erase 2).filter (fun r => ¬ r ∈ ({3} : Finset ℕ)) :=
    fun hmem => (Finset.mem_filter.mp hmem).2 (Finset.mem_singleton_self 3)
  have hcases : n.factorization 3 = 2 ∨ n.factorization 3 = 3 ∨ n.factorization 3 = 4 := by omega
  rcases hcases with h3 | h3 | h3
  · exact eq_ninety_of_three_sq h h3 hs
  · rw [h3] at E
    exact (core_e3 hP h3P hm (by norm_num at E ⊢; exact E)).elim
  · rw [h3] at E
    exact (core_e4 hP h3P hm (by norm_num at E ⊢; exact E)).elim

theorem prime_dvd_three_pow {e : ℕ} : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
  fun _ hc hd => Finset.mem_singleton.mpr ((Nat.prime_dvd_prime_iff_eq hc Nat.prime_three).mp
    (hc.dvd_of_dvd_pow hd))

theorem core_e6 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 6) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 6 * ∏ p ∈ P, p) :
    False := by
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP prime_dvd_three_pow E
  have hn3 : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  have h73 : 73 ∈ P := S7 73 (by norm_num) (by norm_num) (hn3 (by norm_num)) (by norm_num)
  have h37 : 37 ∈ P := S1 37 (by norm_num) (by norm_num) (hn3 (by norm_num)) 73 h73 (by norm_num)
  have h19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hn3 (by norm_num)) 37 h37 (by norm_num)
  exact S8 5 (by norm_num) (by norm_num) (hn3 (by norm_num)) (by norm_num) 19 h19 (by norm_num)

theorem core_e8 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 8) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 8 * ∏ p ∈ P, p) :
    False := by
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP prime_dvd_three_pow E
  have hn3 : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  have h193 : 193 ∈ P := S7 193 (by norm_num) (by norm_num) (hn3 (by norm_num)) (by norm_num)
  have h97 : 97 ∈ P := S1 97 (by norm_num) (by norm_num) (hn3 (by norm_num)) 193 h193 (by norm_num)
  exact S6 7 (by norm_num) (by norm_num) (hn3 (by norm_num)) 97 h97 (by norm_num)

theorem core_e9 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 9) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 9 * ∏ p ∈ P, p) :
    False := by
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP prime_dvd_three_pow E
  have hn3 : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  have h37 : 37 ∈ P := S7 37 (by norm_num) (by norm_num) (hn3 (by norm_num)) (by norm_num)
  exact S8 19 (by norm_num) (by norm_num) (hn3 (by norm_num)) (by norm_num) 37 h37 (by norm_num)

theorem core_e10 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 10) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 10 * ∏ p ∈ P, p) :
    False := by
  have hn3 : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  apply S_sq hP prime_dvd_three_pow E (c := 5) (by norm_num) (by norm_num) (hn3 (by norm_num))
  have : 5 * 5 ∣ 1 + 3 ^ 10 := by norm_num
  exact (this.mul_left _).mul_right _

theorem core_e12 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 12) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 12 * ∏ p ∈ P, p) :
    False := by
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP prime_dvd_three_pow E
  have hn3 : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  have h41 : 41 ∈ P := S7 41 (by norm_num) (by norm_num) (hn3 (by norm_num)) (by norm_num)
  have h6481 : 6481 ∈ P := S7 6481 (by norm_num) (by norm_num) (hn3 (by norm_num)) (by norm_num)
  have := S3 7 (by norm_num) (by norm_num) (hn3 (by norm_num)) 41 h41 6481 h6481 (by norm_num)
    (by norm_num)
  omega

theorem three_exponent_cases {n : ℕ} (h : Erdos1052.IsUnitaryPerfect n)
    (h3lo : 2 ≤ n.factorization 3) (h3hi : n.factorization 3 ≤ 12)
    (hs : ∀ r ∈ n.primeFactors, r ≠ 2 → r ≠ 3 → n.factorization r = 1) :
    n = 90 ∨ n.factorization 3 = 5 ∨ n.factorization 3 = 7 ∨ n.factorization 3 = 11 := by
  have hn0 : n ≠ 0 := h.2.ne'
  have h2 := two_dvd_of_isUnitaryPerfect h
  have h3pf : 3 ∈ n.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Nat.prime_three, Nat.dvd_of_factorization_pos (by omega), hn0⟩
  have hs' : ∀ r ∈ n.primeFactors, r ≠ 2 → r ∉ ({3} : Finset ℕ) → n.factorization r = 1 :=
    fun r hr hr2 hrN => hs r hr hr2 (fun e => hrN (Finset.mem_singleton.mpr e))
  have E := kernel_balance (N := {3}) h h2 hs'
  rw [filter_mem_singleton h3pf (by norm_num), Finset.prod_singleton, Finset.prod_singleton] at E
  have hP : ∀ p ∈ (n.primeFactors.erase 2).filter (fun r => ¬ r ∈ ({3} : Finset ℕ)),
      p.Prime ∧ p ≠ 2 := fun p hp => by
    have h1 := (Finset.mem_filter.mp hp).1
    exact ⟨Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase h1), Finset.ne_of_mem_erase h1⟩
  by_cases h4 : n.factorization 3 ≤ 4
  · exact Or.inl (eq_ninety_of_three_pow_le_four h h3lo h4 hs)
  · right
    by_contra hcon
    have hcases : n.factorization 3 = 6 ∨ n.factorization 3 = 8 ∨ n.factorization 3 = 9 ∨
        n.factorization 3 = 10 ∨ n.factorization 3 = 12 := by omega
    rcases hcases with h3 | h3 | h3 | h3 | h3 <;> rw [h3] at E
    · exact core_e6 hP E
    · exact core_e8 hP E
    · exact core_e9 hP E
    · exact core_e10 hP E
    · exact core_e12 hP E

theorem zleaf_form {q z : ℕ} (hz : z.Prime) (hz2 : z ≠ 2) (hq : q.Prime) (hq2 : q ≠ 2)
    (hleaf : ∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c ∈ ({z} : Finset ℕ))
    (hnm : ¬ ∃ k, q + 1 = 2 ^ k) : ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * z ^ j := by
  obtain ⟨k, j, hkj⟩ := two_pow_mul_pow_of_odd_primes_eq (M := q + 1) (z := z) (by omega)
    (fun c hc hc2 hcd => Finset.mem_singleton.mp (hleaf c hc hc2 hcd))
  have hqodd : q % 2 = 1 := by
    rcases hq.eq_two_or_odd with h' | h'
    · exact absurd h' hq2
    · exact h'
  have hzodd : z % 2 = 1 := by
    rcases hz.eq_two_or_odd with h' | h'
    · exact absurd h' hz2
    · exact h'
  refine ⟨k, j, ?_, ?_, hkj⟩
  · by_contra hk
    have hk0 : k = 0 := by omega
    rw [hk0, pow_zero, one_mul] at hkj
    have : (z ^ j) % 2 = 1 := by
      simp [Nat.pow_mod, hzodd]
    omega
  · by_contra hj
    have hj0 : j = 0 := by omega
    rw [hj0, pow_zero, mul_one] at hkj
    exact hnm ⟨k, hkj⟩

theorem prime_dvd_prime_pow {z e : ℕ} (hz : z.Prime) :
    ∀ c : ℕ, c.Prime → c ∣ z ^ e → c ∈ ({z} : Finset ℕ) :=
  fun _ hc hd => Finset.mem_singleton.mpr ((Nat.prime_dvd_prime_iff_eq hc hz).mp
    (hc.dvd_of_dvd_pow hd))

theorem kernel_balance_one {n z : ℕ} (h : Erdos1052.IsUnitaryPerfect n) (hz : z ∈ n.primeFactors)
    (hz2 : z ≠ 2) (hs : ∀ r ∈ n.primeFactors, r ≠ 2 → r ≠ z → n.factorization r = 1) :
    (∀ p ∈ (n.primeFactors.erase 2).filter (fun r => ¬ r ∈ ({z} : Finset ℕ)), p.Prime ∧ p ≠ 2) ∧
    (2 ^ n.factorization 2 + 1) * (1 + z ^ n.factorization z) *
        ∏ p ∈ (n.primeFactors.erase 2).filter (fun r => ¬ r ∈ ({z} : Finset ℕ)), (p + 1) =
      2 ^ (n.factorization 2 + 1) * z ^ n.factorization z *
        ∏ p ∈ (n.primeFactors.erase 2).filter (fun r => ¬ r ∈ ({z} : Finset ℕ)), p := by
  have h2 := two_dvd_of_isUnitaryPerfect h
  have hs' : ∀ r ∈ n.primeFactors, r ≠ 2 → r ∉ ({z} : Finset ℕ) → n.factorization r = 1 :=
    fun r hr hr2 hrN => hs r hr hr2 (fun e => hrN (Finset.mem_singleton.mpr e))
  have E := kernel_balance (N := {z}) h h2 hs'
  rw [filter_mem_singleton hz hz2, Finset.prod_singleton, Finset.prod_singleton] at E
  refine ⟨fun p hp => ?_, E⟩
  have h1 := (Finset.mem_filter.mp hp).1
  exact ⟨Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase h1), Finset.ne_of_mem_erase h1⟩

theorem one_add_pow_dvd_of_odd_mul {z e0 e : ℕ} (h : e % (2 * e0) = e0) :
    1 + z ^ e0 ∣ 1 + z ^ e := by
  obtain ⟨t, rfl⟩ : ∃ t, e = e0 * (2 * t + 1) := ⟨e / (2 * e0), by
    have := Nat.div_add_mod e (2 * e0)
    rw [h] at this
    linarith [this]⟩
  have hd := Odd.nat_add_dvd_pow_add_pow (z ^ e0) 1 (n := 2 * t + 1) ⟨t, rfl⟩
  rw [one_pow, ← pow_mul] at hd
  simpa [add_comm] using hd

theorem odd_pow_add_one_int (z : ℤ) (k : ℕ) :
    (z + 1) ^ 2 ∣ z ^ (2 * k + 1) + 1 - (2 * (k : ℤ) + 1) * (z + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨z ^ 2 * c + ((2 * (k : ℤ) + 1) * (z - 1) - 1), ?_⟩
    push_cast
    linear_combination z ^ 2 * hc

theorem exists_quot_mod {z e : ℕ} (he : Odd e) :
    ∃ Q : ℕ, 1 + z ^ e = (z + 1) * Q ∧ Q % (z + 1) = e % (z + 1) := by
  obtain ⟨k, rfl⟩ := he
  obtain ⟨Q, hQ⟩ := Odd.nat_add_dvd_pow_add_pow z 1 (n := 2 * k + 1) ⟨k, rfl⟩
  rw [one_pow] at hQ
  refine ⟨Q, by linarith, ?_⟩
  obtain ⟨c, hc⟩ := odd_pow_add_one_int (z : ℤ) k
  have hQ' : ((z : ℤ)) ^ (2 * k + 1) + 1 = ((z : ℤ) + 1) * Q := by exact_mod_cast hQ
  have hz1 : ((z : ℤ) + 1) ≠ 0 := by positivity
  have h2 : (Q : ℤ) - (2 * (k : ℤ) + 1) = ((z : ℤ) + 1) * c := by
    apply mul_left_cancel₀ hz1
    linear_combination hc - hQ'
  have h3 : (Q : ℤ) ≡ ((2 * k + 1 : ℕ) : ℤ) [ZMOD ((z + 1 : ℕ) : ℤ)] := by
    rw [Int.modEq_iff_dvd]
    exact ⟨-c, by push_cast; linarith⟩
  exact Int.natCast_modEq_iff.mp h3

theorem core_odd_exponent {m z e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hz : z.Prime) (hz3 : z % 3 = 2) (hz2 : z ≠ 2) (ho : Odd e)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p) :
    e % 6 = 1 := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ z ^ e → c ∈ ({z} : Finset ℕ) := prime_dvd_prime_pow hz
  have hnz : ∀ {c : ℕ}, c ≠ z → c ∉ ({z} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have hzodd : z % 2 = 1 := by
    rcases hz.eq_two_or_odd with h | h
    · exact absurd h hz2
    · exact h
  obtain ⟨Q, hQ, hQm⟩ := exists_quot_mod (z := z) ho
  have h6 : 6 ∣ z + 1 := by omega
  have hQ6 : Q % 6 = e % 6 := Nat.ModEq.of_dvd h6 hQm
  have heo : e % 2 = 1 := Nat.odd_iff.mp ho
  have h3z : 3 ∣ z + 1 := by omega
  have h3K : 3 ∣ 1 + z ^ e := by rw [hQ]; exact Dvd.dvd.mul_right h3z _
  by_contra hne
  have hcase : e % 6 = 3 ∨ e % 6 = 5 := by omega
  rcases hcase with h3 | h5
  · have h3Q : 3 ∣ Q := by omega
    have h9 : 3 * 3 ∣ 1 + z ^ e := by rw [hQ]; exact mul_dvd_mul h3z h3Q
    exact S_sq hP hK E (c := 3) Nat.prime_three (by norm_num) (hnz (by omega))
      ((h9.mul_left _).mul_right _)
  · have hQ3 : Q % 3 = 2 := by omega
    obtain ⟨r, hrp, hrd, hr3⟩ := exists_prime_mod3 Q hQ3
    have hrK : r ∣ 1 + z ^ e := by rw [hQ]; exact hrd.mul_left _
    have hr2 : r ≠ 2 := by
      rintro rfl
      omega
    have hrz : r ≠ z := by
      rintro rfl
      have he0 : e ≠ 0 := by omega
      have h1 : r ∣ r ^ e := dvd_pow_self r he0
      have h11 : r ∣ 1 := (Nat.dvd_add_left h1).mp hrK
      exact hrp.one_lt.ne' (Nat.dvd_one.mp h11)
    have hrP : r ∈ P := S7 r hrp hr2 (hnz hrz) hrK
    exact S8 3 Nat.prime_three (by norm_num) (hnz (by omega)) h3K r hrP (by omega)

theorem odd_exponent_mod_six {n z : ℕ} (h : Erdos1052.IsUnitaryPerfect n) (hz : z.Prime)
    (hz3 : z % 3 = 2) (hz2 : z ≠ 2)
    (hs : ∀ r ∈ n.primeFactors, r ≠ 2 → r ≠ z → n.factorization r = 1)
    (ho : Odd (n.factorization z)) : n.factorization z % 6 = 1 := by
  have hzpf : z ∈ n.primeFactors := Nat.mem_primeFactors.mpr
    ⟨hz, Nat.dvd_of_factorization_pos (fun h0 => by
      rw [h0] at ho
      exact absurd ho (by decide)), h.2.ne'⟩
  obtain ⟨hP, E⟩ := kernel_balance_one h hzpf hz2 hs
  exact core_odd_exponent hP hz hz3 hz2 ho E

theorem seven_zleaves {Lz : Finset ℕ} {β : ℕ → ℚ} (hp : ∀ q ∈ Lz, q.Prime)
    (hβ : ∀ q ∈ Lz, 0 < β q ∧ β q ≤ ((q : ℚ) + 1) / ((q : ℚ) - 1))
    (hform : ∀ q ∈ Lz, ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 7 ^ j)
    (h13 : β 13 ≤ 56 / 51) :
    ∏ q ∈ Lz, β q ≤ 56 / 51 * (112 / 110) * (49 / 47) * (343 / 340) := by
  classical
  choose! K J hKJ using hform
  have s0 := Finset.prod_filter_mul_prod_filter_not Lz (fun q => q = 13) β
  have h13' : ∏ q ∈ Lz.filter (fun q => q = 13), β q ≤ 56 / 51 := by
    rw [Finset.filter_eq']
    split_ifs
    · rw [Finset.prod_singleton]; exact h13
    · rw [Finset.prod_empty]; norm_num
  have hRL : Lz.filter (fun q => ¬ q = 13) ⊆ Lz := Finset.filter_subset _ _
  have hRB : ∏ q ∈ Lz.filter (fun q => ¬ q = 13), β q ≤
      ∏ q ∈ Lz.filter (fun q => ¬ q = 13), (((q : ℚ) + 1) / ((q : ℚ) - 1)) :=
    Finset.prod_le_prod (fun q hq => (hβ q (hRL hq)).1.le) (fun q hq => (hβ q (hRL hq)).2)
  have hRp : ∀ q ∈ Lz.filter (fun q => ¬ q = 13), q.Prime := fun q hq => hp q (hRL hq)
  have hRKJ : ∀ q ∈ Lz.filter (fun q => ¬ q = 13),
      1 ≤ K q ∧ 1 ≤ J q ∧ q + 1 = 2 ^ K q * 7 ^ J q := fun q hq => hKJ q (hRL hq)
  have hnnB : ∀ S : Finset ℕ, S ⊆ Lz.filter (fun q => ¬ q = 13) →
      (0 : ℚ) ≤ ∏ q ∈ S, (((q : ℚ) + 1) / ((q : ℚ) - 1)) := fun S hS =>
    Finset.prod_nonneg fun q hq => B_nonneg (hRp q (hS hq)).one_lt.le
  have hb3 := zleaf_bound (z := 7) (by norm_num) 3 (by norm_num)
    ((Lz.filter (fun q => ¬ q = 13)).filter (fun q => ¬ J q ≤ 2))
    (fun q hq => by
      obtain ⟨hqR, hJ⟩ := Finset.mem_filter.mp hq
      exact ⟨K q, J q, (hRKJ q hqR).1, by omega, (hRKJ q hqR).2.2⟩)
  have hb2 : ∏ q ∈ ((Lz.filter (fun q => ¬ q = 13)).filter (fun q => J q ≤ 2)).filter
      (fun q => ¬ J q = 1), (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤
      ((49 : ℕ) : ℚ) / (((49 : ℕ) : ℚ) - 2) := by
    refine fiber_bound (by norm_num) _ (fun q hq => ?_)
    obtain ⟨hq1, hJ1⟩ := Finset.mem_filter.mp hq
    obtain ⟨hqR, hJ2⟩ := Finset.mem_filter.mp hq1
    obtain ⟨hk, hj, he⟩ := hRKJ q hqR
    have hJ : J q = 2 := by omega
    rw [hJ] at he
    exact ⟨K q, hk, by rw [he]; norm_num⟩
  have hb1 : ∏ q ∈ ((Lz.filter (fun q => ¬ q = 13)).filter (fun q => J q ≤ 2)).filter
      (fun q => J q = 1), (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤
      ((112 : ℕ) : ℚ) / (((112 : ℕ) : ℚ) - 2) := by
    refine fiber_bound (by norm_num) _ (fun q hq => ?_)
    obtain ⟨hq1, hJ1⟩ := Finset.mem_filter.mp hq
    obtain ⟨hqR, hJ2⟩ := Finset.mem_filter.mp hq1
    obtain ⟨hk, hj, he⟩ := hRKJ q hqR
    rw [hJ1] at he
    have hpq := hRp q hqR
    have hne13 : ¬ q = 13 := (Finset.mem_filter.mp hqR).2
    have hK1 : K q ≠ 1 := fun h1 => by
      rw [h1] at he
      exact hne13 (by omega)
    have hK2 : K q ≠ 2 := fun h1 => by
      rw [h1] at he
      have : q = 27 := by omega
      rw [this] at hpq
      norm_num at hpq
    have hK3 : K q ≠ 3 := fun h1 => by
      rw [h1] at he
      have : q = 55 := by omega
      rw [this] at hpq
      norm_num at hpq
    have hK4 : K q ≠ 4 := fun h1 => by
      rw [h1] at he
      have : q = 111 := by omega
      rw [this] at hpq
      norm_num at hpq
    obtain ⟨k', hk'⟩ : ∃ k', K q = k' + 4 := ⟨K q - 4, by omega⟩
    refine ⟨k', by omega, ?_⟩
    rw [he, hk', pow_add]
    ring
  have s1 := Finset.prod_filter_mul_prod_filter_not (Lz.filter (fun q => ¬ q = 13))
    (fun q => J q ≤ 2) (fun q : ℕ => (((q : ℚ) + 1) / ((q : ℚ) - 1)))
  have s2 := Finset.prod_filter_mul_prod_filter_not
    ((Lz.filter (fun q => ¬ q = 13)).filter (fun q => J q ≤ 2))
    (fun q => J q = 1) (fun q : ℕ => (((q : ℚ) + 1) / ((q : ℚ) - 1)))
  have n1 := hnnB _ (Finset.filter_subset (fun q => ¬ J q ≤ 2) _)
  have n2 := hnnB _ ((Finset.filter_subset (fun q => ¬ J q = 1) _).trans
    (Finset.filter_subset (fun q => J q ≤ 2) _))
  have t2 : ∏ q ∈ (Lz.filter (fun q => ¬ q = 13)).filter (fun q => J q ≤ 2),
      (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 112 / 110 * (49 / 47) := by
    rw [← s2]
    refine mul_le_mul ?_ ?_ n2 (by norm_num)
    · norm_num at hb1 ⊢
      exact hb1
    · norm_num at hb2 ⊢
      exact hb2
  have t3 : ∏ q ∈ Lz.filter (fun q => ¬ q = 13), (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤
      112 / 110 * (49 / 47) * (343 / 340) := by
    rw [← s1]
    refine mul_le_mul t2 ?_ n1 (by norm_num)
    norm_num at hb3 ⊢
    exact hb3
  rw [← s0]
  have hfin := mul_le_mul h13' (hRB.trans t3)
    (Finset.prod_nonneg fun q hq => (hβ q (hRL hq)).1.le) (by norm_num)
  refine hfin.trans (le_of_eq ?_)
  ring

theorem seven_leaf_bound {P L : Finset ℕ} {β : ℕ → ℚ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hLP : L ⊆ P) (h7 : 7 ∉ P)
    (hleaf : ∀ q ∈ L, ∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c ∈ ({7} : Finset ℕ))
    (hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1))
    (h3 : 1 ≤ β 3 ∧ β 3 ≤ 3 / 2) (h31 : 1 ≤ β 31 ∧ β 31 ≤ 16 / 15)
    (h127 : 1 ≤ β 127 ∧ β 127 ≤ 64 / 63) (h13 : β 13 ≤ 56 / 51) :
    ∏ q ∈ L, β q ≤ (3 / 2 * (16 / 15) * (64 / 63) * (2048 / 2047)) *
      (56 / 51 * (112 / 110) * (49 / 47) * (343 / 340)) := by
  classical
  have hpos : ∀ q ∈ L, 0 < β q := fun q hq => by
    have h0 : (0 : ℚ) ≤ 1 / (q : ℚ) := by positivity
    linarith [(hB q (hLP hq)).1]
  have hsplit := Finset.prod_filter_mul_prod_filter_not L (fun q => ∃ k, q + 1 = 2 ^ k) β
  have hM : ∏ q ∈ L.filter (fun q => ∃ k, q + 1 = 2 ^ k), β q ≤
      3 / 2 * (16 / 15) * (64 / 63) * (2048 / 2047) := by
    have e1 : ∏ q ∈ L.filter (fun q => ∃ k, q + 1 = 2 ^ k), β q =
        ∏ q ∈ L.filter (fun q => ∃ k, q + 1 = 2 ^ k), (if q = 7 then (1 : ℚ) else β q) :=
      Finset.prod_congr rfl fun q hq => by
        have hq7 : q ≠ 7 := fun e => h7 (e ▸ hLP (Finset.mem_filter.mp hq).1)
        rw [if_neg hq7]
    have hm := mersenne_bound (fun q => if q = 7 then (1 : ℚ) else β q)
      (L.filter (fun q => ∃ k, q + 1 = 2 ^ k))
      (fun q hq => (hP q (hLP (Finset.mem_filter.mp hq).1)).1)
      (fun q hq => (Finset.mem_filter.mp hq).2)
      (fun q hq => by
        have hqL := (Finset.mem_filter.mp hq).1
        have hq7 : q ≠ 7 := fun e => h7 (e ▸ hLP hqL)
        simp only [if_neg hq7]
        exact ⟨hpos q hqL, (hB q (hLP hqL)).2⟩)
      ⟨by simpa using h3.1, by simp, by simpa using h31.1, by simpa using h127.1⟩
    have hm' : ∏ q ∈ L.filter (fun q => ∃ k, q + 1 = 2 ^ k), (if q = 7 then (1 : ℚ) else β q) ≤
        (β 3 * β 31 * β 127) * (2048 / 2047) := by simpa using hm
    rw [e1]
    refine hm'.trans ?_
    have a : β 3 * β 31 ≤ 3 / 2 * (16 / 15) :=
      mul_le_mul h3.2 h31.2 (by linarith [h31.1]) (by norm_num)
    have b : β 3 * β 31 * β 127 ≤ 3 / 2 * (16 / 15) * (64 / 63) :=
      mul_le_mul a h127.2 (by linarith [h127.1]) (by norm_num)
    exact mul_le_mul_of_nonneg_right b (by norm_num)
  have hZ : ∏ q ∈ L.filter (fun q => ¬ ∃ k, q + 1 = 2 ^ k), β q ≤
      56 / 51 * (112 / 110) * (49 / 47) * (343 / 340) :=
    seven_zleaves (fun q hq => (hP q (hLP (Finset.mem_filter.mp hq).1)).1)
      (fun q hq => ⟨hpos q (Finset.mem_filter.mp hq).1, (hB q (hLP (Finset.mem_filter.mp hq).1)).2⟩)
      (fun q hq => by
        obtain ⟨hqL, hnm⟩ := Finset.mem_filter.mp hq
        exact zleaf_form (by norm_num) (by norm_num) (hP q (hLP hqL)).1 (hP q (hLP hqL)).2
          (hleaf q hqL) hnm)
      h13
  rw [← hsplit]
  exact mul_le_mul hM hZ (Finset.prod_nonneg fun q hq => (hpos q (Finset.mem_filter.mp hq).1).le)
    (by norm_num)

theorem seven_core {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h7 : 7 ∉ P)
    (E : (2 ^ m + 1) * (1 + 7 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 7 ^ e * ∏ p ∈ P, p)
    (he : 3 ≤ e) (hm : 5 ≤ m) (β : ℕ → ℚ)
    (hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1))
    (h4 : ∀ p ∈ P, ∀ c ∈ P, c ∣ p + 1 →
        (∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({7} : Finset ℕ) → c' ∣ p + 1 → c ≤ c') →
        β c ≠ ((c : ℚ) + 1) / ((c : ℚ) - 1) → (1 + 1 / (c : ℚ)) * β p ≤ β c)
    (h3 : 1 ≤ β 3 ∧ β 3 ≤ 3 / 2) (h31 : 1 ≤ β 31 ∧ β 31 ≤ 16 / 15)
    (h127 : 1 ≤ β 127 ∧ β 127 ≤ 64 / 63) (h13 : β 13 ≤ 56 / 51) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 7 ^ e → c ∈ ({7} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  obtain ⟨L, hLP, hleaf, hineq⟩ := master_gen hP hK (by positivity) E β hB h4
  have hb := seven_leaf_bound hP hLP h7 hleaf hB h3 h31 h127 h13
  have h2m : (1 : ℚ) / 2 ^ m ≤ 1 / 32 := by
    have : (2 : ℚ) ^ 5 ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hm
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hKK : (((1 + 7 ^ e : ℕ) : ℚ)) / ((7 ^ e : ℕ) : ℚ) ≤ 344 / 343 := by
    have : (7 : ℚ) ^ 3 ≤ 7 ^ e := pow_le_pow_right₀ (by norm_num) he
    push_cast
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hprodnn : (0 : ℚ) ≤ ∏ q ∈ L, β q := Finset.prod_nonneg fun q hq => by
    have h0 : (0 : ℚ) ≤ 1 / (q : ℚ) := by positivity
    linarith [(hB q (hLP hq)).1]
  have hKnn : (0 : ℚ) ≤ ((1 + 7 ^ e : ℕ) : ℚ) / ((7 ^ e : ℕ) : ℚ) := by positivity
  have h1 : (1 + 1 / (2 : ℚ) ^ m) * (((1 + 7 ^ e : ℕ) : ℚ) / ((7 ^ e : ℕ) : ℚ)) ≤
      33 / 32 * (344 / 343) := mul_le_mul (by linarith) hKK hKnn (by norm_num)
  have h2 := mul_le_mul h1 hb hprodnn (by norm_num)
  have h3' : (33 / 32 * (344 / 343) : ℚ) * ((3 / 2 * (16 / 15) * (64 / 63) * (2048 / 2047)) *
      (56 / 51 * (112 / 110) * (49 / 47) * (343 / 340))) < 2 := by norm_num
  linarith

theorem core7_chain43 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h7 : 7 ∉ P)
    (E : (2 ^ m + 1) * (1 + 7 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 7 ^ e * ∏ p ∈ P, p)
    (he : 3 ≤ e) (hd : 43 ∣ 1 + 7 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 7 ^ e → c ∈ ({7} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 7 → c ∉ ({7} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g43 : 43 ∈ P := S7 43 (by norm_num) (by norm_num) (hnz (by norm_num)) hd
  have g11 : 11 ∈ P := S1 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 43 g43 (by norm_num)
  have g3 : 3 ∈ P := S1 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 11 g11 (by norm_num)
  have hm : 5 ≤ m := by
    by_contra hlt
    have h72 : ¬ 2 ∣ 7 ^ e := fun h => by
      have := Nat.prime_two.dvd_of_dvd_pow h
      omega
    apply not_two_pow_dvd hP h72 E
    have hsub : ({43, 11, 3} : Finset ℕ) ⊆ P := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> assumption
    have h1 : ∏ x ∈ ({43, 11, 3} : Finset ℕ), (x + 1) ∣ ∏ x ∈ P, (x + 1) :=
      Finset.prod_dvd_prod_of_subset _ _ _ hsub
    have hodd : (7 ^ e) % 2 = 1 := by simp [Nat.pow_mod]
    have h2K : 2 ∣ 1 + 7 ^ e := by omega
    have h2 : (2 : ℕ) ^ (m + 2) ∣ 2 * ∏ x ∈ ({43, 11, 3} : Finset ℕ), (x + 1) := by
      have e1 : 2 * ∏ x ∈ ({43, 11, 3} : Finset ℕ), (x + 1) = 2 ^ 7 * 33 := by decide
      rw [e1]
      exact Dvd.dvd.mul_right (pow_dvd_pow 2 (by omega)) _
    rw [mul_assoc]
    exact (h2.trans (mul_dvd_mul h2K h1)).mul_left _
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, β = fun q : ℕ => if q = 3 then (64 / 43 : ℚ) else if q = 11 then (48 / 43 : ℚ) else if q = 43 then (44 / 43 : ℚ) else if q = 13 then 56 / 51 else ((q : ℚ) + 1) / ((q : ℚ) - 1) := ⟨_, rfl⟩
  have b3 : β 3 = 64 / 43 := by rw [hβ]; simp
  have b11 : β 11 = 48 / 43 := by rw [hβ]; simp
  have b43 : β 43 = 44 / 43 := by rw [hβ]; simp
  have b13 : β 13 = 56 / 51 := by rw [hβ]; simp
  have bdef : ∀ q : ℕ, q ≠ 3 → q ≠ 11 → q ≠ 43 → q ≠ 13 → β q = ((q : ℚ) + 1) / ((q : ℚ) - 1) :=
    fun q h0 h1 h2 h13 => by rw [hβ]; simp [h0, h1, h2, h13]
  refine seven_core hP h7 E he hm β ?_ ?_ ?_ ?_ ?_ ?_
  · intro p hp
    by_cases c3 : p = 3
    · subst c3; rw [b3]; norm_num
    by_cases c11 : p = 11
    · subst c11; rw [b11]; norm_num
    by_cases c43 : p = 43
    · subst c43; rw [b43]; norm_num
    by_cases c13 : p = 13
    · subst c13; rw [b13]; norm_num
    rw [bdef p c3 c11 c43 c13]
    exact ⟨one_add_le_B (hP p hp).1.two_le, le_rfl⟩
  · intro p hp c hc hcp hleast hne
    by_cases c3 : c = 3
    · subst c3
      have : p = 11 := S3 3 (by norm_num) (by norm_num) (hnz (by norm_num)) p hp 11 g11 hcp
        (by norm_num)
      subst this
      rw [b11, b3]; norm_num
    by_cases c11 : c = 11
    · subst c11
      have : p = 43 := S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) p hp 43 g43 hcp
        (by norm_num)
      subst this
      rw [b43, b11]; norm_num
    by_cases c43 : c = 43
    · subst c43
      exact absurd hcp (S8 43 (by norm_num) (by norm_num) (hnz (by norm_num)) hd p hp)
    by_cases c13 : c = 13
    · subst c13
      have hpp := (hP p hp).1
      have hp103 : 103 ≤ p := by
        by_contra hlt
        obtain ⟨t, ht⟩ := hcp
        have ht8 : t < 8 := by omega
        interval_cases t <;> simp at ht <;> subst ht <;> first | omega | (norm_num at hpp)
      rw [bdef p (by omega) (by omega) (by omega) (by omega), b13]
      have hBp := B_anti (a := 103) (b := p) (by norm_num) hp103
      have h14 : (0 : ℚ) ≤ 1 + 1 / ((13 : ℕ) : ℚ) := by norm_num
      refine (mul_le_mul_of_nonneg_left hBp h14).trans ?_
      norm_num
    · exact absurd (bdef c c3 c11 c43 c13) hne
  · rw [b3]; norm_num
  · rw [bdef 31 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; norm_num
  · rw [bdef 127 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; norm_num
  · rw [b13]

theorem core7_chain1201 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h7 : 7 ∉ P)
    (E : (2 ^ m + 1) * (1 + 7 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 7 ^ e * ∏ p ∈ P, p)
    (he : 3 ≤ e) (hd : 1201 ∣ 1 + 7 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 7 ^ e → c ∈ ({7} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 7 → c ∉ ({7} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g1201 : 1201 ∈ P := S7 1201 (by norm_num) (by norm_num) (hnz (by norm_num)) hd
  have g601 : 601 ∈ P := S1 601 (by norm_num) (by norm_num) (hnz (by norm_num)) 1201 g1201 (by norm_num)
  have g43 : 43 ∈ P := S1 43 (by norm_num) (by norm_num) (hnz (by norm_num)) 601 g601 (by norm_num)
  have g11 : 11 ∈ P := S1 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 43 g43 (by norm_num)
  have g3 : 3 ∈ P := S1 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 11 g11 (by norm_num)
  have hm : 5 ≤ m := by
    by_contra hlt
    have h72 : ¬ 2 ∣ 7 ^ e := fun h => by
      have := Nat.prime_two.dvd_of_dvd_pow h
      omega
    apply not_two_pow_dvd hP h72 E
    have hsub : ({1201, 601, 43, 11, 3} : Finset ℕ) ⊆ P := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> assumption
    have h1 : ∏ x ∈ ({1201, 601, 43, 11, 3} : Finset ℕ), (x + 1) ∣ ∏ x ∈ P, (x + 1) :=
      Finset.prod_dvd_prod_of_subset _ _ _ hsub
    have hodd : (7 ^ e) % 2 = 1 := by simp [Nat.pow_mod]
    have h2K : 2 ∣ 1 + 7 ^ e := by omega
    have h2 : (2 : ℕ) ^ (m + 2) ∣ 2 * ∏ x ∈ ({1201, 601, 43, 11, 3} : Finset ℕ), (x + 1) := by
      have e1 : 2 * ∏ x ∈ ({1201, 601, 43, 11, 3} : Finset ℕ), (x + 1) = 2 ^ 9 * 5969733 := by decide
      rw [e1]
      exact Dvd.dvd.mul_right (pow_dvd_pow 2 (by omega)) _
    rw [mul_assoc]
    exact (h2.trans (mul_dvd_mul h2K h1)).mul_left _
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, β = fun q : ℕ => if q = 3 then (1792 / 1201 : ℚ) else if q = 11 then (1344 / 1201 : ℚ) else if q = 43 then (1232 / 1201 : ℚ) else if q = 601 then (1204 / 1201 : ℚ) else if q = 1201 then (1202 / 1201 : ℚ) else if q = 13 then 56 / 51 else ((q : ℚ) + 1) / ((q : ℚ) - 1) := ⟨_, rfl⟩
  have b3 : β 3 = 1792 / 1201 := by rw [hβ]; simp
  have b11 : β 11 = 1344 / 1201 := by rw [hβ]; simp
  have b43 : β 43 = 1232 / 1201 := by rw [hβ]; simp
  have b601 : β 601 = 1204 / 1201 := by rw [hβ]; simp
  have b1201 : β 1201 = 1202 / 1201 := by rw [hβ]; simp
  have b13 : β 13 = 56 / 51 := by rw [hβ]; simp
  have bdef : ∀ q : ℕ, q ≠ 3 → q ≠ 11 → q ≠ 43 → q ≠ 601 → q ≠ 1201 → q ≠ 13 → β q = ((q : ℚ) + 1) / ((q : ℚ) - 1) :=
    fun q h0 h1 h2 h3 h4 h13 => by rw [hβ]; simp [h0, h1, h2, h3, h4, h13]
  refine seven_core hP h7 E he hm β ?_ ?_ ?_ ?_ ?_ ?_
  · intro p hp
    by_cases c3 : p = 3
    · subst c3; rw [b3]; norm_num
    by_cases c11 : p = 11
    · subst c11; rw [b11]; norm_num
    by_cases c43 : p = 43
    · subst c43; rw [b43]; norm_num
    by_cases c601 : p = 601
    · subst c601; rw [b601]; norm_num
    by_cases c1201 : p = 1201
    · subst c1201; rw [b1201]; norm_num
    by_cases c13 : p = 13
    · subst c13; rw [b13]; norm_num
    rw [bdef p c3 c11 c43 c601 c1201 c13]
    exact ⟨one_add_le_B (hP p hp).1.two_le, le_rfl⟩
  · intro p hp c hc hcp hleast hne
    by_cases c3 : c = 3
    · subst c3
      have : p = 11 := S3 3 (by norm_num) (by norm_num) (hnz (by norm_num)) p hp 11 g11 hcp
        (by norm_num)
      subst this
      rw [b11, b3]; norm_num
    by_cases c11 : c = 11
    · subst c11
      have : p = 43 := S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) p hp 43 g43 hcp
        (by norm_num)
      subst this
      rw [b43, b11]; norm_num
    by_cases c43 : c = 43
    · subst c43
      have : p = 601 := S3 43 (by norm_num) (by norm_num) (hnz (by norm_num)) p hp 601 g601 hcp
        (by norm_num)
      subst this
      rw [b601, b43]; norm_num
    by_cases c601 : c = 601
    · subst c601
      have : p = 1201 := S3 601 (by norm_num) (by norm_num) (hnz (by norm_num)) p hp 1201 g1201 hcp
        (by norm_num)
      subst this
      rw [b1201, b601]; norm_num
    by_cases c1201 : c = 1201
    · subst c1201
      exact absurd hcp (S8 1201 (by norm_num) (by norm_num) (hnz (by norm_num)) hd p hp)
    by_cases c13 : c = 13
    · subst c13
      have hpp := (hP p hp).1
      have hp103 : 103 ≤ p := by
        by_contra hlt
        obtain ⟨t, ht⟩ := hcp
        have ht8 : t < 8 := by omega
        interval_cases t <;> simp at ht <;> subst ht <;> first | omega | (norm_num at hpp)
      rw [bdef p (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), b13]
      have hBp := B_anti (a := 103) (b := p) (by norm_num) hp103
      have h14 : (0 : ℚ) ≤ 1 + 1 / ((13 : ℕ) : ℚ) := by norm_num
      refine (mul_le_mul_of_nonneg_left hBp h14).trans ?_
      norm_num
    · exact absurd (bdef c c3 c11 c43 c601 c1201 c13) hne
  · rw [b3]; norm_num
  · rw [bdef 31 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; norm_num
  · rw [bdef 127 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; norm_num
  · rw [b13]

theorem core7_chain23 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h7 : 7 ∉ P)
    (E : (2 ^ m + 1) * (1 + 7 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 7 ^ e * ∏ p ∈ P, p)
    (he : 3 ≤ e) (hd : 23 ∣ 1 + 7 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 7 ^ e → c ∈ ({7} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 7 → c ∉ ({7} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g23 : 23 ∈ P := S7 23 (by norm_num) (by norm_num) (hnz (by norm_num)) hd
  have g3 : 3 ∈ P := S1 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 23 g23 (by norm_num)
  have hm : 5 ≤ m := by
    by_contra hlt
    have h72 : ¬ 2 ∣ 7 ^ e := fun h => by
      have := Nat.prime_two.dvd_of_dvd_pow h
      omega
    apply not_two_pow_dvd hP h72 E
    have hsub : ({23, 3} : Finset ℕ) ⊆ P := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    have h1 : ∏ x ∈ ({23, 3} : Finset ℕ), (x + 1) ∣ ∏ x ∈ P, (x + 1) :=
      Finset.prod_dvd_prod_of_subset _ _ _ hsub
    have hodd : (7 ^ e) % 2 = 1 := by simp [Nat.pow_mod]
    have h2K : 2 ∣ 1 + 7 ^ e := by omega
    have h2 : (2 : ℕ) ^ (m + 2) ∣ 2 * ∏ x ∈ ({23, 3} : Finset ℕ), (x + 1) := by
      have e1 : 2 * ∏ x ∈ ({23, 3} : Finset ℕ), (x + 1) = 2 ^ 6 * 3 := by decide
      rw [e1]
      exact Dvd.dvd.mul_right (pow_dvd_pow 2 (by omega)) _
    rw [mul_assoc]
    exact (h2.trans (mul_dvd_mul h2K h1)).mul_left _
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, β = fun q : ℕ => if q = 3 then (32 / 23 : ℚ) else if q = 23 then (24 / 23 : ℚ) else if q = 13 then 56 / 51 else ((q : ℚ) + 1) / ((q : ℚ) - 1) := ⟨_, rfl⟩
  have b3 : β 3 = 32 / 23 := by rw [hβ]; simp
  have b23 : β 23 = 24 / 23 := by rw [hβ]; simp
  have b13 : β 13 = 56 / 51 := by rw [hβ]; simp
  have bdef : ∀ q : ℕ, q ≠ 3 → q ≠ 23 → q ≠ 13 → β q = ((q : ℚ) + 1) / ((q : ℚ) - 1) :=
    fun q h0 h1 h13 => by rw [hβ]; simp [h0, h1, h13]
  refine seven_core hP h7 E he hm β ?_ ?_ ?_ ?_ ?_ ?_
  · intro p hp
    by_cases c3 : p = 3
    · subst c3; rw [b3]; norm_num
    by_cases c23 : p = 23
    · subst c23; rw [b23]; norm_num
    by_cases c13 : p = 13
    · subst c13; rw [b13]; norm_num
    rw [bdef p c3 c23 c13]
    exact ⟨one_add_le_B (hP p hp).1.two_le, le_rfl⟩
  · intro p hp c hc hcp hleast hne
    by_cases c3 : c = 3
    · subst c3
      have : p = 23 := S3 3 (by norm_num) (by norm_num) (hnz (by norm_num)) p hp 23 g23 hcp
        (by norm_num)
      subst this
      rw [b23, b3]; norm_num
    by_cases c23 : c = 23
    · subst c23
      exact absurd hcp (S8 23 (by norm_num) (by norm_num) (hnz (by norm_num)) hd p hp)
    by_cases c13 : c = 13
    · subst c13
      have hpp := (hP p hp).1
      have hp103 : 103 ≤ p := by
        by_contra hlt
        obtain ⟨t, ht⟩ := hcp
        have ht8 : t < 8 := by omega
        interval_cases t <;> simp at ht <;> subst ht <;> first | omega | (norm_num at hpp)
      rw [bdef p (by omega) (by omega) (by omega), b13]
      have hBp := B_anti (a := 103) (b := p) (by norm_num) hp103
      have h14 : (0 : ℚ) ≤ 1 + 1 / ((13 : ℕ) : ℚ) := by norm_num
      refine (mul_le_mul_of_nonneg_left hBp h14).trans ?_
      norm_num
    · exact absurd (bdef c c3 c23 c13) hne
  · rw [b3]; norm_num
  · rw [bdef 31 (by norm_num) (by norm_num) (by norm_num)]; norm_num
  · rw [bdef 127 (by norm_num) (by norm_num) (by norm_num)]; norm_num
  · rw [b13]

theorem zmod_ne_one {p c : ℕ} (h : c % p ≠ 1 % p) : ((c : ℕ) : ZMod p) ≠ 1 := by
  intro h'
  apply h
  have h2 : ((c : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by simpa using h'
  exact (ZMod.natCast_eq_natCast_iff' c 1 p).mp h2

theorem prime_74480363 : Nat.Prime 74480363 := by
  refine lucas_primality 74480363 (2 : ZMod 74480363) ?_ (fun q hq hd => ?_)
  · rw [show 74480363 - 1 = 74480362 from by norm_num]
    reduce_mod_char
  · have e : 74480363 - 1 = [2 ^ 1, 11 ^ 1, 89 ^ 1, 38039 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (74480363 - 1) / 2 = 37240181 from by norm_num]
      have h2 : (2 : ZMod 74480363) ^ 37240181 = ((74480362 : ℕ) : ZMod 74480363) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (74480363 - 1) / 11 = 6770942 from by norm_num]
      have h2 : (2 : ZMod 74480363) ^ 6770942 = ((71668089 : ℕ) : ZMod 74480363) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (74480363 - 1) / 89 = 836858 from by norm_num]
      have h2 : (2 : ZMod 74480363) ^ 836858 = ((48885906 : ℕ) : ZMod 74480363) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (74480363 - 1) / 38039 = 1958 from by norm_num]
      have h2 : (2 : ZMod 74480363) ^ 1958 = ((40588691 : ℕ) : ZMod 74480363) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_234750601 : Nat.Prime 234750601 := by
  refine lucas_primality 234750601 (13 : ZMod 234750601) ?_ (fun q hq hd => ?_)
  · rw [show 234750601 - 1 = 234750600 from by norm_num]
    reduce_mod_char
  · have e : 234750601 - 1 = [2 ^ 3, 3 ^ 2, 5 ^ 2, 7 ^ 1, 31 ^ 1, 601 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (234750601 - 1) / 2 = 117375300 from by norm_num]
      have h2 : (13 : ZMod 234750601) ^ 117375300 = ((234750600 : ℕ) : ZMod 234750601) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (234750601 - 1) / 3 = 78250200 from by norm_num]
      have h2 : (13 : ZMod 234750601) ^ 78250200 = ((44260285 : ℕ) : ZMod 234750601) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (234750601 - 1) / 5 = 46950120 from by norm_num]
      have h2 : (13 : ZMod 234750601) ^ 46950120 = ((60323294 : ℕ) : ZMod 234750601) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (234750601 - 1) / 7 = 33535800 from by norm_num]
      have h2 : (13 : ZMod 234750601) ^ 33535800 = ((625 : ℕ) : ZMod 234750601) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (234750601 - 1) / 31 = 7572600 from by norm_num]
      have h2 : (13 : ZMod 234750601) ^ 7572600 = ((128564925 : ℕ) : ZMod 234750601) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (234750601 - 1) / 601 = 390600 from by norm_num]
      have h2 : (13 : ZMod 234750601) ^ 390600 = ((154538915 : ℕ) : ZMod 234750601) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_266442959 : Nat.Prime 266442959 := by
  refine lucas_primality 266442959 (31 : ZMod 266442959) ?_ (fun q hq hd => ?_)
  · rw [show 266442959 - 1 = 266442958 from by norm_num]
    reduce_mod_char
  · have e : 266442959 - 1 = [2 ^ 1, 823 ^ 1, 161873 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (266442959 - 1) / 2 = 133221479 from by norm_num]
      have h2 : (31 : ZMod 266442959) ^ 133221479 = ((266442958 : ℕ) : ZMod 266442959) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (266442959 - 1) / 823 = 323746 from by norm_num]
      have h2 : (31 : ZMod 266442959) ^ 323746 = ((20559058 : ℕ) : ZMod 266442959) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (266442959 - 1) / 161873 = 1646 from by norm_num]
      have h2 : (31 : ZMod 266442959) ^ 1646 = ((250300792 : ℕ) : ZMod 266442959) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_4795973261 : Nat.Prime 4795973261 := by
  refine lucas_primality 4795973261 (2 : ZMod 4795973261) ?_ (fun q hq hd => ?_)
  · rw [show 4795973261 - 1 = 4795973260 from by norm_num]
    reduce_mod_char
  · have e : 4795973261 - 1 = [2 ^ 2, 5 ^ 1, 13 ^ 2, 89 ^ 1, 107 ^ 1, 149 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4795973261 - 1) / 2 = 2397986630 from by norm_num]
      have h2 : (2 : ZMod 4795973261) ^ 2397986630 = ((4795973260 : ℕ) : ZMod 4795973261) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4795973261 - 1) / 5 = 959194652 from by norm_num]
      have h2 : (2 : ZMod 4795973261) ^ 959194652 = ((802440760 : ℕ) : ZMod 4795973261) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4795973261 - 1) / 13 = 368921020 from by norm_num]
      have h2 : (2 : ZMod 4795973261) ^ 368921020 = ((81 : ℕ) : ZMod 4795973261) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4795973261 - 1) / 89 = 53887340 from by norm_num]
      have h2 : (2 : ZMod 4795973261) ^ 53887340 = ((3452767078 : ℕ) : ZMod 4795973261) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4795973261 - 1) / 107 = 44822180 from by norm_num]
      have h2 : (2 : ZMod 4795973261) ^ 44822180 = ((2319453319 : ℕ) : ZMod 4795973261) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4795973261 - 1) / 149 = 32187740 from by norm_num]
      have h2 : (2 : ZMod 4795973261) ^ 32187740 = ((3024013928 : ℕ) : ZMod 4795973261) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_4885168129 : Nat.Prime 4885168129 := by
  refine lucas_primality 4885168129 (23 : ZMod 4885168129) ?_ (fun q hq hd => ?_)
  · rw [show 4885168129 - 1 = 4885168128 from by norm_num]
    reduce_mod_char
  · have e : 4885168129 - 1 = [2 ^ 14, 3 ^ 1, 19 ^ 1, 5231 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4885168129 - 1) / 2 = 2442584064 from by norm_num]
      have h2 : (23 : ZMod 4885168129) ^ 2442584064 = ((4885168128 : ℕ) : ZMod 4885168129) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4885168129 - 1) / 3 = 1628389376 from by norm_num]
      have h2 : (23 : ZMod 4885168129) ^ 1628389376 = ((4608475808 : ℕ) : ZMod 4885168129) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4885168129 - 1) / 19 = 257114112 from by norm_num]
      have h2 : (23 : ZMod 4885168129) ^ 257114112 = ((244140625 : ℕ) : ZMod 4885168129) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4885168129 - 1) / 5231 = 933888 from by norm_num]
      have h2 : (23 : ZMod 4885168129) ^ 933888 = ((896496351 : ℕ) : ZMod 4885168129) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_13564461457 : Nat.Prime 13564461457 := by
  refine lucas_primality 13564461457 (10 : ZMod 13564461457) ?_ (fun q hq hd => ?_)
  · rw [show 13564461457 - 1 = 13564461456 from by norm_num]
    reduce_mod_char
  · have e : 13564461457 - 1 = [2 ^ 4, 3 ^ 2, 7 ^ 2, 13 ^ 1, 19 ^ 1, 43 ^ 1, 181 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (13564461457 - 1) / 2 = 6782230728 from by norm_num]
      have h2 : (10 : ZMod 13564461457) ^ 6782230728 = ((13564461456 : ℕ) : ZMod 13564461457) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (13564461457 - 1) / 3 = 4521487152 from by norm_num]
      have h2 : (10 : ZMod 13564461457) ^ 4521487152 = ((659414752 : ℕ) : ZMod 13564461457) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (13564461457 - 1) / 7 = 1937780208 from by norm_num]
      have h2 : (10 : ZMod 13564461457) ^ 1937780208 = ((13564343808 : ℕ) : ZMod 13564461457) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (13564461457 - 1) / 13 = 1043420112 from by norm_num]
      have h2 : (10 : ZMod 13564461457) ^ 1043420112 = ((12811611698 : ℕ) : ZMod 13564461457) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (13564461457 - 1) / 19 = 713919024 from by norm_num]
      have h2 : (10 : ZMod 13564461457) ^ 713919024 = ((7354283309 : ℕ) : ZMod 13564461457) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (13564461457 - 1) / 43 = 315452592 from by norm_num]
      have h2 : (10 : ZMod 13564461457) ^ 315452592 = ((2048536126 : ℕ) : ZMod 13564461457) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (13564461457 - 1) / 181 = 74941776 from by norm_num]
      have h2 : (10 : ZMod 13564461457) ^ 74941776 = ((1132807281 : ℕ) : ZMod 13564461457) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_23535794707 : Nat.Prime 23535794707 := by
  refine lucas_primality 23535794707 (5 : ZMod 23535794707) ?_ (fun q hq hd => ?_)
  · rw [show 23535794707 - 1 = 23535794706 from by norm_num]
    reduce_mod_char
  · have e : 23535794707 - 1 = [2 ^ 1, 3 ^ 1, 23 ^ 1, 67 ^ 1, 661 ^ 1, 3851 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (23535794707 - 1) / 2 = 11767897353 from by norm_num]
      have h2 : (5 : ZMod 23535794707) ^ 11767897353 = ((23535794706 : ℕ) : ZMod 23535794707) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (23535794707 - 1) / 3 = 7845264902 from by norm_num]
      have h2 : (5 : ZMod 23535794707) ^ 7845264902 = ((23535528986 : ℕ) : ZMod 23535794707) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (23535794707 - 1) / 23 = 1023295422 from by norm_num]
      have h2 : (5 : ZMod 23535794707) ^ 1023295422 = ((7845264902 : ℕ) : ZMod 23535794707) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (23535794707 - 1) / 67 = 351280518 from by norm_num]
      have h2 : (5 : ZMod 23535794707) ^ 351280518 = ((3973098276 : ℕ) : ZMod 23535794707) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (23535794707 - 1) / 661 = 35606346 from by norm_num]
      have h2 : (5 : ZMod 23535794707) ^ 35606346 = ((6715382745 : ℕ) : ZMod 23535794707) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (23535794707 - 1) / 3851 = 6111606 from by norm_num]
      have h2 : (5 : ZMod 23535794707) ^ 6111606 = ((22322382873 : ℕ) : ZMod 23535794707) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_374857981681 : Nat.Prime 374857981681 := by
  refine lucas_primality 374857981681 (11 : ZMod 374857981681) ?_ (fun q hq hd => ?_)
  · rw [show 374857981681 - 1 = 374857981680 from by norm_num]
    reduce_mod_char
  · have e : 374857981681 - 1 = [2 ^ 4, 3 ^ 1, 5 ^ 1, 7 ^ 1, 13 ^ 1, 17163827 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (374857981681 - 1) / 2 = 187428990840 from by norm_num]
      have h2 : (11 : ZMod 374857981681) ^ 187428990840 = ((374857981680 : ℕ) : ZMod 374857981681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (374857981681 - 1) / 3 = 124952660560 from by norm_num]
      have h2 : (11 : ZMod 374857981681) ^ 124952660560 = ((374664271436 : ℕ) : ZMod 374857981681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (374857981681 - 1) / 5 = 74971596336 from by norm_num]
      have h2 : (11 : ZMod 374857981681) ^ 74971596336 = ((364397628478 : ℕ) : ZMod 374857981681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (374857981681 - 1) / 7 = 53551140240 from by norm_num]
      have h2 : (11 : ZMod 374857981681) ^ 53551140240 = ((374843632774 : ℕ) : ZMod 374857981681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (374857981681 - 1) / 13 = 28835229360 from by norm_num]
      have h2 : (11 : ZMod 374857981681) ^ 28835229360 = ((93704246341 : ℕ) : ZMod 374857981681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (374857981681 - 1) / 17163827 = 21840 from by norm_num]
      have h2 : (11 : ZMod 374857981681) ^ 21840 = ((295873541282 : ℕ) : ZMod 374857981681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_29078814248401 : Nat.Prime 29078814248401 := by
  refine lucas_primality 29078814248401 (26 : ZMod 29078814248401) ?_ (fun q hq hd => ?_)
  · rw [show 29078814248401 - 1 = 29078814248400 from by norm_num]
    reduce_mod_char
  · have e : 29078814248401 - 1 = [2 ^ 4, 3 ^ 1, 5 ^ 2, 7 ^ 1, 17 ^ 1, 1201 ^ 1, 169553 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (29078814248401 - 1) / 2 = 14539407124200 from by norm_num]
      have h2 : (26 : ZMod 29078814248401) ^ 14539407124200 = ((29078814248400 : ℕ) : ZMod 29078814248401) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (29078814248401 - 1) / 3 = 9692938082800 from by norm_num]
      have h2 : (26 : ZMod 29078814248401) ^ 9692938082800 = ((21900516952647 : ℕ) : ZMod 29078814248401) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (29078814248401 - 1) / 5 = 5815762849680 from by norm_num]
      have h2 : (26 : ZMod 29078814248401) ^ 5815762849680 = ((14421480793297 : ℕ) : ZMod 29078814248401) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (29078814248401 - 1) / 7 = 4154116321200 from by norm_num]
      have h2 : (26 : ZMod 29078814248401) ^ 4154116321200 = ((1570219624840 : ℕ) : ZMod 29078814248401) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (29078814248401 - 1) / 17 = 1710518485200 from by norm_num]
      have h2 : (26 : ZMod 29078814248401) ^ 1710518485200 = ((29078814248058 : ℕ) : ZMod 29078814248401) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (29078814248401 - 1) / 1201 = 24212168400 from by norm_num]
      have h2 : (26 : ZMod 29078814248401) ^ 24212168400 = ((14806057737438 : ℕ) : ZMod 29078814248401) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (29078814248401 - 1) / 169553 = 171502800 from by norm_num]
      have h2 : (26 : ZMod 29078814248401) ^ 171502800 = ((8686313601838 : ℕ) : ZMod 29078814248401) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_926510094425921 : Nat.Prime 926510094425921 := by
  refine lucas_primality 926510094425921 (7 : ZMod 926510094425921) ?_ (fun q hq hd => ?_)
  · rw [show 926510094425921 - 1 = 926510094425920 from by norm_num]
    reduce_mod_char
  · have e : 926510094425921 - 1 = [2 ^ 6, 5 ^ 1, 17 ^ 1, 41 ^ 1, 193 ^ 1, 21523361 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (926510094425921 - 1) / 2 = 463255047212960 from by norm_num]
      have h2 : (7 : ZMod 926510094425921) ^ 463255047212960 = ((926510094425920 : ℕ) : ZMod 926510094425921) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (926510094425921 - 1) / 5 = 185302018885184 from by norm_num]
      have h2 : (7 : ZMod 926510094425921) ^ 185302018885184 = ((834337249747077 : ℕ) : ZMod 926510094425921) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (926510094425921 - 1) / 17 = 54500593789760 from by norm_num]
      have h2 : (7 : ZMod 926510094425921) ^ 54500593789760 = ((519647910361382 : ℕ) : ZMod 926510094425921) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (926510094425921 - 1) / 41 = 22597807181120 from by norm_num]
      have h2 : (7 : ZMod 926510094425921) ^ 22597807181120 = ((177954043159788 : ℕ) : ZMod 926510094425921) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (926510094425921 - 1) / 193 = 4800570437440 from by norm_num]
      have h2 : (7 : ZMod 926510094425921) ^ 4800570437440 = ((131834361560385 : ℕ) : ZMod 926510094425921) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (926510094425921 - 1) / 21523361 = 43046720 from by norm_num]
      have h2 : (7 : ZMod 926510094425921) ^ 43046720 = ((197650685928869 : ℕ) : ZMod 926510094425921) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_29754714843945001 : Nat.Prime 29754714843945001 := by
  refine lucas_primality 29754714843945001 (29 : ZMod 29754714843945001) ?_ (fun q hq hd => ?_)
  · rw [show 29754714843945001 - 1 = 29754714843945000 from by norm_num]
    reduce_mod_char
  · have e : 29754714843945001 - 1 = [2 ^ 3, 3 ^ 2, 5 ^ 4, 7 ^ 1, 13 ^ 1, 31 ^ 1, 601 ^ 1, 390001 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (29754714843945001 - 1) / 2 = 14877357421972500 from by norm_num]
      have h2 : (29 : ZMod 29754714843945001) ^ 14877357421972500 = ((29754714843945000 : ℕ) : ZMod 29754714843945001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (29754714843945001 - 1) / 3 = 9918238281315000 from by norm_num]
      have h2 : (29 : ZMod 29754714843945001) ^ 9918238281315000 = ((29541376366429302 : ℕ) : ZMod 29754714843945001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (29754714843945001 - 1) / 5 = 5950942968789000 from by norm_num]
      have h2 : (29 : ZMod 29754714843945001) ^ 5950942968789000 = ((10754338246032706 : ℕ) : ZMod 29754714843945001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (29754714843945001 - 1) / 7 = 4250673549135000 from by norm_num]
      have h2 : (29 : ZMod 29754714843945001) ^ 4250673549135000 = ((1514905240024431 : ℕ) : ZMod 29754714843945001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (29754714843945001 - 1) / 13 = 2288824218765000 from by norm_num]
      have h2 : (29 : ZMod 29754714843945001) ^ 2288824218765000 = ((4451869297174457 : ℕ) : ZMod 29754714843945001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (29754714843945001 - 1) / 31 = 959829511095000 from by norm_num]
      have h2 : (29 : ZMod 29754714843945001) ^ 959829511095000 = ((18923201788542184 : ℕ) : ZMod 29754714843945001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (29754714843945001 - 1) / 601 = 49508676945000 from by norm_num]
      have h2 : (29 : ZMod 29754714843945001) ^ 49508676945000 = ((10658591994907887 : ℕ) : ZMod 29754714843945001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (29754714843945001 - 1) / 390001 = 76293945000 from by norm_num]
      have h2 : (29 : ZMod 29754714843945001) ^ 76293945000 = ((25250557672973904 : ℕ) : ZMod 29754714843945001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_59509429687890001 : Nat.Prime 59509429687890001 := by
  refine lucas_primality 59509429687890001 (22 : ZMod 59509429687890001) ?_ (fun q hq hd => ?_)
  · rw [show 59509429687890001 - 1 = 59509429687890000 from by norm_num]
    reduce_mod_char
  · have e : 59509429687890001 - 1 = [2 ^ 4, 3 ^ 2, 5 ^ 4, 7 ^ 1, 13 ^ 1, 31 ^ 1, 601 ^ 1, 390001 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (59509429687890001 - 1) / 2 = 29754714843945000 from by norm_num]
      have h2 : (22 : ZMod 59509429687890001) ^ 29754714843945000 = ((59509429687890000 : ℕ) : ZMod 59509429687890001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (59509429687890001 - 1) / 3 = 19836476562630000 from by norm_num]
      have h2 : (22 : ZMod 59509429687890001) ^ 19836476562630000 = ((47343618569315113 : ℕ) : ZMod 59509429687890001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (59509429687890001 - 1) / 5 = 11901885937578000 from by norm_num]
      have h2 : (22 : ZMod 59509429687890001) ^ 11901885937578000 = ((18015995908260728 : ℕ) : ZMod 59509429687890001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (59509429687890001 - 1) / 7 = 8501347098270000 from by norm_num]
      have h2 : (22 : ZMod 59509429687890001) ^ 8501347098270000 = ((59509429443749376 : ℕ) : ZMod 59509429687890001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (59509429687890001 - 1) / 13 = 4577648437530000 from by norm_num]
      have h2 : (22 : ZMod 59509429687890001) ^ 4577648437530000 = ((15880862869163333 : ℕ) : ZMod 59509429687890001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (59509429687890001 - 1) / 31 = 1919659022190000 from by norm_num]
      have h2 : (22 : ZMod 59509429687890001) ^ 1919659022190000 = ((53328826706576417 : ℕ) : ZMod 59509429687890001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (59509429687890001 - 1) / 601 = 99017353890000 from by norm_num]
      have h2 : (22 : ZMod 59509429687890001) ^ 99017353890000 = ((45442218348425151 : ℕ) : ZMod 59509429687890001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (59509429687890001 - 1) / 390001 = 152587890000 from by norm_num]
      have h2 : (22 : ZMod 59509429687890001) ^ 152587890000 = ((11785300371927430 : ℕ) : ZMod 59509429687890001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_3421093417510114543 : Nat.Prime 3421093417510114543 := by
  refine lucas_primality 3421093417510114543 (3 : ZMod 3421093417510114543) ?_ (fun q hq hd => ?_)
  · rw [show 3421093417510114543 - 1 = 3421093417510114542 from by norm_num]
    reduce_mod_char
  · have e : 3421093417510114543 - 1 = [2 ^ 1, 3 ^ 1, 7 ^ 1, 23 ^ 1, 1123 ^ 1, 293459 ^ 1, 10746341 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3421093417510114543 - 1) / 2 = 1710546708755057271 from by norm_num]
      have h2 : (3 : ZMod 3421093417510114543) ^ 1710546708755057271 = ((3421093417510114542 : ℕ) : ZMod 3421093417510114543) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3421093417510114543 - 1) / 3 = 1140364472503371514 from by norm_num]
      have h2 : (3 : ZMod 3421093417510114543) ^ 1140364472503371514 = ((1809471187469464874 : ℕ) : ZMod 3421093417510114543) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3421093417510114543 - 1) / 7 = 488727631072873506 from by norm_num]
      have h2 : (3 : ZMod 3421093417510114543) ^ 488727631072873506 = ((1557885139193585188 : ℕ) : ZMod 3421093417510114543) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3421093417510114543 - 1) / 23 = 148743192065657154 from by norm_num]
      have h2 : (3 : ZMod 3421093417510114543) ^ 148743192065657154 = ((3421088669948604600 : ℕ) : ZMod 3421093417510114543) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3421093417510114543 - 1) / 1123 = 3046387727079354 from by norm_num]
      have h2 : (3 : ZMod 3421093417510114543) ^ 3046387727079354 = ((3190964525324633857 : ℕ) : ZMod 3421093417510114543) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3421093417510114543 - 1) / 293459 = 11657824150938 from by norm_num]
      have h2 : (3 : ZMod 3421093417510114543) ^ 11657824150938 = ((1572588222917641538 : ℕ) : ZMod 3421093417510114543) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3421093417510114543 - 1) / 10746341 = 318349605462 from by norm_num]
      have h2 : (3 : ZMod 3421093417510114543) ^ 318349605462 = ((1947475107312795512 : ℕ) : ZMod 3421093417510114543) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_402488219476647465854701 : Nat.Prime 402488219476647465854701 := by
  refine lucas_primality 402488219476647465854701 (6 : ZMod 402488219476647465854701) ?_ (fun q hq hd => ?_)
  · rw [show 402488219476647465854701 - 1 = 402488219476647465854700 from by norm_num]
    reduce_mod_char
  · have e : 402488219476647465854701 - 1 = [2 ^ 2, 3 ^ 1, 5 ^ 2, 7 ^ 1, 29 ^ 1, 113 ^ 1, 911 ^ 1, 4733 ^ 1, 13564461457 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (402488219476647465854701 - 1) / 2 = 201244109738323732927350 from by norm_num]
      have h2 : (6 : ZMod 402488219476647465854701) ^ 201244109738323732927350 = ((402488219476647465854700 : ℕ) : ZMod 402488219476647465854701) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (402488219476647465854701 - 1) / 3 = 134162739825549155284900 from by norm_num]
      have h2 : (6 : ZMod 402488219476647465854701) ^ 134162739825549155284900 = ((57349408746627543130911 : ℕ) : ZMod 402488219476647465854701) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (402488219476647465854701 - 1) / 5 = 80497643895329493170940 from by norm_num]
      have h2 : (6 : ZMod 402488219476647465854701) ^ 80497643895329493170940 = ((277645886499624542164102 : ℕ) : ZMod 402488219476647465854701) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (402488219476647465854701 - 1) / 7 = 57498317068092495122100 from by norm_num]
      have h2 : (6 : ZMod 402488219476647465854701) ^ 57498317068092495122100 = ((25970033723941526042520 : ℕ) : ZMod 402488219476647465854701) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (402488219476647465854701 - 1) / 29 = 13878904119884395374300 from by norm_num]
      have h2 : (6 : ZMod 402488219476647465854701) ^ 13878904119884395374300 = ((117649 : ℕ) : ZMod 402488219476647465854701) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (402488219476647465854701 - 1) / 113 = 3561842650235818281900 from by norm_num]
      have h2 : (6 : ZMod 402488219476647465854701) ^ 3561842650235818281900 = ((214417464591983328782157 : ℕ) : ZMod 402488219476647465854701) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (402488219476647465854701 - 1) / 911 = 441809242016078447700 from by norm_num]
      have h2 : (6 : ZMod 402488219476647465854701) ^ 441809242016078447700 = ((29823435858844902666352 : ℕ) : ZMod 402488219476647465854701) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (402488219476647465854701 - 1) / 4733 = 85038711066268215900 from by norm_num]
      have h2 : (6 : ZMod 402488219476647465854701) ^ 85038711066268215900 = ((259740329791202976958983 : ℕ) : ZMod 402488219476647465854701) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_13564461457).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (402488219476647465854701 - 1) / 13564461457 = 29672259437100 from by norm_num]
      have h2 : (6 : ZMod 402488219476647465854701) ^ 29672259437100 = ((41469317517565739231688 : ℕ) : ZMod 402488219476647465854701) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem kill3_e6 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 6 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g73 : 73 ∈ P := S7 73 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 73 ∣ 1 + 3 ^ 6).trans hd)
  have g37 : 37 ∈ P := S1 37 (by norm_num) (by norm_num) (hnz (by norm_num)) 73 g73 (by norm_num)
  have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 37 g37 (by norm_num)
  exact S8 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 5 ∣ 1 + 3 ^ 6).trans hd) 19 g19 (by norm_num)

theorem kill3_e8 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 8 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g193 : 193 ∈ P := S7 193 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 193 ∣ 1 + 3 ^ 8).trans hd)
  have g97 : 97 ∈ P := S1 97 (by norm_num) (by norm_num) (hnz (by norm_num)) 193 g193 (by norm_num)
  exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 97 g97 (by norm_num)

theorem kill3_e9 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 9 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g37 : 37 ∈ P := S7 37 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 37 ∣ 1 + 3 ^ 9).trans hd)
  exact S8 19 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 19 ∣ 1 + 3 ^ 9).trans hd) 37 g37 (by norm_num)

theorem kill3_e10 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 10 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  exact S_sq hP hK E (c := 5) (by norm_num) (by norm_num) (hnz (by norm_num))
    ((((by norm_num : 5 * 5 ∣ 1 + 3 ^ 10).trans hd).mul_left _).mul_right _)

theorem kill3_e12 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 12 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g41 : 41 ∈ P := S7 41 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 41 ∣ 1 + 3 ^ 12).trans hd)
  have g6481 : 6481 ∈ P := S7 6481 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 6481 ∣ 1 + 3 ^ 12).trans hd)
  have := S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 41 g41 6481 g6481 (by norm_num) (by norm_num)
  omega

theorem kill3_e14 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 14 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g29 : 29 ∈ P := S7 29 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 29 ∣ 1 + 3 ^ 14).trans hd)
  exact S8 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 5 ∣ 1 + 3 ^ 14).trans hd) 29 g29 (by norm_num)

theorem kill3_e15 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 15 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g61 : 61 ∈ P := S7 61 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 61 ∣ 1 + 3 ^ 15).trans hd)
  exact S8 31 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 31 ∣ 1 + 3 ^ 15).trans hd) 61 g61 (by norm_num)

theorem kill3_e16 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 16 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g21523361 : 21523361 ∈ P := S7 21523361 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 21523361 ∣ 1 + 3 ^ 16).trans hd)
  have g61 : 61 ∈ P := S1 61 (by norm_num) (by norm_num) (hnz (by norm_num)) 21523361 g21523361 (by norm_num)
  have := S3 31 (by norm_num) (by norm_num) (hnz (by norm_num)) 21523361 g21523361 61 g61 (by norm_num) (by norm_num)
  omega

theorem kill3_e17 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 17 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g103 : 103 ∈ P := S7 103 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 103 ∣ 1 + 3 ^ 17).trans hd)
  have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 103 g103 (by norm_num)
  have g307 : 307 ∈ P := S7 307 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 307 ∣ 1 + 3 ^ 17).trans hd)
  have := S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 13 g13 307 g307 (by norm_num) (by norm_num)
  omega

theorem kill3_e20 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 20 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g41 : 41 ∈ P := S7 41 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 41 ∣ 1 + 3 ^ 20).trans hd)
  have g42521761 : 42521761 ∈ P := S7 42521761 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 42521761 ∣ 1 + 3 ^ 20).trans hd)
  have g21260881 : 21260881 ∈ P := S1 21260881 (by norm_num) (by norm_num) (hnz (by norm_num)) 42521761 g42521761 (by norm_num)
  have g10630441 : 10630441 ∈ P := S1 10630441 (by norm_num) (by norm_num) (hnz (by norm_num)) 21260881 g21260881 (by norm_num)
  have g139 : 139 ∈ P := S1 139 (by norm_num) (by norm_num) (hnz (by norm_num)) 10630441 g10630441 (by norm_num)
  have := S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 41 g41 139 g139 (by norm_num) (by norm_num)
  omega

theorem kill3_e21 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 21 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  exact S_sq hP hK E (c := 7) (by norm_num) (by norm_num) (hnz (by norm_num))
    ((((by norm_num : 7 * 7 ∣ 1 + 3 ^ 21).trans hd).mul_left _).mul_right _)

theorem kill3_e22 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 22 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g5501 : 5501 ∈ P := S7 5501 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 5501 ∣ 1 + 3 ^ 22).trans hd)
  have g570461 : 570461 ∈ P := S7 570461 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 570461 ∣ 1 + 3 ^ 22).trans hd)
  have g3067 : 3067 ∈ P := S1 3067 (by norm_num) (by norm_num) (hnz (by norm_num)) 570461 g570461 (by norm_num)
  have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 3067 g3067 (by norm_num)
  have := S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 5501 g5501 13 g13 (by norm_num) (by norm_num)
  omega

theorem kill3_e25 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 25 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g151 : 151 ∈ P := S7 151 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 151 ∣ 1 + 3 ^ 25).trans hd)
  have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 151 g151 (by norm_num)
  have g22996651 : 22996651 ∈ P := S7 22996651 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 22996651 ∣ 1 + 3 ^ 25).trans hd)
  have g29 : 29 ∈ P := S1 29 (by norm_num) (by norm_num) (hnz (by norm_num)) 22996651 g22996651 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 19 g19 29 g29 (by norm_num) (by norm_num)
  omega

theorem kill3_e28 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 28 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g41 : 41 ∈ P := S7 41 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 41 ∣ 1 + 3 ^ 28).trans hd)
  have g430697 : 430697 ∈ P := S7 430697 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 430697 ∣ 1 + 3 ^ 28).trans hd)
  have g3121 : 3121 ∈ P := S1 3121 (by norm_num) (by norm_num) (hnz (by norm_num)) 430697 g430697 (by norm_num)
  have := S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 41 g41 3121 g3121 (by norm_num) (by norm_num)
  omega

theorem kill3_e29 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 29 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g5385997 : 5385997 ∈ P := S7 5385997 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 5385997 ∣ 1 + 3 ^ 29).trans hd)
  have g2692999 : 2692999 ∈ P := S1 2692999 (by norm_num) (by norm_num) (hnz (by norm_num)) 5385997 g5385997 (by norm_num)
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 2692999 g2692999 (by norm_num)

theorem kill3_e31 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 31 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g6883 : 6883 ∈ P := S7 6883 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 6883 ∣ 1 + 3 ^ 31).trans hd)
  have g1721 : 1721 ∈ P := S1 1721 (by norm_num) (by norm_num) (hnz (by norm_num)) 6883 g6883 (by norm_num)
  have g41 : 41 ∈ P := S1 41 (by norm_num) (by norm_num) (hnz (by norm_num)) 1721 g1721 (by norm_num)
  have := S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 1721 g1721 41 g41 (by norm_num) (by norm_num)
  omega

theorem kill3_e33 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 33 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g661 : 661 ∈ P := S7 661 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 661 ∣ 1 + 3 ^ 33).trans hd)
  have g331 : 331 ∈ P := S1 331 (by norm_num) (by norm_num) (hnz (by norm_num)) 661 g661 (by norm_num)
  have g83 : 83 ∈ P := S1 83 (by norm_num) (by norm_num) (hnz (by norm_num)) 331 g331 (by norm_num)
  exact S8 7 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 7 ∣ 1 + 3 ^ 33).trans hd) 83 g83 (by norm_num)

theorem kill3_e34 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 34 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g956353 : 956353 ∈ P := S7 956353 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 956353 ∣ 1 + 3 ^ 34).trans hd)
  have g68311 : 68311 ∈ P := S1 68311 (by norm_num) (by norm_num) (hnz (by norm_num)) 956353 g956353 (by norm_num)
  have g8539 : 8539 ∈ P := S1 8539 (by norm_num) (by norm_num) (hnz (by norm_num)) 68311 g68311 (by norm_num)
  exact S8 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 5 ∣ 1 + 3 ^ 34).trans hd) 8539 g8539 (by norm_num)

theorem kill3_e37 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 37 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g18427 : 18427 ∈ P := S7 18427 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 18427 ∣ 1 + 3 ^ 37).trans hd)
  have g271 : 271 ∈ P := S1 271 (by norm_num) (by norm_num) (hnz (by norm_num)) 18427 g18427 (by norm_num)
  have := S3 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 18427 g18427 271 g271 (by norm_num) (by norm_num)
  omega

theorem kill3_e38 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 38 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g5301533 : 5301533 ∈ P := S7 5301533 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 5301533 ∣ 1 + 3 ^ 38).trans hd)
  have g126227 : 126227 ∈ P := S1 126227 (by norm_num) (by norm_num) (hnz (by norm_num)) 5301533 g5301533 (by norm_num)
  have g157 : 157 ∈ P := S1 157 (by norm_num) (by norm_num) (hnz (by norm_num)) 126227 g126227 (by norm_num)
  have g79 : 79 ∈ P := S1 79 (by norm_num) (by norm_num) (hnz (by norm_num)) 157 g157 (by norm_num)
  exact S8 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 5 ∣ 1 + 3 ^ 38).trans hd) 79 g79 (by norm_num)

theorem kill3_e39 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 39 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g157 : 157 ∈ P := S7 157 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 157 ∣ 1 + 3 ^ 39).trans hd)
  exact S8 79 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 79 ∣ 1 + 3 ^ 39).trans hd) 157 g157 (by norm_num)

theorem kill5_e5 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 5 ^ 5 ∣ 1 + 5 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 5 ^ e → c ∈ ({5} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g521 : 521 ∈ P := S7 521 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 521 ∣ 1 + 5 ^ 5).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 521 g521 (by norm_num)

theorem kill5_e6 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 5 ^ 6 ∣ 1 + 5 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 5 ^ e → c ∈ ({5} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g13 : 13 ∈ P := S7 13 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 13 ∣ 1 + 5 ^ 6).trans hd)
  have g601 : 601 ∈ P := S7 601 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 601 ∣ 1 + 5 ^ 6).trans hd)
  have := S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 13 g13 601 g601 (by norm_num) (by norm_num)
  omega

theorem kill5_e7 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 5 ^ 7 ∣ 1 + 5 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 5 ^ e → c ∈ ({5} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g29 : 29 ∈ P := S7 29 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 29 ∣ 1 + 5 ^ 7).trans hd)
  exact S8 3 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 3 ∣ 1 + 5 ^ 7).trans hd) 29 g29 (by norm_num)

theorem kill5_e8 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 5 ^ 8 ∣ 1 + 5 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 5 ^ e → c ∈ ({5} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g17 : 17 ∈ P := S7 17 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 17 ∣ 1 + 5 ^ 8).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 17 g17 (by norm_num)

theorem kill5_e10 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 5 ^ 10 ∣ 1 + 5 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 5 ^ e → c ∈ ({5} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g13 : 13 ∈ P := S7 13 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 13 ∣ 1 + 5 ^ 10).trans hd)
  have g41 : 41 ∈ P := S7 41 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 41 ∣ 1 + 5 ^ 10).trans hd)
  have := S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 13 g13 41 g41 (by norm_num) (by norm_num)
  omega

theorem kill5_e12 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 5 ^ 12 ∣ 1 + 5 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 5 ^ e → c ∈ ({5} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g390001 : 390001 ∈ P := S7 390001 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 390001 ∣ 1 + 5 ^ 12).trans hd)
  have g1789 : 1789 ∈ P := S1 1789 (by norm_num) (by norm_num) (hnz (by norm_num)) 390001 g390001 (by norm_num)
  have g179 : 179 ∈ P := S1 179 (by norm_num) (by norm_num) (hnz (by norm_num)) 1789 g1789 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 179 g179 (by norm_num)

theorem kill5_e13 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 5 ^ 13 ∣ 1 + 5 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 5 ^ e → c ∈ ({5} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g5227 : 5227 ∈ P := S7 5227 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 5227 ∣ 1 + 5 ^ 13).trans hd)
  have g1307 : 1307 ∈ P := S1 1307 (by norm_num) (by norm_num) (hnz (by norm_num)) 5227 g5227 (by norm_num)
  exact S8 3 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 3 ∣ 1 + 5 ^ 13).trans hd) 1307 g1307 (by norm_num)

theorem kill5_e14 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 5 ^ 14 ∣ 1 + 5 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 5 ^ e → c ∈ ({5} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g234750601 : 234750601 ∈ P := S7 234750601 prime_234750601 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 234750601 ∣ 1 + 5 ^ 14).trans hd)
  have g5953 : 5953 ∈ P := S1 5953 (by norm_num) (by norm_num) (hnz (by norm_num)) 234750601 g234750601 (by norm_num)
  exact S8 13 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 13 ∣ 1 + 5 ^ 14).trans hd) 5953 g5953 (by norm_num)

theorem kill5_e16 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 5 ^ 16 ∣ 1 + 5 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 5 ^ e → c ∈ ({5} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g2593 : 2593 ∈ P := S7 2593 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 2593 ∣ 1 + 5 ^ 16).trans hd)
  have g1297 : 1297 ∈ P := S1 1297 (by norm_num) (by norm_num) (hnz (by norm_num)) 2593 g2593 (by norm_num)
  have g11 : 11 ∈ P := S1 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 1297 g1297 (by norm_num)
  have g59 : 59 ∈ P := S1 59 (by norm_num) (by norm_num) (hnz (by norm_num)) 1297 g1297 (by norm_num)
  have := S3 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 11 g11 59 g59 (by norm_num) (by norm_num)
  omega

theorem kill5_e19 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 5 ^ 19 ∣ 1 + 5 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 5 ^ e → c ∈ ({5} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g761 : 761 ∈ P := S7 761 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 761 ∣ 1 + 5 ^ 19).trans hd)
  exact S8 3 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 3 ∣ 1 + 5 ^ 19).trans hd) 761 g761 (by norm_num)

theorem kill5_e20 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 5 ^ 20 ∣ 1 + 5 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 5 ^ e → c ∈ ({5} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g241 : 241 ∈ P := S7 241 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 241 ∣ 1 + 5 ^ 20).trans hd)
  exact S6 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 241 g241 (by norm_num)

theorem kill5_e22 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 5 ^ 22 ∣ 1 + 5 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 5 ^ e → c ∈ ({5} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g89 : 89 ∈ P := S7 89 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 89 ∣ 1 + 5 ^ 22).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 89 g89 (by norm_num)

theorem kill5_e26 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 5 ^ 26 ∣ 1 + 5 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 5 ^ e → c ∈ ({5} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  exact S_sq hP hK E (c := 13) (by norm_num) (by norm_num) (hnz (by norm_num))
    ((((by norm_num : 13 * 13 ∣ 1 + 5 ^ 26).trans hd).mul_left _).mul_right _)

theorem kill5_e29 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 5 ^ 29 ∣ 1 + 5 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 5 ^ e → c ∈ ({5} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g5096867 : 5096867 ∈ P := S7 5096867 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 5096867 ∣ 1 + 5 ^ 29).trans hd)
  exact S8 3 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 3 ∣ 1 + 5 ^ 29).trans hd) 5096867 g5096867 (by norm_num)

theorem kill5_e31 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 5 ^ 31 ∣ 1 + 5 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 5 ^ e → c ∈ ({5} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g1303 : 1303 ∈ P := S7 1303 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 1303 ∣ 1 + 5 ^ 31).trans hd)
  have g163 : 163 ∈ P := S1 163 (by norm_num) (by norm_num) (hnz (by norm_num)) 1303 g1303 (by norm_num)
  have g41 : 41 ∈ P := S1 41 (by norm_num) (by norm_num) (hnz (by norm_num)) 163 g163 (by norm_num)
  exact S8 3 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 3 ∣ 1 + 5 ^ 31).trans hd) 41 g41 (by norm_num)

theorem kill5_e32 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 5 ^ 32 ∣ 1 + 5 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 5 ^ e → c ∈ ({5} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g641 : 641 ∈ P := S7 641 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 641 ∣ 1 + 5 ^ 32).trans hd)
  have g107 : 107 ∈ P := S1 107 (by norm_num) (by norm_num) (hnz (by norm_num)) 641 g641 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 107 g107 (by norm_num)

theorem kill5_e34 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 5 ^ 34 ∣ 1 + 5 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 5 ^ e → c ∈ ({5} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g13 : 13 ∈ P := S7 13 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 13 ∣ 1 + 5 ^ 34).trans hd)
  have g1973 : 1973 ∈ P := S7 1973 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 1973 ∣ 1 + 5 ^ 34).trans hd)
  have := S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 13 g13 1973 g1973 (by norm_num) (by norm_num)
  omega

theorem kill5_e37 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 5 ^ 37 ∣ 1 + 5 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 5 ^ e → c ∈ ({5} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g9103 : 9103 ∈ P := S7 9103 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 9103 ∣ 1 + 5 ^ 37).trans hd)
  have g569 : 569 ∈ P := S1 569 (by norm_num) (by norm_num) (hnz (by norm_num)) 9103 g9103 (by norm_num)
  exact S8 3 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 3 ∣ 1 + 5 ^ 37).trans hd) 569 g569 (by norm_num)

theorem kill7_e2 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 7 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 7 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 7 ^ 2 ∣ 1 + 7 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 7 ^ e → c ∈ ({7} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 7 → c ∉ ({7} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  exact S_sq hP hK E (c := 5) (by norm_num) (by norm_num) (hnz (by norm_num))
    ((((by norm_num : 5 * 5 ∣ 1 + 7 ^ 2).trans hd).mul_left _).mul_right _)

theorem kill7_e5 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 7 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 7 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 7 ^ 5 ∣ 1 + 7 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 7 ^ e → c ∈ ({7} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 7 → c ∉ ({7} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g11 : 11 ∈ P := S7 11 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 11 ∣ 1 + 7 ^ 5).trans hd)
  have g191 : 191 ∈ P := S7 191 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 191 ∣ 1 + 7 ^ 5).trans hd)
  have := S3 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 11 g11 191 g191 (by norm_num) (by norm_num)
  omega

theorem kill7_e7 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 7 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 7 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 7 ^ 7 ∣ 1 + 7 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 7 ^ e → c ∈ ({7} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 7 → c ∉ ({7} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g113 : 113 ∈ P := S7 113 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 113 ∣ 1 + 7 ^ 7).trans hd)
  have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 113 g113 (by norm_num)
  have g5 : 5 ∈ P := S1 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 19 g19 (by norm_num)
  have := S3 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 113 g113 5 g5 (by norm_num) (by norm_num)
  omega

theorem kill7_e8 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 7 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 7 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 7 ^ 8 ∣ 1 + 7 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 7 ^ e → c ∈ ({7} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 7 → c ∉ ({7} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g17 : 17 ∈ P := S7 17 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 17 ∣ 1 + 7 ^ 8).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 17 g17 (by norm_num)

theorem kill7_e13 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 7 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 7 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 7 ^ 13 ∣ 1 + 7 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 7 ^ e → c ∈ ({7} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 7 → c ∉ ({7} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g53 : 53 ∈ P := S7 53 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 53 ∣ 1 + 7 ^ 13).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 53 g53 (by norm_num)

theorem kill7_e16 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 7 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 7 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 7 ^ 16 ∣ 1 + 7 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 7 ^ e → c ∈ ({7} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 7 → c ∉ ({7} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g353 : 353 ∈ P := S7 353 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 353 ∣ 1 + 7 ^ 16).trans hd)
  have g59 : 59 ∈ P := S1 59 (by norm_num) (by norm_num) (hnz (by norm_num)) 353 g353 (by norm_num)
  have := S3 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 353 g353 59 g59 (by norm_num) (by norm_num)
  omega

theorem kill7_e19 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 7 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 7 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 7 ^ 19 ∣ 1 + 7 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 7 ^ e → c ∈ ({7} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 7 → c ∉ ({7} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g351121 : 351121 ∈ P := S7 351121 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 351121 ∣ 1 + 7 ^ 19).trans hd)
  exact S6 419 (by norm_num) (by norm_num) (hnz (by norm_num)) 351121 g351121 (by norm_num)

theorem kill7_e31 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 7 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 7 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 7 ^ 31 ∣ 1 + 7 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 7 ^ e → c ∈ ({7} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 7 → c ∉ ({7} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g373 : 373 ∈ P := S7 373 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 373 ∣ 1 + 7 ^ 31).trans hd)
  have g17 : 17 ∈ P := S1 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 373 g373 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 17 g17 (by norm_num)

theorem kill7_e32 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 7 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 7 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 7 ^ 32 ∣ 1 + 7 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 7 ^ e → c ∈ ({7} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 7 → c ∉ ({7} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g7699649 : 7699649 ∈ P := S7 7699649 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 7699649 ∣ 1 + 7 ^ 32).trans hd)
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 7699649 g7699649 (by norm_num)

theorem kill7_e37 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 7 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 7 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 7 ^ 37 ∣ 1 + 7 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 7 ^ e → c ∈ ({7} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 7 → c ∉ ({7} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g149 : 149 ∈ P := S7 149 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 149 ∣ 1 + 7 ^ 37).trans hd)
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 149 g149 (by norm_num)

theorem kill3_e23 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 23 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g23535794707 : 23535794707 ∈ P := S7 23535794707 prime_23535794707 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 23535794707 ∣ 1 + 3 ^ 23).trans hd)
  have g79 : 79 ∈ P := S1 79 (by norm_num) (by norm_num) (hnz (by norm_num)) 23535794707 g23535794707 (by norm_num)
  have g74480363 : 74480363 ∈ P := S1 74480363 prime_74480363 (by norm_num) (hnz (by norm_num)) 23535794707 g23535794707 (by norm_num)
  have g98519 : 98519 ∈ P := S1 98519 (by norm_num) (by norm_num) (hnz (by norm_num)) 74480363 g74480363 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 79 g79 98519 g98519 (by norm_num) (by norm_num)
  omega

theorem kill3_e26 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 26 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g4795973261 : 4795973261 ∈ P := S7 4795973261 prime_4795973261 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 4795973261 ∣ 1 + 3 ^ 26).trans hd)
  have g266442959 : 266442959 ∈ P := S1 266442959 prime_266442959 (by norm_num) (hnz (by norm_num)) 4795973261 g4795973261 (by norm_num)
  exact S8 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 5 ∣ 1 + 3 ^ 26).trans hd) 266442959 g266442959 (by norm_num)

theorem kill3_e32 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 32 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g926510094425921 : 926510094425921 ∈ P := S7 926510094425921 prime_926510094425921 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 926510094425921 ∣ 1 + 3 ^ 32).trans hd)
  have g6883 : 6883 ∈ P := S1 6883 (by norm_num) (by norm_num) (hnz (by norm_num)) 926510094425921 g926510094425921 (by norm_num)
  have g1721 : 1721 ∈ P := S1 1721 (by norm_num) (by norm_num) (hnz (by norm_num)) 6883 g6883 (by norm_num)
  have g41 : 41 ∈ P := S1 41 (by norm_num) (by norm_num) (hnz (by norm_num)) 1721 g1721 (by norm_num)
  have := S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 1721 g1721 41 g41 (by norm_num) (by norm_num)
  omega

theorem kill3_e35 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 35 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g547 : 547 ∈ P := S7 547 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 547 ∣ 1 + 3 ^ 35).trans hd)
  have g137 : 137 ∈ P := S1 137 (by norm_num) (by norm_num) (hnz (by norm_num)) 547 g547 (by norm_num)
  have g374857981681 : 374857981681 ∈ P := S7 374857981681 prime_374857981681 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 374857981681 ∣ 1 + 3 ^ 35).trans hd)
  have g2851 : 2851 ∈ P := S1 2851 (by norm_num) (by norm_num) (hnz (by norm_num)) 374857981681 g374857981681 (by norm_num)
  have := S3 23 (by norm_num) (by norm_num) (hnz (by norm_num)) 137 g137 2851 g2851 (by norm_num) (by norm_num)
  omega

theorem kill5_e28 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 5 ^ 28 ∣ 1 + 5 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 5 ^ e → c ∈ ({5} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g59509429687890001 : 59509429687890001 ∈ P := S7 59509429687890001 prime_59509429687890001 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 59509429687890001 ∣ 1 + 5 ^ 28).trans hd)
  have g29754714843945001 : 29754714843945001 ∈ P := S1 29754714843945001 prime_29754714843945001 (by norm_num) (hnz (by norm_num)) 59509429687890001 g59509429687890001 (by norm_num)
  have g83 : 83 ∈ P := S1 83 (by norm_num) (by norm_num) (hnz (by norm_num)) 29754714843945001 g29754714843945001 (by norm_num)
  have g7679233 : 7679233 ∈ P := S1 7679233 (by norm_num) (by norm_num) (hnz (by norm_num)) 29754714843945001 g29754714843945001 (by norm_num)
  have g769 : 769 ∈ P := S1 769 (by norm_num) (by norm_num) (hnz (by norm_num)) 7679233 g7679233 (by norm_num)
  have := S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 83 g83 769 g769 (by norm_num) (by norm_num)
  omega

theorem kill5_e38 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 5 ^ 38 ∣ 1 + 5 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 5 ^ e → c ∈ ({5} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g4885168129 : 4885168129 ∈ P := S7 4885168129 prime_4885168129 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 4885168129 ∣ 1 + 5 ^ 38).trans hd)
  have g14737 : 14737 ∈ P := S1 14737 (by norm_num) (by norm_num) (hnz (by norm_num)) 4885168129 g4885168129 (by norm_num)
  have g7369 : 7369 ∈ P := S1 7369 (by norm_num) (by norm_num) (hnz (by norm_num)) 14737 g14737 (by norm_num)
  have g67 : 67 ∈ P := S1 67 (by norm_num) (by norm_num) (hnz (by norm_num)) 7369 g7369 (by norm_num)
  have g17 : 17 ∈ P := S1 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 67 g67 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 17 g17 (by norm_num)

theorem kill7_e17 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 7 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 7 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 7 ^ 17 ∣ 1 + 7 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 7 ^ e → c ∈ ({7} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 7 → c ∉ ({7} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g29078814248401 : 29078814248401 ∈ P := S7 29078814248401 prime_29078814248401 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 29078814248401 ∣ 1 + 7 ^ 17).trans hd)
  have g71 : 71 ∈ P := S1 71 (by norm_num) (by norm_num) (hnz (by norm_num)) 29078814248401 g29078814248401 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 71 g71 (by norm_num)

theorem kill7_e23 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 7 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 7 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 7 ^ 23 ∣ 1 + 7 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 7 ^ e → c ∈ ({7} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 7 → c ∉ ({7} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g3421093417510114543 : 3421093417510114543 ∈ P := S7 3421093417510114543 prime_3421093417510114543 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 3421093417510114543 ∣ 1 + 7 ^ 23).trans hd)
  have g11 : 11 ∈ P := S1 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 3421093417510114543 g3421093417510114543 (by norm_num)
  have g29 : 29 ∈ P := S1 29 (by norm_num) (by norm_num) (hnz (by norm_num)) 3421093417510114543 g3421093417510114543 (by norm_num)
  have := S3 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 11 g11 29 g29 (by norm_num) (by norm_num)
  omega

theorem kill7_e29 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 7 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 7 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 7 ^ 29 ∣ 1 + 7 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 7 ^ e → c ∈ ({7} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 7 → c ∉ ({7} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g402488219476647465854701 : 402488219476647465854701 ∈ P := S7 402488219476647465854701 prime_402488219476647465854701 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 402488219476647465854701 ∣ 1 + 7 ^ 29).trans hd)
  have g239 : 239 ∈ P := S1 239 (by norm_num) (by norm_num) (hnz (by norm_num)) 402488219476647465854701 g402488219476647465854701 (by norm_num)
  have g5 : 5 ∈ P := S1 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 239 g239 (by norm_num)
  have := S3 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 239 g239 5 g5 (by norm_num) (by norm_num)
  omega

theorem core3_residues {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p) :
    e % 12 ≠ 6 ∧
    e % 16 ≠ 8 ∧
    e % 18 ≠ 9 ∧
    e % 20 ≠ 10 ∧
    e % 24 ≠ 12 ∧
    e % 28 ≠ 14 ∧
    e % 30 ≠ 15 ∧
    e % 32 ≠ 16 ∧
    e % 34 ≠ 17 ∧
    e % 40 ≠ 20 ∧
    e % 42 ≠ 21 ∧
    e % 44 ≠ 22 ∧
    e % 46 ≠ 23 ∧
    e % 50 ≠ 25 ∧
    e % 52 ≠ 26 ∧
    e % 56 ≠ 28 ∧
    e % 58 ≠ 29 ∧
    e % 62 ≠ 31 ∧
    e % 64 ≠ 32 ∧
    e % 66 ≠ 33 ∧
    e % 68 ≠ 34 ∧
    e % 70 ≠ 35 ∧
    e % 74 ≠ 37 ∧
    e % 76 ≠ 38 ∧
    e % 78 ≠ 39 :=
  ⟨fun h => kill3_e6 hP E (one_add_pow_dvd_of_odd_mul (e0 := 6) (by omega)),
   fun h => kill3_e8 hP E (one_add_pow_dvd_of_odd_mul (e0 := 8) (by omega)),
   fun h => kill3_e9 hP E (one_add_pow_dvd_of_odd_mul (e0 := 9) (by omega)),
   fun h => kill3_e10 hP E (one_add_pow_dvd_of_odd_mul (e0 := 10) (by omega)),
   fun h => kill3_e12 hP E (one_add_pow_dvd_of_odd_mul (e0 := 12) (by omega)),
   fun h => kill3_e14 hP E (one_add_pow_dvd_of_odd_mul (e0 := 14) (by omega)),
   fun h => kill3_e15 hP E (one_add_pow_dvd_of_odd_mul (e0 := 15) (by omega)),
   fun h => kill3_e16 hP E (one_add_pow_dvd_of_odd_mul (e0 := 16) (by omega)),
   fun h => kill3_e17 hP E (one_add_pow_dvd_of_odd_mul (e0 := 17) (by omega)),
   fun h => kill3_e20 hP E (one_add_pow_dvd_of_odd_mul (e0 := 20) (by omega)),
   fun h => kill3_e21 hP E (one_add_pow_dvd_of_odd_mul (e0 := 21) (by omega)),
   fun h => kill3_e22 hP E (one_add_pow_dvd_of_odd_mul (e0 := 22) (by omega)),
   fun h => kill3_e23 hP E (one_add_pow_dvd_of_odd_mul (e0 := 23) (by omega)),
   fun h => kill3_e25 hP E (one_add_pow_dvd_of_odd_mul (e0 := 25) (by omega)),
   fun h => kill3_e26 hP E (one_add_pow_dvd_of_odd_mul (e0 := 26) (by omega)),
   fun h => kill3_e28 hP E (one_add_pow_dvd_of_odd_mul (e0 := 28) (by omega)),
   fun h => kill3_e29 hP E (one_add_pow_dvd_of_odd_mul (e0 := 29) (by omega)),
   fun h => kill3_e31 hP E (one_add_pow_dvd_of_odd_mul (e0 := 31) (by omega)),
   fun h => kill3_e32 hP E (one_add_pow_dvd_of_odd_mul (e0 := 32) (by omega)),
   fun h => kill3_e33 hP E (one_add_pow_dvd_of_odd_mul (e0 := 33) (by omega)),
   fun h => kill3_e34 hP E (one_add_pow_dvd_of_odd_mul (e0 := 34) (by omega)),
   fun h => kill3_e35 hP E (one_add_pow_dvd_of_odd_mul (e0 := 35) (by omega)),
   fun h => kill3_e37 hP E (one_add_pow_dvd_of_odd_mul (e0 := 37) (by omega)),
   fun h => kill3_e38 hP E (one_add_pow_dvd_of_odd_mul (e0 := 38) (by omega)),
   fun h => kill3_e39 hP E (one_add_pow_dvd_of_odd_mul (e0 := 39) (by omega))⟩

theorem core5_residues {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ e * ∏ p ∈ P, p) :
    e % 10 ≠ 5 ∧
    e % 12 ≠ 6 ∧
    e % 14 ≠ 7 ∧
    e % 16 ≠ 8 ∧
    e % 20 ≠ 10 ∧
    e % 24 ≠ 12 ∧
    e % 26 ≠ 13 ∧
    e % 28 ≠ 14 ∧
    e % 32 ≠ 16 ∧
    e % 38 ≠ 19 ∧
    e % 40 ≠ 20 ∧
    e % 44 ≠ 22 ∧
    e % 52 ≠ 26 ∧
    e % 56 ≠ 28 ∧
    e % 58 ≠ 29 ∧
    e % 62 ≠ 31 ∧
    e % 64 ≠ 32 ∧
    e % 68 ≠ 34 ∧
    e % 74 ≠ 37 ∧
    e % 76 ≠ 38 :=
  ⟨fun h => kill5_e5 hP E (one_add_pow_dvd_of_odd_mul (e0 := 5) (by omega)),
   fun h => kill5_e6 hP E (one_add_pow_dvd_of_odd_mul (e0 := 6) (by omega)),
   fun h => kill5_e7 hP E (one_add_pow_dvd_of_odd_mul (e0 := 7) (by omega)),
   fun h => kill5_e8 hP E (one_add_pow_dvd_of_odd_mul (e0 := 8) (by omega)),
   fun h => kill5_e10 hP E (one_add_pow_dvd_of_odd_mul (e0 := 10) (by omega)),
   fun h => kill5_e12 hP E (one_add_pow_dvd_of_odd_mul (e0 := 12) (by omega)),
   fun h => kill5_e13 hP E (one_add_pow_dvd_of_odd_mul (e0 := 13) (by omega)),
   fun h => kill5_e14 hP E (one_add_pow_dvd_of_odd_mul (e0 := 14) (by omega)),
   fun h => kill5_e16 hP E (one_add_pow_dvd_of_odd_mul (e0 := 16) (by omega)),
   fun h => kill5_e19 hP E (one_add_pow_dvd_of_odd_mul (e0 := 19) (by omega)),
   fun h => kill5_e20 hP E (one_add_pow_dvd_of_odd_mul (e0 := 20) (by omega)),
   fun h => kill5_e22 hP E (one_add_pow_dvd_of_odd_mul (e0 := 22) (by omega)),
   fun h => kill5_e26 hP E (one_add_pow_dvd_of_odd_mul (e0 := 26) (by omega)),
   fun h => kill5_e28 hP E (one_add_pow_dvd_of_odd_mul (e0 := 28) (by omega)),
   fun h => kill5_e29 hP E (one_add_pow_dvd_of_odd_mul (e0 := 29) (by omega)),
   fun h => kill5_e31 hP E (one_add_pow_dvd_of_odd_mul (e0 := 31) (by omega)),
   fun h => kill5_e32 hP E (one_add_pow_dvd_of_odd_mul (e0 := 32) (by omega)),
   fun h => kill5_e34 hP E (one_add_pow_dvd_of_odd_mul (e0 := 34) (by omega)),
   fun h => kill5_e37 hP E (one_add_pow_dvd_of_odd_mul (e0 := 37) (by omega)),
   fun h => kill5_e38 hP E (one_add_pow_dvd_of_odd_mul (e0 := 38) (by omega))⟩

theorem core7_residues {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h7 : 7 ∉ P)
    (E : (2 ^ m + 1) * (1 + 7 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 7 ^ e * ∏ p ∈ P, p) :
    e % 6 ≠ 3 ∧ e % 8 ≠ 4 ∧ e % 22 ≠ 11 ∧
    e % 4 ≠ 2 ∧
    e % 10 ≠ 5 ∧
    e % 14 ≠ 7 ∧
    e % 16 ≠ 8 ∧
    e % 26 ≠ 13 ∧
    e % 32 ≠ 16 ∧
    e % 34 ≠ 17 ∧
    e % 38 ≠ 19 ∧
    e % 46 ≠ 23 ∧
    e % 58 ≠ 29 ∧
    e % 62 ≠ 31 ∧
    e % 64 ≠ 32 ∧
    e % 74 ≠ 37 :=
  ⟨fun h => core7_chain43 hP h7 E (by omega)
      ((by norm_num : 43 ∣ 1 + 7 ^ 3).trans (one_add_pow_dvd_of_odd_mul (e0 := 3) (by omega))),
   fun h => core7_chain1201 hP h7 E (by omega)
      ((by norm_num : 1201 ∣ 1 + 7 ^ 4).trans (one_add_pow_dvd_of_odd_mul (e0 := 4) (by omega))),
   fun h => core7_chain23 hP h7 E (by omega)
      ((by norm_num : 23 ∣ 1 + 7 ^ 11).trans (one_add_pow_dvd_of_odd_mul (e0 := 11) (by omega))),
   fun h => kill7_e2 hP E (one_add_pow_dvd_of_odd_mul (e0 := 2) (by omega)),
   fun h => kill7_e5 hP E (one_add_pow_dvd_of_odd_mul (e0 := 5) (by omega)),
   fun h => kill7_e7 hP E (one_add_pow_dvd_of_odd_mul (e0 := 7) (by omega)),
   fun h => kill7_e8 hP E (one_add_pow_dvd_of_odd_mul (e0 := 8) (by omega)),
   fun h => kill7_e13 hP E (one_add_pow_dvd_of_odd_mul (e0 := 13) (by omega)),
   fun h => kill7_e16 hP E (one_add_pow_dvd_of_odd_mul (e0 := 16) (by omega)),
   fun h => kill7_e17 hP E (one_add_pow_dvd_of_odd_mul (e0 := 17) (by omega)),
   fun h => kill7_e19 hP E (one_add_pow_dvd_of_odd_mul (e0 := 19) (by omega)),
   fun h => kill7_e23 hP E (one_add_pow_dvd_of_odd_mul (e0 := 23) (by omega)),
   fun h => kill7_e29 hP E (one_add_pow_dvd_of_odd_mul (e0 := 29) (by omega)),
   fun h => kill7_e31 hP E (one_add_pow_dvd_of_odd_mul (e0 := 31) (by omega)),
   fun h => kill7_e32 hP E (one_add_pow_dvd_of_odd_mul (e0 := 32) (by omega)),
   fun h => kill7_e37 hP E (one_add_pow_dvd_of_odd_mul (e0 := 37) (by omega))⟩

theorem three_exponent_residues {n : ℕ} (h : Erdos1052.IsUnitaryPerfect n) (h3 : 3 ∣ n)
    (hs : ∀ r ∈ n.primeFactors, r ≠ 2 → r ≠ 3 → n.factorization r = 1) :
    n.factorization 3 % 12 ≠ 6 ∧
    n.factorization 3 % 16 ≠ 8 ∧
    n.factorization 3 % 18 ≠ 9 ∧
    n.factorization 3 % 20 ≠ 10 ∧
    n.factorization 3 % 24 ≠ 12 ∧
    n.factorization 3 % 28 ≠ 14 ∧
    n.factorization 3 % 30 ≠ 15 ∧
    n.factorization 3 % 32 ≠ 16 ∧
    n.factorization 3 % 34 ≠ 17 ∧
    n.factorization 3 % 40 ≠ 20 ∧
    n.factorization 3 % 42 ≠ 21 ∧
    n.factorization 3 % 44 ≠ 22 ∧
    n.factorization 3 % 46 ≠ 23 ∧
    n.factorization 3 % 50 ≠ 25 ∧
    n.factorization 3 % 52 ≠ 26 ∧
    n.factorization 3 % 56 ≠ 28 ∧
    n.factorization 3 % 58 ≠ 29 ∧
    n.factorization 3 % 62 ≠ 31 ∧
    n.factorization 3 % 64 ≠ 32 ∧
    n.factorization 3 % 66 ≠ 33 ∧
    n.factorization 3 % 68 ≠ 34 ∧
    n.factorization 3 % 70 ≠ 35 ∧
    n.factorization 3 % 74 ≠ 37 ∧
    n.factorization 3 % 76 ≠ 38 ∧
    n.factorization 3 % 78 ≠ 39 := by
  have h3pf : 3 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨by norm_num, h3, h.2.ne'⟩
  obtain ⟨hP, E⟩ := kernel_balance_one h h3pf (by norm_num) hs
  exact core3_residues hP E

theorem three_exponent_cases_forty {n : ℕ} (h : Erdos1052.IsUnitaryPerfect n)
    (h3lo : 2 ≤ n.factorization 3) (h3hi : n.factorization 3 ≤ 40)
    (hs : ∀ r ∈ n.primeFactors, r ≠ 2 → r ≠ 3 → n.factorization r = 1) :
    n = 90 ∨ n.factorization 3 = 5 ∨ n.factorization 3 = 7 ∨ n.factorization 3 = 11 ∨
      n.factorization 3 = 13 ∨ n.factorization 3 = 19 := by
  by_cases hle : n.factorization 3 ≤ 12
  · rcases three_exponent_cases h h3lo hle hs with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
  · have h3 : 3 ∣ n := Nat.dvd_of_factorization_pos (by omega)
    obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24⟩ := three_exponent_residues h h3 hs
    right
    omega

theorem five_exponent_residues {n : ℕ} (h : Erdos1052.IsUnitaryPerfect n) (h5 : 5 ∣ n)
    (hs : ∀ r ∈ n.primeFactors, r ≠ 2 → r ≠ 5 → n.factorization r = 1) :
    (n.factorization 5 % 2 = 1 → n.factorization 5 % 6 = 1) ∧
    n.factorization 5 % 10 ≠ 5 ∧
    n.factorization 5 % 12 ≠ 6 ∧
    n.factorization 5 % 14 ≠ 7 ∧
    n.factorization 5 % 16 ≠ 8 ∧
    n.factorization 5 % 20 ≠ 10 ∧
    n.factorization 5 % 24 ≠ 12 ∧
    n.factorization 5 % 26 ≠ 13 ∧
    n.factorization 5 % 28 ≠ 14 ∧
    n.factorization 5 % 32 ≠ 16 ∧
    n.factorization 5 % 38 ≠ 19 ∧
    n.factorization 5 % 40 ≠ 20 ∧
    n.factorization 5 % 44 ≠ 22 ∧
    n.factorization 5 % 52 ≠ 26 ∧
    n.factorization 5 % 56 ≠ 28 ∧
    n.factorization 5 % 58 ≠ 29 ∧
    n.factorization 5 % 62 ≠ 31 ∧
    n.factorization 5 % 64 ≠ 32 ∧
    n.factorization 5 % 68 ≠ 34 ∧
    n.factorization 5 % 74 ≠ 37 ∧
    n.factorization 5 % 76 ≠ 38 := by
  have h5pf : 5 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨by norm_num, h5, h.2.ne'⟩
  obtain ⟨hP, E⟩ := kernel_balance_one h h5pf (by norm_num) hs
  exact ⟨fun ho => odd_exponent_mod_six h (by norm_num) (by norm_num) (by norm_num) hs
    (Nat.odd_iff.mpr ho), core5_residues hP E⟩

theorem five_exponent_cases_forty {n : ℕ} (h : Erdos1052.IsUnitaryPerfect n)
    (h5lo : 2 ≤ n.factorization 5) (h5hi : n.factorization 5 ≤ 40)
    (hs : ∀ r ∈ n.primeFactors, r ≠ 2 → r ≠ 5 → n.factorization r = 1) :
    n.factorization 5 = 2 ∨ n.factorization 5 = 4 := by
  have h5 : 5 ∣ n := Nat.dvd_of_factorization_pos (by omega)
  obtain ⟨ho, r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19⟩ := five_exponent_residues h h5 hs
  omega

theorem seven_exponent_residues {n : ℕ} (h : Erdos1052.IsUnitaryPerfect n) (h7 : 7 ∣ n)
    (hs : ∀ r ∈ n.primeFactors, r ≠ 2 → r ≠ 7 → n.factorization r = 1) :
    n.factorization 7 % 6 ≠ 3 ∧ n.factorization 7 % 8 ≠ 4 ∧ n.factorization 7 % 22 ≠ 11 ∧
    n.factorization 7 % 4 ≠ 2 ∧
    n.factorization 7 % 10 ≠ 5 ∧
    n.factorization 7 % 14 ≠ 7 ∧
    n.factorization 7 % 16 ≠ 8 ∧
    n.factorization 7 % 26 ≠ 13 ∧
    n.factorization 7 % 32 ≠ 16 ∧
    n.factorization 7 % 34 ≠ 17 ∧
    n.factorization 7 % 38 ≠ 19 ∧
    n.factorization 7 % 46 ≠ 23 ∧
    n.factorization 7 % 58 ≠ 29 ∧
    n.factorization 7 % 62 ≠ 31 ∧
    n.factorization 7 % 64 ≠ 32 ∧
    n.factorization 7 % 74 ≠ 37 := by
  have h7pf : 7 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨by norm_num, h7, h.2.ne'⟩
  obtain ⟨hP, E⟩ := kernel_balance_one h h7pf (by norm_num) hs
  exact core7_residues hP
    (fun h' => (Finset.mem_filter.mp h').2 (Finset.mem_singleton.mpr rfl)) E

theorem seven_exponent_gt_forty {n : ℕ} (h : Erdos1052.IsUnitaryPerfect n)
    (h7lo : 2 ≤ n.factorization 7)
    (hs : ∀ r ∈ n.primeFactors, r ≠ 2 → r ≠ 7 → n.factorization r = 1) :
    41 ≤ n.factorization 7 := by
  have h7 : 7 ∣ n := Nat.dvd_of_factorization_pos (by omega)
  obtain ⟨a1, a2, a3, r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12⟩ := seven_exponent_residues h h7 hs
  omega

-- Section 5. The step.

theorem odd_mul_three {e : ℕ}
    (h : e % 12 ≠ 6 ∧
    e % 16 ≠ 8 ∧
    e % 18 ≠ 9 ∧
    e % 20 ≠ 10 ∧
    e % 24 ≠ 12 ∧
    e % 28 ≠ 14 ∧
    e % 30 ≠ 15 ∧
    e % 32 ≠ 16 ∧
    e % 34 ≠ 17 ∧
    e % 40 ≠ 20 ∧
    e % 42 ≠ 21 ∧
    e % 44 ≠ 22 ∧
    e % 46 ≠ 23 ∧
    e % 50 ≠ 25 ∧
    e % 52 ≠ 26 ∧
    e % 56 ≠ 28 ∧
    e % 58 ≠ 29 ∧
    e % 62 ≠ 31 ∧
    e % 64 ≠ 32 ∧
    e % 66 ≠ 33 ∧
    e % 68 ≠ 34 ∧
    e % 70 ≠ 35 ∧
    e % 74 ≠ 37 ∧
    e % 76 ≠ 38 ∧
    e % 78 ≠ 39) :
    ∀ d ∈ ({6, 8, 9, 10, 12, 14, 15, 16, 17, 20, 21, 22, 23, 25, 26, 28, 29, 31, 32, 33, 34, 35, 37, 38, 39} : Finset ℕ), e % (2 * d) ≠ d := by
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24⟩ := h
  intro d hd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

theorem odd_mul_five {e : ℕ}
    (h : (e % 2 = 1 → e % 6 = 1) ∧
    e % 10 ≠ 5 ∧
    e % 12 ≠ 6 ∧
    e % 14 ≠ 7 ∧
    e % 16 ≠ 8 ∧
    e % 20 ≠ 10 ∧
    e % 24 ≠ 12 ∧
    e % 26 ≠ 13 ∧
    e % 28 ≠ 14 ∧
    e % 32 ≠ 16 ∧
    e % 38 ≠ 19 ∧
    e % 40 ≠ 20 ∧
    e % 44 ≠ 22 ∧
    e % 52 ≠ 26 ∧
    e % 56 ≠ 28 ∧
    e % 58 ≠ 29 ∧
    e % 62 ≠ 31 ∧
    e % 64 ≠ 32 ∧
    e % 68 ≠ 34 ∧
    e % 74 ≠ 37 ∧
    e % 76 ≠ 38) :
    ∀ d ∈ ({5, 6, 7, 8, 10, 12, 13, 14, 16, 19, 20, 22, 26, 28, 29, 31, 32, 34, 37, 38} : Finset ℕ), e % (2 * d) ≠ d := by
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20⟩ := h
  intro d hd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

theorem odd_mul_seven {e : ℕ}
    (h : e % 6 ≠ 3 ∧ e % 8 ≠ 4 ∧ e % 22 ≠ 11 ∧
    e % 4 ≠ 2 ∧
    e % 10 ≠ 5 ∧
    e % 14 ≠ 7 ∧
    e % 16 ≠ 8 ∧
    e % 26 ≠ 13 ∧
    e % 32 ≠ 16 ∧
    e % 34 ≠ 17 ∧
    e % 38 ≠ 19 ∧
    e % 46 ≠ 23 ∧
    e % 58 ≠ 29 ∧
    e % 62 ≠ 31 ∧
    e % 64 ≠ 32 ∧
    e % 74 ≠ 37) :
    ∀ d ∈ ({2, 3, 4, 5, 7, 8, 11, 13, 16, 17, 19, 23, 29, 31, 32, 37} : Finset ℕ), e % (2 * d) ≠ d := by
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩ := h
  intro d hd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

theorem main : H1 → H2 → H3 → OMA.R_Erdos1052_erdos_1052_R1_H2_R1.H1 := by
  rintro ⟨A1, h1⟩ ⟨A2, h2⟩ ⟨A3, h3⟩
  refine ⟨max (max A1 A2) (max A3 (padicValNat 2 90)), fun n h _ S hS hna => ?_⟩
  have hn0 : n ≠ 0 := h.2.ne'
  have hsimple : ∀ r ∈ n.primeFactors, r ≠ 2 → r ∉ S → n.factorization r = 1 := by
    intro r hr hr2 hrS
    have hrp := Nat.prime_of_mem_primeFactors hr
    have hpos := hrp.factorization_pos_of_dvd hn0 (Nat.dvd_of_mem_primeFactors hr)
    have : ¬ 2 ≤ n.factorization r := fun he =>
      hrS ((hS r).mpr ⟨hrp, hr2, (hrp.pow_dvd_iff_le_factorization hn0).mpr he⟩)
    omega
  rcases Nat.lt_or_ge S.card 2 with hc | hc
  swap
  · exact (h3 n h S hS hc hna).trans ((le_max_left _ _).trans (le_max_right _ _))
  rcases Nat.lt_or_ge S.card 1 with hc0 | hc1
  · have hS0 : S = ∅ := Finset.card_eq_zero.mp (by omega)
    subst hS0
    exact absurd ⟨by simp, by norm_num⟩ hna
  obtain ⟨z, rfl⟩ := Finset.card_eq_one.mp (show S.card = 1 by omega)
  have hz := (hS z).mp (Finset.mem_singleton_self z)
  have hiff : ∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = z := fun p => by
    rw [← Finset.mem_singleton]
    exact (hS p).symm
  have hs' : ∀ r ∈ n.primeFactors, r ≠ 2 → r ≠ z → n.factorization r = 1 :=
    fun r hr hr2 hrz => hsimple r hr hr2 (by simpa using hrz)
  have he2 : 2 ≤ n.factorization z := (hz.1.pow_dvd_iff_le_factorization hn0).mp hz.2.2
  have hzn : z ∣ n := Nat.dvd_of_factorization_pos (by omega)
  by_cases hz3 : z = 3
  · subst hz3
    by_cases hbig : n.factorization 3 = 5 ∨ n.factorization 3 = 7 ∨ n.factorization 3 = 11 ∨
        n.factorization 3 = 13 ∨ n.factorization 3 = 19 ∨ 41 ≤ n.factorization 3
    · refine (h1 n h hiff hbig ?_).trans ((le_max_left _ _).trans (le_max_left _ _))
      exact odd_mul_three (three_exponent_residues h hzn hs')
    · rcases three_exponent_cases_forty h he2 (by omega) hs' with h90 | h' | h' | h' | h' | h'
      · subst h90
        exact (le_max_right _ _).trans (le_max_right _ _)
      all_goals exact absurd (by omega) hbig
  · have hz5 : 5 ≤ z := by
      have := hz.1.two_le
      rcases Nat.lt_or_ge z 5 with hlt | hge
      · interval_cases z
        · exact absurd rfl hz.2.1
        · exact absurd rfl hz3
        · exact absurd hz.1 (by norm_num)
      · exact hge
    have hlt : z < 2100 := by
      by_contra hge
      have hge' : 2100 ≤ z := by omega
      apply hna
      refine ⟨fun y hy => ?_, ?_⟩
      · rw [Finset.mem_singleton] at hy
        subst hy
        simp only [Finset.card_singleton]
        omega
      · rw [Finset.card_singleton, Finset.prod_singleton]
        have hq : (2100 : ℚ) ≤ z := by exact_mod_cast hge'
        push_cast
        rw [div_le_div_iff₀ (by linarith) (by norm_num)]
        linarith
    refine (h2 n h z hz.1 hz5 hlt hiff
      (fun hm ho => odd_exponent_mod_six h hz.1 hm hz.2.1 hs' ho) (fun h5 => ?_) (fun h7 => ?_)).trans
      ((le_max_right _ _).trans (le_max_left _ _))
    · subst h5
      refine ⟨?_, ?_⟩
      · rcases Nat.lt_or_ge (n.factorization 5) 41 with hle | hge
        · rcases five_exponent_cases_forty h he2 (by omega) hs' with h' | h'
          · exact Or.inl h'
          · exact Or.inr (Or.inl h')
        · exact Or.inr (Or.inr hge)
      · exact odd_mul_five (five_exponent_residues h hzn hs')
    · subst h7
      refine ⟨seven_exponent_gt_forty h he2 hs', ?_⟩
      exact odd_mul_seven (seven_exponent_residues h hzn hs')

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1
