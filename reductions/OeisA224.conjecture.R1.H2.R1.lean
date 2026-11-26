import OMAReductions.R_OeisA224_conjecture_R1

/-!
Reduce the mixed composite case of the Ordowski square residue test.
Square counts multiply on coprime arguments by the Chinese remainder theorem.
For a product of distinct odd primes, the quotient lies strictly between consecutive
integers outside a finite rectangle. The remaining rectangle has a kernel certificate.
Credit: @HudZah
-/

open Finset OeisA224

namespace OMA.R_OeisA224_conjecture_R1_H2_R1

theorem count_coprime {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (h : m.Coprime n) :
    a (m*n) = a m * a n := by
  let sqs (R : Type) [Monoid R] [Fintype R] [DecidableEq R] : Finset R :=
    Finset.univ.image fun t : R => t^2

  have mem_sqs {R : Type} [Monoid R] [Fintype R] [DecidableEq R] (x : R) :
      x ∈ sqs R ↔ ∃ r : R, r^2 = x := by simp [sqs]

  have count_mod (n : ℕ) [NeZero n] : a n = (sqs (ZMod n)).card := by
    have eq : (Finset.range n).image (fun k : ℕ => k^2 % n) =
        (sqs (ZMod n)).image ZMod.val := by
      ext x
      constructor
      · rintro hx
        obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hx
        exact Finset.mem_image.mpr ⟨(k : ZMod n)^2, (mem_sqs _).mpr ⟨k, rfl⟩,
          by rw [← Nat.cast_pow, ZMod.val_natCast]⟩
      · intro hx
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨w, rfl⟩ := (mem_sqs _).mp hv
        exact Finset.mem_image.mpr ⟨w.val, Finset.mem_range.mpr (ZMod.val_lt _),
          by rw [← ZMod.val_natCast, Nat.cast_pow, ZMod.natCast_zmod_val]⟩
    rw [a, if_neg (NeZero.ne n), eq, Finset.card_image_of_injective _ (ZMod.val_injective _)]

  have : NeZero m := ⟨hm.ne'⟩
  have : NeZero n := ⟨hn.ne'⟩
  let e := ZMod.chineseRemainder h
  have eq : (sqs (ZMod (m*n))).image e = sqs (ZMod m) ×ˢ sqs (ZMod n) := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨w, rfl⟩ := (mem_sqs _).mp hy
      rw [map_pow]
      exact Finset.mem_product.mpr ⟨(mem_sqs _).mpr ⟨(e w).1, rfl⟩, (mem_sqs _).mpr ⟨(e w).2, rfl⟩⟩
    · intro hx
      obtain ⟨h1, h2⟩ := Finset.mem_product.mp hx
      obtain ⟨b, hb⟩ := (mem_sqs _).mp h1
      obtain ⟨c, hc⟩ := (mem_sqs _).mp h2
      let w := e.symm (b,c)
      refine Finset.mem_image.mpr ⟨w^2, (mem_sqs _).mpr ⟨w, rfl⟩, ?_⟩
      rw [map_pow, show e w = (b,c) from e.apply_symm_apply _]
      exact Prod.ext hb hc
  rw [count_mod, count_mod m, count_mod n, ← Finset.card_product, ← eq,
    Finset.card_image_of_injective _ e.injective]

private theorem gap {n d k : ℕ} (lo : k*d + 1 < n^2) (hi : n^2 < (k+1)*d+1)
    (hn : 1 ≤ n^2) : ¬ n^2 ≡ 1 [MOD d] := by
  intro ht
  obtain ⟨j, hj⟩ := (Nat.modEq_iff_dvd' hn).mp ht.symm
  rcases le_or_gt j k with h | h
  · have := Nat.mul_le_mul_right d h
    rw [mul_comm d j] at hj
    omega
  · have := Nat.mul_le_mul_right d (show k+1 ≤ j by omega)
    rw [mul_comm d j] at hj
    omega

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4000 in
private theorem sorted_test {u v : ℕ} (hu : 0 < u) (uv : u < v) :
    ¬ ((2*u+1)*(2*v+1))^2 ≡ 1 [MOD ((u+1)*(v+1))*((u+1)*(v+1)-1)] := by
  have pos : 1 ≤ ((2*u+1)*(2*v+1))^2 := Nat.succ_le_of_lt (by positivity)
  have den : (u+1)*(v+1)-1 = u*v+u+v := by
    rw [Nat.sub_eq_iff_eq_add (Nat.succ_le_of_lt (by positivity))]
    ring
  rw [den]
  by_cases large : 30 ≤ u
  · have vl : 30 ≤ v := by omega
    obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le large
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le vl
    apply gap (k := 15) _ _ pos <;> ring_nf <;> omega
  by_cases tail : 901 ≤ v
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le tail
    have upper : u ≤ 29 := by omega
    interval_cases u
    · apply gap (k := 8) _ _ pos <;> ring_nf <;> omega
    · apply gap (k := 11) _ _ pos <;> ring_nf <;> omega
    · apply gap (k := 12) _ _ pos <;> ring_nf <;> omega
    · apply gap (k := 12) _ _ pos <;> ring_nf <;> omega
    · apply gap (k := 13) _ _ pos <;> ring_nf <;> omega
    · apply gap (k := 13) _ _ pos <;> ring_nf <;> omega
    · apply gap (k := 14) _ _ pos <;> ring_nf <;> omega
    · apply gap (k := 14) _ _ pos <;> ring_nf <;> omega
    · apply gap (k := 14) _ _ pos <;> ring_nf <;> omega
    · apply gap (k := 14) _ _ pos <;> ring_nf <;> omega
    · apply gap (k := 14) _ _ pos <;> ring_nf <;> omega
    · apply gap (k := 14) _ _ pos <;> ring_nf <;> omega
    · apply gap (k := 14) _ _ pos <;> ring_nf <;> omega
    · apply gap (k := 14) _ _ pos <;> ring_nf <;> omega
    · apply gap (k := 15) _ _ pos <;> ring_nf <;> omega
    · apply gap (k := 15) _ _ pos <;> ring_nf <;> omega
    · apply gap (k := 15) _ _ pos <;> ring_nf <;> omega
    · apply gap (k := 15) _ _ pos <;> ring_nf <;> omega
    · apply gap (k := 15) _ _ pos <;> ring_nf <;> omega
    · apply gap (k := 15) _ _ pos <;> ring_nf <;> omega
    · apply gap (k := 15) _ _ pos <;> ring_nf <;> omega
    · apply gap (k := 15) _ _ pos <;> ring_nf <;> omega
    · apply gap (k := 15) _ _ pos <;> ring_nf <;> omega
    · apply gap (k := 15) _ _ pos <;> ring_nf <;> omega
    · apply gap (k := 15) _ _ pos <;> ring_nf <;> omega
    · apply gap (k := 15) _ _ pos <;> ring_nf <;> omega
    · apply gap (k := 15) _ _ pos <;> ring_nf <;> omega
    · apply gap (k := 15) _ _ pos <;> ring_nf <;> omega
    · apply gap (k := 15) _ _ pos <;> ring_nf <;> omega

  have small : ∀ u : Fin 30, ∀ v : Fin 901, 0 < u.val → u.val < v.val →
      ¬ ((2*u.val+1)*(2*v.val+1))^2 ≡ 1 [MOD ((u.val+1)*(v.val+1))*(u.val*v.val+u.val+v.val)] := by
    decide +kernel
  exact small ⟨u, by omega⟩ ⟨v, by omega⟩ hu uv

private theorem ordered_primes {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (po : Odd p) (qo : Odd q) (hlt : p < q) :
    ¬ (p*q)^2 ≡ 1 [MOD a (p*q) * (a (p*q)-1)] := by
  have hp2 : p ≠ 2 := by rintro rfl; norm_num at po
  have hq2 : q ≠ 2 := by rintro rfl; norm_num at qo
  have hc : p.Coprime q := (Nat.coprime_primes hp hq).mpr hlt.ne
  rw [count_coprime hp.pos hq.pos hc, OMA.R_OeisA224_conjecture_R1.card_squares_prime p hp hp2, OMA.R_OeisA224_conjecture_R1.card_squares_prime q hq hq2]
  obtain ⟨u, hup⟩ := po
  obtain ⟨v, hvq⟩ := qo
  rw [show (p+1)/2 = u+1 by omega, show (q+1)/2 = v+1 by omega, hup, hvq]
  have hpgt := hp.one_lt
  exact sorted_test (by omega) (by omega)

theorem semiprime_fails {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (po : Odd p) (qo : Odd q) (hne : p ≠ q) :
    ¬ (p*q)^2 ≡ 1 [MOD a (p*q) * (a (p*q)-1)] := by
  rcases lt_or_gt_of_ne hne with h | h
  · exact ordered_primes hp hq po qo h
  · simpa [mul_comm q p] using ordered_primes hq hp qo po h


-- Exactly two distinct prime factors, with at least three factors counted with multiplicity.
def H1 : Prop :=
  ∀ p q e f : ℕ, p.Prime → q.Prime → p ≠ q → Odd p → Odd q →
    0 < e → 0 < f → 3 ≤ e+f →
    ¬ (p^e*q^f)^2 ≡ 1 [MOD a (p^e*q^f) * (a (p^e*q^f)-1)]

-- All cases with three or more distinct prime factors.
def H2 : Prop :=
  ∀ n : ℕ, Odd n → 3 ≤ n.primeFactors.card →
    ¬ n^2 ≡ 1 [MOD a n * (a n - 1)]

theorem main : H1 → H2 → OMA.R_OeisA224_conjecture_R1.H2 := by
  intro two many n hn ho hmixed test
  by_cases h3 : 3 ≤ n.primeFactors.card
  · exact many n ho h3 test
  have hnt := (Nat.not_isPrimePow_iff_nontrivial_of_two_le hn).mp hmixed
  have h2 : n.primeFactors.card = 2 := by
    have := Finset.one_lt_card_iff_nontrivial.mpr hnt
    omega
  obtain ⟨p, q, hpq, heq⟩ := Finset.card_eq_two.mp h2
  have pm : p ∈ n.primeFactors := by simp [heq]
  have qm : q ∈ n.primeFactors := by simp [heq]
  have pp := Nat.prime_of_mem_primeFactors pm
  have qp := Nat.prime_of_mem_primeFactors qm
  have pd := Nat.dvd_of_mem_primeFactors pm
  have qd := Nat.dvd_of_mem_primeFactors qm
  have po : Odd p := by
    by_contra h
    exact ho.not_two_dvd_nat ((even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp h)).trans pd)
  have qo : Odd q := by
    by_contra h
    exact ho.not_two_dvd_nat ((even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp h)).trans qd)
  have nz : n ≠ 0 := by omega
  have pe := pp.factorization_pos_of_dvd nz pd
  have qe := qp.factorization_pos_of_dvd nz qd
  have hab := Nat.prod_primeFactors_pow_factorization nz
  rw [heq] at hab
  simp [hpq] at hab
  rw [hab] at test
  by_cases hs : 3 ≤ n.factorization p + n.factorization q
  · exact two p q _ _ pp qp hpq po qo pe qe hs test
  have pe1 : n.factorization p = 1 := by omega
  have qe1 : n.factorization q = 1 := by omega
  exact semiprime_fails pp qp po qo hpq (by simpa [pe1, qe1] using test)

end OMA.R_OeisA224_conjecture_R1_H2_R1
