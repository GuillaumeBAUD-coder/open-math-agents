import OMAStatements.S_arxiv_1805_03186
import Mathlib

/-!
# The quasiprime CRT systems recover a hidden forest up to the common period

Every grid prime `p` is retained at a cell where its exponent in the gcd grid
is maximal, so `p ^ e_p` divides both shifted coordinates at that cell. A row
(or column) modulus is a product of such prime powers for distinct primes.

* If `u ≡ x` modulo the period, each retained prime power divides `u + i`
  in its row, hence so does the row modulus.
* Conversely, if every row modulus divides `u + i`, then every retained prime
  power divides `x - u`, hence so does the period.

The same argument applies to columns.
-/

namespace QPForest

open OMA.S_arxiv_1805_03186

theorem exists_place {n : ℕ} (hn : 0 < n) (g : Cell n → ℕ) : ∃ place, Valid g place := by
  have hne : (Finset.univ : Finset (Cell n)).Nonempty :=
    ⟨(⟨0, hn⟩, ⟨0, hn⟩), Finset.mem_univ _⟩
  choose f hf using fun p : ℕ =>
    Finset.exists_mem_eq_sup (Finset.univ : Finset (Cell n)) hne
      (fun c => (g c).factorization p)
  refine ⟨f, ?_⟩
  intro p _
  exact (hf p).2.symm

theorem prime_of_mem {n : ℕ} {g : Cell n → ℕ} {p : ℕ} (hp : p ∈ primes g) : p.Prime := by
  unfold primes at hp
  obtain ⟨c, _, hc⟩ := Finset.mem_biUnion.mp hp
  exact Nat.prime_of_mem_primeFactors hc

/-- A product of powers of distinct primes divides an integer once each factor does. -/
theorem prod_dvd_int {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) (e : ℕ → ℕ) {z : ℤ}
    (h : ∀ p ∈ s, ((p ^ e p : ℕ) : ℤ) ∣ z) : ((∏ p ∈ s, p ^ e p : ℕ) : ℤ) ∣ z := by
  rw [Nat.cast_prod]
  apply Finset.prod_dvd_of_coprime
  · intro p hp q hq hne
    have hc : Nat.Coprime (p ^ e p) (q ^ e q) :=
      Nat.Coprime.pow _ _ ((Nat.coprime_primes (hs p hp) (hs q hq)).mpr hne)
    exact Nat.isCoprime_iff_coprime.mpr hc
  · exact h

/-- One coordinate: the moduli grouped by `sel ∘ place` hold exactly on the class of `x`. -/
theorem coord {n : ℕ} (g : Cell n → ℕ) (place : ℕ → Cell n) (hv : Valid g place)
    (sel : Cell n → Fin n) (x : ℕ) (hdiv : ∀ c, g c ∣ x + (sel c).val) (u : ℕ) :
    (∀ i : Fin n, block g (fun p => sel (place p)) i ∣ u + i.val) ↔
      Nat.ModEq (period g) u x := by
  have hpow : ∀ p ∈ primes g,
      ((p ^ exponent g p : ℕ) : ℤ) ∣ (x : ℤ) + ((sel (place p)).val : ℤ) := by
    intro p hp
    have h1 : p ^ exponent g p ∣ g (place p) := by
      rw [← hv p hp]
      exact Nat.ordProj_dvd _ _
    have h2 : p ^ exponent g p ∣ x + (sel (place p)).val := h1.trans (hdiv (place p))
    exact_mod_cast Int.natCast_dvd_natCast.mpr h2
  constructor
  · intro h
    rw [Nat.modEq_iff_dvd]
    unfold period
    apply prod_dvd_int (fun p hp => prime_of_mem hp)
    intro p hp
    have hb : ((p ^ exponent g p : ℕ) : ℤ) ∣ ((u + (sel (place p)).val : ℕ) : ℤ) := by
      apply Int.natCast_dvd_natCast.mpr
      refine Dvd.dvd.trans ?_ (h (sel (place p)))
      unfold block
      exact Finset.dvd_prod_of_mem (fun q => q ^ exponent g q)
        (Finset.mem_filter.mpr ⟨hp, rfl⟩)
    have hx := hpow p hp
    have he : (x : ℤ) - (u : ℤ) =
        ((x : ℤ) + ((sel (place p)).val : ℤ)) - ((u + (sel (place p)).val : ℕ) : ℤ) := by
      push_cast
      ring
    rw [he]
    exact dvd_sub hx hb
  · intro h i
    have hper : ((period g : ℕ) : ℤ) ∣ (x : ℤ) - (u : ℤ) := (Nat.modEq_iff_dvd).mp h
    apply Int.natCast_dvd_natCast.mp
    unfold block
    apply prod_dvd_int (fun p hp => prime_of_mem (Finset.mem_filter.mp hp).1)
    intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_filter.mp hp
    have hp3 : sel (place p) = i := hp2
    have hx := hpow p hp1
    have hpp : ((p ^ exponent g p : ℕ) : ℤ) ∣ (x : ℤ) - (u : ℤ) := by
      refine Dvd.dvd.trans ?_ hper
      apply Int.natCast_dvd_natCast.mpr
      unfold period
      exact Finset.dvd_prod_of_mem (fun q => q ^ exponent g q) hp1
    have he : ((u + i.val : ℕ) : ℤ) =
        ((x : ℤ) + ((sel (place p)).val : ℤ)) - ((x : ℤ) - (u : ℤ)) := by
      rw [hp3]
      push_cast
      ring
    rw [he]
    exact dvd_sub hx hpp

end QPForest

theorem OMA.solution : type_of% @OMA.S_arxiv_1805_03186.main := by
  intro n hn x y _ _ _ g
  refine ⟨QPForest.exists_place hn g, ?_⟩
  intro place hv u v
  have hrow : ∀ c : OMA.S_arxiv_1805_03186.Cell n, g c ∣ x + (Prod.fst c).val :=
    fun c => Nat.gcd_dvd_left (x + c.1.val) (y + c.2.val)
  have hcol : ∀ c : OMA.S_arxiv_1805_03186.Cell n, g c ∣ y + (Prod.snd c).val :=
    fun c => Nat.gcd_dvd_right (x + c.1.val) (y + c.2.val)
  have h1 := QPForest.coord g place hv Prod.fst x hrow u
  have h2 := QPForest.coord g place hv Prod.snd y hcol v
  exact and_congr h1 h2
