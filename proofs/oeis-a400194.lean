import OMAStatements.S_oeis_a400194
import Mathlib

/-!
Proof of oeis-a400194: every 2-dense sublist of divisors of n is closed under halving and under
doubling (inside the divisors of n), hence is a union of full chains d, 2d, ..., 2^e d with d odd.
-/

namespace A400194Proof

open OMA.S_oeis_a400194

theorem mem_terms {n a b d : ℕ} :
    d ∈ terms n a b ↔ d ∈ Nat.divisors n ∧ a ≤ d ∧ d ≤ b := by
  unfold terms
  rw [Finset.mem_filter]

theorem half {n a b d : ℕ} (h : IsDense n a b) (hd : 2 * d ∈ terms n a b) : d ∈ terms n a b := by
  rw [mem_terms] at hd ⊢
  obtain ⟨hdiv, ha, hb⟩ := hd
  have hdn : d ∈ Nat.divisors n := by
    rw [Nat.mem_divisors] at hdiv ⊢
    exact ⟨dvd_trans (Dvd.intro_left 2 rfl) hdiv.1, hdiv.2⟩
  refine ⟨hdn, ?_, by omega⟩
  by_contra hlt
  have := h.2.2.2.2.1 d hdn (by omega)
  omega

theorem dbl {n a b d : ℕ} (h : IsDense n a b) (hd : d ∈ terms n a b) (h2 : 2 * d ∣ n) :
    2 * d ∈ terms n a b := by
  rw [mem_terms] at hd ⊢
  obtain ⟨hdiv, ha, hb⟩ := hd
  have hdn : 2 * d ∈ Nat.divisors n := by
    rw [Nat.mem_divisors] at hdiv ⊢
    exact ⟨h2, hdiv.2⟩
  refine ⟨hdn, by omega, ?_⟩
  by_contra hlt
  have := h.2.2.2.2.2 (2 * d) hdn (by omega)
  omega

theorem half_pow {n a b : ℕ} (h : IsDense n a b) (k : ℕ) :
    ∀ d, 2 ^ k * d ∈ terms n a b → d ∈ terms n a b := by
  induction k with
  | zero => intro d hd; simpa using hd
  | succ k ih =>
    intro d hd
    apply ih
    apply half h
    have : 2 * (2 ^ k * d) = 2 ^ (k + 1) * d := by ring
    rw [this]; exact hd

theorem dbl_pow {n a b d : ℕ} (hn : n ≠ 0) (h : IsDense n a b) (hd : d ∈ terms n a b)
    (hodd : Odd d) (k : ℕ) : k ≤ padicValNat 2 n → 2 ^ k * d ∈ terms n a b := by
  induction k with
  | zero => intro _; simpa using hd
  | succ k ih =>
    intro hk
    have h1 := ih (by omega)
    have e : 2 ^ (k + 1) * d = 2 * (2 ^ k * d) := by ring
    rw [e]
    apply dbl h h1
    rw [← e]
    have hdn : d ∣ n := (Nat.mem_divisors.mp (mem_terms.mp hd).1).1
    have hp : 2 ^ (k + 1) ∣ n := (padicValNat_dvd_iff_le hn).mpr hk
    have hc : Nat.Coprime (2 ^ (k + 1)) d :=
      Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hodd)
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hc hp hdn

theorem val_pow_mul {k d : ℕ} (hodd : Odd d) : padicValNat 2 (2 ^ k * d) = k := by
  have hd : d ≠ 0 := by rintro rfl; simp at hodd
  rw [padicValNat.mul (by positivity) hd, padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (by rw [← Nat.not_even_iff_odd] at hodd; rwa [even_iff_two_dvd] at hodd)]
  rfl

theorem card_terms {n a b : ℕ} (hn : n ≠ 0) (h : IsDense n a b) :
    (terms n a b).card = (padicValNat 2 n + 1) * ((terms n a b).filter Odd).card := by
  have key : terms n a b =
      (((terms n a b).filter Odd) ×ˢ Finset.range (padicValNat 2 n + 1)).image
        (fun p => 2 ^ p.2 * p.1) := by
    ext t
    simp only [Finset.mem_image, Finset.mem_product, Finset.mem_filter, Finset.mem_range,
      Prod.exists]
    constructor
    · intro ht
      have ht0 : t ≠ 0 := by
        intro h0
        have := (Nat.mem_divisors.mp (mem_terms.mp ht).1).1
        rw [h0] at this
        exact hn (zero_dvd_iff.mp this)
      obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd ht0
      refine ⟨m, k, ⟨⟨half_pow h k m ht, hm⟩, ?_⟩, rfl⟩
      have hdvd : 2 ^ k ∣ n :=
        dvd_trans (Dvd.intro _ rfl) (Nat.mem_divisors.mp (mem_terms.mp ht).1).1
      have := (padicValNat_dvd_iff_le hn).mp hdvd
      omega
    · rintro ⟨m, k, ⟨⟨hm, hodd⟩, hk⟩, rfl⟩
      exact dbl_pow hn h hm hodd k (by omega)
  have inj : Set.InjOn (fun p : ℕ × ℕ => 2 ^ p.2 * p.1)
      (↑(((terms n a b).filter Odd) ×ˢ Finset.range (padicValNat 2 n + 1)) : Set (ℕ × ℕ)) := by
    rintro ⟨d, j⟩ hp ⟨d', j'⟩ hp' heq
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_filter] at hp hp'
    simp only at heq
    have hj : j = j' := by
      have := congrArg (padicValNat 2) heq
      rwa [val_pow_mul hp.1.2, val_pow_mul hp'.1.2] at this
    subst hj
    have : d = d' := Nat.eq_of_mul_eq_mul_left (by positivity) heq
    rw [this]
  conv_lhs => rw [key]
  rw [Finset.card_image_of_injOn inj, Finset.card_product, Finset.card_range, mul_comm]

theorem ruler {n : ℕ} (hn : n ≠ 0) : a001511 n = padicValNat 2 n + 1 := by
  unfold a001511
  rw [padicValNat.mul two_ne_zero hn, padicValNat_self]
  omega

theorem main' : ∀ n : ℕ, 1 ≤ n → a n = a001511 n * a400195 n := by
  intro n hn1
  have hn : n ≠ 0 := by omega
  rw [ruler hn]
  unfold a a400195
  have hf : ∀ p ∈ denseLists n, (terms n p.1 p.2).card =
      (padicValNat 2 n + 1) * ((terms n p.1 p.2).filter Odd).card := by
    intro p hp
    exact card_terms hn (Finset.mem_filter.mp hp).2
  apply le_antisymm
  · apply Finset.sup_le
    intro p hp
    rw [hf p hp]
    exact Nat.mul_le_mul_left _
      (Finset.le_sup (f := fun p => ((terms n p.1 p.2).filter Odd).card) hp)
  · rcases (denseLists n).eq_empty_or_nonempty with he | hne
    · rw [he]; simp
    · obtain ⟨p, hp, hpe⟩ := Finset.exists_mem_eq_sup (denseLists n) hne
        (fun p => ((terms n p.1 p.2).filter Odd).card)
      rw [hpe, ← hf p hp]
      exact Finset.le_sup (f := fun p => (terms n p.1 p.2).card) hp

end A400194Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a400194.main := A400194Proof.main'
