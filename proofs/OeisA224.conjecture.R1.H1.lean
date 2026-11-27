import OMAReductions.R_OeisA224_conjecture_R1
import Mathlib

-- Step OeisA224.conjecture.R1.H1: hypothesis H1 of reduction OeisA224.conjecture.R1
-- Credit: @ivillar
-- Credit-note: the lemmas count_step, prime_count and count_formula below are copied verbatim from
-- @HudZah's merged reduction reductions/OeisA224.conjecture.R1.H2.R1.H1.R1.lean (its module cannot be
-- imported here, as only Mathlib imports may follow the first import).
--
-- Proof. Write N = p^k (k >= 2) and A = a(N). The closed form gives
-- 2 (p + 1) (A - 1) + e = p N with e = p for even k and e = 1 for odd k.
-- Even k: p divides A - 1, so p divides A (A - 1), while N^2 = 0 mod p: N^2 = 1 mod A (A - 1) fails.
-- Odd k: if N^2 - 1 = t A (A - 1), then 4 (p+1)^2 (N^2 - 1) = t (p N - 1) (p N + 2 p + 1).
-- Size comparison gives 5 <= t <= 7, and reducing mod p gives t = 4 mod p, so p = 3, t = 7,
-- which leaves N^2 = 126 N + 15: impossible for a natural number N.

open Finset OeisA224

namespace OMA.A224H1

theorem count_step (p e : ℕ) (hp : p.Prime) (hne : p ≠ 2) :
    a (p^(e+2)) = a (p^e) + (p^(e+1)*(p-1))/2 := by
  classical
  let residues (n : ℕ) : Finset ℕ :=
    (Finset.range n).image (fun k => k^2 % n)

  have mem_res {n r : ℕ} (hn : 0 < n) :
      r ∈ residues n ↔ ∃ k : ℕ, k^2 % n = r := by
    constructor
    · intro hr
      obtain ⟨k, _, h⟩ := Finset.mem_image.mp hr
      exact ⟨k, h⟩
    · rintro ⟨k, rfl⟩
      exact Finset.mem_image.mpr ⟨k % n, Finset.mem_range.mpr (Nat.mod_lt _ hn), (Nat.pow_mod ..).symm⟩

  let unitSq (n : ℕ) [NeZero n] : Finset ℕ := by
    classical
    exact Finset.univ.image (fun u : (powMonoidHom 2 : (ZMod n)ˣ →* (ZMod n)ˣ).range =>
      (u.val.val).val)

  have mem_unitSq {n x : ℕ} [NeZero n] :
      x ∈ unitSq n ↔ ∃ u : (ZMod n)ˣ, ((u : ZMod n)^2).val = x := by
    classical
    constructor
    · intro hx
      obtain ⟨u, _, hu⟩ := Finset.mem_image.mp hx
      obtain ⟨v, hv⟩ := u.property
      exact ⟨v, by simpa [← hv] using hu⟩
    · rintro ⟨u, rfl⟩
      exact Finset.mem_image.mpr ⟨⟨u ^ 2, u, rfl⟩, Finset.mem_univ _, rfl⟩

  have unitSq_card (n : ℕ) [NeZero n] [IsCyclic (ZMod n)ˣ] (hn : 2 < n) :
      (unitSq n).card = n.totient / 2 := by
    classical
    unfold unitSq
    have hi : Function.Injective (fun u : (powMonoidHom 2 : (ZMod n)ˣ →* (ZMod n)ˣ).range =>
        u.val.val.val) := fun _ _ h => Subtype.ext (Units.ext (ZMod.val_injective n h))
    rw [Finset.card_image_of_injective _ hi, Finset.card_univ, ← Nat.card_eq_fintype_card,
      IsCyclic.card_powMonoidHom_range, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
      Nat.gcd_eq_right (even_iff_two_dvd.mp (Nat.totient_even hn))]

  let N := p^(e+2)
  have hp0 := hp.pos
  have hn0 : 0 < N := pow_pos hp0 _
  have : NeZero N := ⟨hn0.ne'⟩
  have : IsCyclic (ZMod N)ˣ := ZMod.isCyclic_units_of_prime_pow p hp hne (e+2)
  have fact (u : ℕ) : (p*u)^2 % N = p^2 * (u^2 % p^e) := by
    rw [show N = p^2*p^e by dsimp [N]; ring, mul_pow, Nat.mul_mod_mul_left]
  let M := (residues (p^e)).image (fun t => p^2*t)
  have split : residues N = M ∪ unitSq N := by
    ext r
    constructor
    · intro hr
      obtain ⟨k, rfl⟩ := (mem_res hn0).mp hr
      by_cases hpk : p ∣ k
      · obtain ⟨u, rfl⟩ := hpk
        exact Finset.mem_union_left _ (Finset.mem_image.mpr
          ⟨u^2 % p^e, (mem_res (pow_pos hp0 _)).mpr ⟨u, rfl⟩, (fact u).symm⟩)
      · have hu : IsUnit (k : ZMod N) := (ZMod.isUnit_natCast_iff_not_dvd_pow hp (by omega)).mpr hpk
        apply Finset.mem_union_right
        apply mem_unitSq.mpr
        exact ⟨hu.unit, by rw [IsUnit.unit_spec, ← Nat.cast_pow, ZMod.val_natCast]⟩
    · intro hr
      rcases Finset.mem_union.mp hr with hr | hr
      · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hr
        obtain ⟨u, rfl⟩ := (mem_res (pow_pos hp0 _)).mp ht
        exact (mem_res hn0).mpr ⟨p*u, fact u⟩
      · obtain ⟨u, rfl⟩ := mem_unitSq.mp hr
        exact (mem_res hn0).mpr ⟨u.val.val, by rw [← ZMod.val_natCast, Nat.cast_pow, ZMod.natCast_zmod_val]⟩
  have disj : Disjoint M (unitSq N) := by
    apply Finset.disjoint_left.mpr
    rintro r hr hunit
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨u, hu⟩ := mem_unitSq.mp hunit
    have hU : IsUnit (((p^2*t : ℕ) : ZMod N)) := by
      rw [← hu, ZMod.natCast_zmod_val]
      exact u.isUnit.pow 2
    exact (ZMod.isUnit_natCast_iff_not_dvd_pow hp (show 0 < e+2 by omega)).mp hU
      ((dvd_pow_self p (by decide : 2 ≠ 0)).trans (dvd_mul_right _ _))
  have high : 2 < N := lt_of_lt_of_le (lt_of_le_of_ne hp.two_le (Ne.symm hne))
    (Nat.le_pow (by omega : 0 < e+2))
  have hcnt : (unitSq N).card = _ := unitSq_card N high
  have hcard : (residues (p^e)).card = a (p^e) := by rw [a, if_neg (pow_ne_zero _ hp.ne_zero)]
  change a N = _
  rw [a, if_neg hn0.ne']
  change (residues N).card = _
  rw [split, Finset.card_union_of_disjoint disj, hcnt]
  dsimp only [M]
  rw [Finset.card_image_of_injective _ (fun _ _ h => Nat.eq_of_mul_eq_mul_left (pow_pos hp0 2) h), hcard]
  dsimp only [N]
  rw [Nat.totient_prime_pow_succ hp]

private theorem prime_count {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) : a p = p / 2 + 1 := by
  rw [OMA.R_OeisA224_conjecture_R1.card_squares_prime p hp hodd]
  have := Nat.odd_iff.mp (hp.odd_of_ne_two hodd)
  omega

theorem count_formula (p : ℕ) (hp : p.Prime) (po : Odd p) (e : ℕ) :
    2*(p+1)*(a (p^e)-1) + (if Even e then p else 1) = p^(e+1) := by
  have hne : p ≠ 2 := by rintro rfl; norm_num at po
  induction e using Nat.twoStepInduction with
  | zero => simp [a_1]
  | one =>
    simp only [pow_one, prime_count hp hne, Nat.add_sub_cancel]
    obtain ⟨k, hk⟩ := po
    have hhalf : p/2 = k := by omega
    rw [hhalf, hk]
    simp
    ring
  | more e ih _ =>
    let x := p^(e+1)
    let q := x*(p-1)/2
    have hdouble : 2*q = x*(p-1) := by
      apply Nat.mul_div_cancel'
      apply dvd_mul_of_dvd_right
      have hh := Nat.odd_iff.mp po
      omega
    have ha : 1 ≤ a (p^e) := by
      rw [a, if_neg (pow_ne_zero _ hp.ne_zero), Finset.one_le_card]
      exact ⟨0, Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (pow_pos hp.pos e), by simp⟩⟩
    have hadd : a (p^(e+2)) - 1 = (a (p^e) - 1) + q := by
      rw [count_step p e hp hne]
      change a (p^e) + q - 1 = _
      omega
    have ev : Even (e+2) ↔ Even e := by simp only [Nat.even_iff]; omega
    rw [hadd, if_congr ev rfl rfl]
    calc
      _ = (2*(p+1)*(a (p^e)-1) + (if Even e then p else 1)) + (p+1)*(2*q) := by ring
      _ = x + (p+1)*(x*(p-1)) := by rw [ih, hdouble]
      _ = p^((e+2)+1) := by
        rw [show e+2+1 = (e+1)+2 by omega, pow_add]
        change x + (p+1)*(x*(p-1)) = x*p^2
        obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne_zero
        rw [hj]
        simp only [Nat.succ_sub_one, Nat.succ_eq_add_one]
        ring


theorem bounds (p N t : ℤ) (hp : 3 ≤ p) (hN : p ^ 2 ≤ N) (ht : 0 ≤ t)
    (h : 4 * (p + 1) ^ 2 * (N ^ 2 - 1) = t * (p * N - 1) * (p * N + 2 * p + 1)) :
    5 ≤ t ∧ t ≤ 7 := by
  have hN0 : 9 ≤ N := by nlinarith
  have hX : 0 ≤ (p * N - 1) * (p * N + 2 * p + 1) := by
    apply mul_nonneg <;> nlinarith
  constructor
  · by_contra hlt
    push_neg at hlt
    have ht4 : t ≤ 4 := by omega
    have h1 : t * (p * N - 1) * (p * N + 2 * p + 1) ≤ 4 * ((p * N - 1) * (p * N + 2 * p + 1)) := by
      have := mul_le_mul_of_nonneg_right ht4 hX
      linarith
    have h2 : p ^ 2 * N ≤ N * N := by nlinarith
    have h3 : 0 < (2 * p + 1) * N ^ 2 - 2 * p ^ 2 * N - p ^ 2 := by
      have h4 : (2 * p + 1) * (p ^ 2 * N) ≤ (2 * p + 1) * (N * N) :=
        mul_le_mul_of_nonneg_left h2 (by linarith)
      nlinarith
    nlinarith
  · by_contra hgt
    push_neg at hgt
    have ht8 : 8 ≤ t := by omega
    have h1 : 8 * ((p * N - 1) * (p * N + 2 * p + 1)) ≤ t * (p * N - 1) * (p * N + 2 * p + 1) := by
      have := mul_le_mul_of_nonneg_right ht8 hX
      linarith
    have h5 : 4 * (p + 1) ^ 2 ≤ 8 * p ^ 2 := by nlinarith
    have h6 : 4 * (p + 1) ^ 2 * N ^ 2 ≤ 8 * p ^ 2 * N ^ 2 :=
      mul_le_mul_of_nonneg_right h5 (by positivity)
    nlinarith

end OMA.A224H1

theorem OMA.solution : OMA.R_OeisA224_conjecture_R1.H1 := by
  unfold OMA.R_OeisA224_conjecture_R1.H1
  intro p k hp hp2 hk h
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hpo : Odd p := hp.odd_of_ne_two hp2
  have hform := OMA.A224H1.count_formula p hp hpo k
  have hA2 : 2 ≤ OeisA224.a (p ^ k) :=
    OMA.R_OeisA224_conjecture_R1.two_le_a _ (le_trans hp.two_le (Nat.le_self_pow (by omega) p))
  have hNp : p ∣ p ^ k := dvd_pow_self p (by omega)
  by_cases hev : Even k
  · rw [if_pos hev] at hform
    have hdiv : p ∣ 2 * (p + 1) * (OeisA224.a (p ^ k) - 1) := by
      rw [Nat.eq_sub_of_add_eq hform]
      exact Nat.dvd_sub (dvd_pow_self p (by omega)) dvd_rfl
    have hA1 : p ∣ OeisA224.a (p ^ k) - 1 := by
      rcases (Nat.Prime.dvd_mul hp).mp hdiv with h1 | h1
      · rcases (Nat.Prime.dvd_mul hp).mp h1 with h2 | h2
        · have := Nat.le_of_dvd (by norm_num) h2
          omega
        · have h3 : p ∣ 1 := (Nat.dvd_add_right (dvd_refl p)).mp h2
          have := Nat.le_of_dvd (by norm_num) h3
          omega
      · exact h1
    have hD : p ∣ OeisA224.a (p ^ k) * (OeisA224.a (p ^ k) - 1) := dvd_mul_of_dvd_right hA1 _
    have hmod := Nat.ModEq.of_dvd hD h
    unfold Nat.ModEq at hmod
    rw [Nat.mod_eq_zero_of_dvd (dvd_pow hNp (by norm_num)), Nat.mod_eq_of_lt hp.one_lt] at hmod
    exact absurd hmod (by norm_num)
  · rw [if_neg hev] at hform
    have hk3 : 3 ≤ k := by
      rcases Nat.even_or_odd k with he | ho
      · exact absurd he hev
      · obtain ⟨j, rfl⟩ := ho
        omega
    have hN1 : 1 ≤ (p ^ k) ^ 2 := Nat.one_le_pow _ _ (pow_pos hp.pos k)
    obtain ⟨t, ht⟩ := (Nat.modEq_iff_dvd' hN1).mp h.symm
    set A := OeisA224.a (p ^ k) with hAdef
    set N := p ^ k with hNdef
    obtain ⟨B, hB⟩ : ∃ B, A = B + 1 := ⟨A - 1, by omega⟩
    rw [hB, Nat.add_sub_cancel] at hform ht
    have hform' : 2 * (p + 1) * B + 1 = p * N := by
      rw [hform, pow_succ, mul_comm]
    -- integer versions
    have hBz : 2 * ((p : ℤ) + 1) * (B : ℤ) + 1 = (p : ℤ) * (N : ℤ) := by exact_mod_cast hform'
    have htz : (N : ℤ) ^ 2 - 1 = ((B : ℤ) + 1) * (B : ℤ) * (t : ℤ) := by
      have : ((N ^ 2 - 1 : ℕ) : ℤ) = (((B + 1) * B * t : ℕ) : ℤ) := by rw [ht]
      push_cast [Nat.cast_sub hN1] at this
      linarith
    have hstar : 4 * ((p : ℤ) + 1) ^ 2 * ((N : ℤ) ^ 2 - 1) =
        (t : ℤ) * ((p : ℤ) * N - 1) * ((p : ℤ) * N + 2 * p + 1) := by
      rw [htz, ← hBz]
      ring
    have hNp2 : (p : ℤ) ^ 2 ≤ (N : ℤ) := by
      have : p ^ 2 ≤ N := Nat.pow_le_pow_right hp.pos (by omega)
      exact_mod_cast this
    obtain ⟨t5, t7⟩ := OMA.A224H1.bounds p N t (by exact_mod_cast hp3) hNp2 (by positivity) hstar
    -- N = p * M
    obtain ⟨M, hM⟩ := hNp
    have hMz : (N : ℤ) = (p : ℤ) * (M : ℤ) := by exact_mod_cast hM
    have hdvd : (p : ℤ) ∣ (t : ℤ) - 4 := by
      refine ⟨(t : ℤ) * ((p : ℤ) ^ 3 * M ^ 2 + 2 * (p : ℤ) ^ 2 * M - 2) -
        4 * ((p : ℤ) + 1) ^ 2 * p * M ^ 2 + 4 * p + 8, ?_⟩
      rw [hMz] at hstar
      linear_combination hstar
    have hple : (p : ℤ) ≤ (t : ℤ) - 4 := Int.le_of_dvd (by omega) hdvd
    have hp3' : (p : ℤ) = 3 := by
      have : (3 : ℤ) ≤ p := by exact_mod_cast hp3
      omega
    have ht7 : (t : ℤ) = 7 := by omega
    rw [hp3', ht7] at hstar
    have hN0 : (0 : ℤ) ≤ N := by positivity
    rcases le_or_gt (N : ℤ) 126 with hle | hgt
    · nlinarith
    · nlinarith
