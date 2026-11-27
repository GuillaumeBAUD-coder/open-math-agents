import OMAReductions.R_OeisA105751_conjecture_variants_moll_p_mod_4_eq_1_R1

/-!
# Factorial divisibility of the imaginary part in A105751

For a prime congruent to 1 modulo 4, evaluate the Gaussian product at the two
square roots of -1 modulo a power of the prime. Each evaluation vanishes when
the prime power divides the factorial. Their difference recovers the imaginary part.

The Gaussian product and its identification with A105751 are from eitanteperman's
proof of `OeisA105751.prime_divides_some_term` (PR 397). The target is the first
step of ZenimXD's reduction (PR 1276).
-/

namespace OMA.A105751

/-- The Gaussian integer `∏_{k < n} (1 + k i)`. -/
def Zg (n : ℕ) : GaussianInt := ∏ k ∈ Finset.range n, (⟨1, k⟩ : GaussianInt)

lemma a_eq (n : ℕ) : OeisA105751.a n = (Zg (n + 1)).im := by
  unfold OeisA105751.a Zg
  have h : (∏ k ∈ Finset.range (n + 1), (1 + (k : ℂ) * Complex.I)) =
      GaussianInt.toComplex (∏ k ∈ Finset.range (n + 1), (⟨1, k⟩ : GaussianInt)) := by
    rw [map_prod]
    refine Finset.prod_congr rfl (fun k _ => ?_)
    rw [GaussianInt.toComplex_def']
    push_cast
    ring
  simp only
  rw [h, ← GaussianInt.intCast_im, Int.floor_intCast]

/-- Raising an integer square root of -1 to the p-th power lifts it one level. -/
private lemma roots_at_powers (p : ℕ) [Fact p.Prime] (hp : p % 4 = 1) (e : ℕ) :
    ∃ x : ℤ, (p : ℤ) ^ (e + 1) ∣ x ^ 2 - (-1) := by
  induction e with
  | zero =>
    obtain ⟨r, hr⟩ := (ZMod.exists_sq_eq_neg_one_iff (p := p)).2 (by omega)
    refine ⟨r.val, ?_⟩
    rw [zero_add, pow_one, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    simp [pow_two, hr]
  | succ e ih =>
    obtain ⟨x, hx⟩ := ih
    have hpdiv : (p : ℤ) ∣ x ^ 2 - (-1) :=
      dvd_trans (dvd_pow_self _ (by omega : e + 1 ≠ 0)) hx
    have hodd : Odd p := Nat.odd_iff.mpr (by omega)
    refine ⟨x ^ p, ?_⟩
    calc
      (p : ℤ) ^ (e + 1 + 1) ∣
          (∑ i ∈ Finset.range p, (x ^ 2) ^ i * (-1 : ℤ) ^ (p - 1 - i)) *
            (x ^ 2 - (-1)) := by
              rw [pow_succ']
              exact mul_dvd_mul (dvd_geom_sum₂_self hpdiv) hx
      _ = (x ^ 2) ^ p - (-1 : ℤ) ^ p := geom_sum₂_mul _ _ _
      _ = (x ^ p) ^ 2 - (-1) := by rw [hodd.neg_one_pow, ← pow_mul, Nat.mul_comm 2 p, pow_mul]

/-- At a root of -1, the product is a unit power times a product of consecutive integers. -/
private lemma eval_vanishes {q : ℕ} [NeZero q] (n : ℕ) (hq : q ∣ n.factorial)
    (r : ZMod q) (hr : r * r = -1) :
    ((Zg (n + 1)).re : ZMod q) + ((Zg (n + 1)).im : ZMod q) * r = 0 := by
  let φ : GaussianInt →+* ZMod q := Zsqrtd.lift ⟨r, by simpa using hr⟩
  change φ (Zg (n + 1)) = 0
  rw [Zg, map_prod]
  let a := (-r).val
  have ha : (a : ZMod q) = -r := ZMod.natCast_zmod_val _
  have factors (k : ℕ) : φ (⟨1, k⟩ : GaussianInt) = r * ((a : ZMod q) + k) := by
    change ((1 : ℤ) : ZMod q) + ((k : ℤ) : ZMod q) * r = _
    push_cast
    rw [ha]
    linear_combination hr
  simp_rw [factors]
  rw [Finset.prod_mul_distrib]
  suffices ∏ k ∈ Finset.range (n + 1), ((a : ZMod q) + k) = 0 by rw [this, mul_zero]
  have hd : q ∣ a.ascFactorial (n + 1) :=
    hq.trans ((Nat.factorial_dvd_factorial (by omega : n ≤ n + 1)).trans
      (Nat.factorial_dvd_ascFactorial a (n + 1)))
  have hz := (ZMod.natCast_eq_zero_iff _ _).2 hd
  simpa [Nat.ascFactorial_eq_prod_range] using hz

end OMA.A105751

open OMA.A105751 in
theorem OMA.solution : OMA.R_OeisA105751_conjecture_variants_moll_p_mod_4_eq_1_R1.H1 := by
  intro p hp hm n
  let : Fact p.Prime := ⟨hp⟩
  let e := padicValNat p n.factorial
  change (p : ℤ) ^ e ∣ _
  cases he : e with
  | zero => simp
  | succ k =>
    let q := p ^ (k + 1)
    have : NeZero q := ⟨pow_ne_zero _ hp.ne_zero⟩
    obtain ⟨x, hx⟩ := roots_at_powers p hm k
    have hx' : (q : ℤ) ∣ x ^ 2 - (-1) := by simpa [q] using hx
    let r : ZMod q := x
    have hr : r * r = -1 := by
      have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).2 hx'
      push_cast at hz
      simpa [r, pow_two] using sub_eq_zero.mp hz
    have hd : q ∣ n.factorial := by
      change p ^ (k + 1) ∣ _
      rw [← he]
      exact pow_padicValNat_dvd
    have plus := eval_vanishes n hd r hr
    have minus := eval_vanishes n hd (-r) (by simpa using hr)
    have twice : 2 * ((Zg (n + 1)).im : ZMod q) = 0 := by
      linear_combination (-r) * plus + r * minus + (2 * ((Zg (n + 1)).im : ZMod q)) * hr
    have hunit : IsUnit (2 : ZMod q) := by
      apply (ZMod.isUnit_iff_coprime 2 q).2
      exact (Nat.prime_two.coprime_iff_not_dvd.mpr (by omega : ¬ 2 ∣ p)).pow_right _
    rw [a_eq]
    change (p : ℤ) ^ (k + 1) ∣ _
    rw [← Nat.cast_pow]
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).1
    exact hunit.mul_right_inj.mp (by simpa using twice)
