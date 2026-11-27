import OMAReductions.R_Erdos978_erdos_978_parts_i_R1
import Mathlib

/-! An irreducible integer polynomial f is separable over Q, so a f + b f' = D for integer
polynomials a, b and a nonzero integer D. For primes p not dividing D and the leading
coefficient, two roots of f modulo p^k that agree modulo p agree modulo p^k (Taylor expansion,
f' is a unit at a root modulo p), so reduction modulo p embeds the roots modulo p^k into the
roots of f modulo p, of which there are at most deg f. -/

open Polynomial Finset Filter

namespace E978P2

/-- Integer Bezout identity between an irreducible integer polynomial and its derivative. -/
theorem bezout (f : ℤ[X]) (hf : Irreducible f) (hd : f.natDegree ≠ 0) :
    ∃ (a b : ℤ[X]) (D : ℤ), D ≠ 0 ∧ a * f + b * derivative f = C D := by
  have hprim : f.IsPrimitive := hf.isPrimitive hd
  have hQ : Irreducible (f.map (Int.castRingHom ℚ)) :=
    (IsPrimitive.Int.irreducible_iff_irreducible_map_cast hprim).mp hf
  obtain ⟨A, B, hAB⟩ := hQ.separable
  obtain ⟨bA, hbA, hA⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) A
  obtain ⟨bB, hbB, hB⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) B
  set A' := IsLocalization.integerNormalization (nonZeroDivisors ℤ) A
  set B' := IsLocalization.integerNormalization (nonZeroDivisors ℤ) B
  have hbA0 : bA ≠ 0 := nonZeroDivisors.ne_zero hbA
  have hbB0 : bB ≠ 0 := nonZeroDivisors.ne_zero hbB
  refine ⟨C bB * A', C bA * B', bA * bB, mul_ne_zero hbA0 hbB0, ?_⟩
  apply Polynomial.map_injective (Int.castRingHom ℚ) (RingHom.injective_int _)
  have hA2 : A'.map (Int.castRingHom ℚ) = C (bA : ℚ) * A := by
    rw [← algebraMap_int_eq, hA]; ext n; simp
  have hB2 : B'.map (Int.castRingHom ℚ) = C (bB : ℚ) * B := by
    rw [← algebraMap_int_eq, hB]; ext n; simp
  rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_mul,
    Polynomial.map_mul, Polynomial.map_C, Polynomial.map_C, Polynomial.map_C, hA2, hB2,
    ← Polynomial.derivative_map]
  simp only [Int.coe_castRingHom, Int.cast_mul]
  calc C (bB : ℚ) * (C (bA : ℚ) * A) * f.map (Int.castRingHom ℚ) +
        C (bA : ℚ) * (C (bB : ℚ) * B) * derivative (f.map (Int.castRingHom ℚ))
      = C ((bA : ℚ) * bB) * (A * f.map (Int.castRingHom ℚ) +
          B * derivative (f.map (Int.castRingHom ℚ))) := by rw [C_mul]; ring
    _ = C ((bA : ℚ) * bB) := by rw [hAB, mul_one]


theorem lift_dvd (f a b : ℤ[X]) (D : ℤ) (hab : a * f + b * derivative f = C D) (p : ℕ)
    (hp : p.Prime) (hpD : ¬ (p : ℤ) ∣ D) (k : ℕ) (hk : 1 ≤ k) (r s : ℕ)
    (hr : (p : ℤ) ^ k ∣ f.eval (r : ℤ)) (hs : (p : ℤ) ^ k ∣ f.eval (s : ℤ))
    (hrs : (p : ℤ) ∣ (s : ℤ) - r) : (p : ℤ) ^ k ∣ (s : ℤ) - r := by
  have hp' : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  set h : ℤ := (s : ℤ) - r with hh
  obtain ⟨c, hc⟩ := f.binomExpansion (r : ℤ) h
  have hrh : (r : ℤ) + h = s := by rw [hh]; ring
  rw [hrh] at hc
  have hpr : (p : ℤ) ∣ f.eval (r : ℤ) := (dvd_pow_self _ (by omega)).trans hr
  have hfr' : ¬ (p : ℤ) ∣ (derivative f).eval (r : ℤ) := by
    intro h1
    apply hpD
    have e := congrArg (eval (r : ℤ)) hab
    simp only [eval_add, eval_mul, eval_C] at e
    rw [← e]
    exact dvd_add (dvd_mul_of_dvd_right hpr _) (dvd_mul_of_dvd_right h1 _)
  have hdiff : (p : ℤ) ^ k ∣ h * ((derivative f).eval (r : ℤ) + c * h) := by
    have : h * ((derivative f).eval (r : ℤ) + c * h) = f.eval (s : ℤ) - f.eval (r : ℤ) := by
      rw [hc]; ring
    rw [this]; exact dvd_sub hs hr
  have main : ∀ i, i ≤ k → (p : ℤ) ^ i ∣ h := by
    intro i
    induction i with
    | zero => intro _; simp
    | succ i ih =>
      intro hi
      obtain ⟨u, hu⟩ := ih (by omega)
      have h1 : (p : ℤ) ^ i * (p : ℤ) ∣ (p : ℤ) ^ i * (u * ((derivative f).eval (r : ℤ) + c * h)) := by
        rw [← pow_succ, ← mul_assoc, ← hu]
        exact (pow_dvd_pow _ hi).trans hdiff
      have hp0 : (p : ℤ) ^ i ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.ne_zero)
      rw [mul_dvd_mul_iff_left hp0] at h1
      rcases hp'.dvd_or_dvd h1 with h2 | h2
      · rw [hu, pow_succ]; exact mul_dvd_mul_left _ h2
      · exfalso
        apply hfr'
        have : (p : ℤ) ∣ c * h := dvd_mul_of_dvd_right hrs _
        have := dvd_sub h2 this
        simpa using this
  exact main k le_rfl

theorem count_le (f a b : ℤ[X]) (D : ℤ) (hab : a * f + b * derivative f = C D) (p : ℕ)
    (hp : p.Prime) (hpD : ¬ (p : ℤ) ∣ D) (hlc : ¬ (p : ℤ) ∣ f.leadingCoeff) (k : ℕ) (hk : 1 ≤ k) :
    Nat.count (fun r : ℕ => (p : ℤ) ^ k ∣ f.eval (r : ℤ)) (p ^ k) ≤ f.natDegree := by
  classical
  have := Fact.mk hp
  rw [Nat.count_eq_card_filter_range]
  set S := (range (p ^ k)).filter (fun r : ℕ => (p : ℤ) ^ k ∣ f.eval (r : ℤ)) with hS
  have hne : f.map (Int.castRingHom (ZMod p)) ≠ 0 := by
    intro h0
    have e := congrArg (fun q => q.coeff f.natDegree) h0
    simp only [coeff_map, coeff_zero] at e
    apply hlc
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
    rw [Polynomial.leadingCoeff]
    exact e
  have hmaps : ∀ r ∈ S, ((r : ℕ) : ZMod p) ∈ (f.map (Int.castRingHom (ZMod p))).roots.toFinset := by
    intro r hr
    rw [Multiset.mem_toFinset, mem_roots hne, IsRoot.def]
    have hdv : (p : ℤ) ∣ f.eval (r : ℤ) := (dvd_pow_self _ (by omega)).trans (mem_filter.mp hr).2
    have e := eval_intCast_map (Int.castRingHom (ZMod p)) f (r : ℤ)
    rw [Int.cast_natCast] at e
    rw [e]
    simpa using (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hdv
  have hinj : Set.InjOn (fun r : ℕ => (r : ZMod p)) S := by
    intro r hr s hs hrs
    simp only at hrs
    have hr' := mem_filter.mp hr
    have hs' := mem_filter.mp hs
    have hd : (p : ℤ) ∣ (s : ℤ) - r := by
      apply (ZMod.intCast_eq_intCast_iff_dvd_sub (r : ℤ) (s : ℤ) p).mp
      rw [Int.cast_natCast, Int.cast_natCast]
      exact hrs
    have hk' := lift_dvd f a b D hab p hp hpD k hk r s hr'.2 hs'.2 hd
    have hm : (r : ℤ) ≡ s [ZMOD ((p ^ k : ℕ) : ℤ)] := by
      rw [Int.modEq_iff_dvd]; push_cast; exact hk'
    rw [Int.natCast_modEq_iff] at hm
    exact hm.eq_of_lt_of_lt (mem_range.mp hr'.1) (mem_range.mp hs'.1)
  calc S.card = (S.image (fun r : ℕ => (r : ZMod p))).card := (card_image_of_injOn hinj).symm
    _ ≤ (f.map (Int.castRingHom (ZMod p))).roots.toFinset.card := card_le_card (fun x hx => by
          obtain ⟨r, hr, rfl⟩ := mem_image.mp hx; exact hmaps r hr)
    _ ≤ Multiset.card (f.map (Int.castRingHom (ZMod p))).roots := Multiset.toFinset_card_le _
    _ ≤ (f.map (Int.castRingHom (ZMod p))).natDegree := card_roots' _
    _ ≤ f.natDegree := natDegree_map_le

end E978P2

open E978P2 in
theorem OMA.solution : OMA.R_Erdos978_erdos_978_parts_i_R1.H1 := by
  unfold OMA.R_Erdos978_erdos_978_parts_i_R1.H1
  intro f hf hd
  obtain ⟨a, b, D, hD, hab⟩ := bezout f hf (by omega)
  have hf0 : f ≠ 0 := hf.ne_zero
  have hlc0 : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hf0
  filter_upwards [eventually_gt_atTop (D.natAbs * f.leadingCoeff.natAbs)] with p hpbig hp
  have hDa : 0 < D.natAbs := Int.natAbs_pos.mpr hD
  have hLa : 0 < f.leadingCoeff.natAbs := Int.natAbs_pos.mpr hlc0
  apply count_le f a b D hab p hp _ _ _ (by omega)
  · intro h
    have h1 := Nat.le_of_dvd hDa (Int.natCast_dvd.mp h)
    have : D.natAbs ≤ D.natAbs * f.leadingCoeff.natAbs := Nat.le_mul_of_pos_right _ hLa
    omega
  · intro h
    have h1 := Nat.le_of_dvd hLa (Int.natCast_dvd.mp h)
    have : f.leadingCoeff.natAbs ≤ D.natAbs * f.leadingCoeff.natAbs := Nat.le_mul_of_pos_left _ hDa
    omega

