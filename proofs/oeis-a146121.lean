import OMAStatements.S_oeis_a146121

/-!
# Proof of Greubel's conjecture on A146121 (Bell numbers mod 31)

General argument for any prime `p`, then specialised to `p = 31`.
* The functional `L (∑ cᵢ Xⁱ) = ∑ cᵢ Bᵢ` on `𝔽_p[X]` satisfies `L (X f) = L (f (X + 1))`
  (the Bell recurrence), hence `L (X (X-1) ⋯ (X-p+1) g) = L (g (X + p)) = L g`. Since
  `X (X-1) ⋯ (X-p+1) = X^p - X` over `𝔽_p`, this is Touchard's congruence
  `B(n+p) ≡ B(n+1) + B(n)`.
* In `𝔽_p[X] / (X^p - X - 1)` Frobenius gives `x^(p^j) = x + j`, so
  `x^(1 + p + ⋯ + p^(p-1)) = ∏_j (x + j) = x^p - x = 1`. Thus `X^p - X - 1 ∣ X^N - 1`
  with `N = (p^p - 1)/(p - 1)`, and applying both polynomials to the shift operator on the
  sequence of Bell numbers mod `p` gives `B(n + N) ≡ B(n)`.
-/

namespace OMA.S_oeis_a146121.Proof

open Polynomial Finset

variable (p : ℕ) [hp : Fact p.Prime]

/-- Bell numbers in `ZMod p`. -/
def b (n : ℕ) : ZMod p := (Nat.bell n : ZMod p)

/-- The Bell functional `L (∑ cᵢ Xⁱ) = ∑ cᵢ Bᵢ`. -/
noncomputable def L : (ZMod p)[X] →ₗ[ZMod p] ZMod p :=
  Polynomial.lsum fun i => b p i • LinearMap.id

lemma L_monomial (n : ℕ) (c : ZMod p) : L p (monomial n c) = c * b p n := by
  simp [L, mul_comm]

lemma L_X_pow (n : ℕ) : L p (X ^ n) = b p n := by
  rw [← monomial_one_right_eq_X_pow, L_monomial, one_mul]

lemma bell_succ_sum (n : ℕ) :
    b p (n + 1) = ∑ k ∈ range (n + 1), (n.choose k : ZMod p) * b p k := by
  unfold b
  rw [Nat.bell_succ, ← Nat.range_succ_eq_Iic, ← sum_range_reflect]
  push_cast
  refine sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
  rw [Nat.choose_symm hk', show n - (n - k) = k by omega]

lemma L_X_mul (f : (ZMod p)[X]) : L p (X * f) = L p (f.comp (X + 1)) := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg => rw [mul_add, map_add, hf, hg, add_comp, map_add]
  | monomial n c =>
    rw [← C_mul_X_pow_eq_monomial, show X * (C c * X ^ n) = C c * X ^ (n + 1) by ring,
      mul_comp, C_comp, X_pow_comp, ← smul_eq_C_mul, ← smul_eq_C_mul, map_smul, map_smul,
      L_X_pow, add_pow, map_sum, bell_succ_sum]
    congr 1
    refine sum_congr rfl fun k _ => ?_
    rw [one_pow, mul_one, ← Nat.cast_comm, ← C_eq_natCast, ← smul_eq_C_mul, map_smul, L_X_pow,
      smul_eq_mul]

lemma L_prod (m : ℕ) (g : (ZMod p)[X]) :
    L p ((∏ j ∈ range m, (X - C (j : ZMod p))) * g) = L p (g.comp (X + C (m : ZMod p))) := by
  induction m generalizing g with
  | zero => simp
  | succ m ih =>
    rw [prod_range_succ', Nat.cast_zero, C_0, sub_zero,
      show (∏ j ∈ range m, (X - C ((j + 1 : ℕ) : ZMod p))) * X * g =
        X * ((∏ j ∈ range m, (X - C ((j + 1 : ℕ) : ZMod p))) * g) by ring,
      L_X_mul, mul_comp, Polynomial.prod_comp]
    have : ∀ j ∈ range m, (X - C ((j + 1 : ℕ) : ZMod p)).comp (X + 1) = X - C (j : ZMod p) := by
      intro j _; simp
    rw [prod_congr rfl this, ih, comp_assoc]
    congr 2
    simp; ring

/-- `∏_{a ∈ 𝔽_p} (X - a) = X^p - X`. -/
lemma prod_univ_X_sub_C : ∏ a : ZMod p, (X - C a) = X ^ p - X := by
  have hmon : (X ^ p - X : (ZMod p)[X]).Monic :=
    monic_X_pow_sub (by simpa using hp.out.one_lt)
  have hroots := FiniteField.roots_X_pow_card_sub_X (ZMod p)
  rw [ZMod.card] at hroots
  have hcard : Multiset.card (X ^ p - X : (ZMod p)[X]).roots =
      (X ^ p - X : (ZMod p)[X]).natDegree := by
    rw [hroots, FiniteField.X_pow_card_sub_X_natDegree_eq _ hp.out.one_lt]
    simp
  have := prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmon hcard
  rw [hroots] at this
  exact this

lemma prod_range_eq_univ (f : ZMod p → (ZMod p)[X]) :
    ∏ j ∈ range p, f (j : ZMod p) = ∏ a : ZMod p, f a := by
  have hinj : Set.InjOn (Nat.cast : ℕ → ZMod p) (range p) := by
    intro x hx y hy hxy
    simp only [coe_range, Set.mem_Iio] at hx hy
    rwa [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at hxy
  have himg : (range p).image (Nat.cast : ℕ → ZMod p) = univ := by
    apply eq_univ_of_card
    rw [card_image_of_injOn hinj, card_range, ZMod.card]
  rw [← himg, prod_image hinj]

lemma prod_range_X_sub_C : ∏ j ∈ range p, (X - C (j : ZMod p)) = X ^ p - X := by
  rw [prod_range_eq_univ p (fun a => X - C a), prod_univ_X_sub_C]

lemma prod_range_X_add_C : ∏ j ∈ range p, (X + C (j : ZMod p)) = X ^ p - X := by
  rw [prod_range_eq_univ p (fun a => X + C a), ← prod_univ_X_sub_C]
  exact Fintype.prod_equiv (Equiv.neg _) _ _ (fun a => by simp [sub_eq_add_neg])

/-- Touchard's congruence. -/
lemma touchard (n : ℕ) : b p (n + p) = b p (n + 1) + b p n := by
  have h := L_prod p p (X ^ n)
  rw [prod_range_X_sub_C, ZMod.natCast_self, C_0, add_zero, X_pow_comp] at h
  rw [sub_mul, ← pow_add, ← pow_succ', map_sub, L_X_pow, L_X_pow, L_X_pow,
    add_comm p n] at h
  rw [← h]; ring

/-- `X^p - X - 1` divides `X^N - 1` where `N = 1 + p + ... + p^(p-1)`. -/
lemma dvd_X_pow_sub_one :
    (X ^ p - X - 1 : (ZMod p)[X]) ∣ X ^ (∑ j ∈ range p, p ^ j) - 1 := by
  set q : (ZMod p)[X] := X ^ p - X - 1
  set π := Ideal.Quotient.mk (Ideal.span {q})
  have hq : π q = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
  have hXp : π X ^ p = π X + 1 := by
    have : π (X ^ p) = π (X + 1) := by
      rw [Ideal.Quotient.eq]; exact Ideal.subset_span (by simp [q]; ring)
    simpa using this
  have frob : ∀ j : ℕ, (X + C (j : ZMod p)) ^ p = X ^ p + C (j : ZMod p) := by
    intro j
    rw [add_pow_char, ← C_pow, ZMod.pow_card]
  have key : ∀ j : ℕ, π X ^ (p ^ j) = π (X + C (j : ZMod p)) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ, pow_mul, ih, ← map_pow, frob, map_add, map_pow, hXp, map_add]
      push_cast
      rw [C_add, map_add, C_1, map_one]; ring
  have hprod : π X ^ (∑ j ∈ range p, p ^ j) = 1 := by
    rw [← prod_pow_eq_pow_sum, prod_congr rfl fun j _ => key j, ← map_prod,
      prod_range_X_add_C]
    have : π (X ^ p - X) = π 1 := by
      rw [Ideal.Quotient.eq]; exact Ideal.subset_span (by simp [q])
    rw [this, map_one]
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, hprod,
    map_one, sub_self]

/-- The shift operator on sequences. -/
def E : Module.End (ZMod p) (ℕ → ZMod p) where
  toFun s n := s (n + 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma E_pow_apply (k : ℕ) (s : ℕ → ZMod p) (n : ℕ) : (E p ^ k) s n = s (n + k) := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply]
    show (E p ^ k) s (n + 1) = s (n + (k + 1))
    rw [ih]; congr 1; omega

theorem periodic (n : ℕ) : b p (n + ∑ j ∈ range p, p ^ j) = b p n := by
  obtain ⟨r, hr⟩ := dvd_X_pow_sub_one p
  have hzero : aeval (E p) (X ^ p - X - 1 : (ZMod p)[X]) (b p) = 0 := by
    ext m
    simp only [map_sub, map_pow, aeval_X, map_one, LinearMap.sub_apply, Module.End.one_apply,
      Pi.sub_apply, E_pow_apply, Pi.zero_apply]
    rw [show (E p) (b p) m = b p (m + 1) from rfl, touchard]; ring
  have h := congrArg (fun f => aeval (E p) f (b p) n) (hr.trans (mul_comm _ _))
  simp only [map_mul, Module.End.mul_apply, hzero, map_zero, Pi.zero_apply] at h
  simp only [map_sub, map_pow, aeval_X, map_one, LinearMap.sub_apply, Module.End.one_apply,
    Pi.sub_apply, E_pow_apply] at h
  exact sub_eq_zero.mp h

/-- The statement as OEIS states it, with `%`. -/
theorem bell_mod_periodic (n : ℕ) :
    Nat.bell (n + (p ^ p - 1) / (p - 1)) % p = Nat.bell n % p := by
  have := periodic p n
  rw [Nat.geomSum_eq hp.out.two_le] at this
  unfold b at this
  exact (ZMod.natCast_eq_natCast_iff' _ _ _).mp this

end OMA.S_oeis_a146121.Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a146121.main := by
  have : Fact (Nat.Prime 31) := ⟨by norm_num⟩
  intro n
  have h := OMA.S_oeis_a146121.Proof.bell_mod_periodic 31 n
  norm_num at h
  exact h
