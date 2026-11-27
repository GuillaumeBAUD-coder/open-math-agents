import FormalConjectures.Other.SymbolLengthMilnorKTheory

-- Problem: the lower bound m - 1 for the symbol length of K_2(C(x_1, ..., x_m))/p
-- (Becher and Hoffmann, Proposition 4.5).
-- Upstream: formal-conjectures FormalConjectures/Other/SymbolLengthMilnorKTheory.lean
-- (declaration SymbolLengthMilnorKTheory.symbol_length_problem.variants.degree_two_ge)
--
-- Proof. Write m = n + 1 and view C[x_0, ..., x_n] as polynomials in x_1, ..., x_n over C[x_0].
-- For a monomial order, the exponents w_1, ..., w_n of the leading monomial, and the order of
-- vanishing v_i at x_0 = i of the leading coefficient, extend to homomorphisms from the units of
-- the fraction field to the integers. If a + b = 1 then, for each i, the vectors
-- (w(a), v_i(a)) and (w(b), v_i(b)) are equal or one of them vanishes (ultrametric trichotomy),
-- so every pair (L, M) taken among w_1, ..., w_n, v_i gives a map K_2/p -> Z/p sending the
-- symbol of a, b to L(a) M(b) - M(a) L(b); it is built from a ring homomorphism to 4 x 4
-- matrices over Z/p. Evaluating these maps on the sum over j of the symbols of x_0 - j, x_j,
-- written as a sum of k symbols, shows that a 2n x 2n alternating matrix which factors through
-- a space of dimension 2k has the block form [0, -1; 1, *]. That matrix is invertible, so
-- 2n <= 2k.

namespace OMA.SL

open MilnorK MvPolynomial

theorem exists_hom {R F : Type*} [CommRing R] [IsDomain R] [Field F] [Algebra R F]
    [IsFractionRing R F] (l : R → ℤ)
    (hl : ∀ f g : R, f ≠ 0 → g ≠ 0 → l (f * g) = l f + l g) :
    ∃ L : Additive Fˣ →+ ℤ, ∀ (u : Fˣ) (n d : R), d ≠ 0 →
      (u : F) * algebraMap R F d = algebraMap R F n → L (Additive.ofMul u) = l n - l d := by
  have hinj : Function.Injective (algebraMap R F) := IsFractionRing.injective R F
  have hex : ∀ u : Fˣ, ∃ nd : R × R, nd.2 ≠ 0 ∧
      (u : F) * algebraMap R F nd.2 = algebraMap R F nd.1 := by
    intro u
    obtain ⟨n, d, hd, hnd⟩ := IsFractionRing.div_surjective (A := R) (u : F)
    have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
    refine ⟨(n, d), hd0, ?_⟩
    have : algebraMap R F d ≠ 0 := (map_ne_zero_iff _ hinj).mpr hd0
    rw [← hnd]
    field_simp
  choose nd hnd0 hndeq using hex
  have hnum : ∀ (u : Fˣ) (n d : R), d ≠ 0 → (u : F) * algebraMap R F d = algebraMap R F n →
      n ≠ 0 := by
    rintro u n d hd h rfl
    rw [map_zero] at h
    exact (mul_ne_zero u.ne_zero ((map_ne_zero_iff _ hinj).mpr hd)) h
  have key : ∀ (u : Fˣ) (n d : R), d ≠ 0 → (u : F) * algebraMap R F d = algebraMap R F n →
      l (nd u).1 - l (nd u).2 = l n - l d := by
    intro u n d hd h
    have hn : n ≠ 0 := hnum u n d hd h
    have hn' : (nd u).1 ≠ 0 := hnum u _ _ (hnd0 u) (hndeq u)
    have heq : n * (nd u).2 = (nd u).1 * d := by
      apply hinj
      rw [map_mul, map_mul, ← h, ← hndeq u]
      ring
    have := congrArg l heq
    rw [hl _ _ hn (hnd0 u), hl _ _ hn' hd] at this
    linarith
  refine ⟨AddMonoidHom.mk' (fun a => l (nd a.toMul).1 - l (nd a.toMul).2) ?_, ?_⟩
  · intro a b
    have h1 := hndeq a.toMul
    have h2 := hndeq b.toMul
    have hprod : (((a + b).toMul : Fˣ) : F) *
        algebraMap R F ((nd a.toMul).2 * (nd b.toMul).2) =
        algebraMap R F ((nd a.toMul).1 * (nd b.toMul).1) := by
      rw [map_mul, map_mul, ← h1, ← h2, toMul_add, Units.val_mul]
      ring
    have := key (a + b).toMul _ _ (mul_ne_zero (hnd0 _) (hnd0 _)) hprod
    show l (nd (a + b).toMul).1 - l (nd (a + b).toMul).2 =
      (l (nd a.toMul).1 - l (nd a.toMul).2) + (l (nd b.toMul).1 - l (nd b.toMul).2)
    rw [this, hl _ _ (hnum _ _ _ (hnd0 _) h1) (hnum _ _ _ (hnd0 _) h2),
      hl _ _ (hnd0 _) (hnd0 _)]
    ring
  · intro u n d hd h
    exact key u n d hd h

theorem steinberg_of_trichotomy {R F : Type*} [CommRing R] [IsDomain R] [Field F] [Algebra R F]
    [IsFractionRing R F] (l1 l2 : R → ℤ) (L1 L2 : Additive Fˣ →+ ℤ)
    (h1 : ∀ (u : Fˣ) (n d : R), d ≠ 0 →
      (u : F) * algebraMap R F d = algebraMap R F n → L1 (Additive.ofMul u) = l1 n - l1 d)
    (h2 : ∀ (u : Fˣ) (n d : R), d ≠ 0 →
      (u : F) * algebraMap R F d = algebraMap R F n → L2 (Additive.ofMul u) = l2 n - l2 d)
    (htri : ∀ f g : R, f ≠ 0 → g ≠ 0 → f + g ≠ 0 →
      (l1 f = l1 g ∧ l2 f = l2 g) ∨ (l1 (f + g) = l1 f ∧ l2 (f + g) = l2 f) ∨
        (l1 (f + g) = l1 g ∧ l2 (f + g) = l2 g))
    (a b : Fˣ) (hab : (a : F) + (b : F) = 1) :
    L1 (Additive.ofMul a) * L2 (Additive.ofMul b) =
      L2 (Additive.ofMul a) * L1 (Additive.ofMul b) := by
  have hinj : Function.Injective (algebraMap R F) := IsFractionRing.injective R F
  obtain ⟨n, d, hd, hnd⟩ := IsFractionRing.div_surjective (A := R) (a : F)
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  have hd' : algebraMap R F d ≠ 0 := (map_ne_zero_iff _ hinj).mpr hd0
  have ha : (a : F) * algebraMap R F d = algebraMap R F n := by
    rw [← hnd]
    field_simp
  have hb : (b : F) * algebraMap R F d = algebraMap R F (d - n) := by
    have : (b : F) = 1 - (a : F) := by rw [← hab]; ring
    rw [this, map_sub, ← ha]
    ring
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [map_zero] at ha
    exact (mul_ne_zero a.ne_zero hd') ha
  have hm0 : d - n ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hb
    exact (mul_ne_zero b.ne_zero hd') hb
  have hsum : n + (d - n) = d := by ring
  have hs0 : n + (d - n) ≠ 0 := by rw [hsum]; exact hd0
  rw [h1 a n d hd0 ha, h2 a n d hd0 ha, h1 b (d - n) d hd0 hb, h2 b (d - n) d hd0 hb]
  rcases htri n (d - n) hn0 hm0 hs0 with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩
  · rw [e1, e2]
    ring
  · rw [hsum] at e1 e2
    rw [e1, e2]
    ring
  · rw [hsum] at e1 e2
    rw [e1, e2]
    ring

theorem mat_add {S : Type*} [CommRing S] (l m l' m' : S) :
    (!![0, l + l', -(m + m'), 0; 0, 0, 0, m + m'; 0, 0, 0, l + l'; 0, 0, 0, 0] :
      Matrix (Fin 4) (Fin 4) S) =
    !![0, l, -m, 0; 0, 0, 0, m; 0, 0, 0, l; 0, 0, 0, 0] +
      !![0, l', -m', 0; 0, 0, 0, m'; 0, 0, 0, l'; 0, 0, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

theorem mat_mul {S : Type*} [CommRing S] (l m l' m' : S) :
    (!![0, l, -m, 0; 0, 0, 0, m; 0, 0, 0, l; 0, 0, 0, 0] : Matrix (Fin 4) (Fin 4) S) *
      !![0, l', -m', 0; 0, 0, 0, m'; 0, 0, 0, l'; 0, 0, 0, 0] =
    !![0, 0, 0, l * m' - m * l'; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem mat_zero {S : Type*} [CommRing S] :
    (!![0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0] : Matrix (Fin 4) (Fin 4) S) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem exists_symbol_map {F : Type*} [Field F] (p : ℕ) (L M : Additive Fˣ →+ ℤ)
    (hst : ∀ a b : Fˣ, (a : F) + (b : F) = 1 →
      L (Additive.ofMul a) * M (Additive.ofMul b) =
        M (Additive.ofMul a) * L (Additive.ofMul b)) :
    ∃ Φ : MilnorK F p →+ ZMod p, ∀ a b : Fˣ, Φ (MilnorK.of p a * MilnorK.of p b) =
      ((L (Additive.ofMul a) * M (Additive.ofMul b) -
        M (Additive.ofMul a) * L (Additive.ofMul b) : ℤ) : ZMod p) := by
  obtain ⟨G, hGdef⟩ : ∃ G : Additive Fˣ →+ Matrix (Fin 4) (Fin 4) (ZMod p), ∀ a, G a =
      !![0, (L a : ZMod p), -(M a : ZMod p), 0;
        0, 0, 0, (M a : ZMod p); 0, 0, 0, (L a : ZMod p); 0, 0, 0, 0] := by
    refine ⟨AddMonoidHom.mk' (fun a => !![0, (L a : ZMod p), -(M a : ZMod p), 0;
      0, 0, 0, (M a : ZMod p); 0, 0, 0, (L a : ZMod p); 0, 0, 0, 0]) ?_, fun a => rfl⟩
    intro a b
    rw [← mat_add, map_add, map_add, Int.cast_add, Int.cast_add]
  have hG : ∀ a b : Additive Fˣ, G a * G b =
      !![0, 0, 0, ((L a * M b - M a * L b : ℤ) : ZMod p);
        0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0] := by
    intro a b
    rw [hGdef, hGdef, mat_mul]
    push_cast
    rfl
  have hrel : ∀ ⦃x y : TensorAlgebra ℤ (Additive Fˣ)⦄, MilnorK.Rel F p x y →
      (TensorAlgebra.lift ℤ G.toIntLinearMap).toRingHom x =
        (TensorAlgebra.lift ℤ G.toIntLinearMap).toRingHom y := by
    intro x y h
    cases h with
    | steinberg a b h =>
      have h0 := hst a b h
      have h3 := hG (Additive.ofMul a) (Additive.ofMul b)
      rw [h0, sub_self, Int.cast_zero, mat_zero] at h3
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_mul, TensorAlgebra.lift_ι_apply,
        AddMonoidHom.coe_toIntLinearMap, map_zero]
      exact h3
    | natCast =>
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_natCast, map_zero]
      ext i j
      simp [Matrix.natCast_apply]
  have hρ : ∀ a : Fˣ, RingQuot.lift ⟨(TensorAlgebra.lift ℤ G.toIntLinearMap).toRingHom, hrel⟩
      (MilnorK.of p a) = G (Additive.ofMul a) := by
    intro a
    simp [MilnorK.of, RingQuot.lift_mkRingHom_apply]
  refine ⟨AddMonoidHom.mk' (fun x =>
    RingQuot.lift ⟨(TensorAlgebra.lift ℤ G.toIntLinearMap).toRingHom, hrel⟩ x 0 3)
    (by intro x y; simp [map_add]), ?_⟩
  intro a b
  show RingQuot.lift ⟨(TensorAlgebra.lift ℤ G.toIntLinearMap).toRingHom, hrel⟩
    (MilnorK.of p a * MilnorK.of p b) 0 3 = _
  rw [map_mul, hρ, hρ, hG]
  simp

theorem rm_neg (a : ℂ) (Q : Polynomial ℂ) :
    (-Q).rootMultiplicity a = Q.rootMultiplicity a := by
  by_cases hQ : Q = 0
  · simp [hQ]
  · have h : Polynomial.C (-1 : ℂ) * Q ≠ 0 := mul_ne_zero (by simp) hQ
    have h2 := Polynomial.rootMultiplicity_mul (x := a) h
    rw [Polynomial.rootMultiplicity_C, zero_add] at h2
    rw [← h2]
    congr 1
    simp

theorem rm_add_of_lt (a : ℂ) (P Q : Polynomial ℂ) (hP : P ≠ 0) (hPQ : P + Q ≠ 0)
    (h : P.rootMultiplicity a < Q.rootMultiplicity a) :
    (P + Q).rootMultiplicity a = P.rootMultiplicity a := by
  have h1 := Polynomial.rootMultiplicity_add a hPQ
  have e : (P + Q) + (-Q) = P := by ring
  have hP' : (P + Q) + (-Q) ≠ 0 := by rw [e]; exact hP
  have h2 := Polynomial.rootMultiplicity_add a hP'
  rw [rm_neg, e] at h2
  rcases min_le_iff.mp h1 with h3 | h3 <;> rcases min_le_iff.mp h2 with h4 | h4 <;> omega

theorem tri {σ : Type*} (m : MonomialOrder σ) (a : ℂ) (f g : MvPolynomial σ (Polynomial ℂ))
    (hf : f ≠ 0) (hg : g ≠ 0) :
    (m.degree f = m.degree g ∧
      (m.leadingCoeff f).rootMultiplicity a = (m.leadingCoeff g).rootMultiplicity a) ∨
    (m.degree (f + g) = m.degree f ∧
      (m.leadingCoeff (f + g)).rootMultiplicity a = (m.leadingCoeff f).rootMultiplicity a) ∨
    (m.degree (f + g) = m.degree g ∧
      (m.leadingCoeff (f + g)).rootMultiplicity a = (m.leadingCoeff g).rootMultiplicity a) := by
  have hlf : m.leadingCoeff f ≠ 0 := m.leadingCoeff_ne_zero_iff.mpr hf
  have hlg : m.leadingCoeff g ≠ 0 := m.leadingCoeff_ne_zero_iff.mpr hg
  rcases lt_trichotomy (m.toSyn (m.degree f)) (m.toSyn (m.degree g)) with h | h | h
  · right; right
    refine ⟨m.degree_add_eq_right_of_lt h, ?_⟩
    rw [add_comm, m.leadingCoeff_add_of_lt h]
  · have hd : m.degree f = m.degree g := m.toSyn.injective h
    by_cases hc : m.leadingCoeff f + m.leadingCoeff g = 0
    · left
      refine ⟨hd, ?_⟩
      have h2 : m.leadingCoeff f = -m.leadingCoeff g := eq_neg_of_add_eq_zero_left hc
      rw [h2, rm_neg]
    · have hcoeff : (f + g).coeff (m.degree f) = m.leadingCoeff f + m.leadingCoeff g := by
        have e1 : m.leadingCoeff f = f.coeff (m.degree f) := rfl
        have e2 : m.leadingCoeff g = g.coeff (m.degree f) := by rw [hd]; rfl
        rw [coeff_add, e1, e2]
      have hdeg : m.degree (f + g) = m.degree f := by
        apply m.toSyn.injective
        apply le_antisymm
        · have h3 := m.degree_add_le (f := f) (g := g)
          rw [← h, sup_idem] at h3
          exact h3
        · apply m.le_degree
          rw [mem_support_iff, hcoeff]
          exact hc
      have hlc : m.leadingCoeff (f + g) = m.leadingCoeff f + m.leadingCoeff g := by
        rw [← hcoeff, ← hdeg]
        rfl
      rcases lt_trichotomy ((m.leadingCoeff f).rootMultiplicity a)
        ((m.leadingCoeff g).rootMultiplicity a) with h' | h' | h'
      · right; left
        refine ⟨hdeg, ?_⟩
        rw [hlc]
        exact rm_add_of_lt a _ _ hlf hc h'
      · left
        exact ⟨hd, h'⟩
      · right; right
        refine ⟨hdeg.trans hd, ?_⟩
        rw [hlc, add_comm]
        exact rm_add_of_lt a _ _ hlg (by rwa [add_comm]) h'
  · right; left
    exact ⟨m.degree_add_of_lt h, by rw [m.leadingCoeff_add_of_lt h]⟩

theorem lower_bound_abstract {R F : Type*} [CommRing R] [IsDomain R] [Field F] [Algebra R F]
    [IsFractionRing R F] (n : ℕ) (e : R →+* MvPolynomial (Fin n) (Polynomial ℂ))
    (he : Function.Injective e) (g y : Fin n → R)
    (hg : ∀ j : Fin n, e (g j) = C (Polynomial.X - Polynomial.C ((j : ℕ) : ℂ)))
    (hy : ∀ j : Fin n, e (y j) = X j) (p : ℕ) (hp : p.Prime) (k : ℕ)
    (hk : k ∈ symbolLengthBounds F p 2) : n ≤ k := by
  have : Fact p.Prime := ⟨hp⟩
  have hinj : Function.Injective (algebraMap R F) := IsFractionRing.injective R F
  obtain ⟨m⟩ : Nonempty (MonomialOrder (Fin n)) := ⟨MonomialOrder.lex⟩
  have he0 : ∀ f : R, f ≠ 0 → e f ≠ 0 := fun f hf => (map_ne_zero_iff e he).mpr hf
  have hLw : ∀ j : Fin n, ∃ L : Additive Fˣ →+ ℤ, ∀ (u : Fˣ) (nn d : R), d ≠ 0 →
      (u : F) * algebraMap R F d = algebraMap R F nn →
      L (Additive.ofMul u) = ((m.degree (e nn) j : ℕ) : ℤ) - ((m.degree (e d) j : ℕ) : ℤ) := by
    intro j
    exact exists_hom (fun f => ((m.degree (e f) j : ℕ) : ℤ)) (by
      intro f g hf hg
      rw [map_mul, m.degree_mul (he0 f hf) (he0 g hg)]
      simp)
  have hLv : ∀ i : Fin n, ∃ L : Additive Fˣ →+ ℤ, ∀ (u : Fˣ) (nn d : R), d ≠ 0 →
      (u : F) * algebraMap R F d = algebraMap R F nn →
      L (Additive.ofMul u) =
        (((m.leadingCoeff (e nn)).rootMultiplicity ((i : ℕ) : ℂ) : ℕ) : ℤ) -
          (((m.leadingCoeff (e d)).rootMultiplicity ((i : ℕ) : ℂ) : ℕ) : ℤ) := by
    intro i
    exact exists_hom
      (fun f => (((m.leadingCoeff (e f)).rootMultiplicity ((i : ℕ) : ℂ) : ℕ) : ℤ)) (by
      intro f g hf hg
      have h1 : m.leadingCoeff (e f) * m.leadingCoeff (e g) ≠ 0 :=
        mul_ne_zero (m.leadingCoeff_ne_zero_iff.mpr (he0 f hf))
          (m.leadingCoeff_ne_zero_iff.mpr (he0 g hg))
      rw [map_mul, m.leadingCoeff_mul, Polynomial.rootMultiplicity_mul h1]
      simp)
  choose Lw hLw using hLw
  choose Lv hLv using hLv
  have hΦww : ∀ j j2 : Fin n, ∃ Φ : MilnorK F p →+ ZMod p, ∀ a b : Fˣ,
      Φ (MilnorK.of p a * MilnorK.of p b) =
        ((Lw j (Additive.ofMul a) * Lw j2 (Additive.ofMul b) -
          Lw j2 (Additive.ofMul a) * Lw j (Additive.ofMul b) : ℤ) : ZMod p) := by
    intro j j2
    refine exists_symbol_map p (Lw j) (Lw j2) ?_
    refine steinberg_of_trichotomy (fun f => ((m.degree (e f) j : ℕ) : ℤ))
      (fun f => ((m.degree (e f) j2 : ℕ) : ℤ)) (Lw j) (Lw j2) (hLw j) (hLw j2) ?_
    intro f g hf hg _
    rcases tri m 0 (e f) (e g) (he0 f hf) (he0 g hg) with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
    · left
      simp only [h1, and_self]
    · right; left
      simp only [map_add, h1, and_self]
    · right; right
      simp only [map_add, h1, and_self]
  have hΦwv : ∀ j i : Fin n, ∃ Φ : MilnorK F p →+ ZMod p, ∀ a b : Fˣ,
      Φ (MilnorK.of p a * MilnorK.of p b) =
        ((Lw j (Additive.ofMul a) * Lv i (Additive.ofMul b) -
          Lv i (Additive.ofMul a) * Lw j (Additive.ofMul b) : ℤ) : ZMod p) := by
    intro j i
    refine exists_symbol_map p (Lw j) (Lv i) ?_
    refine steinberg_of_trichotomy (fun f => ((m.degree (e f) j : ℕ) : ℤ))
      (fun f => (((m.leadingCoeff (e f)).rootMultiplicity ((i : ℕ) : ℂ) : ℕ) : ℤ))
      (Lw j) (Lv i) (hLw j) (hLv i) ?_
    intro f g hf hg _
    rcases tri m ((i : ℕ) : ℂ) (e f) (e g) (he0 f hf) (he0 g hg) with
      ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      simp only [h1, h2, and_self]
    · right; left
      simp only [map_add, h1, h2, and_self]
    · right; right
      simp only [map_add, h1, h2, and_self]
  choose Φww hΦww using hΦww
  choose Φwv hΦwv using hΦwv
  have hg0 : ∀ l : Fin n, g l ≠ 0 := by
    intro l h
    have h1 := hg l
    rw [h, map_zero] at h1
    have h2 : (Polynomial.X - Polynomial.C ((l : ℕ) : ℂ)) = 0 :=
      C_injective (Fin n) (Polynomial ℂ) (h1.symm.trans (map_zero C).symm)
    exact Polynomial.X_sub_C_ne_zero _ h2
  have hy0 : ∀ l : Fin n, y l ≠ 0 := by
    intro l h
    have h1 := hy l
    rw [h, map_zero] at h1
    exact X_ne_zero l h1.symm
  obtain ⟨gu, hgu⟩ : ∃ gu : Fin n → Fˣ, ∀ l, (gu l : F) = algebraMap R F (g l) :=
    ⟨fun l => Units.mk0 _ ((map_ne_zero_iff _ hinj).mpr (hg0 l)), fun l => rfl⟩
  obtain ⟨yu, hyu⟩ : ∃ yu : Fin n → Fˣ, ∀ l, (yu l : F) = algebraMap R F (y l) :=
    ⟨fun l => Units.mk0 _ ((map_ne_zero_iff _ hinj).mpr (hy0 l)), fun l => rfl⟩
  have vw_g : ∀ j l : Fin n, Lw j (Additive.ofMul (gu l)) = 0 := by
    intro j l
    rw [hLw j (gu l) (g l) 1 one_ne_zero (by rw [hgu, map_one, mul_one]), hg, map_one,
      MonomialOrder.degree_C, MonomialOrder.degree_one]
    simp
  have vw_y : ∀ j l : Fin n, Lw j (Additive.ofMul (yu l)) = if l = j then 1 else 0 := by
    intro j l
    rw [hLw j (yu l) (y l) 1 one_ne_zero (by rw [hyu, map_one, mul_one]), hy, map_one,
      MonomialOrder.degree_X, MonomialOrder.degree_one, Finsupp.single_apply]
    split_ifs <;> simp
  have vv_g : ∀ i l : Fin n, Lv i (Additive.ofMul (gu l)) = if i = l then 1 else 0 := by
    intro i l
    rw [hLv i (gu l) (g l) 1 one_ne_zero (by rw [hgu, map_one, mul_one]), hg, map_one,
      MonomialOrder.leadingCoeff_C, MonomialOrder.leadingCoeff_one,
      Polynomial.rootMultiplicity_X_sub_C, ← Polynomial.C_1, Polynomial.rootMultiplicity_C]
    have hiff : (((i : ℕ) : ℂ) = ((l : ℕ) : ℂ)) ↔ i = l := by
      rw [Nat.cast_inj, Fin.val_inj]
    simp only [hiff]
    split_ifs <;> simp
  have vv_y : ∀ i l : Fin n, Lv i (Additive.ofMul (yu l)) = 0 := by
    intro i l
    rw [hLv i (yu l) (y l) 1 one_ne_zero (by rw [hyu, map_one, mul_one]), hy, map_one,
      MonomialOrder.leadingCoeff_X, MonomialOrder.leadingCoeff_one,
      ← Polynomial.C_1, Polynomial.rootMultiplicity_C]
    simp
  have hξ : (∑ l, MilnorK.of p (gu l) * MilnorK.of p (yu l)) ∈ MilnorK.grade F p 2 := by
    refine sum_mem fun l _ => ?_
    rw [← symbol_pair]
    exact symbol_mem_grade F p _
  obtain ⟨k2, hk2, s, hs⟩ := hk _ hξ
  have hsym : ∀ t, symbol p (s t) = MilnorK.of p (s t 0) * MilnorK.of p (s t 1) := by
    intro t
    simp [symbol_succ]
  simp only [hsym] at hs
  obtain ⟨H, hH1, hH2⟩ : ∃ H : Fin n ⊕ Fin n → Additive Fˣ →+ ℤ,
      (∀ j, H (Sum.inl j) = Lw j) ∧ (∀ i, H (Sum.inr i) = Lv i) :=
    ⟨Sum.elim Lw Lv, fun j => rfl, fun i => rfl⟩
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (ZMod p), ∀ r r2, M r r2 =
      ∑ t, ((H r (Additive.ofMul (s t 0)) * H r2 (Additive.ofMul (s t 1)) -
        H r2 (Additive.ofMul (s t 0)) * H r (Additive.ofMul (s t 1)) : ℤ) : ZMod p) :=
    ⟨Matrix.of fun r r2 => ∑ t, ((H r (Additive.ofMul (s t 0)) * H r2 (Additive.ofMul (s t 1)) -
        H r2 (Additive.ofMul (s t 0)) * H r (Additive.ofMul (s t 1)) : ℤ) : ZMod p),
      fun r r2 => rfl⟩
  have hrank : M.rank ≤ Fintype.card (Fin k2 ⊕ Fin k2) := by
    have hfact : M = Matrix.fromCols
        (Matrix.of fun r t => ((H r (Additive.ofMul (s t 0)) : ℤ) : ZMod p))
        (Matrix.of fun r t => ((H r (Additive.ofMul (s t 1)) : ℤ) : ZMod p)) *
        Matrix.fromRows
        (Matrix.of fun t r => ((H r (Additive.ofMul (s t 1)) : ℤ) : ZMod p))
        (Matrix.of fun t r => -((H r (Additive.ofMul (s t 0)) : ℤ) : ZMod p)) := by
      ext r r2
      rw [hM, Matrix.fromCols_mul_fromRows, Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun t _ => ?_
      simp only [Matrix.of_apply]
      push_cast
      ring
    rw [hfact]
    exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_card_width _)
  have c1 : ∀ j j2 : Fin n, M (Sum.inl j) (Sum.inl j2) = 0 := by
    intro j j2
    have h1 := congrArg (Φww j j2) hs
    rw [map_sum, map_sum] at h1
    simp only [hΦww, vw_g] at h1
    rw [hM]
    simp only [hH1]
    rw [← h1]
    simp
  have c2 : ∀ j i : Fin n, M (Sum.inl j) (Sum.inr i) = if j = i then -1 else 0 := by
    intro j i
    have h1 := congrArg (Φwv j i) hs
    rw [map_sum, map_sum] at h1
    simp only [hΦwv, vw_g, vw_y, vv_g, vv_y] at h1
    rw [hM]
    simp only [hH1, hH2]
    rw [← h1]
    by_cases hji : j = i
    · subst hji
      simp
    · have hij : ¬ i = j := fun h => hji h.symm
      simp [hji, hij]
  have c3 : ∀ r r2, M r2 r = -M r r2 := by
    intro r r2
    rw [hM, hM, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    push_cast
    ring
  have hblocks : M = Matrix.fromBlocks 0 (-1) 1 M.toBlocks₂₂ := by
    ext r r2
    rcases r with j | i <;> rcases r2 with j2 | i2
    · simp [c1]
    · rw [c2]
      by_cases h : j = i2 <;> simp [h, Matrix.one_apply]
    · rw [c3, c2]
      by_cases h : j2 = i
      · subst h
        simp
      · have h2 : ¬ i = j2 := fun hh => h hh.symm
        simp [h, h2, Matrix.one_apply]
    · rfl
  have hone : M * Matrix.fromBlocks M.toBlocks₂₂ 1 (-1) 0 = 1 := by
    conv_lhs => rw [hblocks]
    rw [Matrix.fromBlocks_multiply]
    simp [Matrix.fromBlocks_one]
  have h2n : 2 * n ≤ 2 * k2 := by
    calc 2 * n = Fintype.card (Fin n ⊕ Fin n) := by simp; ring
      _ = (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (ZMod p)).rank := Matrix.rank_one.symm
      _ = (M * Matrix.fromBlocks M.toBlocks₂₂ 1 (-1) 0).rank := by rw [hone]
      _ ≤ M.rank := Matrix.rank_mul_le_left _ _
      _ ≤ Fintype.card (Fin k2 ⊕ Fin k2) := hrank
      _ = 2 * k2 := by simp; ring
  omega

theorem lower_bound (m : ℕ) (hm : 1 ≤ m) (p : ℕ) (hp : p.Prime) :
    ∀ k ∈ symbolLengthBounds (MvRatFunc (Fin m) ℂ) p 2, m - 1 ≤ k := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  intro k hk
  rw [Nat.add_sub_cancel]
  refine lower_bound_abstract (R := MvPolynomial (Fin (n + 1)) ℂ) (F := MvRatFunc (Fin (n + 1)) ℂ) n
    (((renameEquiv ℂ (_root_.finSuccEquiv n)).trans (optionEquivRight ℂ (Fin n))).toAlgHom.toRingHom)
    (AlgEquiv.injective _) (fun j => X 0 - C ((j : ℕ) : ℂ)) (fun j => X j.succ) ?_ ?_ p hp k hk
  · intro j
    simp [optionEquivRight_X_none, optionEquivRight_C]
  · intro j
    simp [optionEquivRight_X_some]

end OMA.SL

theorem OMA.solution : type_of% @SymbolLengthMilnorKTheory.symbol_length_problem.variants.degree_two_ge := by
  intro m hm p hp k hk
  exact OMA.SL.lower_bound m hm p hp k hk
