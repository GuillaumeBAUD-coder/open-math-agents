import FormalConjectures.OEIS.«226163»

/-!
# The determinant of the Legendre symbol matrix

Sun proposed this conjecture in 2013. The OEIS Open project proved it in 2026
([arXiv:2608.11941](https://arxiv.org/abs/2608.11941)).

Write `m = (p - 1) / 2` and `c = m!`. For even `m`, Wilson’s theorem gives
`c² = -1`. Interpolation and a Vandermonde matrix then show that the determinant is
nonzero modulo `p`. For odd `m`, reindex by the nonzero squares and split the entries
into two commuting character matrices. One is symmetric and the other is skew-symmetric.
Their sum gives a normal integer matrix to which the signed determinant identity applies.

Credit: @MrSeizy
-/

open Matrix Polynomial Finset

/-- A normal matrix and its transpose have the same null vectors over the integers. -/
private lemma shared_null {ι : Type*} [Fintype ι] (U : Matrix ι ι ℤ)
    (normal : Uᵀ * U = U * Uᵀ) {v : ι → ℤ} (hv : v ᵥ* U = 0) : v ᵥ* Uᵀ = 0 := by
  rw [vecMul_transpose]
  apply dotProduct_self_eq_zero.mp
  calc
    (U *ᵥ v) ⬝ᵥ (U *ᵥ v) = v ⬝ᵥ (Uᵀ *ᵥ (U *ᵥ v)) := by
      symm
      rw [dotProduct_mulVec, vecMul_transpose]
    _ = v ⬝ᵥ (U *ᵥ (Uᵀ *ᵥ v)) := by rw [mulVec_mulVec, normal, ← mulVec_mulVec]
    _ = 0 := by rw [mulVec_transpose, hv, mulVec_zero, dotProduct_zero]

/-- An odd-dimensional normal matrix gives a singular difference after a symmetric involution of determinant one. -/
private lemma det_normal_signed {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U D : Matrix ι ι ℤ) (normal : Uᵀ * U = U * Uᵀ)
    (sym : Dᵀ = D) (invol : D * D = 1)
    (sign : D.det = 1) (odd : Odd (Fintype.card ι)) :
    (U - Uᵀ * D).det = 0 := by
  by_cases hu : U.det = 0
  · obtain ⟨v, hv, hvU⟩ := exists_vecMul_eq_zero_iff.mpr hu
    apply exists_vecMul_eq_zero_iff.mp
    refine ⟨v, hv, ?_⟩
    rw [vecMul_sub, ← vecMul_vecMul, hvU, shared_null U normal hvU, zero_vecMul, sub_zero]
  · let M := U - Uᵀ * D
    have h : M * D * U = -(U * Mᵀ) := by
      dsimp [M]
      rw [sub_mul, mul_assoc Uᵀ, invol, mul_one, sub_mul,
        transpose_sub, transpose_mul, sym, transpose_transpose, mul_sub, neg_sub, normal]
      noncomm_ring
    have hdet := congrArg Matrix.det h
    rw [det_mul, det_mul, sign, mul_one, det_neg, odd.neg_one_pow, det_mul, det_transpose] at hdet
    change M.det = 0
    have hz : (2 * M.det) * U.det = 0 := by linarith [hdet, mul_comm U.det M.det]
    exact (by rcases mul_eq_zero.mp hz with left | right <;> omega : M.det = 0)

private lemma factorial_product (p m : ℕ) :
    ∏ i ∈ range m, ((i+1 : ℕ) : ZMod p) = (m.factorial : ZMod p) := by
  rw [← Nat.cast_prod, prod_range_add_one_eq_factorial]

/-- Pair the two halves of Wilson’s product by negation. -/
private lemma half_factorial_sq (p m : ℕ) [Fact p.Prime]
    (hp : p = m + m + 1) (hm : Even m) : (m.factorial : ZMod p)^2 = -1 := by
  let f (i : ℕ) : ZMod p := (i + 1 : ℕ)
  have small : ∏ i ∈ range m, f i = (m.factorial : ZMod p) := factorial_product p m
  have reflect (i : ℕ) (hi : i ∈ range m) : f (m+i) = -1 * f (m-1-i) := by
    have hi' := mem_range.mp hi
    have eqn : m+i+1 + (m-1-i+1) = p := by omega
    have e : f (m+i) + f (m-1-i) = 0 := by
      dsimp only [f]
      rw [← Nat.cast_add, eqn, ZMod.natCast_self]
    linear_combination e
  have large : ∏ i ∈ range m, f (m+i) = (m.factorial : ZMod p) := by
    calc
      _ = ∏ i ∈ range m, (-1 : ZMod p) * f (m-1-i) := prod_congr rfl reflect
      _ = _ := by rw [prod_mul_distrib, prod_const, card_range, hm.neg_one_pow,
                    one_mul, prod_range_reflect, small]
  have w := ZMod.wilsons_lemma p
  rw [show p-1 = m+m by omega, ← factorial_product, prod_range_add] at w
  change (∏ i ∈ range m, f i) * (∏ i ∈ range m, f (m+i)) = -1 at w
  simpa only [small, large, pow_two] using w

private lemma cast_injective_half (p m : ℕ) [Fact p.Prime] (hp : p = m + m + 1) :
    Function.Injective (fun i : Fin m => (((i.val + 1 : ℕ) : ZMod p))^2) := by
  intro i j eqn
  obtain eq | opp := sq_eq_sq_iff_eq_or_eq_neg.mp eqn
  · have e := congrArg ZMod.val eq
    rw [ZMod.val_natCast_of_lt (show i.val+1 < p by omega),
      ZMod.val_natCast_of_lt (show j.val+1 < p by omega)] at e
    exact Fin.ext (by omega)
  · have hz : (↑((i.val+1)+(j.val+1)) : ZMod p) = 0 := by rw [Nat.cast_add, opp, neg_add_cancel]
    have hd := (ZMod.natCast_eq_zero_iff _ _).mp hz
    have bound := Nat.le_of_dvd (show 0 < i.val+1+(j.val+1) by omega) hd
    omega

/-- The product of the shifted column parameters has square equal to minus one. -/
private lemma prod_scaled_half_ne_one (p m : ℕ) [Fact p.Prime] (hp : p = m+m+1)
    (hp2 : 2 < p) (hm : Even m) :
    (∏ j : Fin m, (m.factorial : ZMod p) * ((j.val+1 : ℕ) : ZMod p)) ≠ 1 := by
  let c : ZMod p := m.factorial
  have hs : c ^ 2 = -1 := half_factorial_sq p m hp hm
  have ho : Odd (m+1) := hm.add_one
  have prod : (∏ j : Fin m, c * ((j.val+1 : ℕ) : ZMod p)) = c^(m+1) := by
    rw [prod_mul_distrib, prod_const, card_univ, Fintype.card_fin,
        Fin.prod_univ_eq_prod_range (fun i => ((i+1 : ℕ) : ZMod p)), factorial_product, pow_succ]
  intro he
  change (∏ j : Fin m, c * ((j.val+1 : ℕ) : ZMod p)) = 1 at he
  rw [prod] at he
  have neg : (1 : ZMod p) = -1 := calc
    1 = (c^(m+1))^2 := by rw [he, one_pow]
    _ = (c^2)^(m+1) := by rw [← pow_mul, Nat.mul_comm, pow_mul]
    _ = -1 := by rw [hs, ho.neg_one_pow]
  have hz : (2 : ZMod p) = 0 := by linear_combination neg
  have hd := (ZMod.natCast_eq_zero_iff 2 p).mp (by exact_mod_cast hz)
  have hp_le := Nat.le_of_dvd (by decide : 0 < 2) hd
  omega

/-- The shifted powers are nonsingular when the row parameters are distinct roots of unity and the column product differs from one. -/
private lemma det_shifted_powers (p m : ℕ) [hp : Fact p.Prime] (hm : 0 < m) (hp' : m < p)
    (x y : Fin m → ZMod p) (hx : Function.Injective x) (hy : Function.Injective y)
    (hxm : ∀ i, x i ^ m = 1) (hprod : (∏ j, y j) ≠ 1) :
    (Matrix.of (fun i j => (x i - y j)^m)).det ≠ 0 := by
  classical
  intro hz
  obtain ⟨v,hv,hzero⟩ := exists_vecMul_eq_zero_iff.mpr hz
  let R : (ZMod p)[X] := ∏ j, (X + C (y j))
  let P (i : Fin m) : (ZMod p)[X] := (X + C (x i))^m
  -- Subtract the same monic polynomial from each summand to cancel the leading term.
  let G := ∑ i, C (v i) * (P i - R)
  have mr : IsMonicOfDegree R m := by
    constructor
    · simp [R, natDegree_prod_of_monic _ _ (fun j _ => monic_X_add_C (y j))]
    · exact monic_prod_of_monic _ _ (fun j _ => monic_X_add_C (y j))
  have mp (i : Fin m) : IsMonicOfDegree (P i) m := by
    simpa only [one_mul] using (isMonicOfDegree_X_add_one (x i)).pow m
  have degG : G.natDegree < m := by
    apply lt_of_le_of_lt (b := m - 1) _ (by omega)
    apply natDegree_sum_le_of_forall_le
    intro i _
    have hi := IsMonicOfDegree.natDegree_sub_lt hm.ne' (mp i) mr
    exact (natDegree_C_mul_le _ _).trans (by omega)
  have rootR (j : Fin m) : R.eval (-y j) = 0 := by
    simp only [R, eval_prod, eval_add, eval_X, eval_C]
    exact prod_eq_zero (mem_univ j) (neg_add_cancel _)
  have rootG (j : Fin m) : G.eval (-y j) = 0 := by
    simp only [G, eval_finsetSum, eval_mul, eval_C, eval_sub, rootR, sub_zero, P,
      eval_pow, eval_add, eval_X, add_comm (-y j), ← sub_eq_add_neg]
    exact congrFun hzero j
  have gz := eq_zero_of_natDegree_lt_card_of_eval_eq_zero G (f := fun j => -y j)
    (fun _ _ eqn => hy (neg_inj.mp eqn)) rootG (by simpa only [Fintype.card_fin] using degG)
  -- Evaluation at zero uses the column product to show that the weights sum to zero.
  have sum0 : ∑ i, v i = 0 := by
    have eqn := congrArg (Polynomial.eval 0) gz
    simp only [G, eval_finsetSum, eval_mul, eval_C, eval_sub, P, eval_pow, eval_add, eval_X,
      zero_add, hxm, R, eval_prod, eval_zero, ← sum_mul] at eqn
    exact (mul_eq_zero.mp eqn).resolve_right (sub_ne_zero.mpr (Ne.symm hprod))
  have pz : ∑ i, C (v i) * P i = 0 := by
    dsimp only [G] at gz
    simpa only [mul_sub, sum_sub_distrib, ← sum_mul, ← map_sum, sum0, map_zero, zero_mul,
      sub_zero] using gz
  -- The remaining coefficient equations are precisely the Vandermonde equations.
  apply det_vandermonde_ne_zero_iff.mpr hx
  apply exists_vecMul_eq_zero_iff.mp
  refine ⟨v,hv,?_⟩
  funext k
  let r := m-k.val
  have hc := congrArg (fun f : (ZMod p)[X] => f.coeff r) pz
  have kr : m-r = k.val := by dsimp [r]; omega
  simp only [finsetSum_coeff, coeff_C_mul, P, coeff_X_add_C_pow, kr, coeff_zero,
    ← mul_assoc, ← sum_mul] at hc
  have nonzero : (m.choose r : ZMod p) ≠ 0 := by
    intro h
    have hdiv : p ∣ m.choose r := (ZMod.natCast_eq_zero_iff _ _).mp h
    have hdvd : m.choose r ∣ m.factorial := by
      use r.factorial * (m-r).factorial
      rw [← mul_assoc, Nat.choose_mul_factorial_mul_factorial (show r ≤ m by dsimp [r]; omega)]
    exact (Nat.not_le.mpr hp') (hp.out.dvd_factorial.mp (hdiv.trans hdvd))
  exact (mul_eq_zero.mp hc).resolve_right nonzero

private lemma half_representative (p m : ℕ) [Fact p.Prime] (hp : p = m+m+1)
    (z : ZMod p) (hz : z ≠ 0) :
    ∃ i : Fin m, ((i.val+1 : ℕ) : ZMod p) = z ∨ ((i.val+1 : ℕ) : ZMod p) = -z := by
  have hl := z.val_lt
  have hn := (ZMod.val_ne_zero z).mpr hz
  by_cases hv : z.val ≤ m
  · refine ⟨⟨z.val-1, by omega⟩, Or.inl ?_⟩
    change ((z.val-1+1 : ℕ) : ZMod p) = z
    rw [show z.val-1+1 = z.val by omega, ZMod.natCast_zmod_val]
  · refine ⟨⟨p-z.val-1, by omega⟩, Or.inr ?_⟩
    change ((p-z.val-1+1 : ℕ) : ZMod p) = -z
    apply eq_neg_of_add_eq_zero_left
    nth_rw 2 [← ZMod.natCast_zmod_val z]
    rw [← Nat.cast_add, show p-z.val-1+1+z.val = p by omega, ZMod.natCast_self]

/-- Represent the involution sending x to xᵢxⱼ/x on the nonzero squares. -/
private lemma quotient_perm {p m : ℕ} [Fact p.Prime] (t : Fin m → ZMod p)
    (tn : ∀ i, t i ≠ 0) (inj : Function.Injective (fun i => t i ^ 2))
    (rep : ∀ z ≠ 0, ∃ k, t k = z ∨ t k = -z) (i j : Fin m) :
    ∃ e : Equiv.Perm (Fin m), ∀ k, (t (e k))^2 = (t i * t j / t k)^2 := by
  classical
  have h (k : Fin m) : ∃ r, (t r)^2 = (t i * t j / t k)^2 := by
    obtain ⟨r,hr⟩ := rep _ (div_ne_zero (mul_ne_zero (tn i) (tn j)) (tn k))
    exact ⟨r,sq_eq_sq_iff_eq_or_eq_neg.mpr hr⟩
  choose f hf using h
  have inv (k : Fin m) : f (f k) = k := by
    apply inj
    change (t (f (f k)))^2 = (t k)^2
    rw [hf, div_pow, hf]
    field_simp [tn i, tn j, tn k]
  exact ⟨⟨f,f,inv,inv⟩,hf⟩

/-- Reindex the matrix product by reciprocal pairs to interchange the two characters. -/
private lemma character_commutes {p m : ℕ} [Fact p.Prime] (t : Fin m → ZMod p)
    (tn : ∀ i, t i ≠ 0) (inj : Function.Injective (fun i => t i ^ 2))
    (rep : ∀ z ≠ 0, ∃ k, t k = z ∨ t k = -z) (K S : Matrix (Fin m) (Fin m) ℤ)
    (hk : ∀ i j, K i j = quadraticChar (ZMod p) (t i^2 - t j^2))
    (hs : ∀ i j, S i j = quadraticChar (ZMod p) (t i^2 + t j^2)) : K*S = S*K := by
  classical
  ext i j
  obtain ⟨e,he⟩ := quotient_perm t tn inj rep i j
  change (∑ k, K i k * S k j) = ∑ k, S i k * K k j
  rw [← Equiv.sum_comp e (fun k => S i k * K k j)]
  apply sum_congr rfl
  intro k _
  have scale (a : Fin m) (v : ZMod p) :
      quadraticChar (ZMod p) ((t a/t k)^2 * v) = quadraticChar (ZMod p) v := by
    rw [map_mul, quadraticChar_sq_one' (div_ne_zero (tn a) (tn k)), one_mul]
  have add : t i^2 + t (e k)^2 = (t i/t k)^2 * (t k^2 + t j^2) := by
    rw [he]
    field_simp [tn k]
  have sub : t (e k)^2 - t j^2 = (t j/t k)^2 * (t i^2 - t k^2) := by
    rw [he]
    field_simp [tn k]
  rw [hk, hs, hs, hk, add, sub, scale, scale, mul_comm]

/-- The quadratic character distinguishes the two signs and gives a permutation of columns. -/
private lemma column_perm {p m : ℕ} [Fact p.Prime] (t : Fin m → ZMod p)
    (tn : ∀ i, t i ≠ 0) (inj : Function.Injective (fun i => t i ^ 2))
    (rep : ∀ z ≠ 0, ∃ k, t k = z ∨ t k = -z) (c : ZMod p) (hc : c ≠ 0)
    (negchi : ∀ z, quadraticChar (ZMod p) (-z) = -quadraticChar (ZMod p) z) :
    ∃ e : Equiv.Perm (Fin m), ∀ j, c * t (e j) = t j^2 ∨ c * t (e j) = -(t j^2) := by
  classical
  have h (j : Fin m) : ∃ k, c * t k = t j^2 ∨ c * t k = -(t j^2) := by
    obtain ⟨k,h | h⟩ := rep (t j^2 / c) (div_ne_zero (pow_ne_zero _ (tn j)) hc)
    · exact ⟨k, Or.inl (by rw [h]; field_simp)⟩
    · exact ⟨k, Or.inr (by rw [h]; field_simp)⟩
  choose f hf using h
  have fi : Function.Injective f := by
    intro i j hij
    have both (k : Fin m) := sq_eq_sq_iff_eq_or_eq_neg.mpr (hf k)
    have eqn : (t i^2)^2 = (t j^2)^2 := by rw [← both i, ← both j, hij]
    obtain he | he := sq_eq_sq_iff_eq_or_eq_neg.mp eqn
    · exact inj he
    · have ch := congrArg (quadraticChar (ZMod p)) he
      rw [negchi, quadraticChar_sq_one' (tn i), quadraticChar_sq_one' (tn j)] at ch
      omega
  exact ⟨Equiv.ofBijective f fi.bijective_of_finite,hf⟩

/-- Express twice the permuted Legendre matrix as a difference involving a normal matrix. -/
private lemma odd_decomposition (p : ℕ) (hp : p.Prime) (h3 : p%4 = 3) :
    ∃ (e : Equiv.Perm (Fin ((p-1)/2))) (U D : Matrix (Fin ((p-1)/2)) (Fin ((p-1)/2)) ℤ),
      Uᵀ * U = U * Uᵀ ∧ Dᵀ = D ∧ D * D = 1 ∧ D.det = 1 ∧
        (2 : ℤ) • ((OeisA226163.legendreMatrix p).submatrix id e) = U - Uᵀ * D := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  let m := (p-1)/2
  have hr : p = m+m+1 := by dsimp [m]; omega
  let t (i : Fin m) : ZMod p := (i.val+1 : ℕ)
  let c : ZMod p := m.factorial
  let χ := quadraticChar (ZMod p)
  have tn (i : Fin m) : t i ≠ 0 := by
    intro h0
    have hd := (ZMod.natCast_eq_zero_iff _ _).mp h0
    have bound := Nat.le_of_dvd (show 0 < i.val+1 by omega) hd
    omega
  have cn : c ≠ 0 := by
    intro h
    have hd := (ZMod.natCast_eq_zero_iff _ _).mp h
    have bound := hp.dvd_factorial.mp hd
    omega
  have inj : Function.Injective (fun i => t i^2) := cast_injective_half p m hr
  have rep : ∀ z ≠ 0, ∃ i, t i = z ∨ t i = -z := half_representative p m hr
  have negOne : χ (-1) = -1 :=
    quadraticChar_neg_one_iff_not_isSquare.mpr (by rw [ZMod.exists_sq_eq_neg_one_iff]; simp [h3])
  have neg (z : ZMod p) : χ (-z) = -χ z := by
    rw [← neg_one_mul z, map_mul, negOne, neg_one_mul]
  have sqchar (i : Fin m) : χ (t i^2) = 1 := quadraticChar_sq_one' (tn i)
  obtain ⟨e,he⟩ := column_perm t tn inj rep c cn neg
  let K : Matrix (Fin m) (Fin m) ℤ := Matrix.of fun i j => χ (t i^2 - t j^2)
  let S : Matrix (Fin m) (Fin m) ℤ := Matrix.of fun i j => χ (t i^2 + t j^2)
  let d (j : Fin m) := χ (c * t (e j))
  have comm : K * S = S * K := character_commutes t tn inj rep K S (fun _ _ => rfl) (fun _ _ => rfl)
  have kt : Kᵀ = -K := by
    ext i j
    change χ (t j^2 - t i^2) = -χ (t i^2 - t j^2)
    rw [← neg, neg_sub]
  have st : Sᵀ = S := by
    ext i j
    change χ (t j^2 + t i^2) = χ (t i^2 + t j^2)
    rw [add_comm]
  refine ⟨e,K+S,diagonal d,?_,diagonal_transpose _,?_,?_,?_⟩
  · simp only [transpose_add, kt, st, mul_add, add_mul, neg_mul, mul_neg, comm]
    abel
  · rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext k
    change χ (c * t (e k)) * χ (c * t (e k)) = 1
    rw [← pow_two]
    exact quadraticChar_sq_one (mul_ne_zero cn (tn _))
  · rw [det_diagonal]
    change (∏ j, χ (c * t (e j))) = 1
    rw [Equiv.prod_comp e (fun j => χ (c * t j)), ← map_prod]
    have hprod : (∏ j, c * t j) = c^(m+1) := by
      rw [prod_mul_distrib, prod_const, card_univ, Fintype.card_fin]
      change c^m * (∏ j : Fin m, ((j.val+1 : ℕ) : ZMod p)) = c^(m+1)
      rw [Fin.prod_univ_eq_prod_range (fun i => ((i+1 : ℕ) : ZMod p)), factorial_product, pow_succ]
    rw [hprod, map_pow]
    have evenM : Even (m+1) := Nat.even_iff.mpr (by dsimp [m]; omega)
    rcases quadraticChar_dichotomy cn with h | h
    · change χ c = 1 at h
      rw [h, one_pow]
    · change χ c = -1 at h
      rw [h, evenM.neg_one_pow]
  · have entry (i j : Fin m) : OeisA226163.legendreMatrix p i j = χ (t i^2 - c*t j) := by
      change jacobiSym _ p = _
      rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym]
      dsimp [χ,t,c,OeisA226163.legendreMatrix]
      push_cast
      rw [pow_two]
    ext i j
    change 2 * OeisA226163.legendreMatrix p i (e j) =
      (K i j + S i j) - ((K+S)ᵀ * diagonal d) i j
    rw [mul_diagonal, transpose_add, kt, st, Matrix.add_apply, Matrix.neg_apply, entry]
    rcases he j with h | h
    · have dj : d j = 1 := by dsimp only [d]; rw [h, sqchar]
      rw [h, dj]
      change 2 * K i j = K i j + S i j - (-K i j + S i j) * 1
      ring
    · have dj : d j = -1 := by dsimp only [d]; rw [h, neg, sqchar]
      rw [h, dj, sub_neg_eq_add]
      change 2 * S i j = K i j + S i j - (-K i j + S i j) * (-1)
      ring

private lemma det_ne_zero_of_even (p : ℕ) [hp : Fact p.Prime] (hp2 : 2 < p)
    (hmod : p % 4 = 1) : (OeisA226163.legendreMatrix p).det ≠ 0 := by
  let m := (p-1)/2
  have hr : p = m+m+1 := by dsimp [m]; omega
  have hm : Even m := Nat.even_iff.mpr (by dsimp [m]; omega)
  let t (i : Fin m) : ZMod p := (i.val+1 : ℕ)
  let c : ZMod p := m.factorial
  have tc (i : Fin m) : t i ≠ 0 := by
    intro h0
    have hd := (ZMod.natCast_eq_zero_iff _ _).mp h0
    have b := Nat.le_of_dvd (show 0 < i.val+1 by omega) hd
    omega
  have cc : c ≠ 0 := by
    have hs := half_factorial_sq p m hr hm
    change c^2 = -1 at hs
    rintro rfl₀
    simp [rfl₀] at hs
  have ty : Function.Injective (fun i => c * t i) := by
    intro i j hij
    have eqn := congrArg ZMod.val (mul_left_cancel₀ cc hij)
    change ZMod.val ((i.val+1 : ℕ) : ZMod p) = ZMod.val ((j.val+1 : ℕ) : ZMod p) at eqn
    rw [ZMod.val_natCast_of_lt (show i.val+1 < p by omega),
        ZMod.val_natCast_of_lt (show j.val+1 < p by omega)] at eqn
    exact Fin.ext (by omega)
  have xp (i : Fin m) : (t i ^ 2)^m = 1 := by
    rw [← pow_mul, show 2*m = p-1 by omega]
    exact ZMod.pow_card_sub_one_eq_one (tc i)
  have dn := det_shifted_powers p m (by omega) (by omega) (fun i => t i ^ 2) (fun i => c * t i)
    (cast_injective_half p m hr) ty xp (prod_scaled_half_ne_one p m hr hp2 hm)
  let f := Int.castRingHom (ZMod p)
  have matrix_eq : f.mapMatrix (OeisA226163.legendreMatrix p) =
      Matrix.of (fun (i j : Fin m) => (t i^2 - c*t j)^m) := by
    ext i j
    change (↑(jacobiSym (((i.val : ℤ)+1)*((i.val:ℤ)+1) -
      ((m.factorial:ℤ)*((j.val:ℤ)+1))) p) : ZMod p) = (t i^2 - c*t j)^m
    rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym.eq_pow]
    dsimp [t, c]
    push_cast
    rw [show p / 2 = m by omega, pow_two]
  intro hd
  apply dn
  rw [← matrix_eq, ← f.map_det, hd, map_zero]

theorem OMA.solution : type_of% @OeisA226163.conjecture := by
  intro n hn
  let p := Nat.nth Nat.Prime (n-1)
  have hp : p.Prime := Nat.prime_nth_prime _
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : 2 < p := by
    have h := Nat.nth_strictMono Nat.infinite_setOfPred_prime (show 0 < n-1 by omega)
    simpa only [Nat.nth_prime_zero_eq_two] using h
  have oddp := Nat.odd_iff.mp (hp.odd_of_ne_two (by omega))
  change (OeisA226163.legendreMatrix p).det = 0 ↔ p%4 = 3
  constructor
  · intro hd
    by_contra hc
    exact det_ne_zero_of_even p hp2 (by omega) hd
  · intro h3
    obtain ⟨e,U,D,hu,hd,hi,hsign,he⟩ := odd_decomposition p hp h3
    have ho : Odd (Fintype.card (Fin ((p-1)/2))) := by
      rw [Fintype.card_fin, Nat.odd_iff]
      omega
    have zero := det_normal_signed U D hu hd hi hsign ho
    rw [← he, det_smul, det_permute'] at zero
    have ne : (↑(Equiv.Perm.sign e) : ℤ) ≠ 0 := Units.ne_zero _
    exact (mul_eq_zero.mp ((mul_eq_zero.mp zero).resolve_left (pow_ne_zero _ (by decide)))).resolve_left ne
