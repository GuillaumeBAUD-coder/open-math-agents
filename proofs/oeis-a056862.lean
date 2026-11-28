import OMAStatements.S_oeis_a056862

-- Problem: A056862: Triangle T(n,k) is the number of restricted growth strings (RGS) of set partitions of {1..n} that have a decrease at index k (1<=k<n)
-- Upstream: statements/oeis-a056862.lean (declaration OMA.S_oeis_a056862.main)
-- Credit: @timlantin (the owner of the agent is credited as the solver)
--
-- Proof sketch. A restricted growth string of length n+1 is one of length n, of maximum M, followed
-- by a letter v in 1..M+1; the new maximum is max M v. So for f on the maxima, the sum of f(max s)
-- over the strings of length n+1 is the sum of (Tr f)(max t) over those of length n, with
-- (Tr f)(M) = M f(M) + f(M+1), and the same holds for the sums restricted to the strings with
-- s_3 > s_4 once the length is at least 4. Peeling the letters s_4, s_3 and then s_2, s_1 off the
-- strings of length 4 gives: the sum of f(max s) over the four strings with s_3 > s_4 is
-- 2 f(2) + 2 f(3) (they are 1121, 1221, 1231, 1232). Hence T(4+r,3) = 2 E(r,2) + 2 E(r,3) with
-- E(r,.) = Tr^r 1, that is E(r+1,m) = m E(r,m) + E(r,m+1) and E(0,m) = 1.
-- Bell numbers: let L be the linear form on polynomials with L(X^j) = B(j). The recurrence
-- B(j+1) = sum_i C(j,i) B(j-i) says L(X p) = L(p(X+1)), so G(r,m) = L((X+m)^r) satisfies the
-- recursion of E, and G(r,0) = B(r). Therefore E(r,1) = B(r+1), E(r,2) = B(r+2) - B(r+1),
-- E(r,3) = B(r+3) - 3 B(r+2) + 2 B(r+1), and T(4+r,3) = 2 (B(r+3) - 2 B(r+2) + B(r+1)).

namespace OMA.P056862
open OMA.S_oeis_a056862 Polynomial

/-- The linear form on polynomials sending `X^j` to the Bell number `B(j)`. -/
noncomputable def L : ℕ[X] →ₗ[ℕ] ℕ :=
  Polynomial.lsum fun j => Nat.bell j • (LinearMap.id : ℕ →ₗ[ℕ] ℕ)

lemma L_monomial (j a : ℕ) : L (monomial j a) = a * Nat.bell j := by
  unfold L
  rw [Polynomial.lsum_apply, Polynomial.sum_monomial_index]
  · simp [mul_comm]
  · simp

lemma L_X_mul (p : ℕ[X]) : L (X * p) = L (p.comp (X + 1)) := by
  refine Polynomial.induction_on' p (fun p q hp hq => ?_) (fun n a => ?_)
  · rw [mul_add, add_comp, map_add, map_add, hp, hq]
  · rw [X_mul_monomial, L_monomial, monomial_comp, ← smul_eq_C_mul, map_smul,
      add_comm (X : ℕ[X]) 1, add_pow, map_sum, Nat.bell_succ, smul_eq_mul,
      ← Nat.range_succ_eq_Iic]
    congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    have h : (1 : ℕ[X]) ^ m * X ^ (n - m) * (n.choose m : ℕ[X]) =
        monomial (n - m) (n.choose m) := by
      rw [one_pow, one_mul, ← C_eq_natCast, mul_comm, C_mul_X_pow_eq_monomial, Nat.cast_id]
    rw [h, L_monomial]

noncomputable def G (r m : ℕ) : ℕ := L ((X + C m) ^ r)

lemma G_succ (r m : ℕ) : G (r + 1) m = m * G r m + G r (m + 1) := by
  unfold G
  have h : (X + C m : ℕ[X]) ^ (r + 1) = m • (X + C m) ^ r + X * (X + C m) ^ r := by
    rw [pow_succ, smul_eq_C_mul]
    ring
  have h2 : ((X + C m : ℕ[X]) ^ r).comp (X + 1) = (X + C (m + 1)) ^ r := by
    rw [pow_comp, add_comp, X_comp, C_comp, C_add, C_1]
    congr 1
    ring
  rw [h, map_add, map_smul, L_X_mul, smul_eq_mul, h2]

lemma G_zero (r : ℕ) : G r 0 = Nat.bell r := by
  unfold G
  rw [C_0, add_zero, X_pow_eq_monomial, L_monomial, one_mul]

/-- The transfer operator on functions of the maximum. -/
def Tr (f : ℕ → ℕ) : ℕ → ℕ := fun m => m * f m + f (m + 1)

lemma Tr_iter (r : ℕ) : ∀ m, Tr^[r] (fun _ => 1) m = G r m := by
  induction r with
  | zero =>
    intro m
    show (1 : ℕ) = G 0 m
    rw [G, pow_zero, ← monomial_zero_one, L_monomial]
    simp
  | succ r ih =>
    intro m
    rw [Function.iterate_succ_apply', G_succ]
    show m * _ + _ = _
    rw [ih, ih]

/-- The restricted growth strings of length `n`, built letter by letter. -/
def R : (n : ℕ) → Finset (Fin n → ℕ)
  | 0 => {fun _ => 0}
  | n + 1 => ((R n).sigma fun s => Finset.Icc 1 (Finset.univ.sup s + 1)).image
      fun p => (Fin.snoc p.1 p.2 : Fin (n + 1) → ℕ)

lemma sc {n : ℕ} (t : Fin n → ℕ) (v : ℕ) (i : Fin n) :
    (Fin.snoc t v : Fin (n + 1) → ℕ) i.castSucc = t i := by simp

lemma sl {n : ℕ} (t : Fin n → ℕ) (v : ℕ) :
    (Fin.snoc t v : Fin (n + 1) → ℕ) (Fin.last n) = v := by simp

lemma sk {n : ℕ} (t : Fin n → ℕ) (v k : ℕ) (h : k < n) :
    (Fin.snoc t v : Fin (n + 1) → ℕ) ⟨k, by omega⟩ = t ⟨k, h⟩ := sc t v ⟨k, h⟩

lemma sup_snoc {n : ℕ} (t : Fin n → ℕ) (v : ℕ) :
    Finset.univ.sup (Fin.snoc t v : Fin (n + 1) → ℕ) = max (Finset.univ.sup t) v := by
  apply le_antisymm
  · apply Finset.sup_le
    intro j _
    refine Fin.lastCases ?_ (fun i => ?_) j
    · rw [sl]
      exact le_max_right _ _
    · rw [sc]
      exact le_trans (Finset.le_sup (f := t) (Finset.mem_univ i)) (le_max_left _ _)
  · apply max_le
    · apply Finset.sup_le
      intro i _
      have h := Finset.le_sup (f := (Fin.snoc t v : Fin (n + 1) → ℕ))
        (Finset.mem_univ i.castSucc)
      rwa [sc] at h
    · have h := Finset.le_sup (f := (Fin.snoc t v : Fin (n + 1) → ℕ))
        (Finset.mem_univ (Fin.last n))
      rwa [sl] at h

lemma sup_Iio_castSucc {n : ℕ} (t : Fin n → ℕ) (v : ℕ) (i : Fin n) :
    (Finset.Iio i.castSucc).sup (Fin.snoc t v : Fin (n + 1) → ℕ) = (Finset.Iio i).sup t := by
  apply le_antisymm
  · apply Finset.sup_le
    intro j hj
    have h0 : j < i.castSucc := Finset.mem_Iio.mp hj
    have h1 : (j : ℕ) < (i : ℕ) := h0
    have h2 := i.isLt
    have hj' : j = (⟨j, by omega⟩ : Fin n).castSucc := Fin.ext rfl
    rw [hj', sc]
    exact Finset.le_sup (f := t) (Finset.mem_Iio.mpr (Fin.lt_def.mpr h1))
  · apply Finset.sup_le
    intro j hj
    have h1 : j < i := Finset.mem_Iio.mp hj
    have h := Finset.le_sup (f := (Fin.snoc t v : Fin (n + 1) → ℕ))
      (show j.castSucc ∈ Finset.Iio i.castSucc from
        Finset.mem_Iio.mpr (Fin.castSucc_lt_castSucc_iff.mpr h1))
    rwa [sc] at h

lemma sup_Iio_last {n : ℕ} (t : Fin n → ℕ) (v : ℕ) :
    (Finset.Iio (Fin.last n)).sup (Fin.snoc t v : Fin (n + 1) → ℕ) = Finset.univ.sup t := by
  apply le_antisymm
  · apply Finset.sup_le
    intro j hj
    have h0 : j < Fin.last n := Finset.mem_Iio.mp hj
    have h1 : (j : ℕ) < n := h0
    have hj' : j = (⟨j, h1⟩ : Fin n).castSucc := Fin.ext rfl
    rw [hj', sc]
    exact Finset.le_sup (f := t) (Finset.mem_univ _)
  · apply Finset.sup_le
    intro j _
    have h := Finset.le_sup (f := (Fin.snoc t v : Fin (n + 1) → ℕ))
      (show j.castSucc ∈ Finset.Iio (Fin.last n) from Finset.mem_Iio.mpr (Fin.castSucc_lt_last j))
    rwa [sc] at h

lemma isRGS_snoc {n : ℕ} (t : Fin n → ℕ) (v : ℕ) :
    IsRGS (Fin.snoc t v : Fin (n + 1) → ℕ) ↔
      IsRGS t ∧ v ∈ Finset.Icc 1 (Finset.univ.sup t + 1) := by
  unfold IsRGS
  rw [Fin.forall_fin_succ']
  simp only [sc, sl, sup_Iio_castSucc, sup_Iio_last, Finset.mem_Icc]
  refine and_congr Iff.rfl (and_congr Iff.rfl ?_)
  omega

lemma mem_R : ∀ (n : ℕ) (s : Fin n → ℕ), s ∈ R n ↔ IsRGS s := by
  intro n
  induction n with
  | zero =>
    intro s
    rw [R, Finset.mem_singleton]
    constructor
    · intro _ i
      exact i.elim0
    · intro _
      funext i
      exact i.elim0
  | succ n ih =>
    intro s
    have e : (Fin.snoc (Fin.init s) (s (Fin.last n)) : Fin (n + 1) → ℕ) = s :=
      Fin.snoc_init_self s
    rw [R, Finset.mem_image]
    constructor
    · rintro ⟨p, hp, rfl⟩
      rw [Finset.mem_sigma] at hp
      exact (isRGS_snoc _ _).mpr ⟨(ih _).mp hp.1, hp.2⟩
    · intro h
      have h' := (isRGS_snoc (Fin.init s) (s (Fin.last n))).mp (by rw [e]; exact h)
      exact ⟨⟨Fin.init s, s (Fin.last n)⟩,
        Finset.mem_sigma.mpr ⟨(ih _).mpr h'.1, h'.2⟩, e⟩

lemma sum_R_succ (n : ℕ) (g : (Fin (n + 1) → ℕ) → ℕ) :
    ∑ s ∈ R (n + 1), g s =
      ∑ t ∈ R n, ∑ v ∈ Finset.Icc 1 (Finset.univ.sup t + 1), g (Fin.snoc t v) := by
  rw [R, Finset.sum_image, Finset.sum_sigma]
  rintro ⟨a, b⟩ _ ⟨c, d⟩ _ h
  have h0 : (Fin.snoc a b : Fin (n + 1) → ℕ) = Fin.snoc c d := h
  have h1 : a = c := by
    funext i
    have h3 := congrFun h0 i.castSucc
    rwa [sc, sc] at h3
  have h2 : b = d := by
    have h3 := congrFun h0 (Fin.last n)
    rwa [sl, sl] at h3
  subst h1
  subst h2
  rfl

lemma sum_sup_step (M : ℕ) (f : ℕ → ℕ) :
    ∑ v ∈ Finset.Icc 1 (M + 1), f (max M v) = Tr f M := by
  have h : ∑ v ∈ Finset.Icc 1 M, f (max M v) = ∑ v ∈ Finset.Icc 1 M, f M :=
    Finset.sum_congr rfl fun v hv => by rw [max_eq_left (Finset.mem_Icc.mp hv).2]
  rw [Finset.sum_Icc_succ_top (by omega), h, Finset.sum_const, Nat.card_Icc,
    max_eq_right (Nat.le_succ M)]
  show _ = M * f M + f (M + 1)
  simp

lemma Q (n : ℕ) : ∀ h : ℕ → ℕ, ∑ s ∈ R n, h (Finset.univ.sup s) = Tr^[n] h 0 := by
  induction n with
  | zero =>
    intro h
    simp [R]
  | succ n ih =>
    intro h
    rw [sum_R_succ, Function.iterate_succ_apply, ← ih]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [sup_snoc]
    exact sum_sup_step _ _

/-- Sum of `f (max s)` over the strings of length `n` with `s_3 > s_4`. -/
def Dn (n : ℕ) (h : 4 ≤ n) (f : ℕ → ℕ) : ℕ :=
  ∑ s ∈ R n, if s ⟨3, by omega⟩ < s ⟨2, by omega⟩ then f (Finset.univ.sup s) else 0

lemma Dn_succ (n : ℕ) (h : 4 ≤ n) (f : ℕ → ℕ) :
    Dn (n + 1) (by omega) f = Dn n h (Tr f) := by
  unfold Dn
  rw [sum_R_succ]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [sk t _ 3 (by omega), sk t _ 2 (by omega), sup_snoc]
  by_cases hc : t ⟨3, by omega⟩ < t ⟨2, by omega⟩
  · simp only [if_pos hc]
    exact sum_sup_step _ _
  · simp only [if_neg hc]
    simp

lemma Dn_eq (r : ℕ) : ∀ f : ℕ → ℕ,
    Dn (4 + r) (by omega) f = Dn 4 (le_refl 4) (Tr^[r] f) := by
  induction r with
  | zero =>
    intro f
    rfl
  | succ r ih =>
    intro f
    rw [Function.iterate_succ_apply, ← ih]
    exact Dn_succ (4 + r) (by omega) f

lemma D_base (f : ℕ → ℕ) : Dn 4 (le_refl 4) f = 2 * f 2 + 2 * f 3 := by
  have e1 : Dn 4 (le_refl 4) f = ∑ s ∈ R (3 + 1),
      (if s (Fin.last 3) < s (Fin.last 2).castSucc then f (Finset.univ.sup s) else 0) := rfl
  have A : ∀ M a : ℕ, a ≤ M →
      ∑ v ∈ Finset.Icc 1 (M + 1), (if v < a then f (max M v) else 0) = (a - 1) * f M := by
    intro M a ha
    have e : (Finset.Icc 1 (M + 1)).filter (fun v => v < a) = Finset.Ico 1 a := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ico]
      omega
    have h : ∑ v ∈ Finset.Ico 1 a, f (max M v) = ∑ v ∈ Finset.Ico 1 a, f M :=
      Finset.sum_congr rfl fun v hv => by
        have h3 := (Finset.mem_Ico.mp hv).2
        rw [max_eq_left (by omega)]
    rw [← Finset.sum_filter, e, h, Finset.sum_const, Nat.card_Ico, smul_eq_mul]
  have Bm : ∀ M : ℕ, ∑ v ∈ Finset.Icc 1 (M + 1), (v - 1) * f (max M v) =
      (∑ v ∈ Finset.Icc 1 M, (v - 1)) * f M + M * f (M + 1) := by
    intro M
    have h : ∑ v ∈ Finset.Icc 1 M, (v - 1) * f (max M v) =
        ∑ v ∈ Finset.Icc 1 M, (v - 1) * f M :=
      Finset.sum_congr rfl fun v hv => by rw [max_eq_left (Finset.mem_Icc.mp hv).2]
    rw [Finset.sum_Icc_succ_top (by omega), h, Finset.sum_mul, max_eq_right (Nat.le_succ M)]
    simp
  rw [e1, sum_R_succ]
  simp only [sl, sc, sup_snoc]
  rw [Finset.sum_congr rfl (fun t _ => A _ _ (Finset.le_sup (f := t) (Finset.mem_univ _)))]
  rw [sum_R_succ]
  simp only [sl, sup_snoc, Bm]
  refine (Q 2 (fun M => (∑ v ∈ Finset.Icc 1 M, (v - 1)) * f M + M * f (M + 1))).trans ?_
  have s1 : ∑ v ∈ Finset.Icc 1 1, (v - 1) = 0 := by decide
  have s2 : ∑ v ∈ Finset.Icc 1 2, (v - 1) = 1 := by decide
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp, id, Tr, s1, s2]
  ring

lemma T_eq (n : ℕ) (h : 4 ≤ n) : T n 3 = Dn n h (fun _ => 1) := by
  unfold T Dn
  have e : {s : Fin n → ℕ | IsRGS s ∧
      ∃ i j : Fin n, (i : ℕ) + 1 = 3 ∧ (j : ℕ) = 3 ∧ s j < s i} =
      ((R n).filter fun s => s ⟨3, by omega⟩ < s ⟨2, by omega⟩ : Finset (Fin n → ℕ)) := by
    ext s
    simp only [Set.mem_setOf_eq, Finset.coe_filter, mem_R]
    refine and_congr Iff.rfl ⟨?_, fun hs => ⟨⟨2, by omega⟩, ⟨3, by omega⟩, rfl, rfl, hs⟩⟩
    rintro ⟨i, j, hi, hj, hs⟩
    have hi' : i = ⟨2, by omega⟩ := Fin.ext (by show (i : ℕ) = 2; omega)
    have hj' : j = ⟨3, by omega⟩ := Fin.ext (by show (j : ℕ) = 3; omega)
    rw [hi', hj'] at hs
    exact hs
  rw [e, Set.ncard_coe_finset, Finset.card_filter]

end OMA.P056862

open OMA.S_oeis_a056862 OMA.P056862 in
theorem OMA.solution : type_of% @OMA.S_oeis_a056862.main := by
  intro n hn
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [T_eq (4 + r) hn, Dn_eq r, D_base, Tr_iter, Tr_iter]
  have a0 : G (r + 1) 0 = 0 * G r 0 + G r 1 := G_succ r 0
  have b0 : G (r + 2) 0 = 0 * G (r + 1) 0 + G (r + 1) 1 := G_succ (r + 1) 0
  have c0 : G (r + 3) 0 = 0 * G (r + 2) 0 + G (r + 2) 1 := G_succ (r + 2) 0
  have a1 : G (r + 1) 1 = 1 * G r 1 + G r 2 := G_succ r 1
  have b1 : G (r + 2) 1 = 1 * G (r + 1) 1 + G (r + 1) 2 := G_succ (r + 1) 1
  have a2 : G (r + 1) 2 = 2 * G r 2 + G r 3 := G_succ r 2
  simp only [G_zero] at a0 b0 c0
  have e : 4 + r - 3 = r + 1 := by omega
  rw [e]
  show ((2 * G r 2 + 2 * G r 3 : ℕ) : ℤ) =
    2 * ((Nat.bell (r + 3) : ℤ) - 2 * (Nat.bell (r + 2) : ℤ) + (Nat.bell (r + 1) : ℤ))
  zify at a0 b0 c0 a1 b1 a2
  push_cast
  linarith
