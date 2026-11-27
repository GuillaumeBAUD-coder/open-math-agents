import OMAStatements.S_oeis_a178299

-- Problem: A178299: Number of collinear point 4-tuples in a 6 X 6 X 6 X... n-dimensional cubic grid.
-- Upstream: statements/oeis-a178299.lean (declaration OMA.S_oeis_a178299.main)
-- Credit: @jared-jasinski (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.P_oeis_a178299

open OMA.S_oeis_a178299 Finset

/-- The 10 valid step patterns `(a1, a2, D)` with `D ∈ {3, 4, 5}` and `0 < a1 < a2 < D`. -/
def validPats : Finset (ℕ × ℕ × ℕ) :=
  {(1, 2, 3),
   (1, 2, 4), (1, 3, 4), (2, 3, 4),
   (1, 2, 5), (1, 3, 5), (1, 4, 5), (2, 3, 5), (2, 4, 5), (3, 4, 5)}

/-- Valid `(coord, dir)` pairs for a given span `D`, where `dir ∈ {-1, 0, 1}` and `0 ≤ coord + D * dir ≤ 5`. -/
def goodCoord (D : ℕ) : Finset (Fin 6 × ℤ) :=
  (Finset.univ ×ˢ ({-1, 0, 1} : Finset ℤ)).filter fun xd =>
    0 ≤ (xd.1.val : ℤ) + (D : ℤ) * xd.2 ∧ (xd.1.val : ℤ) + (D : ℤ) * xd.2 ≤ 5

lemma card_goodCoord_3 : (goodCoord 3).card = 12 := by decide
lemma card_goodCoord_4 : (goodCoord 4).card = 10 := by decide
lemma card_goodCoord_5 : (goodCoord 5).card = 8 := by decide

/-- Valid `(coord, dir)` pairs with `dir = 0`. -/
def zeroCoord (D : ℕ) : Finset (Fin 6 × ℤ) :=
  (goodCoord D).filter fun xd => xd.2 = 0

lemma card_zeroCoord (D : ℕ) : (zeroCoord D).card = 6 := by
  have h : zeroCoord D = Finset.univ.image (fun x : Fin 6 => (x, (0 : ℤ))) := by
    ext ⟨x, d⟩
    simp only [zeroCoord, goodCoord, Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
      Finset.mem_insert, Finset.mem_singleton, Finset.mem_image, true_and, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨_, h1, h2⟩, rfl⟩
      exact ⟨x, rfl, rfl⟩
    · rintro ⟨x', rfl, rfl⟩
      exact ⟨⟨Or.inr (Or.inl rfl), by omega, by omega⟩, rfl⟩
  rw [h, Finset.card_image_of_injective _ (fun _ _ he => (Prod.mk.inj he).1), Finset.card_fin]

/-- For a span `D` and dimension `n`, valid coordinate-direction functions with nonzero direction. -/
def goodFuns (D n : ℕ) : Finset (Fin n → Fin 6 × ℤ) :=
  (Fintype.piFinset (fun _ : Fin n => goodCoord D)).filter fun f => ∃ i : Fin n, (f i).2 ≠ 0

lemma card_goodFuns (D n : ℕ) : (goodFuns D n).card = (goodCoord D).card ^ n - 6 ^ n := by
  let allF := Fintype.piFinset (fun _ : Fin n => goodCoord D)
  let zeroF := Fintype.piFinset (fun _ : Fin n => zeroCoord D)
  have hsub : zeroF ⊆ allF := by
    intro f hf
    simp only [allF, zeroF, Fintype.mem_piFinset] at hf ⊢
    intro i
    exact (Finset.mem_filter.mp (hf i)).1
  have hpart : goodFuns D n = allF \ zeroF := by
    ext f
    simp only [goodFuns, allF, zeroF, Finset.mem_filter, Finset.mem_sdiff, Fintype.mem_piFinset]
    constructor
    · rintro ⟨hf, i, hi⟩
      refine ⟨hf, ?_⟩
      intro hz
      exact hi (Finset.mem_filter.mp (hz i)).2
    · rintro ⟨hf, hnz⟩
      refine ⟨hf, ?_⟩
      by_contra h
      push_neg at h
      exact hnz fun i => Finset.mem_filter.mpr ⟨hf i, h i⟩
  have hunion : (allF \ zeroF) ∪ zeroF = allF := Finset.sdiff_union_of_subset hsub
  have hcard : (allF \ zeroF).card + zeroF.card = allF.card := by
    rw [← Finset.card_union_of_disjoint disjoint_sdiff_self_left, hunion]
  have hall : allF.card = (goodCoord D).card ^ n := by
    simp only [allF, Fintype.card_piFinset_const, Fintype.card_fin]
  have hzero : zeroF.card = 6 ^ n := by
    simp only [zeroF, Fintype.card_piFinset_const, Fintype.card_fin, card_zeroCoord]
  rw [hpart]
  omega

/-- All parameterizations `((a1, a2, D), f)` of ordered collinear 4-tuples in `{0..5}^n`. -/
def params (n : ℕ) : Finset ((ℕ × ℕ × ℕ) × (Fin n → Fin 6 × ℤ)) :=
  validPats.sigma (fun pat => goodFuns pat.2.2 n) |>.map
    ⟨fun x => (x.1, x.2), fun x y h => by cases x; cases y; simp_all⟩

lemma card_params (n : ℕ) :
    ((params n).card : ℤ) = 6 * 8 ^ n + 3 * 10 ^ n - 10 * 6 ^ n + 12 ^ n := by
  have hcard : (params n).card = ∑ pat ∈ validPats, (goodFuns pat.2.2 n).card := by
    rw [params, Finset.card_map, Finset.card_sigma]
  have hsum : ∑ pat ∈ validPats, (goodFuns pat.2.2 n).card =
      (12 ^ n - 6 ^ n) + 3 * (10 ^ n - 6 ^ n) + 6 * (8 ^ n - 6 ^ n) := by
    simp [validPats, card_goodFuns, card_goodCoord_3, card_goodCoord_4, card_goodCoord_5]
    ring
  rw [hcard, hsum]
  have h6_8 : 6 ^ n ≤ 8 ^ n := Nat.pow_le_pow_left (by omega) n
  have h6_10 : 6 ^ n ≤ 10 ^ n := Nat.pow_le_pow_left (by omega) n
  have h6_12 : 6 ^ n ≤ 12 ^ n := Nat.pow_le_pow_left (by omega) n
  push_cast [Nat.cast_sub h6_8, Nat.cast_sub h6_10, Nat.cast_sub h6_12]
  ring

/-- Evaluate point at integer step `t` along `f` (valid when `0 ≤ t ≤ D` and `f i ∈ goodCoord D`). -/
def evalPt {n : ℕ} (f : Fin n → Fin 6 × ℤ) (t : ℕ) : Fin n → Fin 6 :=
  fun i => ⟨(((f i).1.val : ℤ) + (t : ℤ) * (f i).2).toNat % 6, Nat.mod_lt _ (by decide)⟩

lemma evalPt_val {n : ℕ} {D t : ℕ} {f : Fin n → Fin 6 × ℤ} (ht : t ≤ D)
    (hf : ∀ i, f i ∈ goodCoord D) (i : Fin n) :
    ((evalPt f t i).val : ℤ) = ((f i).1.val : ℤ) + (t : ℤ) * (f i).2 := by
  have hmem := Finset.mem_filter.mp (hf i)
  have hd : (f i).2 = -1 ∨ (f i).2 = 0 ∨ (f i).2 = 1 := by
    have := (Finset.mem_product.mp hmem.1).2
    simpa using this
  have hbounds : 0 ≤ ((f i).1.val : ℤ) + (t : ℤ) * (f i).2 ∧
      ((f i).1.val : ℤ) + (t : ℤ) * (f i).2 ≤ 5 := by
    rcases hd with h | h | h <;> rw [h] at hmem ⊢ <;> omega
  have htoNat : (((f i).1.val : ℤ) + (t : ℤ) * (f i).2).toNat < 6 := by omega
  have hmod : (((f i).1.val : ℤ) + (t : ℤ) * (f i).2).toNat % 6 =
      (((f i).1.val : ℤ) + (t : ℤ) * (f i).2).toNat := Nat.mod_eq_of_lt htoNat
  change (((((f i).1.val : ℤ) + (t : ℤ) * (f i).2).toNat % 6 : ℕ) : ℤ) = _
  rw [hmod]
  omega

/-- The 4-element set associated to a parameterization. -/
def paramToSet {n : ℕ} (x : (ℕ × ℕ × ℕ) × (Fin n → Fin 6 × ℤ)) : Finset (Fin n → Fin 6) :=
  {evalPt x.2 0, evalPt x.2 x.1.1, evalPt x.2 x.1.2.1, evalPt x.2 x.1.2.2}

lemma evalPt_injective {n : ℕ} {D : ℕ} {f : Fin n → Fin 6 × ℤ}
    (hf : f ∈ goodFuns D n) {t1 t2 : ℕ} (ht1 : t1 ≤ D) (ht2 : t2 ≤ D)
    (heq : evalPt f t1 = evalPt f t2) : t1 = t2 := by
  obtain ⟨hf_all, i, hi⟩ := Finset.mem_filter.mp hf
  have hmem : ∀ j, f j ∈ goodCoord D := Fintype.mem_piFinset.mp hf_all
  have h1 := evalPt_val ht1 hmem i
  have h2 := evalPt_val ht2 hmem i
  have h3 : ((evalPt f t1 i).val : ℤ) = ((evalPt f t2 i).val : ℤ) := by rw [heq]
  have : (t1 : ℤ) * (f i).2 = (t2 : ℤ) * (f i).2 := by linarith
  have : (t1 : ℤ) = (t2 : ℤ) := mul_right_cancel₀ hi this
  exact_mod_cast this

lemma pat_bounds {pat : ℕ × ℕ × ℕ} (hpat : pat ∈ validPats) :
    0 < pat.1 ∧ pat.1 < pat.2.1 ∧ pat.2.1 < pat.2.2 ∧
      (pat.2.2 = 3 ∨ pat.2.2 = 4 ∨ pat.2.2 = 5) := by
  simp only [validPats, Finset.mem_insert, Finset.mem_singleton] at hpat
  rcases hpat with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

lemma paramToSet_card {n : ℕ} {x : (ℕ × ℕ × ℕ) × (Fin n → Fin 6 × ℤ)} (hx : x ∈ params n) :
    (paramToSet x).card = 4 := by
  rcases x with ⟨pat, f⟩
  have hx' : pat ∈ validPats ∧ f ∈ goodFuns pat.2.2 n := by
    simp only [params, Finset.mem_map, Finset.mem_sigma, Function.Embedding.coeFn_mk] at hx
    rcases hx with ⟨⟨p', f'⟩, ⟨hp', hf'⟩, heq⟩
    cases heq
    exact ⟨hp', hf'⟩
  obtain ⟨h0, h1, h2, _⟩ := pat_bounds hx'.1
  have hinj := fun (t1 t2 : ℕ) (ht1 : t1 ≤ pat.2.2) (ht2 : t2 ≤ pat.2.2) (h : evalPt f t1 = evalPt f t2) =>
    evalPt_injective hx'.2 ht1 ht2 h
  dsimp [paramToSet]
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_insert_of_notMem, Finset.card_singleton]
  · simp only [Finset.mem_singleton]
    intro h; exact absurd (hinj _ _ (by omega) le_rfl h) (by omega)
  · simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (h | h)
    · exact absurd (hinj _ _ (by omega) (by omega) h) (by omega)
    · exact absurd (hinj _ _ (by omega) le_rfl h) (by omega)
  · simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (h | h | h)
    · exact absurd (hinj _ _ (by omega) (by omega) h) (by omega)
    · exact absurd (hinj _ _ (by omega) (by omega) h) (by omega)
    · exact absurd (hinj _ _ (by omega) le_rfl h) (by omega)

lemma paramToSet_collinear {n : ℕ} {x : (ℕ × ℕ × ℕ) × (Fin n → Fin 6 × ℤ)} (hx : x ∈ params n) :
    Collinear ℝ (toReal '' (paramToSet x : Set (Fin n → Fin 6))) := by
  rcases x with ⟨pat, f⟩
  have hx' : pat ∈ validPats ∧ f ∈ goodFuns pat.2.2 n := by
    simp only [params, Finset.mem_map, Finset.mem_sigma, Function.Embedding.coeFn_mk] at hx
    rcases hx with ⟨⟨p', f'⟩, ⟨hp', hf'⟩, heq⟩
    cases heq
    exact ⟨hp', hf'⟩
  obtain ⟨h0, h1, h2, _⟩ := pat_bounds hx'.1
  have hmem : ∀ i, f i ∈ goodCoord pat.2.2 := Fintype.mem_piFinset.mp (Finset.mem_filter.mp hx'.2).1
  rw [collinear_iff_exists_forall_eq_smul_vadd]
  refine ⟨fun i => ((f i).1.val : ℝ), fun i => ((f i).2 : ℝ), ?_⟩
  rintro _ ⟨q, hq, rfl⟩
  simp only [paramToSet, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hq
  have hstep : ∀ t : ℕ, t ≤ pat.2.2 →
      toReal (evalPt f t) = (t : ℝ) • (fun i => ((f i).2 : ℝ)) +ᵥ (fun i => ((f i).1.val : ℝ)) := by
    intro t ht
    ext i
    simp only [toReal, vadd_eq_add, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hv := evalPt_val ht hmem i
    have hvR : ((evalPt f t i).val : ℝ) = ((f i).1.val : ℝ) + (t : ℝ) * ((f i).2 : ℝ) := by
      exact_mod_cast hv
    linarith
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨((0 : ℕ) : ℝ), hstep 0 (by omega)⟩
  · exact ⟨pat.1, hstep pat.1 (by omega)⟩
  · exact ⟨pat.2.1, hstep pat.2.1 (by omega)⟩
  · exact ⟨pat.2.2, hstep pat.2.2 le_rfl⟩

/-- The finite set of collinear 4-element subsets of `{0..5}^n`. -/
noncomputable def collinear4 (n : ℕ) : Finset (Finset (Fin n → Fin 6)) :=
  by
    classical
    exact Finset.univ.filter fun s => s.card = 4 ∧ Collinear ℝ (toReal '' (s : Set (Fin n → Fin 6)))

lemma a_eq_card_collinear4 (n : ℕ) : a n = (collinear4 n).card := by
  classical
  dsimp [a, collinear4]
  rw [← Set.ncard_coe_finset]
  congr 1
  ext s
  simp

lemma toReal_injective {n : ℕ} : Function.Injective (@toReal n) := by
  intro p q h
  ext i
  have hi : ((p i).val : ℝ) = ((q i).val : ℝ) := congrFun h i
  exact_mod_cast hi

/-- Key divisibility lemma: for `D ∈ {3, 4, 5}`, `0 < a1 < a2 < D`, and `|Δ| ≤ 5`,
if `D ∣ a1 * Δ` and `D ∣ a2 * Δ`, then `Δ ∈ {-D, 0, D}`. -/
lemma span_dvd_cases (D a1 a2 : ℕ) (Δ : ℤ)
    (hD : D = 3 ∨ D = 4 ∨ D = 5) (ha1 : 0 < a1) (ha12 : a1 < a2) (ha2 : a2 < D)
    (hΔ : -5 ≤ Δ ∧ Δ ≤ 5)
    (hd1 : (D : ℤ) ∣ (a1 : ℤ) * Δ) (hd2 : (D : ℤ) ∣ (a2 : ℤ) * Δ) :
    Δ = -(D : ℤ) ∨ Δ = 0 ∨ Δ = (D : ℤ) := by
  obtain ⟨k1, hk1⟩ := hd1
  obtain ⟨k2, hk2⟩ := hd2
  have ha1_ub : a1 < 5 := by omega
  have ha2_ub : a2 < 5 := by omega
  rcases hD with rfl | rfl | rfl <;> interval_cases a1 <;> interval_cases a2 <;> omega

/-- Reversal of a parameterization gives another parameterization with the same 4-set. -/
def revParam {n : ℕ} (x : (ℕ × ℕ × ℕ) × (Fin n → Fin 6 × ℤ)) :
    (ℕ × ℕ × ℕ) × (Fin n → Fin 6 × ℤ) :=
  ((x.1.2.2 - x.1.2.1, x.1.2.2 - x.1.1, x.1.2.2),
   fun i => (evalPt x.2 x.1.2.2 i, -(x.2 i).2))

lemma revParam_mem {n : ℕ} {x : (ℕ × ℕ × ℕ) × (Fin n → Fin 6 × ℤ)} (hx : x ∈ params n) :
    revParam x ∈ params n := by
  rcases x with ⟨pat, f⟩
  have hx' : pat ∈ validPats ∧ f ∈ goodFuns pat.2.2 n := by
    simp only [params, Finset.mem_map, Finset.mem_sigma, Function.Embedding.coeFn_mk] at hx
    rcases hx with ⟨⟨p', f'⟩, ⟨hp', hf'⟩, heq⟩
    cases heq
    exact ⟨hp', hf'⟩
  have hpat' : (pat.2.2 - pat.2.1, pat.2.2 - pat.1, pat.2.2) ∈ validPats := by
    have hp := hx'.1
    simp only [validPats, Finset.mem_insert, Finset.mem_singleton] at hp ⊢
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hf_all : ∀ i, f i ∈ goodCoord pat.2.2 := Fintype.mem_piFinset.mp (Finset.mem_filter.mp hx'.2).1
  obtain ⟨i0, hi0⟩ := (Finset.mem_filter.mp hx'.2).2
  simp only [params, revParam, Finset.mem_map, Finset.mem_sigma, Function.Embedding.coeFn_mk]
  refine ⟨⟨(pat.2.2 - pat.2.1, pat.2.2 - pat.1, pat.2.2), fun i => (evalPt f pat.2.2 i, -(f i).2)⟩,
    ⟨hpat', ?_⟩, rfl⟩
  simp only [goodFuns, Finset.mem_filter, Fintype.mem_piFinset]
  refine ⟨fun i => ?_, i0, by omega⟩
  have hmem := Finset.mem_filter.mp (hf_all i)
  have hd : (f i).2 = -1 ∨ (f i).2 = 0 ∨ (f i).2 = 1 := by
    have := (Finset.mem_product.mp hmem.1).2; simpa using this
  have hev := evalPt_val (le_rfl : pat.2.2 ≤ pat.2.2) hf_all i
  simp only [goodCoord, Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
    Finset.mem_insert, Finset.mem_singleton, true_and]
  refine ⟨by rcases hd with h | h | h <;> simp [h], ?_, ?_⟩ <;> linarith [(f i).1.isLt]

lemma revParam_ne {n : ℕ} {x : (ℕ × ℕ × ℕ) × (Fin n → Fin 6 × ℤ)} (hx : x ∈ params n) :
    revParam x ≠ x := by
  rcases x with ⟨pat, f⟩
  have hx' : f ∈ goodFuns pat.2.2 n := by
    simp only [params, Finset.mem_map, Finset.mem_sigma, Function.Embedding.coeFn_mk] at hx
    rcases hx with ⟨⟨p', f'⟩, ⟨_, hf'⟩, heq⟩
    cases heq; exact hf'
  obtain ⟨i0, hi0⟩ := (Finset.mem_filter.mp hx').2
  intro heq
  have h2 := congrArg (fun z => (z.2 i0).2) heq
  dsimp [revParam] at h2
  omega

lemma paramToSet_revParam {n : ℕ} {x : (ℕ × ℕ × ℕ) × (Fin n → Fin 6 × ℤ)} (hx : x ∈ params n) :
    paramToSet (revParam x) = paramToSet x := by
  rcases x with ⟨pat, f⟩
  have hx' : pat ∈ validPats ∧ f ∈ goodFuns pat.2.2 n := by
    simp only [params, Finset.mem_map, Finset.mem_sigma, Function.Embedding.coeFn_mk] at hx
    rcases hx with ⟨⟨p', f'⟩, ⟨hp', hf'⟩, heq⟩
    cases heq; exact ⟨hp', hf'⟩
  have hrev := revParam_mem hx
  have hrev' : (fun i => (evalPt f pat.2.2 i, -(f i).2)) ∈ goodFuns pat.2.2 n := by
    simp only [params, revParam, Finset.mem_map, Finset.mem_sigma, Function.Embedding.coeFn_mk] at hrev
    rcases hrev with ⟨⟨p', f'⟩, ⟨_, hf'⟩, heq⟩
    cases heq; exact hf'
  have hf_all : ∀ i, f i ∈ goodCoord pat.2.2 := Fintype.mem_piFinset.mp (Finset.mem_filter.mp hx'.2).1
  have hr_all : ∀ i, (evalPt f pat.2.2 i, -(f i).2) ∈ goodCoord pat.2.2 :=
    Fintype.mem_piFinset.mp (Finset.mem_filter.mp hrev').1
  obtain ⟨h0, h1, h2, _⟩ := pat_bounds hx'.1
  have hpt : ∀ t : ℕ, t ≤ pat.2.2 →
      evalPt (fun i => (evalPt f pat.2.2 i, -(f i).2)) t = evalPt f (pat.2.2 - t) := by
    intro t ht
    ext i
    have h1 := evalPt_val ht hr_all i
    have h2 := evalPt_val (le_rfl : pat.2.2 ≤ pat.2.2) hf_all i
    have h3 := evalPt_val (Nat.sub_le pat.2.2 t) hf_all i
    have hcast : ((pat.2.2 - t : ℕ) : ℤ) = (pat.2.2 : ℤ) - (t : ℤ) := Nat.cast_sub ht
    dsimp only at h1
    have : ((evalPt (fun i => (evalPt f pat.2.2 i, -(f i).2)) t i).val : ℤ) =
        ((evalPt f (pat.2.2 - t) i).val : ℤ) := by
      rw [h1, h2, h3, hcast]; ring
    exact_mod_cast this
  dsimp [paramToSet, revParam]
  rw [hpt 0 (by omega), hpt (pat.2.2 - pat.2.1) (by omega),
      hpt (pat.2.2 - pat.1) (by omega), hpt pat.2.2 le_rfl]
  have hs0 : pat.2.2 - 0 = pat.2.2 := Nat.sub_zero _
  have hs1 : pat.2.2 - (pat.2.2 - pat.2.1) = pat.2.1 := Nat.sub_sub_self (by omega)
  have hs2 : pat.2.2 - (pat.2.2 - pat.1) = pat.1 := Nat.sub_sub_self (by omega)
  have hs3 : pat.2.2 - pat.2.2 = 0 := Nat.sub_self _
  rw [hs0, hs1, hs2, hs3]
  ext q
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto

lemma mem_validPats_of_bounds {a1 a2 D : ℕ}
    (h1 : 0 < a1) (h2 : a1 < a2) (h3 : a2 < D) (h4 : D = 3 ∨ D = 4 ∨ D = 5) :
    (a1, a2, D) ∈ validPats := by
  have ha1 : a1 < 5 := by omega
  have ha2 : a2 < 5 := by omega
  rcases h4 with rfl | rfl | rfl <;> interval_cases a1 <;> interval_cases a2 <;>
    first | omega | decide

/-- Every collinear 4-set has a parameterization in `params n`. -/
lemma exists_param_of_collinear4 {n : ℕ} {S : Finset (Fin n → Fin 6)}
    (hS : S ∈ collinear4 n) : ∃ x ∈ params n, paramToSet x = S := by
  classical
  have hS' : S.card = 4 ∧ Collinear ℝ (toReal '' (S : Set (Fin n → Fin 6))) := by
    simpa [collinear4] using hS
  obtain ⟨hcard, hcoll⟩ := hS'
  rw [collinear_iff_exists_forall_eq_smul_vadd] at hcoll
  obtain ⟨p0, w, hw⟩ := hcoll
  -- Extract the scalar parameter for each element of S
  have hparam : ∀ q ∈ S, ∃ t : ℝ, toReal q = t • w + p0 := by
    intro q hq
    obtain ⟨t, ht⟩ := hw (toReal q) ⟨q, hq, rfl⟩
    exact ⟨t, by simpa [vadd_eq_add] using ht⟩
  choose t_of ht_of using hparam
  -- Show w ≠ 0
  have hw_ne : w ≠ 0 := by
    intro hw0
    have hle1 : S.card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      apply toReal_injective
      rw [ht_of a ha, ht_of b hb, hw0, smul_zero, smul_zero]
    omega
  -- Show t_of is injective on S
  have ht_inj : ∀ a ha b hb, t_of a ha = t_of b hb → a = b := by
    intro a ha b hb hteq
    apply toReal_injective
    rw [ht_of a ha, ht_of b hb, hteq]
  -- Sort the 4 elements of S by their t-values
  let ts : Finset ℝ := S.attach.image fun q => t_of q.1 q.2
  have hts_card : ts.card = 4 := by
    rw [Finset.card_image_of_injective]
    · rw [Finset.card_attach, hcard]
    · intro a b hab
      exact Subtype.ext (ht_inj a.1 a.2 b.1 b.2 hab)
  let L := ts.sort (· ≤ ·)
  have hL_len : L.length = 4 := by rw [Finset.length_sort, hts_card]
  have hL_nodup : L.Nodup := Finset.sort_nodup _ _
  have hL_sorted : L.Pairwise (· ≤ ·) := Finset.pairwise_sort _ _
  -- Extract the 4 sorted real numbers t0 < t1 < t2 < t3
  rcases hL_eq : L with _ | ⟨t0, _ | ⟨t1, _ | ⟨t2, _ | ⟨t3, _ | _⟩⟩⟩⟩
  · simp [hL_eq] at hL_len
  · simp [hL_eq] at hL_len
  · simp [hL_eq] at hL_len
  · simp [hL_eq] at hL_len
  swap
  · simp [hL_eq] at hL_len
  have ht_mem : ∀ r ∈ [t0, t1, t2, t3], r ∈ ts := by
    intro r hr
    rw [← hL_eq] at hr
    exact (Finset.mem_sort (· ≤ ·)).mp hr
  have ht_lt : t0 < t1 ∧ t1 < t2 ∧ t2 < t3 := by
    rw [hL_eq] at hL_sorted hL_nodup
    simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, List.Pairwise.nil, and_true, List.nodup_cons, not_or] at hL_sorted hL_nodup
    exact ⟨lt_of_le_of_ne hL_sorted.1.1 hL_nodup.1.1,
           lt_of_le_of_ne hL_sorted.2.1.1 hL_nodup.2.1.1,
           lt_of_le_of_ne hL_sorted.2.2.1 hL_nodup.2.2.1⟩
  -- Pull back t0, t1, t2, t3 to x0, x1, x2, x3 ∈ S
  have hex_x : ∀ r ∈ ts, ∃ q ∈ S, toReal q = r • w + p0 := by
    intro r hr
    rcases Finset.mem_image.mp hr with ⟨⟨q, hq⟩, _, rfl⟩
    exact ⟨q, hq, ht_of q hq⟩
  obtain ⟨x0, hx0S, hx0⟩ := hex_x t0 (ht_mem t0 (by simp))
  obtain ⟨x1, hx1S, hx1⟩ := hex_x t1 (ht_mem t1 (by simp))
  obtain ⟨x2, hx2S, hx2⟩ := hex_x t2 (ht_mem t2 (by simp))
  obtain ⟨x3, hx3S, hx3⟩ := hex_x t3 (ht_mem t3 (by simp))
  -- S = {x0, x1, x2, x3}
  have hS_eq : ({x0, x1, x2, x3} : Finset _) = S := by
    apply Finset.eq_of_subset_of_card_le
    · intro q hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl | rfl | rfl <;> assumption
    · rw [hcard]
      have hne_of_t : ∀ a b : Fin n → Fin 6, ∀ ta tb : ℝ,
          toReal a = ta • w + p0 → toReal b = tb • w + p0 → ta ≠ tb → a ≠ b := by
        intro a b ta tb ha hb hne hab
        rw [hab] at ha
        have h1 : (ta - tb) • w = 0 := by
          rw [sub_smul]; exact sub_eq_zero.mpr (add_right_cancel (ha.symm.trans hb))
        rcases smul_eq_zero.mp h1 with hsub | hw0
        · exact hne (sub_eq_zero.mp hsub)
        · exact hw_ne hw0
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
          Finset.card_insert_of_notMem, Finset.card_singleton]
      · simp only [Finset.mem_singleton]
        exact hne_of_t x2 x3 t2 t3 hx2 hx3 (ne_of_lt ht_lt.2.2)
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hne_of_t x1 x2 t1 t2 hx1 hx2 (ne_of_lt ht_lt.2.1),
               hne_of_t x1 x3 t1 t3 hx1 hx3 (ne_of_lt (lt_trans ht_lt.2.1 ht_lt.2.2))⟩
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hne_of_t x0 x1 t0 t1 hx0 hx1 (ne_of_lt ht_lt.1),
               hne_of_t x0 x2 t0 t2 hx0 hx2 (ne_of_lt (lt_trans ht_lt.1 ht_lt.2.1)),
               hne_of_t x0 x3 t0 t3 hx0 hx3 (ne_of_lt (lt_trans ht_lt.1 (lt_trans ht_lt.2.1 ht_lt.2.2)))⟩
  -- Pick coordinate i0 where w i0 ≠ 0
  have hex_i0 : ∃ i0 : Fin n, w i0 ≠ 0 := by
    by_contra h
    push_neg at h
    exact hw_ne (funext h)
  obtain ⟨i0, hi0⟩ := hex_i0
  -- Coordinatewise affine relation
  have hcoord : ∀ (k : Fin n),
      ((x1 k).val : ℝ) - ((x0 k).val : ℝ) = (t1 - t0) * w k ∧
      ((x2 k).val : ℝ) - ((x0 k).val : ℝ) = (t2 - t0) * w k ∧
      ((x3 k).val : ℝ) - ((x0 k).val : ℝ) = (t3 - t0) * w k := by
    intro k
    have h0 := congrFun hx0 k
    have h1 := congrFun hx1 k
    have h2 := congrFun hx2 k
    have h3 := congrFun hx3 k
    simp only [toReal, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h0 h1 h2 h3
    exact ⟨by linarith, by linarith, by linarith⟩
  -- At coordinate i0, the 4 values are strictly monotone in {0..5}, so D ∈ {3, 4, 5}
  have hc0 := hcoord i0
  let Δ0 : ℤ := ((x3 i0).val : ℤ) - ((x0 i0).val : ℤ)
  let δ1 : ℤ := ((x1 i0).val : ℤ) - ((x0 i0).val : ℤ)
  let δ2 : ℤ := ((x2 i0).val : ℤ) - ((x0 i0).val : ℤ)
  have hΔ0_bounds : (0 < δ1 ∧ δ1 < δ2 ∧ δ2 < Δ0 ∧ Δ0 ≤ 5) ∨
      (-5 ≤ Δ0 ∧ Δ0 < δ2 ∧ δ2 < δ1 ∧ δ1 < 0) := by
    have hlt0 : 0 < t1 - t0 := by linarith
    have hlt1 : 0 < t2 - t1 := by linarith
    have hlt2 : 0 < t3 - t2 := by linarith
    have h0lt : (x0 i0).val < 6 := (x0 i0).isLt
    have h3lt : (x3 i0).val < 6 := (x3 i0).isLt
    rcases lt_or_gt_of_ne hi0 with hwneg | hwpos
    · right
      have h1 : ((x3 i0).val : ℝ) < ((x2 i0).val : ℝ) := by nlinarith
      have h2 : ((x2 i0).val : ℝ) < ((x1 i0).val : ℝ) := by nlinarith
      have h3 : ((x1 i0).val : ℝ) < ((x0 i0).val : ℝ) := by nlinarith
      have h1z : ((x3 i0).val : ℤ) < ((x2 i0).val : ℤ) := by exact_mod_cast h1
      have h2z : ((x2 i0).val : ℤ) < ((x1 i0).val : ℤ) := by exact_mod_cast h2
      have h3z : ((x1 i0).val : ℤ) < ((x0 i0).val : ℤ) := by exact_mod_cast h3
      dsimp [Δ0, δ1, δ2]; omega
    · left
      have h1 : ((x0 i0).val : ℝ) < ((x1 i0).val : ℝ) := by nlinarith
      have h2 : ((x1 i0).val : ℝ) < ((x2 i0).val : ℝ) := by nlinarith
      have h3 : ((x2 i0).val : ℝ) < ((x3 i0).val : ℝ) := by nlinarith
      have h1z : ((x0 i0).val : ℤ) < ((x1 i0).val : ℤ) := by exact_mod_cast h1
      have h2z : ((x1 i0).val : ℤ) < ((x2 i0).val : ℤ) := by exact_mod_cast h2
      have h3z : ((x2 i0).val : ℤ) < ((x3 i0).val : ℤ) := by exact_mod_cast h3
      dsimp [Δ0, δ1, δ2]; omega
  let D : ℕ := Δ0.natAbs
  let a1 : ℕ := δ1.natAbs
  let a2 : ℕ := δ2.natAbs
  have hpat_info : 0 < a1 ∧ a1 < a2 ∧ a2 < D ∧ (D = 3 ∨ D = 4 ∨ D = 5) := by
    dsimp [D, a1, a2]
    rcases hΔ0_bounds with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ <;> omega
  have hpat_mem : (a1, a2, D) ∈ validPats :=
    mem_validPats_of_bounds hpat_info.1 hpat_info.2.1 hpat_info.2.2.1 hpat_info.2.2.2
  -- Cross-multiplication identity: for all k, D * (x1 k - x0 k) = a1 * (x3 k - x0 k) and D * (x2 k - x0 k) = a2 * (x3 k - x0 k)
  have hratio_i0 : (a1 : ℝ) * (t3 - t0) = (D : ℝ) * (t1 - t0) ∧
      (a2 : ℝ) * (t3 - t0) = (D : ℝ) * (t2 - t0) := by
    have hsign : ((a1 : ℝ) * ((x3 i0).val - (x0 i0).val : ℝ) = (D : ℝ) * ((x1 i0).val - (x0 i0).val : ℝ)) ∧
        ((a2 : ℝ) * ((x3 i0).val - (x0 i0).val : ℝ) = (D : ℝ) * ((x2 i0).val - (x0 i0).val : ℝ)) := by
      have h1z : (a1 : ℤ) * Δ0 = (D : ℤ) * δ1 := by
        dsimp [a1, D]
        rcases hΔ0_bounds with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
        · rw [Int.natAbs_of_nonneg (by omega), Int.natAbs_of_nonneg (by omega)]; ring
        · have ha : ((δ1.natAbs : ℕ) : ℤ) = -δ1 := by omega
          have hd : ((Δ0.natAbs : ℕ) : ℤ) = -Δ0 := by omega
          rw [ha, hd]; ring
      have h2z : (a2 : ℤ) * Δ0 = (D : ℤ) * δ2 := by
        dsimp [a2, D]
        rcases hΔ0_bounds with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
        · rw [Int.natAbs_of_nonneg (by omega), Int.natAbs_of_nonneg (by omega)]; ring
        · have ha : ((δ2.natAbs : ℕ) : ℤ) = -δ2 := by omega
          have hd : ((Δ0.natAbs : ℕ) : ℤ) = -Δ0 := by omega
          rw [ha, hd]; ring
      constructor
      · have h1R : ((a1 : ℤ) * Δ0 : ℝ) = ((D : ℤ) * δ1 : ℝ) := by exact_mod_cast h1z
        dsimp [Δ0, δ1] at h1R; push_cast at h1R; exact h1R
      · have h2R : ((a2 : ℤ) * Δ0 : ℝ) = ((D : ℤ) * δ2 : ℝ) := by exact_mod_cast h2z
        dsimp [Δ0, δ2] at h2R; push_cast at h2R; exact h2R
    constructor
    · have h1 := hsign.1
      rw [hc0.1, hc0.2.2] at h1
      have : ((a1 : ℝ) * (t3 - t0) - (D : ℝ) * (t1 - t0)) * w i0 = 0 := by linarith
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hi0)
    · have h2 := hsign.2
      rw [hc0.2.1, hc0.2.2] at h2
      have : ((a2 : ℝ) * (t3 - t0) - (D : ℝ) * (t2 - t0)) * w i0 = 0 := by linarith
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hi0)
  have hcross : ∀ k : Fin n,
      (D : ℤ) * (((x1 k).val : ℤ) - ((x0 k).val : ℤ)) = (a1 : ℤ) * (((x3 k).val : ℤ) - ((x0 k).val : ℤ)) ∧
      (D : ℤ) * (((x2 k).val : ℤ) - ((x0 k).val : ℤ)) = (a2 : ℤ) * (((x3 k).val : ℤ) - ((x0 k).val : ℤ)) := by
    intro k
    have hck := hcoord k
    have h1R : (D : ℝ) * (((x1 k).val : ℝ) - ((x0 k).val : ℝ)) =
        (a1 : ℝ) * (((x3 k).val : ℝ) - ((x0 k).val : ℝ)) := by
      rw [hck.1, hck.2.2]
      calc (D : ℝ) * ((t1 - t0) * w k) = ((D : ℝ) * (t1 - t0)) * w k := by ring
        _ = ((a1 : ℝ) * (t3 - t0)) * w k := by rw [← hratio_i0.1]
        _ = (a1 : ℝ) * ((t3 - t0) * w k) := by ring
    have h2R : (D : ℝ) * (((x2 k).val : ℝ) - ((x0 k).val : ℝ)) =
        (a2 : ℝ) * (((x3 k).val : ℝ) - ((x0 k).val : ℝ)) := by
      rw [hck.2.1, hck.2.2]
      calc (D : ℝ) * ((t2 - t0) * w k) = ((D : ℝ) * (t2 - t0)) * w k := by ring
        _ = ((a2 : ℝ) * (t3 - t0)) * w k := by rw [← hratio_i0.2]
        _ = (a2 : ℝ) * ((t3 - t0) * w k) := by ring
    exact ⟨by exact_mod_cast h1R, by exact_mod_cast h2R⟩
  -- For every coordinate k, Δ_k = x3 k - x0 k ∈ {-D, 0, D}
  have hΔ_cases : ∀ k : Fin n,
      (((x3 k).val : ℤ) - ((x0 k).val : ℤ)) = -(D : ℤ) ∨
      (((x3 k).val : ℤ) - ((x0 k).val : ℤ)) = 0 ∨
      (((x3 k).val : ℤ) - ((x0 k).val : ℤ)) = (D : ℤ) := by
    intro k
    have hck := hcross k
    have h0lt : (x0 k).val < 6 := (x0 k).isLt
    have h3lt : (x3 k).val < 6 := (x3 k).isLt
    exact span_dvd_cases D a1 a2 (((x3 k).val : ℤ) - ((x0 k).val : ℤ))
      hpat_info.2.2.2 hpat_info.1 hpat_info.2.1 hpat_info.2.2.1 (by omega)
      ⟨((x1 k).val : ℤ) - ((x0 k).val : ℤ), hck.1.symm⟩
      ⟨((x2 k).val : ℤ) - ((x0 k).val : ℤ), hck.2.symm⟩
  -- Build f : Fin n → Fin 6 × ℤ
  let f : Fin n → Fin 6 × ℤ := fun k => (x0 k, (((x3 k).val : ℤ) - ((x0 k).val : ℤ)) / (D : ℤ))
  have hf_dir : ∀ k, (f k).2 = -1 ∨ (f k).2 = 0 ∨ (f k).2 = 1 := by
    intro k
    dsimp [f]
    have hDpos : (0 : ℤ) < (D : ℤ) := by omega
    rcases hΔ_cases k with h | h | h <;> rw [h]
    · left; exact Int.neg_ediv_of_dvd (dvd_refl _) ▸ by simp [Int.ediv_self (ne_of_gt hDpos)]
    · right; left; simp
    · right; right; exact Int.ediv_self (ne_of_gt hDpos)
  have hf_mul : ∀ k, (D : ℤ) * (f k).2 = ((x3 k).val : ℤ) - ((x0 k).val : ℤ) := by
    intro k
    dsimp [f]
    have hDpos : (0 : ℤ) < (D : ℤ) := by omega
    rcases hΔ_cases k with h | h | h <;> rw [h]
    · have : -(D : ℤ) / (D : ℤ) = -1 := by
        rw [Int.neg_ediv_of_dvd (dvd_refl _), Int.ediv_self (ne_of_gt hDpos)]
      rw [this]; ring
    · simp
    · rw [Int.ediv_self (ne_of_gt hDpos)]; ring
  have hf_good : f ∈ goodFuns D n := by
    simp only [goodFuns, Finset.mem_filter, Fintype.mem_piFinset]
    refine ⟨fun k => ?_, i0, ?_⟩
    · simp only [goodCoord, Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
        Finset.mem_insert, Finset.mem_singleton, true_and]
      have h3lt := (x3 k).isLt
      refine ⟨hf_dir k, ?_, ?_⟩ <;> dsimp [f] <;> linarith [hf_mul k]
    · intro h0
      have h := hf_mul i0
      rw [h0, mul_zero] at h
      rcases hΔ0_bounds with ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ <;> dsimp [Δ0] at * <;> omega
  have hx_mem : ((a1, a2, D), f) ∈ params n := by
    simp only [params, Finset.mem_map, Finset.mem_sigma, Function.Embedding.coeFn_mk]
    exact ⟨⟨(a1, a2, D), f⟩, ⟨hpat_mem, hf_good⟩, rfl⟩
  refine ⟨((a1, a2, D), f), hx_mem, ?_⟩
  have hf_all : ∀ k, f k ∈ goodCoord D := Fintype.mem_piFinset.mp (Finset.mem_filter.mp hf_good).1
  have hDne : (D : ℤ) ≠ 0 := by omega
  have hev0 : evalPt f 0 = x0 := by
    ext k
    have h := evalPt_val (Nat.zero_le D) hf_all k
    simp only [Nat.cast_zero, zero_mul, add_zero] at h
    exact_mod_cast h
  have hev1 : evalPt f a1 = x1 := by
    ext k
    have h := evalPt_val (by omega : a1 ≤ D) hf_all k
    have hck := (hcross k).1
    have hmul := hf_mul k
    have : (D : ℤ) * ((evalPt f a1 k).val : ℤ) = (D : ℤ) * ((x1 k).val : ℤ) := by
      calc (D : ℤ) * ((evalPt f a1 k).val : ℤ)
          = (D : ℤ) * (((x0 k).val : ℤ) + (a1 : ℤ) * (f k).2) := by rw [h]
        _ = (D : ℤ) * ((x0 k).val : ℤ) + (a1 : ℤ) * ((D : ℤ) * (f k).2) := by ring
        _ = (D : ℤ) * ((x0 k).val : ℤ) + (a1 : ℤ) * (((x3 k).val : ℤ) - ((x0 k).val : ℤ)) := by rw [hmul]
        _ = (D : ℤ) * ((x0 k).val : ℤ) + (D : ℤ) * (((x1 k).val : ℤ) - ((x0 k).val : ℤ)) := by rw [hck]
        _ = (D : ℤ) * ((x1 k).val : ℤ) := by ring
    exact_mod_cast mul_left_cancel₀ hDne this
  have hev2 : evalPt f a2 = x2 := by
    ext k
    have h := evalPt_val (by omega : a2 ≤ D) hf_all k
    have hck := (hcross k).2
    have hmul := hf_mul k
    have : (D : ℤ) * ((evalPt f a2 k).val : ℤ) = (D : ℤ) * ((x2 k).val : ℤ) := by
      calc (D : ℤ) * ((evalPt f a2 k).val : ℤ)
          = (D : ℤ) * (((x0 k).val : ℤ) + (a2 : ℤ) * (f k).2) := by rw [h]
        _ = (D : ℤ) * ((x0 k).val : ℤ) + (a2 : ℤ) * ((D : ℤ) * (f k).2) := by ring
        _ = (D : ℤ) * ((x0 k).val : ℤ) + (a2 : ℤ) * (((x3 k).val : ℤ) - ((x0 k).val : ℤ)) := by rw [hmul]
        _ = (D : ℤ) * ((x0 k).val : ℤ) + (D : ℤ) * (((x2 k).val : ℤ) - ((x0 k).val : ℤ)) := by rw [hck]
        _ = (D : ℤ) * ((x2 k).val : ℤ) := by ring
    exact_mod_cast mul_left_cancel₀ hDne this
  have hev3 : evalPt f D = x3 := by
    ext k
    have h := evalPt_val (le_rfl : D ≤ D) hf_all k
    have hmul := hf_mul k
    have : ((evalPt f D k).val : ℤ) = ((x3 k).val : ℤ) := by linarith
    exact_mod_cast this
  dsimp [paramToSet]
  rw [hev0, hev1, hev2, hev3, hS_eq]

lemma eq_of_strict_mono_finset_eq {a0 a1 a2 a3 b0 b1 b2 b3 : ℤ}
    (ha : a0 < a1 ∧ a1 < a2 ∧ a2 < a3) (hb : b0 < b1 ∧ b1 < b2 ∧ b2 < b3)
    (heq : ({a0, a1, a2, a3} : Finset ℤ) = {b0, b1, b2, b3}) :
    a0 = b0 ∧ a1 = b1 ∧ a2 = b2 ∧ a3 = b3 := by
  have hmem : ∀ z, z ∈ ({a0, a1, a2, a3} : Finset ℤ) ↔ z ∈ ({b0, b1, b2, b3} : Finset ℤ) :=
    fun z => by rw [heq]
  have ha0 := (hmem a0).mp (by simp)
  have ha1 := (hmem a1).mp (by simp)
  have ha2 := (hmem a2).mp (by simp)
  have ha3 := (hmem a3).mp (by simp)
  have hb0 := (hmem b0).mpr (by simp)
  have hb1 := (hmem b1).mpr (by simp)
  have hb2 := (hmem b2).mpr (by simp)
  have hb3 := (hmem b3).mpr (by simp)
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3
  have e0 : a0 = b0 := by omega
  have e3 : a3 = b3 := by omega
  have e1 : a1 = b1 := by omega
  have e2 : a2 = b2 := by omega
  exact ⟨e0, e1, e2, e3⟩

lemma finset_rev4 {α : Type*} [DecidableEq α] (a b c d : α) :
    ({d, c, b, a} : Finset α) = {a, b, c, d} := by
  ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto

lemma param_eq_or_rev {n : ℕ} {x y : (ℕ × ℕ × ℕ) × (Fin n → Fin 6 × ℤ)}
    (hx : x ∈ params n) (hy : y ∈ params n) (heq : paramToSet x = paramToSet y) :
    y = x ∨ y = revParam x := by
  rcases x with ⟨px, fx⟩
  rcases y with ⟨py, fy⟩
  have hx' : px ∈ validPats ∧ fx ∈ goodFuns px.2.2 n := by
    simp only [params, Finset.mem_map, Finset.mem_sigma] at hx
    rcases hx with ⟨⟨p', f'⟩, ⟨hp', hf'⟩, h⟩; cases h; exact ⟨hp', hf'⟩
  have hy' : py ∈ validPats ∧ fy ∈ goodFuns py.2.2 n := by
    simp only [params, Finset.mem_map, Finset.mem_sigma] at hy
    rcases hy with ⟨⟨p', f'⟩, ⟨hp', hf'⟩, h⟩; cases h; exact ⟨hp', hf'⟩
  obtain ⟨hx0, hx1, hx2, _⟩ := pat_bounds hx'.1
  obtain ⟨hy0, hy1, hy2, _⟩ := pat_bounds hy'.1
  have hfx_all : ∀ k, fx k ∈ goodCoord px.2.2 := Fintype.mem_piFinset.mp (Finset.mem_filter.mp hx'.2).1
  have hfy_all : ∀ k, fy k ∈ goodCoord py.2.2 := Fintype.mem_piFinset.mp (Finset.mem_filter.mp hy'.2).1
  obtain ⟨i0, hi0⟩ := (Finset.mem_filter.mp hx'.2).2
  have hvx : ∀ t, t ≤ px.2.2 → ∀ k, ((evalPt fx t k).val : ℤ) = ((fx k).1.val : ℤ) + (t : ℤ) * (fx k).2 :=
    fun t ht k => evalPt_val ht hfx_all k
  have hvy : ∀ t, t ≤ py.2.2 → ∀ k, ((evalPt fy t k).val : ℤ) = ((fy k).1.val : ℤ) + (t : ℤ) * (fy k).2 :=
    fun t ht k => evalPt_val ht hfy_all k
  have hset_i0 : ({((evalPt fx 0 i0).val : ℤ), ((evalPt fx px.1 i0).val : ℤ),
      ((evalPt fx px.2.1 i0).val : ℤ), ((evalPt fx px.2.2 i0).val : ℤ)} : Finset ℤ) =
      {((evalPt fy 0 i0).val : ℤ), ((evalPt fy py.1 i0).val : ℤ),
       ((evalPt fy py.2.1 i0).val : ℤ), ((evalPt fy py.2.2 i0).val : ℤ)} := by
    have := congrArg (Finset.image fun q : Fin n → Fin 6 => ((q i0).val : ℤ)) heq
    simpa [paramToSet] using this
  have hdx : (fx i0).2 = -1 ∨ (fx i0).2 = 1 := by
    have := (Finset.mem_product.mp (Finset.mem_filter.mp (hfx_all i0)).1).2
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with h | h | h <;> [left; exact absurd h hi0; right] <;> exact h
  have h0x := hvx 0 (by omega) i0
  have h1x := hvx px.1 (by omega) i0
  have h2x := hvx px.2.1 (by omega) i0
  have h3x := hvx px.2.2 le_rfl i0
  have h0y := hvy 0 (by omega) i0
  have h1y := hvy py.1 (by omega) i0
  have h2y := hvy py.2.1 (by omega) i0
  have h3y := hvy py.2.2 le_rfl i0
  have hfy_i0 : (fy i0).2 ≠ 0 := by
    intro h0
    have hcard_x : ({((evalPt fx 0 i0).val : ℤ), ((evalPt fx px.1 i0).val : ℤ),
        ((evalPt fx px.2.1 i0).val : ℤ), ((evalPt fx px.2.2 i0).val : ℤ)} : Finset ℤ).card = 4 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
          Finset.card_insert_of_notMem, Finset.card_singleton] <;>
        simp only [Finset.mem_insert, Finset.mem_singleton] <;>
        rcases hdx with h | h <;> rw [h] at h0x h1x h2x h3x <;> omega
    have hcard_y : ({((evalPt fy 0 i0).val : ℤ), ((evalPt fy py.1 i0).val : ℤ),
        ((evalPt fy py.2.1 i0).val : ℤ), ((evalPt fy py.2.2 i0).val : ℤ)} : Finset ℤ).card ≤ 1 := by
      rw [h0] at h0y h1y h2y h3y
      have e1 : ((evalPt fy py.1 i0).val : ℤ) = ((evalPt fy 0 i0).val : ℤ) := by omega
      have e2 : ((evalPt fy py.2.1 i0).val : ℤ) = ((evalPt fy 0 i0).val : ℤ) := by omega
      have e3 : ((evalPt fy py.2.2 i0).val : ℤ) = ((evalPt fy 0 i0).val : ℤ) := by omega
      rw [e1, e2, e3]; simp
    rw [hset_i0] at hcard_x
    omega
  have hdy : (fy i0).2 = -1 ∨ (fy i0).2 = 1 := by
    have := (Finset.mem_product.mp (Finset.mem_filter.mp (hfy_all i0)).1).2
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with h | h | h <;> [left; exact absurd h hfy_i0; right] <;> exact h
  -- Unique point in paramToSet (px, fx) for each i0-coordinate value
  have huniq_x : ∀ q ∈ paramToSet (px, fx), ∀ t : ℕ, t ∈ ({0, px.1, px.2.1, px.2.2} : Finset ℕ) →
      ((q i0).val : ℤ) = ((evalPt fx t i0).val : ℤ) → q = evalPt fx t := by
    intro q hq t ht hval
    simp only [paramToSet, Finset.mem_insert, Finset.mem_singleton] at hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases hdx with h | h <;> rw [h] at h0x h1x h2x h3x
    all_goals
      rcases hq with rfl | rfl | rfl | rfl <;> rcases ht with rfl | rfl | rfl | rfl <;>
      first | rfl | omega
  have hmem_of_eq : ∀ q, q ∈ paramToSet (py, fy) → q ∈ paramToSet (px, fx) := fun q hq => by
    rw [heq]; exact hq
  by_cases hsame : (fy i0).2 = (fx i0).2
  · left
    have hcoords_eq : ((evalPt fy 0 i0).val : ℤ) = ((evalPt fx 0 i0).val : ℤ) ∧
        ((evalPt fy py.1 i0).val : ℤ) = ((evalPt fx px.1 i0).val : ℤ) ∧
        ((evalPt fy py.2.1 i0).val : ℤ) = ((evalPt fx px.2.1 i0).val : ℤ) ∧
        ((evalPt fy py.2.2 i0).val : ℤ) = ((evalPt fx px.2.2 i0).val : ℤ) := by
      rcases hdx with h | h <;> rw [h] at hsame h0x h1x h2x h3x <;> rw [hsame] at h0y h1y h2y h3y
      · have hrev_set : ({((evalPt fx px.2.2 i0).val : ℤ), ((evalPt fx px.2.1 i0).val : ℤ),
            ((evalPt fx px.1 i0).val : ℤ), ((evalPt fx 0 i0).val : ℤ)} : Finset ℤ) =
            {((evalPt fy py.2.2 i0).val : ℤ), ((evalPt fy py.2.1 i0).val : ℤ),
             ((evalPt fy py.1 i0).val : ℤ), ((evalPt fy 0 i0).val : ℤ)} := by
          rw [finset_rev4 ((evalPt fx 0 i0).val : ℤ), finset_rev4 ((evalPt fy 0 i0).val : ℤ)]
          exact hset_i0
        have hm := eq_of_strict_mono_finset_eq (by omega) (by omega) hrev_set
        exact ⟨hm.2.2.2.symm, hm.2.2.1.symm, hm.2.1.symm, hm.1.symm⟩
      · have hm := eq_of_strict_mono_finset_eq (by omega) (by omega) hset_i0
        exact ⟨hm.1.symm, hm.2.1.symm, hm.2.2.1.symm, hm.2.2.2.symm⟩
    have hmatch0 : evalPt fy 0 = evalPt fx 0 :=
      huniq_x _ (hmem_of_eq _ (by simp [paramToSet])) 0 (by simp) hcoords_eq.1
    have hmatch3 : evalPt fy py.2.2 = evalPt fx px.2.2 :=
      huniq_x _ (hmem_of_eq _ (by simp [paramToSet])) px.2.2 (by simp) hcoords_eq.2.2.2
    have hpy_eq : py = px := by
      rcases hdx with h | h <;> rw [h] at hsame h0x h1x h2x h3x <;> rw [hsame] at h0y h1y h2y h3y
      all_goals
        rcases px with ⟨a1, a2, D⟩; rcases py with ⟨b1, b2, D'⟩
        simp only [Prod.mk.injEq] at *
        omega
    have hfy_eq : fy = fx := by
      ext k
      · have c0 := congrArg (fun q : Fin n → Fin 6 => ((q k).val : ℤ)) hmatch0
        have hk0x := hvx 0 (by omega) k
        have hk0y := hvy 0 (by omega) k
        simp only [Nat.cast_zero, zero_mul, add_zero] at hk0x hk0y
        exact_mod_cast (by linarith : ((fy k).1.val : ℤ) = ((fx k).1.val : ℤ))
      · have c0 := congrArg (fun q : Fin n → Fin 6 => ((q k).val : ℤ)) hmatch0
        have c3 := congrArg (fun q : Fin n → Fin 6 => ((q k).val : ℤ)) hmatch3
        have hk0x := hvx 0 (by omega) k
        have hk3x := hvx px.2.2 le_rfl k
        have hk0y := hvy 0 (by omega) k
        have hk3y := hvy py.2.2 le_rfl k
        simp only [Nat.cast_zero, zero_mul, add_zero] at hk0x hk0y
        rw [hpy_eq] at hk3y c3
        have hDne : (px.2.2 : ℤ) ≠ 0 := by omega
        have : (px.2.2 : ℤ) * (fy k).2 = (px.2.2 : ℤ) * (fx k).2 := by linarith
        exact mul_left_cancel₀ hDne this
    exact Prod.ext hpy_eq hfy_eq
  · right
    have hopp : (fy i0).2 = -(fx i0).2 := by
      rcases hdx with h1 | h1 <;> rcases hdy with h2 | h2 <;> omega
    have hcoords_eq : ((evalPt fy 0 i0).val : ℤ) = ((evalPt fx px.2.2 i0).val : ℤ) ∧
        ((evalPt fy py.1 i0).val : ℤ) = ((evalPt fx px.2.1 i0).val : ℤ) ∧
        ((evalPt fy py.2.1 i0).val : ℤ) = ((evalPt fx px.1 i0).val : ℤ) ∧
        ((evalPt fy py.2.2 i0).val : ℤ) = ((evalPt fx 0 i0).val : ℤ) := by
      rcases hdx with h | h <;> rw [h] at hopp h0x h1x h2x h3x <;> rw [hopp] at h0y h1y h2y h3y
      · have hrev_set : ({((evalPt fx px.2.2 i0).val : ℤ), ((evalPt fx px.2.1 i0).val : ℤ),
            ((evalPt fx px.1 i0).val : ℤ), ((evalPt fx 0 i0).val : ℤ)} : Finset ℤ) =
            {((evalPt fy 0 i0).val : ℤ), ((evalPt fy py.1 i0).val : ℤ),
             ((evalPt fy py.2.1 i0).val : ℤ), ((evalPt fy py.2.2 i0).val : ℤ)} := by
          rw [finset_rev4]; exact hset_i0
        have hm := eq_of_strict_mono_finset_eq (by omega) (by omega) hrev_set
        exact ⟨hm.1.symm, hm.2.1.symm, hm.2.2.1.symm, hm.2.2.2.symm⟩
      · have hrev_set : ({((evalPt fx 0 i0).val : ℤ), ((evalPt fx px.1 i0).val : ℤ),
            ((evalPt fx px.2.1 i0).val : ℤ), ((evalPt fx px.2.2 i0).val : ℤ)} : Finset ℤ) =
            {((evalPt fy py.2.2 i0).val : ℤ), ((evalPt fy py.2.1 i0).val : ℤ),
             ((evalPt fy py.1 i0).val : ℤ), ((evalPt fy 0 i0).val : ℤ)} := by
          rw [finset_rev4 ((evalPt fy 0 i0).val : ℤ)]; exact hset_i0
        have hm := eq_of_strict_mono_finset_eq (by omega) (by omega) hrev_set
        exact ⟨hm.2.2.2.symm, hm.2.2.1.symm, hm.2.1.symm, hm.1.symm⟩
    have hmatch0 : evalPt fy 0 = evalPt fx px.2.2 :=
      huniq_x _ (hmem_of_eq _ (by simp [paramToSet])) px.2.2 (by simp) hcoords_eq.1
    have hmatch3 : evalPt fy py.2.2 = evalPt fx 0 :=
      huniq_x _ (hmem_of_eq _ (by simp [paramToSet])) 0 (by simp) hcoords_eq.2.2.2
    have hpy_eq : py = (px.2.2 - px.2.1, px.2.2 - px.1, px.2.2) := by
      rcases hdx with h | h <;> rw [h] at hopp h0x h1x h2x h3x <;> rw [hopp] at h0y h1y h2y h3y
      all_goals
        rcases px with ⟨a1, a2, D⟩; rcases py with ⟨b1, b2, D'⟩
        simp only [Prod.mk.injEq] at *
        omega
    have hfy_eq : fy = fun k => (evalPt fx px.2.2 k, -(fx k).2) := by
      ext k
      · have c0 := congrArg (fun q : Fin n → Fin 6 => ((q k).val : ℤ)) hmatch0
        have hk0y := hvy 0 (by omega) k
        simp only [Nat.cast_zero, zero_mul, add_zero] at hk0y
        exact_mod_cast (by linarith : ((fy k).1.val : ℤ) = ((evalPt fx px.2.2 k).val : ℤ))
      · have c0 := congrArg (fun q : Fin n → Fin 6 => ((q k).val : ℤ)) hmatch0
        have c3 := congrArg (fun q : Fin n → Fin 6 => ((q k).val : ℤ)) hmatch3
        have hk0x := hvx 0 (by omega) k
        have hk3x := hvx px.2.2 le_rfl k
        have hk0y := hvy 0 (by omega) k
        have hk3y := hvy py.2.2 le_rfl k
        simp only [Nat.cast_zero, zero_mul, add_zero] at hk0x hk0y
        have hD_eq : py.2.2 = px.2.2 := by rw [hpy_eq]
        rw [hD_eq] at hk3y c3
        have hDne : (px.2.2 : ℤ) ≠ 0 := by omega
        have : (px.2.2 : ℤ) * (fy k).2 = (px.2.2 : ℤ) * (-(fx k).2) := by linarith
        exact mul_left_cancel₀ hDne this
    exact Prod.ext hpy_eq hfy_eq

lemma two_mul_card_collinear4 (n : ℕ) : 2 * (collinear4 n).card = (params n).card := by
  classical
  have hmaps : ∀ x ∈ params n, paramToSet x ∈ collinear4 n := by
    intro x hx
    simp only [collinear4, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨paramToSet_card hx, paramToSet_collinear hx⟩
  have hfiber : ∀ S ∈ collinear4 n, ((params n).filter (fun x => paramToSet x = S)).card = 2 := by
    intro S hS
    obtain ⟨x, hx, hxS⟩ := exists_param_of_collinear4 hS
    have hset : (params n).filter (fun y => paramToSet y = S) = {x, revParam x} := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hy, hyS⟩
        exact param_eq_or_rev hx hy (hxS.trans hyS.symm)
      · rintro (rfl | rfl)
        · exact ⟨hx, hxS⟩
        · exact ⟨revParam_mem hx, (paramToSet_revParam hx).trans hxS⟩
    rw [hset, Finset.card_pair (Ne.symm (revParam_ne hx))]
  have hsum := Finset.card_eq_sum_card_fiberwise hmaps
  rw [Finset.sum_congr rfl hfiber, Finset.sum_const, smul_eq_mul, mul_comm] at hsum
  exact hsum.symm

end OMA.P_oeis_a178299

theorem OMA.solution : type_of% @OMA.S_oeis_a178299.main := by
  intro n
  rw [OMA.P_oeis_a178299.a_eq_card_collinear4]
  have h2 := OMA.P_oeis_a178299.two_mul_card_collinear4 n
  have h2z : 2 * ((OMA.P_oeis_a178299.collinear4 n).card : ℤ) = ((OMA.P_oeis_a178299.params n).card : ℤ) := by
    exact_mod_cast h2
  rw [h2z, OMA.P_oeis_a178299.card_params]
