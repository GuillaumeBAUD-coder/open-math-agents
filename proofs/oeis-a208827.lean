import OMAStatements.S_oeis_a208827
import Mathlib

/-!
Proof: Burnside's lemma for the dihedral group of order 12 acting on the labelings. The labelings
fixed by a group element are the zero-sum labelings constant on its cycles, so they are counted
by zero-sum tuples in a box (rotations, and reflections through edges) or by solutions of
`x + y + 2 a + 2 b = 0` (reflections through beads). The zero-sum tuples are counted by the
coefficient of `X ^ (k n)` in `(1 + X + ... + X ^ (2 n)) ^ k`, read off from
`(1 - X ^ (2 n + 1)) ^ k * (1 - X) ^ (-k)`; the weighted count is an explicit piecewise sum.
This gives `a n` as a polynomial in `n` for `n ≥ 1`, from which both conjectures follow.
-/

namespace OMA.P_oeis_a208827

open PowerSeries

/-! ## Zero-sum tuples in a box, via power series -/

/-- Tuples of `k` integers in `-n..n` with sum zero. -/
def Z (k n : ℕ) : Type := {f : Fin k → ℤ // (∀ i, -(n : ℤ) ≤ f i ∧ f i ≤ n) ∧ ∑ i, f i = 0}

def cY (k L t : ℕ) : ℕ := ∑ y : Fin k → Fin L, if ∑ i, (y i : ℕ) = t then 1 else 0

lemma cY_zero (L t : ℕ) : cY 0 L t = if t = 0 then 1 else 0 := by
  simp [cY, eq_comm]

lemma cY_succ (k L t : ℕ) :
    cY (k + 1) L t = ∑ a : Fin L, if (a : ℕ) ≤ t then cY k L (t - a) else 0 := by
  unfold cY
  rw [← (Fin.consEquiv fun _ => Fin L).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
  split_ifs with h
  · refine Finset.sum_congr rfl fun y _ => ?_
    congr 1
    apply propext
    omega
  · refine Finset.sum_eq_zero fun y _ => ?_
    rw [if_neg (by omega)]

noncomputable def G (L : ℕ) : ℤ⟦X⟧ := ∑ j ∈ Finset.range L, X ^ j

lemma coeff_G (L i : ℕ) : coeff i (G L) = if i < L then 1 else 0 := by
  simp only [G, map_sum, coeff_X_pow]
  rw [Finset.sum_ite_eq]
  simp

lemma sum_swap_range (L t : ℕ) (g : ℕ → ℤ) :
    ∑ i ∈ Finset.range L, (if i ≤ t then g i else 0) =
      ∑ i ∈ Finset.range (t + 1), (if i < L then g i else 0) := by
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

lemma cY_coeff : ∀ (k L t : ℕ), (cY k L t : ℤ) = coeff t (G L ^ k)
  | 0, L, t => by
    rw [cY_zero, pow_zero, coeff_one]
    split_ifs <;> simp
  | k + 1, L, t => by
    rw [cY_succ, pow_succ', coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    push_cast
    rw [Fin.sum_univ_eq_sum_range (fun a => if a ≤ t then (cY k L (t - a) : ℤ) else 0) L,
      sum_swap_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [coeff_G, cY_coeff k L (t - i)]
    split_ifs <;> simp

lemma G_eq (L : ℕ) : G L = (1 - X ^ L) * mk 1 := by
  have h := mk_one_mul_one_sub_eq_one ℤ
  calc G L = G L * (mk 1 * (1 - X)) := by rw [h, mul_one]
    _ = (G L * (1 - X)) * mk 1 := by ring
    _ = (1 - X ^ L) * mk 1 := by rw [G, geom_sum_mul_neg]

lemma coeff_G_pow (k L t : ℕ) :
    coeff t (G L ^ (k + 1)) = ∑ j ∈ Finset.range (k + 2),
      (-1) ^ j * ((k + 1).choose j : ℤ) *
        (if L * j ≤ t then ((k + (t - L * j)).choose k : ℤ) else 0) := by
  have e1 : (1 - X ^ L : ℤ⟦X⟧) = C (-1) * X ^ L + 1 := by
    rw [map_neg, map_one]
    ring
  rw [G_eq, mul_pow, mk_one_pow_eq_mk_choose_add, e1, add_pow, Finset.sum_mul,
    map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e : (C (-1) * X ^ L : ℤ⟦X⟧) ^ j * 1 ^ (k + 1 - j) * ((k + 1).choose j : ℤ⟦X⟧) *
      mk (fun n => ((k + n).choose k : ℤ)) =
      C ((-1) ^ j * ((k + 1).choose j : ℤ)) * (X ^ (L * j) * mk fun n => ((k + n).choose k : ℤ)) := by
    rw [mul_pow, ← map_pow, ← pow_mul, one_pow, mul_one, map_mul, map_natCast]
    ring
  rw [e, coeff_C_mul, coeff_X_pow_mul', coeff_mk]

theorem card_Z (k n : ℕ) : Nat.card (Z k n) = cY k (2 * n + 1) (k * n) := by
  have hb : Function.Bijective (fun y : {y : Fin k → Fin (2 * n + 1) // ∑ i, (y i : ℕ) = k * n} =>
      (⟨fun i => (y.1 i : ℤ) - n, fun i => by dsimp only; have := (y.1 i).2; omega, by
        have h := y.2
        rw [Finset.sum_sub_distrib]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        have h' : ((∑ i, (y.1 i : ℕ) : ℕ) : ℤ) = ((k * n : ℕ) : ℤ) := by rw [h]
        push_cast at h'
        rw [h']
        ring⟩ : Z k n)) := by
    constructor
    · rintro ⟨y₁, h₁⟩ ⟨y₂, h₂⟩ h
      simp only [Subtype.mk.injEq] at h
      apply Subtype.ext
      funext i
      have := congrFun h i
      apply Fin.ext
      simp only [sub_left_inj, Nat.cast_inj] at this
      exact this
    · rintro ⟨f, hf, hs⟩
      refine ⟨⟨fun i => ⟨(f i + n).toNat, by have := hf i; omega⟩, ?_⟩, ?_⟩
      · have : ((∑ i, (f i + n).toNat : ℕ) : ℤ) = ((k * n : ℕ) : ℤ) := by
          push_cast
          rw [Finset.sum_congr rfl fun i _ => Int.toNat_of_nonneg (by have := hf i; omega),
            Finset.sum_add_distrib, hs]
          simp
        exact_mod_cast this
      · apply Subtype.ext
        funext i
        simp only
        have := hf i
        omega
  refine (Nat.card_eq_of_bijective _ hb).symm.trans ?_
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter, cY]

/-- Closed form for the number of zero-sum tuples. -/
theorem card_Z_formula (k n : ℕ) : (Nat.card (Z (k + 1) n) : ℤ) = ∑ j ∈ Finset.range (k + 2),
      (-1) ^ j * ((k + 1).choose j : ℤ) *
        (if (2 * n + 1) * j ≤ (k + 1) * n then
          ((k + ((k + 1) * n - (2 * n + 1) * j)).choose k : ℤ) else 0) := by
  rw [card_Z, cY_coeff, coeff_G_pow]

end OMA.P_oeis_a208827

namespace OMA.P_oeis_a208827

open PowerSeries

/-! ## The count `Q` of `x + y + 2 a + 2 b = 0` -/

lemma cY2_raw (n t : ℕ) : (cY 2 (2 * n + 1) t : ℤ) =
    ((1 + t : ℕ) : ℤ) - 2 * (if 2 * n + 1 ≤ t then ((1 + (t - (2 * n + 1)) : ℕ) : ℤ) else 0) +
      (if (2 * n + 1) * 2 ≤ t then ((1 + (t - (2 * n + 1) * 2) : ℕ) : ℤ) else 0) := by
  rw [cY_coeff, show 2 = 1 + 1 from rfl, coeff_G_pow]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.choose_one_right]
  simp only [pow_zero, pow_one, one_mul, mul_zero, mul_one, Nat.sub_zero, Nat.choose_zero_right,
    Nat.reduceAdd, Nat.choose_self, Nat.choose_one_right, if_pos (Nat.zero_le t)]
  push_cast
  ring

lemma cY2_lo (n t : ℕ) (h : t ≤ 2 * n) : (cY 2 (2 * n + 1) t : ℤ) = t + 1 := by
  rw [cY2_raw, if_neg (by omega), if_neg (by omega)]
  push_cast
  ring

lemma cY2_mid (n t : ℕ) (h1 : 2 * n + 1 ≤ t) (h2 : t ≤ 4 * n + 1) :
    (cY 2 (2 * n + 1) t : ℤ) = 4 * n + 1 - t := by
  rw [cY2_raw, if_pos h1, if_neg (by omega), Nat.cast_add, Nat.cast_add, Nat.cast_sub h1]
  push_cast
  ring

lemma cY2_hi (n t : ℕ) (h : 4 * n + 2 ≤ t) : (cY 2 (2 * n + 1) t : ℤ) = 0 := by
  rw [cY2_raw, if_pos (by omega), if_pos (by omega), Nat.cast_add, Nat.cast_add, Nat.cast_add,
    Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  push_cast
  ring

/-- Grouping a sum over tuples by the sum of the tuple. -/
lemma sum_fiber (k L M : ℕ) (hM : k * (L - 1) < M) (g : ℕ → ℤ) :
    ∑ z : Fin k → Fin L, g (∑ i, (z i : ℕ)) = ∑ s ∈ Finset.range M, (cY k L s : ℤ) * g s := by
  simp only [cY, Nat.cast_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => ?_
  have hz : ∑ i, (z i : ℕ) < M := by
    have : ∑ i, (z i : ℕ) ≤ ∑ _i : Fin k, (L - 1) :=
      Finset.sum_le_sum fun i _ => by have := (z i).2; omega
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at this
    omega
  simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq, if_pos (Finset.mem_range.2 hz)]

def QS (n : ℕ) : Type :=
  {v : Fin 4 → ℤ // (∀ i, -(n : ℤ) ≤ v i ∧ v i ≤ n) ∧ v 0 + v 1 + 2 * v 2 + 2 * v 3 = 0}

theorem card_QS (n : ℕ) : (Nat.card (QS n) : ℤ) = ∑ s ∈ Finset.range (4 * n + 2),
    (cY 2 (2 * n + 1) s : ℤ) *
      (if 2 * s ≤ 6 * n then (cY 2 (2 * n + 1) (6 * n - 2 * s) : ℤ) else 0) := by
  have hb : Function.Bijective (fun p : {p : (Fin 2 → Fin (2 * n + 1)) × (Fin 2 → Fin (2 * n + 1)) //
      ∑ i, (p.1 i : ℕ) + 2 * ∑ i, (p.2 i : ℕ) = 6 * n} =>
      (⟨![(p.1.1 0 : ℤ) - n, (p.1.1 1 : ℤ) - n, (p.1.2 0 : ℤ) - n, (p.1.2 1 : ℤ) - n], by
        refine ⟨fun i => ?_, ?_⟩
        · have := (p.1.1 0).2; have := (p.1.1 1).2; have := (p.1.2 0).2; have := (p.1.2 1).2
          fin_cases i <;> simp <;> omega
        · have h := p.2
          simp only [Fin.sum_univ_two] at h
          simp
          omega⟩ : QS n)) := by
    constructor
    · rintro ⟨⟨w₁, z₁⟩, h₁⟩ ⟨⟨w₂, z₂⟩, h₂⟩ h
      have h' := congrArg Subtype.val h
      have e0 := congrFun h' 0
      have e1 := congrFun h' 1
      have e2 := congrFun h' 2
      have e3 := congrFun h' 3
      simp at e0 e1 e2 e3
      apply Subtype.ext
      simp only [Prod.mk.injEq]
      constructor <;> funext i <;> fin_cases i <;> apply Fin.ext <;> simp <;> omega
    · rintro ⟨v, hv, hs⟩
      have b0 := hv 0
      have b1 := hv 1
      have b2 := hv 2
      have b3 := hv 3
      refine ⟨⟨(![⟨(v 0 + n).toNat, by omega⟩, ⟨(v 1 + n).toNat, by omega⟩],
        ![⟨(v 2 + n).toNat, by omega⟩, ⟨(v 3 + n).toNat, by omega⟩]), ?_⟩, ?_⟩
      · simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
        omega
      · apply Subtype.ext
        funext i
        fin_cases i <;> simp <;> omega
  have e : Nat.card (QS n) = _ := (Nat.card_eq_of_bijective _ hb).symm
  rw [e, Nat.card_eq_fintype_card, Fintype.card_subtype,
    Finset.card_filter, Fintype.sum_prod_type, Finset.sum_comm]
  rw [← sum_fiber 2 (2 * n + 1) (4 * n + 2) (by omega)
    (fun s => if 2 * s ≤ 6 * n then (cY 2 (2 * n + 1) (6 * n - 2 * s) : ℤ) else 0)]
  push_cast
  refine Finset.sum_congr rfl fun z _ => ?_
  split_ifs with h
  · simp only [cY, Nat.cast_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    congr 1
    apply propext
    omega
  · refine Finset.sum_eq_zero fun w _ => ?_
    rw [if_neg (by omega)]

theorem card_QS_pieces (n : ℕ) : (Nat.card (QS n) : ℤ) =
    ∑ s ∈ Finset.Ico n (2 * n + 1), ((s : ℤ) + 1) * (2 * s - 2 * n + 1) +
      ∑ s ∈ Finset.Ico (2 * n + 1) (3 * n + 1), (4 * n + 1 - (s : ℤ)) * (6 * n + 1 - 2 * s) := by
  rw [card_QS, ← Finset.sum_range_add_sum_Ico _ (show n ≤ 4 * n + 2 by omega),
    ← Finset.sum_Ico_consecutive _ (show n ≤ 2 * n + 1 by omega) (show 2 * n + 1 ≤ 4 * n + 2 by omega),
    ← Finset.sum_Ico_consecutive _ (show 2 * n + 1 ≤ 3 * n + 1 by omega)
      (show 3 * n + 1 ≤ 4 * n + 2 by omega)]
  have p1 : ∑ s ∈ Finset.range n, (cY 2 (2 * n + 1) s : ℤ) *
      (if 2 * s ≤ 6 * n then (cY 2 (2 * n + 1) (6 * n - 2 * s) : ℤ) else 0) = 0 := by
    refine Finset.sum_eq_zero fun s hs => ?_
    rw [Finset.mem_range] at hs
    rw [if_pos (by omega), cY2_hi n (6 * n - 2 * s) (by omega), mul_zero]
  have p4 : ∑ s ∈ Finset.Ico (3 * n + 1) (4 * n + 2), (cY 2 (2 * n + 1) s : ℤ) *
      (if 2 * s ≤ 6 * n then (cY 2 (2 * n + 1) (6 * n - 2 * s) : ℤ) else 0) = 0 := by
    refine Finset.sum_eq_zero fun s hs => ?_
    rw [Finset.mem_Ico] at hs
    rw [if_neg (by omega), mul_zero]
  rw [p1, p4, zero_add, add_zero]
  congr 1
  · refine Finset.sum_congr rfl fun s hs => ?_
    rw [Finset.mem_Ico] at hs
    rw [if_pos (by omega), cY2_lo n s (by omega)]
    rcases le_or_gt (6 * n - 2 * s) (2 * n) with h | h
    · rw [cY2_lo n (6 * n - 2 * s) h, Nat.cast_sub (by omega)]
      push_cast
      have : s = 2 * n := by omega
      subst this
      push_cast
      ring
    · rw [cY2_mid n (6 * n - 2 * s) (by omega) (by omega), Nat.cast_sub (by omega)]
      push_cast
      ring
  · refine Finset.sum_congr rfl fun s hs => ?_
    rw [Finset.mem_Ico] at hs
    rw [if_pos (by omega), cY2_mid n s (by omega) (by omega), cY2_lo n (6 * n - 2 * s) (by omega),
      Nat.cast_sub (by omega)]
    push_cast
    ring

lemma piece2 (n : ℕ) : ∀ m : ℕ, 6 * ∑ s ∈ Finset.Ico n (n + m), ((s : ℤ) + 1) * (2 * s - 2 * n + 1) =
    6 * (n + 1) * m ^ 2 + 2 * (m - 1) * m * (2 * m - 1) + 3 * m * (m - 1)
  | 0 => by simp
  | m + 1 => by
    rw [show n + (m + 1) = n + m + 1 by ring, Finset.sum_Ico_succ_top (by omega), mul_add,
      piece2 n m]
    push_cast
    ring

lemma piece3 (n : ℕ) : ∀ m : ℕ, 6 * ∑ s ∈ Finset.Ico (2 * n + 1) (2 * n + 1 + m),
    (4 * n + 1 - (s : ℤ)) * (6 * n + 1 - 2 * s) =
    12 * n * (2 * n - 1) * m - 3 * (6 * n - 1) * m * (m - 1) + 2 * (m - 1) * m * (2 * m - 1)
  | 0 => by simp
  | m + 1 => by
    rw [show 2 * n + 1 + (m + 1) = 2 * n + 1 + m + 1 by ring, Finset.sum_Ico_succ_top (by omega),
      mul_add, piece3 n m]
    push_cast
    ring

theorem card_QS_closed (n : ℕ) : 3 * (Nat.card (QS n) : ℤ) = 10 * n ^ 3 + 15 * n ^ 2 + 11 * n + 3 := by
  have h2 := piece2 n (n + 1)
  have h3 := piece3 n n
  rw [show n + (n + 1) = 2 * n + 1 by ring] at h2
  rw [show 2 * n + 1 + n = 3 * n + 1 by ring] at h3
  have := card_QS_pieces n
  push_cast at h2 h3
  have key : 2 * (3 * (Nat.card (QS n) : ℤ)) = 2 * (10 * n ^ 3 + 15 * n ^ 2 + 11 * n + 3) := by
    linear_combination 6 * this + h2 + h3
  omega

end OMA.P_oeis_a208827

namespace OMA.P_oeis_a208827

open DihedralGroup OMA.S_oeis_a208827

/-! ## The dihedral group acting on labelings -/

def act : DihedralGroup 6 → Fin 6 → Fin 6
  | r i => fun j => j + (show Fin 6 from i)
  | sr i => fun j => (show Fin 6 from i) - j

lemma act_mul : ∀ (g h : DihedralGroup 6) (j : Fin 6), act (g * h) j = act h (act g j) := by
  decide

lemma act_one : ∀ j : Fin 6, act 1 j = j := by decide

lemma act_bij : ∀ g : DihedralGroup 6, Function.Bijective (act g) := by decide

instance (n : ℕ) : MulAction (DihedralGroup 6) (L n) where
  smul g f := ⟨fun j => f.1 (act g j), fun j => f.2.1 _, by
    rw [(act_bij g).sum_comp f.1]
    exact f.2.2⟩
  one_smul f := Subtype.ext (funext fun j => by
    show f.1 (act 1 j) = f.1 j
    rw [act_one])
  mul_smul g h f := Subtype.ext (funext fun j => by
    show f.1 (act (g * h) j) = f.1 (act h (act g j))
    rw [act_mul])

lemma smul_val (n : ℕ) (g : DihedralGroup 6) (f : L n) (j : Fin 6) :
    (g • f).1 j = f.1 (act g j) := rfl

lemma same_iff (n : ℕ) (f g : L n) :
    SameNecklace n f g ↔ (MulAction.orbitRel (DihedralGroup 6) (L n)) f g := by
  rw [(MulAction.orbitRel (DihedralGroup 6) (L n)).comm', MulAction.orbitRel_apply,
    MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨i, h | h⟩
    · exact ⟨r i, Subtype.ext (funext fun j => (h j).symm)⟩
    · exact ⟨sr i, Subtype.ext (funext fun j => (h j).symm)⟩
  · rintro ⟨x, rfl⟩
    cases x with
    | r i => exact ⟨i, Or.inl fun j => rfl⟩
    | sr i => exact ⟨i, Or.inr fun j => rfl⟩

instance (n : ℕ) : Finite (L n) := by
  refine Finite.of_injective (fun f : L n => fun i => (⟨(f.1 i + n).toNat, by
    have := f.2.1 i; omega⟩ : Fin (2 * n + 1))) ?_
  intro f g h
  apply Subtype.ext
  funext i
  have := congrFun h i
  simp only [Fin.mk.injEq] at this
  have := f.2.1 i
  have := g.2.1 i
  omega

theorem burnside (n : ℕ) : Nat.card (Quot (SameNecklace n)) * 12 =
    ∑ g : DihedralGroup 6, Nat.card {f : L n // ∀ j, f.1 (act g j) = f.1 j} := by
  classical
  haveI : Fintype (L n) := Fintype.ofFinite _
  have hb := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group (DihedralGroup 6) (L n)
  rw [DihedralGroup.card] at hb
  have hrel : SameNecklace n = fun f g => (MulAction.orbitRel (DihedralGroup 6) (L n)) f g :=
    funext fun f => funext fun g => propext (same_iff n f g)
  rw [hrel]
  have e : Nat.card (Quot fun f g => (MulAction.orbitRel (DihedralGroup 6) (L n)) f g) =
      Nat.card (Quotient (MulAction.orbitRel (DihedralGroup 6) (L n))) := rfl
  rw [e, Nat.card_eq_fintype_card, show (12 : ℕ) = 2 * 6 from rfl, ← hb]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [← Nat.card_eq_fintype_card]
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro f
  rw [MulAction.mem_fixedBy]
  exact ⟨fun h j => by rw [← smul_val, h], fun h => Subtype.ext (funext fun j => by
    rw [smul_val, h])⟩

theorem fix_card (n : ℕ) (σ : Fin 6 → Fin 6) (k : ℕ) (cyc : Fin 6 → Fin k) (rep : Fin k → Fin 6)
    (h1 : ∀ i, cyc (rep i) = i) (h2 : ∀ j, cyc (σ j) = cyc j)
    (h3 : ∀ j, ∃ m : Fin 7, σ^[m] (rep (cyc j)) = j) :
    Nat.card {f : L n // ∀ j, f.1 (σ j) = f.1 j} =
      Nat.card {v : Fin k → ℤ // (∀ i, -(n : ℤ) ≤ v i ∧ v i ≤ n) ∧ ∑ j, v (cyc j) = 0} := by
  symm
  apply Nat.card_eq_of_bijective (fun v => ⟨⟨fun j => v.1 (cyc j), fun j => v.2.1 _, v.2.2⟩,
    fun j => by simp only [h2]⟩)
  constructor
  · rintro ⟨v₁, h₁⟩ ⟨v₂, h₂⟩ h
    have h' := congrArg (fun x => x.1.1) h
    apply Subtype.ext
    funext i
    have := congrFun h' (rep i)
    simpa [h1] using this
  · rintro ⟨f, hf⟩
    have hit : ∀ (m : ℕ) (x : Fin 6), f.1 (σ^[m] x) = f.1 x := by
      intro m
      induction m with
      | zero => intro x; rfl
      | succ m ih => intro x; rw [Function.iterate_succ_apply', hf, ih]
    have key : ∀ j, f.1 (rep (cyc j)) = f.1 j := by
      intro j
      obtain ⟨m, hm⟩ := h3 j
      calc f.1 (rep (cyc j)) = f.1 (σ^[m] (rep (cyc j))) := (hit m _).symm
        _ = f.1 j := by rw [hm]
    refine ⟨⟨fun i => f.1 (rep i), fun i => f.2.1 _, ?_⟩, ?_⟩
    · simp only [key]
      exact f.2.2
    · apply Subtype.ext
      apply Subtype.ext
      funext j
      exact key j

end OMA.P_oeis_a208827

namespace OMA.P_oeis_a208827

open DihedralGroup OMA.S_oeis_a208827

lemma card_cyc_Z (n k : ℕ) (cyc : Fin 6 → Fin k) (c : ℤ) (hc : c ≠ 0)
    (hsum : ∀ v : Fin k → ℤ, ∑ j, v (cyc j) = c * ∑ i, v i) :
    Nat.card {v : Fin k → ℤ // (∀ i, -(n : ℤ) ≤ v i ∧ v i ≤ n) ∧ ∑ j, v (cyc j) = 0} =
      Nat.card (Z k n) := by
  apply Nat.card_congr
  exact Equiv.subtypeEquivRight fun v => by
    rw [hsum, mul_eq_zero, or_iff_right hc]

lemma card_cyc_Q (n : ℕ) (cyc : Fin 6 → Fin 4)
    (hsum : ∀ v : Fin 4 → ℤ, ∑ j, v (cyc j) = v 0 + v 1 + 2 * v 2 + 2 * v 3) :
    Nat.card {v : Fin 4 → ℤ // (∀ i, -(n : ℤ) ≤ v i ∧ v i ≤ n) ∧ ∑ j, v (cyc j) = 0} =
      Nat.card (QS n) := by
  apply Nat.card_congr
  exact Equiv.subtypeEquivRight fun v => by rw [hsum]

noncomputable abbrev F (n : ℕ) (g : DihedralGroup 6) : ℕ := Nat.card {f : L n // ∀ j, f.1 (act g j) = f.1 j}

lemma sum_dihedral (n : ℕ) : ∑ g : DihedralGroup 6, F n g =
    ∑ i : Fin 6, F n (r i) + ∑ i : Fin 6, F n (sr i) := by
  rw [Fintype.sum_equiv equivSum (F n) (fun s => F n (equivSum.symm s)) (fun g => by cases g <;> rfl),
    Fintype.sum_sum_type]
  rfl

theorem sum12 (n : ℕ) : ∑ g : DihedralGroup 6, F n g =
    Nat.card (Z 6 n) + 2 * Nat.card (Z 1 n) + 2 * Nat.card (Z 2 n) + 4 * Nat.card (Z 3 n) +
      3 * Nat.card (QS n) := by
  rw [sum_dihedral, Fin.sum_univ_six, Fin.sum_univ_six]
  have r0 : F n (r (0 : Fin 6)) = Nat.card (Z 6 n) := by
    rw [F, fix_card n _ 6 id id (by decide) (by decide) (by decide),
      card_cyc_Z n 6 id 1 one_ne_zero (fun v => by simp)]
  have r1 : F n (r (1 : Fin 6)) = Nat.card (Z 1 n) := by
    rw [F, fix_card n _ 1 ![0, 0, 0, 0, 0, 0] ![0] (by decide) (by decide) (by decide),
      card_cyc_Z n 1 _ 6 (by norm_num) (fun v => by simp [Fin.sum_univ_six]; ring)]
  have r5 : F n (r (5 : Fin 6)) = Nat.card (Z 1 n) := by
    rw [F, fix_card n _ 1 ![0, 0, 0, 0, 0, 0] ![0] (by decide) (by decide) (by decide),
      card_cyc_Z n 1 _ 6 (by norm_num) (fun v => by simp [Fin.sum_univ_six]; ring)]
  have r2 : F n (r (2 : Fin 6)) = Nat.card (Z 2 n) := by
    rw [F, fix_card n _ 2 ![0, 1, 0, 1, 0, 1] ![0, 1] (by decide) (by decide) (by decide),
      card_cyc_Z n 2 _ 3 (by norm_num) (fun v => by simp [Fin.sum_univ_six]; ring)]
  have r4 : F n (r (4 : Fin 6)) = Nat.card (Z 2 n) := by
    rw [F, fix_card n _ 2 ![0, 1, 0, 1, 0, 1] ![0, 1] (by decide) (by decide) (by decide),
      card_cyc_Z n 2 _ 3 (by norm_num) (fun v => by simp [Fin.sum_univ_six]; ring)]
  have r3 : F n (r (3 : Fin 6)) = Nat.card (Z 3 n) := by
    rw [F, fix_card n _ 3 ![0, 1, 2, 0, 1, 2] ![0, 1, 2] (by decide) (by decide) (by decide),
      card_cyc_Z n 3 _ 2 (by norm_num) (fun v => by simp [Fin.sum_univ_six, Fin.sum_univ_three]; ring)]
  have s1 : F n (sr (1 : Fin 6)) = Nat.card (Z 3 n) := by
    rw [F, fix_card n _ 3 ![0, 0, 1, 2, 2, 1] ![0, 2, 3] (by decide) (by decide) (by decide),
      card_cyc_Z n 3 _ 2 (by norm_num) (fun v => by simp [Fin.sum_univ_six, Fin.sum_univ_three]; ring)]
  have s3 : F n (sr (3 : Fin 6)) = Nat.card (Z 3 n) := by
    rw [F, fix_card n _ 3 ![0, 1, 1, 0, 2, 2] ![0, 1, 4] (by decide) (by decide) (by decide),
      card_cyc_Z n 3 _ 2 (by norm_num) (fun v => by simp [Fin.sum_univ_six, Fin.sum_univ_three]; ring)]
  have s5 : F n (sr (5 : Fin 6)) = Nat.card (Z 3 n) := by
    rw [F, fix_card n _ 3 ![0, 1, 2, 2, 1, 0] ![0, 1, 2] (by decide) (by decide) (by decide),
      card_cyc_Z n 3 _ 2 (by norm_num) (fun v => by simp [Fin.sum_univ_six, Fin.sum_univ_three]; ring)]
  have s0 : F n (sr (0 : Fin 6)) = Nat.card (QS n) := by
    rw [F, fix_card n _ 4 ![0, 2, 3, 1, 3, 2] ![0, 3, 1, 2] (by decide) (by decide) (by decide),
      card_cyc_Q n _ (fun v => by simp [Fin.sum_univ_six]; ring)]
  have s2 : F n (sr (2 : Fin 6)) = Nat.card (QS n) := by
    rw [F, fix_card n _ 4 ![2, 0, 2, 3, 1, 3] ![1, 4, 0, 3] (by decide) (by decide) (by decide),
      card_cyc_Q n _ (fun v => by simp [Fin.sum_univ_six]; ring)]
  have s4 : F n (sr (4 : Fin 6)) = Nat.card (QS n) := by
    rw [F, fix_card n _ 4 ![2, 3, 0, 3, 2, 1] ![2, 5, 0, 1] (by decide) (by decide) (by decide),
      card_cyc_Q n _ (fun v => by simp [Fin.sum_univ_six]; ring)]
  rw [r0, r1, r2, r3, r4, r5, s0, s1, s2, s3, s4, s5]
  ring

end OMA.P_oeis_a208827

namespace OMA.P_oeis_a208827

lemma desc_cast (m : ℕ) : ∀ k : ℕ, (m.descFactorial k : ℚ) = ∏ i ∈ Finset.range k, ((m : ℚ) - i)
  | 0 => by simp
  | k + 1 => by
    rw [Nat.descFactorial_succ, Finset.prod_range_succ, Nat.cast_mul, desc_cast m k, mul_comm]
    rcases le_or_gt k m with h | h
    · rw [Nat.cast_sub h]
    · have h0 : m.descFactorial k = 0 := Nat.descFactorial_eq_zero_iff_lt.2 h
      rw [← desc_cast m k, h0]
      simp

lemma choose_cast (m k : ℕ) : (m.choose k : ℚ) = (∏ i ∈ Finset.range k, ((m : ℚ) - i)) / k.factorial := by
  rw [← desc_cast, Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
  field_simp

theorem Z1_val (n : ℕ) : (Nat.card (Z 1 n) : ℚ) = 1 := by
  have h := card_Z_formula 0 n
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at h
  rw [if_pos (by omega), if_neg (by omega)] at h
  simp only [Nat.choose_zero_right] at h
  exact_mod_cast (by simpa using h : (Nat.card (Z 1 n) : ℤ) = 1)

theorem Z2_val (n : ℕ) : (Nat.card (Z 2 n) : ℚ) = 2 * n + 1 := by
  have h := card_Z_formula 1 n
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at h
  rw [if_pos (by omega), if_neg (by omega), if_neg (by omega),
    show 1 + ((1 + 1) * n - (2 * n + 1) * 0) = 2 * n + 1 by omega] at h
  have hq := congrArg (fun x : ℤ => (x : ℚ)) h
  push_cast at hq
  rw [hq]
  norm_num [Nat.choose_one_right]

theorem Z3_val (n : ℕ) (hn : 1 ≤ n) : (Nat.card (Z 3 n) : ℚ) = 3 * n ^ 2 + 3 * n + 1 := by
  have h := card_Z_formula 2 n
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at h
  rw [if_pos (by omega), if_pos (by omega), if_neg (by omega), if_neg (by omega),
    show 2 + ((2 + 1) * n - (2 * n + 1) * 0) = 3 * n + 2 by omega,
    show 2 + ((2 + 1) * n - (2 * n + 1) * 1) = n + 1 by omega] at h
  have hq := congrArg (fun x : ℤ => (x : ℚ)) h
  push_cast at hq
  rw [hq, choose_cast (3 * n + 2), choose_cast (n + 1)]
  simp only [Finset.prod_range_succ, Finset.prod_range_zero]
  norm_num [Nat.choose_one_right, Nat.factorial]
  ring

theorem Z6_val (n : ℕ) (hn : 1 ≤ n) : (Nat.card (Z 6 n) : ℚ) =
    (6 * n + 5) * (6 * n + 4) * (6 * n + 3) * (6 * n + 2) * (6 * n + 1) / 120 -
      6 * ((4 * n + 4) * (4 * n + 3) * (4 * n + 2) * (4 * n + 1) * (4 * n) / 120) +
      15 * ((2 * n + 3) * (2 * n + 2) * (2 * n + 1) * (2 * n) * (2 * n - 1) / 120) := by
  have h := card_Z_formula 5 n
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at h
  rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega),
    show 5 + ((5 + 1) * n - (2 * n + 1) * 0) = 6 * n + 5 by omega,
    show 5 + ((5 + 1) * n - (2 * n + 1) * 1) = 4 * n + 4 by omega,
    show 5 + ((5 + 1) * n - (2 * n + 1) * 2) = 2 * n + 3 by omega] at h
  have hq := congrArg (fun x : ℤ => (x : ℚ)) h
  push_cast at hq
  rw [hq, choose_cast (6 * n + 5), choose_cast (4 * n + 4), choose_cast (2 * n + 3)]
  simp only [Finset.prod_range_succ, Finset.prod_range_zero]
  norm_num [Nat.choose_one_right, Nat.choose_two_right, Nat.factorial]
  ring

end OMA.P_oeis_a208827

namespace OMA.P_oeis_a208827

open PowerSeries OMA.S_oeis_a208827

/-- The closed form of `a n` for `n ≥ 1`. -/
noncomputable def pz (x : ℚ) : ℚ :=
  ((6 * x + 5) * (6 * x + 4) * (6 * x + 3) * (6 * x + 2) * (6 * x + 1) / 120 -
      6 * ((4 * x + 4) * (4 * x + 3) * (4 * x + 2) * (4 * x + 1) * (4 * x) / 120) +
      15 * ((2 * x + 3) * (2 * x + 2) * (2 * x + 1) * (2 * x) * (2 * x - 1) / 120) +
    2 + 2 * (2 * x + 1) + 4 * (3 * x ^ 2 + 3 * x + 1) + (10 * x ^ 3 + 15 * x ^ 2 + 11 * x + 3)) / 12

theorem a_val (n : ℕ) (hn : 1 ≤ n) : (a n : ℚ) = pz n := by
  have hb := burnside n
  rw [sum12] at hb
  have hq := card_QS_closed n
  have hq' : (3 * (Nat.card (QS n) : ℚ)) = 10 * n ^ 3 + 15 * n ^ 2 + 11 * n + 3 := by
    exact_mod_cast hq
  have hb' : (Nat.card (Quot (SameNecklace n)) : ℚ) * 12 = Nat.card (Z 6 n) +
      2 * Nat.card (Z 1 n) + 2 * Nat.card (Z 2 n) + 4 * Nat.card (Z 3 n) +
      3 * Nat.card (QS n) := by exact_mod_cast hb
  rw [Z6_val n hn, Z1_val, Z2_val, Z3_val n hn] at hb'
  show (Nat.card (Quot (SameNecklace n)) : ℚ) = pz n
  rw [pz]
  linear_combination hb' / 12 + hq' / 12

theorem gf_core (f : ℕ → ℚ) (h0 : f 0 = 0) (hp : ∀ n : ℕ, 1 ≤ n → f n = pz n) :
    mk f * (1 - X) ^ 6 = X * (18 + 59 * X + 96 * X ^ 2 - 2 * X ^ 3 + 6 * X ^ 4 - X ^ 5) := by
  have e : mk f * (1 - X) ^ 6 = mk f - C 6 * (X ^ 1 * mk f) + C 15 * (X ^ 2 * mk f) -
      C 20 * (X ^ 3 * mk f) + C 15 * (X ^ 4 * mk f) - C 6 * (X ^ 5 * mk f) + X ^ 6 * mk f := by
    simp only [map_ofNat]
    ring
  have e2 : (X * (18 + 59 * X + 96 * X ^ 2 - 2 * X ^ 3 + 6 * X ^ 4 - X ^ 5) : ℚ⟦X⟧) =
      C 18 * X ^ 1 + C 59 * X ^ 2 + C 96 * X ^ 3 - C 2 * X ^ 4 + C 6 * X ^ 5 - X ^ 6 := by
    simp only [map_ofNat]
    ring
  have v1 : f 1 = 18 := by rw [hp 1 le_rfl, pz]; norm_num
  have v2 : f 2 = 167 := by rw [hp 2 (by norm_num), pz]; norm_num
  have v3 : f 3 = 828 := by rw [hp 3 (by norm_num), pz]; norm_num
  have v4 : f 4 = 2821 := by rw [hp 4 (by norm_num), pz]; norm_num
  have v5 : f 5 = 7582 := by rw [hp 5 (by norm_num), pz]; norm_num
  have v6 : f 6 = 17339 := by rw [hp 6 (by norm_num), pz]; norm_num
  rw [e, e2]
  ext N
  simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow_mul', coeff_mk, coeff_X_pow]
  rcases lt_or_ge N 7 with h | h
  · interval_cases N <;> simp [h0, v1, v2, v3, v4, v5, v6] <;> norm_num
  · obtain ⟨M, rfl⟩ : ∃ M, N = M + 7 := ⟨N - 7, by omega⟩
    rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_pos (by omega),
      if_pos (by omega), if_pos (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      show M + 7 - 1 = M + 6 by omega, show M + 7 - 2 = M + 5 by omega,
      show M + 7 - 3 = M + 4 by omega, show M + 7 - 4 = M + 3 by omega,
      show M + 7 - 5 = M + 2 by omega, show M + 7 - 6 = M + 1 by omega]
    rw [hp (M + 7) (by omega), hp (M + 6) (by omega), hp (M + 5) (by omega), hp (M + 4) (by omega),
      hp (M + 3) (by omega), hp (M + 2) (by omega), hp (M + 1) (by omega)]
    simp only [pz]
    push_cast
    ring

end OMA.P_oeis_a208827

open PowerSeries OMA.S_oeis_a208827 OMA.P_oeis_a208827 in
theorem OMA.solution : type_of% @OMA.S_oeis_a208827.main := by
  refine ⟨gf_core _ (by simp) (fun n hn => by simp [show n ≠ 0 by omega, a_val n hn]), ?_⟩
  intro n hn
  obtain ⟨M, rfl⟩ : ∃ M, n = M + 7 := ⟨n - 7, by omega⟩
  rw [show M + 7 - 1 = M + 6 by omega, show M + 7 - 2 = M + 5 by omega,
    show M + 7 - 3 = M + 4 by omega, show M + 7 - 4 = M + 3 by omega,
    show M + 7 - 5 = M + 2 by omega, show M + 7 - 6 = M + 1 by omega]
  have key : (a (M + 7) : ℚ) = 6 * a (M + 6) - 15 * a (M + 5) + 20 * a (M + 4) -
      15 * a (M + 3) + 6 * a (M + 2) - a (M + 1) := by
    rw [a_val _ (by omega), a_val _ (by omega), a_val _ (by omega), a_val _ (by omega),
      a_val _ (by omega), a_val _ (by omega), a_val _ (by omega)]
    simp only [pz]
    push_cast
    ring
  exact_mod_cast key
