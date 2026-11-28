import OMAStatements.S_oeis_a262327

/-!
# Proof of OEIS A262327

We prove Colin Barker's closed forms and rational generating function for OEIS A262327.
Tracking column residues in `(ZMod 3)^4`, the row-append operator `T` satisfies
`T V = 6 * V` and `T (T R) = 6 * V + 9 * R` on the 27-element subspace `V` and the
6-element valid-row set `R`, yielding `9 * a (2 * k) = 2 * 36 ^ k + 7 * 9 ^ k` and
`a (2 * k + 1) = 6 * a (2 * k)`.
-/

-- Credit: @PrimordialAA

namespace OMA.A262327
open OMA.S_oeis_a262327 PowerSeries

abbrev S := Fin 4 → ZMod 3
def bv (r : Row) (j : Fin 4) : ZMod 3 := if r.1 j then 1 else 0
def cm {m : ℕ} (r : Fin m → Row) : S := fun j => (binaryValue fun i => (r i).1 j : ZMod 3)
def cnt (m : ℕ) (s : S) : ℕ := Fintype.card {r : Fin m → Row // cm r = s}
def rL : Fin 6 → Row := let F := false; let U := true
  ![⟨![F,F,F,F], by decide⟩, ⟨![F,F,U,U], by decide⟩, ⟨![F,U,U,F], by decide⟩,
    ⟨![U,F,F,U], by decide⟩, ⟨![U,U,F,F], by decide⟩, ⟨![U,U,U,U], by decide⟩]
def rI (r : Row) : Fin 6 := match r.1 0, r.1 1, r.1 2 with
  | false, false, false => 0 | false, false, true => 1 | false, true, _ => 2
  | true, false, _ => 3 | true, true, false => 4 | true, true, true => 5
def eR : Fin 6 ≃ Row := ⟨rL, rI, by decide, by decide⟩
def T (f : S → ℕ) (s : S) : ℕ := ∑ i : Fin 6, f fun j => 2 * (s j - bv (rL i) j)
def V (s : S) : ℕ := if 2 * s 0 + s 1 + 2 * s 2 + s 3 = 0 then 1 else 0
def R (s : S) : ℕ := if (∀ j, s j ≠ 2) ∧ 2 * s 0 + s 1 + 2 * s 2 + s 3 = 0 then 1 else 0

lemma z3 (x y s : ZMod 3) : 2 * x + y = s ↔ x = 2 * (s - y) := by revert x y s; decide

lemma a_eq (n : ℕ) : a n = cnt (n + 1) 0 := Fintype.card_congr <| Equiv.subtypeEquivRight fun _ =>
  ⟨fun h => funext fun j => (ZMod.natCast_eq_zero_iff _ 3).mpr (h j),
   fun h j => (ZMod.natCast_eq_zero_iff _ 3).mp (congr_fun h j)⟩

lemma cnt_zero (s : S) : cnt 0 s = if s = 0 then 1 else 0 := by
  unfold cnt; split_ifs with h
  · subst h
    exact @Fintype.card_unique _ ⟨⟨⟨Fin.elim0, by ext j; rfl⟩⟩, fun ⟨_, _⟩ => by ext i; exact Fin.elim0 i⟩ _
  · exact @Fintype.card_eq_zero _ _ ⟨fun ⟨_, hr⟩ => h (by rw [← hr]; ext j; rfl)⟩

lemma cnt_succ (m : ℕ) (s : S) : cnt (m + 1) s = T (cnt m) s := by
  rw [show T (cnt m) s = ∑ w : Row, cnt m fun j => 2 * (s j - bv w j) from
    eR.sum_comp fun w => cnt m fun j => 2 * (s j - bv w j)]
  unfold cnt; rw [← Fintype.card_sigma]
  refine Fintype.card_congr
    { toFun := fun ⟨r, hr⟩ => ⟨r (Fin.last m), ⟨fun i => r i.castSucc, funext fun j =>
        (z3 _ _ _).mp (by simpa [cm, bv, binaryValue] using congr_fun hr j)⟩⟩
      invFun := fun ⟨w, ⟨r', hr'⟩⟩ => ⟨Fin.snoc (α := fun _ => Row) r' w, funext fun j => by
        have h := (z3 (cm r' j) (bv w j) (s j)).mpr (congr_fun hr' j)
        change ((2 * binaryValue (fun i : Fin m => (Fin.snoc (α := fun _ => Row) r' w i.castSucc).1 j) +
          if (Fin.snoc (α := fun _ => Row) r' w (Fin.last m)).1 j then 1 else 0 : ℕ) : ZMod 3) = s j
        simpa [cm, bv, Fin.snoc_castSucc, Fin.snoc_last] using h⟩
      left_inv := fun ⟨r, _⟩ => by
        ext i j; refine Fin.lastCases ?_ (fun k => ?_) i <;> simp [Fin.snoc_last, Fin.snoc_castSucc]
      right_inv := fun ⟨w, ⟨r', _⟩⟩ => by
        dsimp only; refine Sigma.ext (Fin.snoc_last (α := fun _ => Row) w r') ?_
        rw [Subtype.heq_iff_coe_eq fun _ => by simp [Fin.snoc_last]]
        ext i j; simp [Fin.snoc_castSucc] }

lemma T_lin (a b : ℕ) (f g : S → ℕ) (s : S) :
    T (fun t => a * f t + b * g t) s = a * T f s + b * T g s := by
  simp only [T, Finset.sum_add_distrib, Finset.mul_sum]

lemma T_z : ∀ s : S, T (fun t => if t = 0 then 1 else 0) s = R s := by decide
lemma T_V : ∀ s : S, T V s = 6 * V s := by decide
lemma T2_R : ∀ s : S, T (T R) s = 6 * V s + 9 * R s := by decide
lemma T_R0 : T R 0 = 6 := by decide

lemma h9 (k : ℕ) (s : S) :
    9 * cnt (2 * k + 1) s + 2 * 9 ^ k * V s = 2 * 36 ^ k * V s + 9 ^ (k + 1) * R s := by
  induction k generalizing s with
  | zero =>
    rw [show 2 * 0 + 1 = 1 by rfl, cnt_succ, show cnt 0 = _ from funext cnt_zero, T_z]; ring
  | succ k ih =>
    have hL := congr_arg (fun f => T (T f) s) (funext ih)
    have hT2 : ∀ c d f g, T (T fun t => c * f t + d * g t) s = c * T (T f) s + d * T (T g) s :=
      fun c d f g => by rw [show T (fun t => c * f t + d * g t) = _ from funext (T_lin c d f g), T_lin]
    have hTV2 : T (T V) s = 36 * V s := by
      rw [show T V = fun t => 6 * V t from funext T_V, T, ← Finset.mul_sum]; change 6 * T V s = _
      rw [T_V]; ring
    have hstep : T (T (cnt (2 * k + 1))) s = cnt (2 * (k + 1) + 1) s := by
      rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 1 + 1 by omega, cnt_succ,
        show cnt (2 * k + 1 + 1) = T (cnt (2 * k + 1)) from funext (cnt_succ _)]
    rw [hT2, hT2, hstep, hTV2, T2_R] at hL; simp only [pow_succ] at hL ⊢; linarith

lemma nine_a (k : ℕ) : 9 * a (2 * k) = 2 * 36 ^ k + 7 * 9 ^ k := by
  have h := h9 k 0; have hV : V 0 = 1 := by decide
  have hR : R 0 = 1 := by decide
  rw [a_eq]; rw [hV, hR, pow_succ] at h; linarith

lemma a_odd (k : ℕ) : a (2 * k + 1) = 6 * a (2 * k) := by
  have hL := congr_arg (fun f => T f 0) (funext (h9 k))
  rw [T_lin, T_lin, ← cnt_succ, ← a_eq, T_V, T_R0] at hL
  have hV : V 0 = 1 := by decide
  have h9a := nine_a k; rw [hV, pow_succ] at hL; omega

lemma p32 (k : ℕ) : 3 ^ (2 * k) = 9 ^ k := by rw [pow_mul]; norm_num
lemma p92 (k : ℕ) : 9 ^ k * 2 ^ (2 * k) = 36 ^ k := by
  rw [pow_mul, show (36 : ℕ) = 9 * 4 by norm_num, mul_pow]; norm_num

lemma f_even (n : ℕ) (h1 : 1 ≤ n) (h2 : n % 2 = 0) : 2 * a n = 3 ^ (n - 2) * (14 + 2 ^ (n + 2)) := by
  obtain ⟨k, rfl⟩ := Nat.dvd_of_mod_eq_zero h2
  cases k with
  | zero => omega
  | succ k =>
    have h := nine_a (k + 1); have := p92 k
    rw [show 2 * (k + 1) - 2 = 2 * k by omega, p32,
      show 2 * (k + 1) + 2 = 2 * k + 4 by omega, pow_add]
    simp only [pow_succ] at h; linarith

lemma f_odd (n : ℕ) (_ : 1 ≤ n) (h2 : n % 2 = 1) : 6 * a n = 3 ^ (n - 1) * (28 + 2 ^ (n + 2)) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k + 1 := ⟨n / 2, by omega⟩
  rw [a_odd, show 2 * k + 1 - 1 = 2 * k by omega, p32,
    show 2 * k + 1 + 2 = 2 * k + 3 by omega, pow_add]
  have := nine_a k; have := p92 k; linarith

lemma gf : (1 - C 3 * X) * (1 + C 3 * X) * (1 - C 6 * X) * generatingSeries =
    C 3 * X * (C 2 - C 7 * X - C 18 * X ^ 2) := by
  have ⟨ha1, ha2, ha3⟩ : a 1 = 6 ∧ a 2 = 15 ∧ a 3 = 90 := by
    have := nine_a 0; have := nine_a 1; have := a_odd 0; have := a_odd 1; norm_num at *; omega
  rw [show (1 - C (3 : ℤ) * X) * (1 + C 3 * X) * (1 - C 6 * X) =
      1 - C 6 * X ^ 1 - C 9 * X ^ 2 + C 54 * X ^ 3 by simp only [map_ofNat]; ring,
    show C (3 : ℤ) * X * (C 2 - C 7 * X - C 18 * X ^ 2) =
      C 6 * X ^ 1 - C 21 * X ^ 2 - C 54 * X ^ 3 by simp only [map_ofNat]; ring]
  ext n
  simp only [add_mul, sub_mul, one_mul, map_add, map_sub, mul_assoc, coeff_C_mul,
    coeff_X_pow_mul', coeff_X_pow, generatingSeries, coeff_mk]
  by_cases hn : n < 4
  · interval_cases n <;> simp [ha1, ha2, ha3]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    simp (disch := omega) only [if_pos, if_neg, mul_zero, sub_zero]
    rcases Nat.even_or_odd m with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · rw [show k + k + 4 = 2 * (k + 2) by omega, show 2 * (k + 2) - 1 = 2 * (k + 1) + 1 by omega,
        show 2 * (k + 2) - 2 = 2 * (k + 1) by omega, show 2 * (k + 2) - 3 = 2 * k + 1 by omega,
        a_odd (k + 1), a_odd k]
      have e : ∀ j, (9 : ℤ) * a (2 * j) = 2 * 36 ^ j + 7 * 9 ^ j := fun j => by exact_mod_cast nine_a j
      have e0 := e (k + 2); have e1 := e (k + 1); have e2 := e k
      simp only [pow_succ] at e0 e1; push_cast; linarith
    · rw [show 2 * k + 1 + 4 = 2 * (k + 2) + 1 by omega, show 2 * (k + 2) + 1 - 1 = 2 * (k + 2) by omega,
        show 2 * (k + 2) + 1 - 2 = 2 * (k + 1) + 1 by omega, show 2 * (k + 2) + 1 - 3 = 2 * (k + 1) by omega,
        a_odd (k + 2), a_odd (k + 1)]
      push_cast; ring

end OMA.A262327

theorem OMA.solution : type_of% @OMA.S_oeis_a262327.main :=
  ⟨OMA.A262327.f_even, OMA.A262327.f_odd, OMA.A262327.gf⟩
