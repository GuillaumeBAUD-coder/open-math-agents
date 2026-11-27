import OMAReductions.R_Erdos724_erdos_724_variants_bose_parker_shrikhande_R1
import Mathlib

-- Step Erdos724.erdos_724.variants.bose_parker_shrikhande.R1.H2: hypothesis H2 of reduction Erdos724.erdos_724.variants.bose_parker_shrikhande.R1
-- Credit: @luciusacarr

/-! Orders divisible by `4`: write `n = 2^k * m` with `m` odd and `k ≥ 2`. Orthogonal pairs exist for
`4` and `8` (from `GF(4)`, `GF(8)`, checked by `decide`), for odd `m` (`i + j`, `i + 2j`), and
pairs multiply under the direct product of Latin squares. -/

open Erdos724

namespace OMA724four

/-- `n` has a pair of orthogonal Latin squares. -/
def Pair (n : ℕ) : Prop := ∃ L M : LatinSquare n, IsOrthogonal L M

lemma ne_of_orth {n : ℕ} (hn : 2 ≤ n) {L M : LatinSquare n} (h : IsOrthogonal L M) : L ≠ M := by
  rintro rfl
  let i0 : Fin n := ⟨0, by omega⟩
  let i1 : Fin n := ⟨1, by omega⟩
  obtain ⟨j, hj⟩ := (Finite.injective_iff_surjective.mp (L.row_injective i1)) (L.mat i0 i0)
  have := h (a₁ := (i0, i0)) (a₂ := (i1, j)) (by simp [hj])
  have : i0 = i1 := congrArg Prod.fst this
  simp [i0, i1, Fin.ext_iff] at this

lemma fin_eq_of_modEq {n : ℕ} {a b : Fin n} (h : a.val ≡ b.val [MOD n]) : a = b :=
  Fin.ext (Nat.ModEq.eq_of_lt_of_lt h a.isLt b.isLt)

/-- The Latin square `(i, j) ↦ i + c * j (mod n)` for `c` coprime to `n`. -/
def sq (n c : ℕ) (hc : Nat.Coprime c n) (hn : 0 < n) : LatinSquare n where
  mat i j := ⟨(i.val + c * j.val) % n, Nat.mod_lt _ hn⟩
  row_injective i j j' h := by
    have h' : i.val + c * j.val ≡ i.val + c * j'.val [MOD n] := by
      unfold Nat.ModEq; simpa [Fin.ext_iff] using h
    exact fin_eq_of_modEq (Nat.ModEq.cancel_left_of_coprime (by
      rw [Nat.gcd_comm]; exact hc) (Nat.ModEq.add_left_cancel' _ h'))
  col_injective j i i' h := by
    have h' : i.val + c * j.val ≡ i'.val + c * j.val [MOD n] := by
      unfold Nat.ModEq
      exact congrArg Fin.val h
    exact fin_eq_of_modEq (Nat.ModEq.add_right_cancel' _ h')

lemma pair_odd {n : ℕ} (hodd : Odd n) : Pair n := by
  have hn0 : 0 < n := hodd.pos
  have h2 : Nat.Coprime 2 n := (Nat.coprime_two_left).mpr hodd
  refine ⟨sq n 1 (Nat.coprime_one_left n) hn0, sq n 2 h2 hn0, ?_⟩
  rintro ⟨i, j⟩ ⟨i', j'⟩ h
  simp only [sq, Prod.mk.injEq, Fin.ext_iff] at h
  obtain ⟨ha, hb⟩ := h
  have ha' : i.val + j.val ≡ i'.val + j'.val [MOD n] := by unfold Nat.ModEq; simpa using ha
  have hb' : (i.val + j.val) + j.val ≡ (i.val + j.val) + j'.val [MOD n] := by
    have : i.val + 2 * j.val ≡ i'.val + 2 * j'.val [MOD n] := hb
    have e1 : i.val + 2 * j.val = (i.val + j.val) + j.val := by ring
    have e2 : i'.val + 2 * j'.val = (i'.val + j'.val) + j'.val := by ring
    rw [e1, e2] at this
    exact this.trans (Nat.ModEq.add_right _ ha'.symm)
  have hj : j = j' := fin_eq_of_modEq (Nat.ModEq.add_left_cancel' _ hb')
  subst hj
  have hi : i = i' := fin_eq_of_modEq (Nat.ModEq.add_right_cancel' _ ha')
  subst hi
  rfl

/-- Direct product of Latin squares, on `Fin (a * b)` via `finProdFinEquiv`. -/
def prodSq {a b : ℕ} (P : LatinSquare a) (Q : LatinSquare b) : LatinSquare (a * b) where
  mat x y := finProdFinEquiv (P.mat (finProdFinEquiv.symm x).1 (finProdFinEquiv.symm y).1,
    Q.mat (finProdFinEquiv.symm x).2 (finProdFinEquiv.symm y).2)
  row_injective x y y' h := by
    have h' := Prod.mk.inj (finProdFinEquiv.injective h)
    apply finProdFinEquiv.symm.injective
    exact Prod.ext (P.row_injective _ h'.1) (Q.row_injective _ h'.2)
  col_injective y x x' h := by
    have h' := Prod.mk.inj (finProdFinEquiv.injective h)
    apply finProdFinEquiv.symm.injective
    exact Prod.ext (P.col_injective _ h'.1) (Q.col_injective _ h'.2)

lemma pair_mul {a b : ℕ} (ha : Pair a) (hb : Pair b) : Pair (a * b) := by
  obtain ⟨L1, M1, h1⟩ := ha
  obtain ⟨L2, M2, h2⟩ := hb
  refine ⟨prodSq L1 L2, prodSq M1 M2, ?_⟩
  rintro ⟨x, y⟩ ⟨x', y'⟩ h
  simp only [prodSq, Prod.mk.injEq] at h
  obtain ⟨hL, hM⟩ := h
  have hL' := Prod.mk.inj (finProdFinEquiv.injective hL)
  have hM' := Prod.mk.inj (finProdFinEquiv.injective hM)
  have e1 := h1 (a₁ := ((finProdFinEquiv.symm x).1, (finProdFinEquiv.symm y).1))
    (a₂ := ((finProdFinEquiv.symm x').1, (finProdFinEquiv.symm y').1))
    (by simp only [Prod.mk.injEq]; exact ⟨hL'.1, hM'.1⟩)
  have e2 := h2 (a₁ := ((finProdFinEquiv.symm x).2, (finProdFinEquiv.symm y).2))
    (a₂ := ((finProdFinEquiv.symm x').2, (finProdFinEquiv.symm y').2))
    (by simp only [Prod.mk.injEq]; exact ⟨hL'.2, hM'.2⟩)
  simp only [Prod.mk.injEq] at e1 e2
  have hx : x = x' := finProdFinEquiv.symm.injective (Prod.ext e1.1 e2.1)
  have hy : y = y' := finProdFinEquiv.symm.injective (Prod.ext e1.2 e2.2)
  rw [hx, hy]

def L4 : Matrix (Fin 4) (Fin 4) (Fin 4) :=
  !![0, 1, 2, 3;
    1, 0, 3, 2;
    2, 3, 0, 1;
    3, 2, 1, 0]

def M4 : Matrix (Fin 4) (Fin 4) (Fin 4) :=
  !![0, 2, 3, 1;
    1, 3, 2, 0;
    2, 0, 1, 3;
    3, 1, 0, 2]

def L8 : Matrix (Fin 8) (Fin 8) (Fin 8) :=
  !![0, 1, 2, 3, 4, 5, 6, 7;
    1, 0, 3, 2, 5, 4, 7, 6;
    2, 3, 0, 1, 6, 7, 4, 5;
    3, 2, 1, 0, 7, 6, 5, 4;
    4, 5, 6, 7, 0, 1, 2, 3;
    5, 4, 7, 6, 1, 0, 3, 2;
    6, 7, 4, 5, 2, 3, 0, 1;
    7, 6, 5, 4, 3, 2, 1, 0]

def M8 : Matrix (Fin 8) (Fin 8) (Fin 8) :=
  !![0, 2, 4, 6, 3, 1, 7, 5;
    1, 3, 5, 7, 2, 0, 6, 4;
    2, 0, 6, 4, 1, 3, 5, 7;
    3, 1, 7, 5, 0, 2, 4, 6;
    4, 6, 0, 2, 7, 5, 3, 1;
    5, 7, 1, 3, 6, 4, 2, 0;
    6, 4, 2, 0, 5, 7, 1, 3;
    7, 5, 3, 1, 4, 6, 0, 2]

def mk4 (m : Matrix (Fin 4) (Fin 4) (Fin 4)) (hr : ∀ i, Function.Injective (m i))
    (hc : ∀ j, Function.Injective (m.transpose j)) : LatinSquare 4 := ⟨m, hr, hc⟩

def mk8 (m : Matrix (Fin 8) (Fin 8) (Fin 8)) (hr : ∀ i, Function.Injective (m i))
    (hc : ∀ j, Function.Injective (m.transpose j)) : LatinSquare 8 := ⟨m, hr, hc⟩

lemma pair4 : Pair 4 := by
  refine ⟨mk4 L4 (by show ∀ i, Function.Injective fun j ↦ L4 i j; decide +kernel)
      (by show ∀ j, Function.Injective fun i ↦ L4 i j; decide +kernel),
    mk4 M4 (by show ∀ i, Function.Injective fun j ↦ M4 i j; decide +kernel)
      (by show ∀ j, Function.Injective fun i ↦ M4 i j; decide +kernel), ?_⟩
  unfold IsOrthogonal mk4
  decide +kernel

lemma pair8 : Pair 8 := by
  refine ⟨mk8 L8 (by show ∀ i, Function.Injective fun j ↦ L8 i j; decide +kernel)
      (by show ∀ j, Function.Injective fun i ↦ L8 i j; decide +kernel),
    mk8 M8 (by show ∀ i, Function.Injective fun j ↦ M8 i j; decide +kernel)
      (by show ∀ j, Function.Injective fun i ↦ M8 i j; decide +kernel), ?_⟩
  unfold IsOrthogonal mk8
  decide +kernel

lemma pair_two_pow : ∀ k : ℕ, 2 ≤ k → Pair (2 ^ k) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases (show k = 2 ∨ k = 3 ∨ 4 ≤ k by omega) with rfl | rfl | h4
    · exact pair4
    · exact pair8
    · have e : 2 ^ k = 2 ^ (k - 2) * 4 := by
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]; congr 1; omega
      rw [e]
      exact pair_mul (ih (k - 2) (by omega) (by omega)) pair4

theorem main_H2 : OMA.R_Erdos724_erdos_724_variants_bose_parker_shrikhande_R1.H2 := by
  unfold OMA.R_Erdos724_erdos_724_variants_bose_parker_shrikhande_R1.H2
  intro n h4 hn
  obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd (show n ≠ 0 by omega)
  have hk : 2 ≤ k := by
    by_contra hk
    obtain ⟨t, rfl⟩ := hm
    interval_cases k <;> omega
  obtain ⟨L, M, h⟩ := pair_mul (pair_two_pow k hk) (pair_odd hm)
  exact ⟨L, M, ne_of_orth (by omega) h, h⟩

end OMA724four

theorem OMA.solution : OMA.R_Erdos724_erdos_724_variants_bose_parker_shrikhande_R1.H2 := OMA724four.main_H2
