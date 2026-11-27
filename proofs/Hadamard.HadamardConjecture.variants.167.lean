import FormalConjectures.Wikipedia.Hadamard
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.Circulant
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Data.Matrix.Composition
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.FieldTheory.Finite.GaloisField

/-! # Hadamard matrices through order 668

The proof combines Paley, Goethals–Seidel, bordered Goethals–Seidel (Spence)
and Kronecker constructions. Integer autocorrelations verify each seed.
The Williamson, supplementary difference set and Turyn-type seeds are from
the SageMath tables and the HadamardR database. The Spence data at order 596
are transcribed from the Hadamard construction in upstream PR 3464. At order
668 the four circulant sequences reconstruct Levent Alpöge's Hadamard matrix
as documented in the nreff/hadamard-search HM-668 construction notes.
-/

namespace OMA.Had
open Matrix
def Has (n : ℕ) := ∃ M : Matrix (Fin n) (Fin n) ℝ, (∀ i j, M i j = 1 ∨ M i j = -1) ∧
  M.transpose * M = Matrix.diagonal (fun _ => (n : ℝ))

theorem of_index {X : Type} [Fintype X] [DecidableEq X] {n : ℕ} (hX : Fintype.card X = n)
    (M : Matrix X X ℝ) (he : ∀ i j, M i j = 1 ∨ M i j = -1)
    (hg : M.transpose * M = Matrix.diagonal (fun _ => (n : ℝ))) : Has n := by
  let e := Fintype.equivFinOfCardEq hX
  refine ⟨Matrix.reindex e e M, fun i j => he _ _, ?_⟩
  rw [Matrix.transpose_reindex]
  change Matrix.reindexRingEquiv ℝ e M.transpose * Matrix.reindexRingEquiv ℝ e M = _
  rw [← map_mul,hg]
  ext i j
  simp [Matrix.reindexRingEquiv, Matrix.diagonal_apply]

theorem two : Has 2 := by
  let M : Matrix (Fin 2) (Fin 2) ℝ := !![1,1;1,-1]
  refine ⟨M, ?_, ?_⟩
  · intro i j; fin_cases i <;> fin_cases j <;> norm_num [M]
  · ext i j; fin_cases i <;> fin_cases j <;> norm_num [M, Matrix.mul_apply, Fin.sum_univ_two]

theorem times {n k : ℕ} (hn : Has n) (hk : Has k) : Has (n*k) := by
  rcases hn with ⟨A,ha,hg⟩
  rcases hk with ⟨B,hb,hh⟩
  apply of_index (X := Fin n × Fin k) (by simp) (Matrix.kroneckerMap (·*·) A B)
  · intro i j
    change A i.1 j.1 * B i.2 j.2 = 1 ∨ A i.1 j.1 * B i.2 j.2 = -1
    rcases ha i.1 j.1 with h|h <;> rcases hb i.2 j.2 with h'|h' <;> rw [h,h'] <;> norm_num
  · rw [← Matrix.kroneckerMap_transpose, ← Matrix.mul_kronecker_mul, hg, hh,
        Matrix.diagonal_kronecker_diagonal]
    simp

variable {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]

def rev (f : G → ℝ) (a : G) : ℝ := f (-a)
theorem rev_rev (f : G → ℝ) : rev (rev f) = f := by ext; simp [rev]
abbrev C (f : G → ℝ) := Matrix.circulant f
def R (G : Type) [AddCommGroup G] [DecidableEq G] : Matrix G G ℝ := (Equiv.neg G).toPEquiv.toMatrix
def S (f : G → ℝ) := C f * R G

theorem ct (f : G → ℝ) : (C f).transpose = C (rev f) := Matrix.transpose_circulant _
theorem s_apply (f : G → ℝ) (i j : G) : S f i j = f (i+j) := by
  simp [S, R, PEquiv.mul_toMatrix_toPEquiv, Matrix.circulant_apply]
theorem st (f : G → ℝ) : (S f).transpose = S f := by
  ext i j; simp [s_apply, add_comm]
theorem rr : R G * R G = 1 := by
  ext i j
  simp [R, PEquiv.mul_toMatrix_toPEquiv, PEquiv.toMatrix_apply, Matrix.one_apply]

theorem rc (f : G → ℝ) : R G * C f = C (rev f) * R G := by
  ext i j
  simp [R, PEquiv.mul_toMatrix_toPEquiv, PEquiv.toMatrix_toPEquiv_mul, rev, Matrix.circulant_apply]
  abel_nf

theorem cc (f g : G → ℝ) : C f * C g = C g * C f := Matrix.circulant_mul_comm _ _
theorem cs (f g : G → ℝ) : C f * S g = S g * C (rev f) := by
  unfold S
  rw [← Matrix.mul_assoc, cc f g, Matrix.mul_assoc, Matrix.mul_assoc, rc, rev_rev]

theorem ss (f g : G → ℝ) : S f * S g = C f * C (rev g) := by
  unfold S
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (R G), rc, Matrix.mul_assoc, rr, Matrix.mul_one]

def gs (a b c d : G → ℝ) : Matrix (Fin 4) (Fin 4) (Matrix G G ℝ) :=
  !![C a, S b, S c, S d;
    -S b, C a, -S (rev d), S (rev c);
    -S c, S (rev d), C a, -S (rev b);
    -S d, -S (rev c), S (rev b), C a]

set_option maxHeartbeats 4000000 in
theorem gsgram (a b c d : G → ℝ) (n : ℕ)
  (h : C (rev a)*C a + C (rev b)*C b + C (rev c)*C c + C (rev d)*C d =
    Matrix.diagonal (fun _ => (n:ℝ))) :
  ((gs a b c d).transpose.map (·.transpose)) * gs a b c d =
    Matrix.diagonal (fun _ => Matrix.diagonal (fun _ => (n : ℝ))) := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_four, gs, Matrix.diagonal_apply] <;>
    simp only [Matrix.transpose_neg, ct, st, neg_mul, mul_neg, neg_neg, ss, cs, cc, rev_rev,
      neg_one_smul] at * <;>
    first | exact h | (rw [← h]; abel_nf) | abel_nf
  all_goals
    simp only [neg_one_zsmul, Matrix.transpose_neg, ct, st, neg_mul, mul_neg, neg_neg, ss, cs, cc, rev_rev]
    try abel

def zi (b : Bool) : ℤ := if b then -1 else 1
def rs (f : G → Bool) (j : G) : ℝ := zi (f j)
def corr (f : G → Bool) (i : G) : ℤ := ∑ j : G, zi (f (j-i)) * zi (f j)
def balanced (a b c d : G → Bool) : Prop :=
  ∀ i : G, corr a i + corr b i + corr c i + corr d i =
    if i = 0 then ((4*Fintype.card G : ℕ) : ℤ) else 0
instance (a b c d : G → Bool) : Decidable (balanced a b c d) := by unfold balanced; infer_instance

theorem autocorr (f : G → Bool) (i j : G) :
    (C (rev (rs f))*C (rs f)) i j = (corr f (i-j) : ℝ) := by
  rw [Matrix.circulant_mul]
  simp [C, Matrix.circulant_apply, Matrix.mulVec, dotProduct, corr, rev, rs, neg_sub]

theorem gs_has (a b c d : G → Bool) (hc : balanced a b c d) : Has (4*Fintype.card G) := by
  let B := gs (rs a) (rs b) (rs c) (rs d)
  refine of_index (X := Fin 4 × G) (by simp) (Matrix.comp (Fin 4) (Fin 4) G G ℝ B) ?_ ?_
  · rintro ⟨i,x⟩ ⟨j,y⟩
    change B i j x y = 1 ∨ B i j x y = -1
    have sig (f : G → Bool) (x : G) : rs f x = 1 ∨ rs f x = -1 := by
      cases h : f x <;> simp [rs,zi,h]
    fin_cases i <;> fin_cases j <;>
      norm_num [B, gs, s_apply, Matrix.circulant_apply, rev] <;>
      first | apply sig | (simpa only [neg_eq_iff_eq_neg] using (sig _ _)) |
        (apply Or.symm; simpa only [neg_eq_iff_eq_neg] using (sig _ _))
  · rw [Matrix.transpose_comp]
    change Matrix.compRingEquiv (Fin 4) G ℝ _ * Matrix.compRingEquiv (Fin 4) G ℝ _ = _
    rw [← map_mul]
    have h :
        C (rev (rs a))*C (rs a) + C (rev (rs b))*C (rs b) +
        C (rev (rs c))*C (rs c) + C (rev (rs d))*C (rs d) =
        Matrix.diagonal (fun _ => ((4*Fintype.card G : ℕ) : ℝ)) := by
      ext i j
      simp only [Matrix.add_apply,autocorr]
      have hh := hc (i-j)
      by_cases hij : i = j
      · subst j
        simp at hh ⊢
        exact_mod_cast hh
      · simp [sub_ne_zero.mpr hij] at hh
        rw [Matrix.diagonal_apply_ne _ hij]
        exact_mod_cast hh
    rw [show B.transpose.map (·.transpose) * B = _ from gsgram _ _ _ _ _ h]
    simp


end OMA.Had

namespace OMA.Had
open Finset Matrix
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem paley_corr_int (hF : ringChar F ≠ 2) {a b : F} (hab : a ≠ b) :
    ∑ x : F, quadraticChar F (x-a) * quadraticChar F (x-b) = -1 := by
  let χ := quadraticChar F
  have jac := jacobiSum_nontrivial_inv (quadraticChar_ne_one hF)
  rw [(quadraticChar_isQuadratic F).inv] at jac
  change (∑ t : F, χ t * χ (1-t)) = -χ (-1) at jac
  have hsq : χ (b-a)^2 = 1 := quadraticChar_sq_one (sub_ne_zero.mpr hab.symm)
  have hneg : χ (-1)^2 = 1 := quadraticChar_sq_one (neg_ne_zero.mpr one_ne_zero)
  let e := (Equiv.mulLeft₀ (b-a) (sub_ne_zero.mpr hab.symm)).trans (Equiv.addRight a)
  calc
    _ = ∑ t : F, χ (e t-a) * χ (e t-b) := (e.sum_comp _).symm
    _ = ∑ t : F, χ (-1) * (χ t * χ (1-t)) := by
      apply sum_congr rfl
      intro t _
      change χ ((b-a)*t+a-a) * χ ((b-a)*t+a-b) = _
      rw [add_sub_cancel_right, show (b-a)*t+a-b = (b-a)*((-1)*(1-t)) by ring]
      simp only [map_mul]
      linear_combination (χ (-1) * χ t * χ (1-t)) * hsq
    _ = -1 := by rw [← mul_sum, jac]; nlinarith

theorem paley_corr (hF : ringChar F ≠ 2) {a b : F} (hab : a ≠ b) :
    ∑ x : F, (quadraticChar F (x-a) : ℝ) * (quadraticChar F (x-b) : ℝ) = -1 := by
  exact_mod_cast paley_corr_int hF hab

noncomputable def conf (F : Type*) [Field F] [Fintype F] [DecidableEq F] :
    Matrix (Option F) (Option F) ℝ
  | none, none => 0
  | none, some _ => 1
  | some _, none => quadraticChar F (-1)
  | some a, some b => quadraticChar F (a-b)

theorem paley_shift (hF : ringChar F ≠ 2) (a : F) :
    ∑ x : F, (quadraticChar F (x-a) : ℝ) = 0 := by
  have h : (∑ x : F, quadraticChar F (x-a)) = 0 := by
    exact ((Equiv.subRight a).sum_comp _).trans (quadraticChar_sum_zero hF)
  exact_mod_cast h

theorem paley_gram (hF : ringChar F ≠ 2) :
    (conf F).transpose * conf F = diagonal (fun _ => (Fintype.card F : ℝ)) := by
  ext i j
  rw [mul_apply, Fintype.sum_option]
  simp only [transpose_apply]
  have hneg : (quadraticChar F (-1) : ℝ) ^ 2 = 1 := by
    exact_mod_cast quadraticChar_sq_one (neg_ne_zero.mpr (one_ne_zero' F))
  cases i with
  | none => cases j with
    | none =>
      simp only [conf, ← sq, hneg, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, diagonal_apply_eq]
      norm_num
    | some b =>
      simp only [conf, zero_mul, zero_add, diagonal_apply_ne _ (by simp : none ≠ some b)]
      rw [← mul_sum, paley_shift hF, mul_zero]
  | some a => cases j with
    | none =>
      simp only [conf, mul_zero, zero_add, diagonal_apply_ne _ (by simp : some a ≠ none)]
      rw [← sum_mul, paley_shift hF, zero_mul]
    | some b =>
      by_cases hab : a = b
      · subst b
        simp only [conf, one_mul, diagonal_apply_eq]
        have term (x : F) : (quadraticChar F (x-a) : ℝ) * (quadraticChar F (x-a) : ℝ) =
            if x = a then 0 else 1 := by
          split_ifs with h
          · simp [h]
          · rw [← sq]; exact_mod_cast quadraticChar_sq_one (sub_ne_zero.mpr h)
        have indicator (x : F) : (if x = a then (0 : ℝ) else 1) = 1 - (if x = a then 1 else 0) := by
          split_ifs <;> norm_num
        simp_rw [term, indicator]
        rw [Finset.sum_sub_distrib]
        simp
      · simp only [conf, one_mul, diagonal_apply_ne _ (by simpa using hab : some a ≠ some b)]
        rw [paley_corr hF hab]; norm_num
theorem paley_transpose :
    (conf F).transpose = (quadraticChar F (-1) : ℝ) • conf F := by
  ext i j
  have sq : (quadraticChar F (-1) : ℝ)^2 = 1 := by
    exact_mod_cast quadraticChar_sq_one (neg_ne_zero.mpr (one_ne_zero' F))
  cases i <;> cases j
  · simp [conf]
  · simp [conf]
  · simpa [conf, ← pow_two] using sq.symm
  · rename_i a b
    change (quadraticChar F (b-a) : ℝ) = (quadraticChar F (-1) : ℝ) * (quadraticChar F (a-b) : ℝ)
    rw [show b-a = (-1)*(a-b) by ring, map_mul, Int.cast_mul]
end OMA.Had

namespace OMA.Had
open Matrix
private def PaleyHas (n : ℕ) : Prop := ∃ M : Matrix (Fin n) (Fin n) ℝ,
  (∀ i j, M i j = 1 ∨ M i j = -1) ∧ M.transpose * M = diagonal (fun _ => (n : ℝ))

private lemma movePaley {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (hc : Fintype.card ι = n) (M : Matrix ι ι ℝ)
    (he : ∀ i j, M i j = 1 ∨ M i j = -1) (hg : M.transpose * M = n) : PaleyHas n := by
  let e := (Fintype.equivFinOfCardEq hc).symm
  refine ⟨M.submatrix e e, fun i j => he _ _, ?_⟩
  change M.transpose.submatrix e e * M.submatrix e e = _
  rw [submatrix_mul_equiv, hg]
  exact submatrix_diagonal_equiv _ e
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
private theorem conf_diagonal (i : Option F) : conf F i i = 0 := by
  cases i <;> simp [conf]
private theorem conf_off {i j : Option F} (h : i ≠ j) : conf F i j = 1 ∨ conf F i j = -1 := by
  have sides {x : F} (hx : x ≠ 0) : (quadraticChar F x : ℝ) = 1 ∨ (quadraticChar F x : ℝ) = -1 := by
    rcases quadraticChar_dichotomy hx with hp | hm
    · left; simp [hp]
    · right; simp [hm]
  cases i <;> cases j
  · contradiction
  · exact Or.inl rfl
  · exact sides (neg_ne_zero.mpr one_ne_zero)
  · apply sides
    exact sub_ne_zero.mpr (fun eq => h (congrArg some eq))
private theorem confEntry (i j : Option F) :
    ((conf F + 1) i j = 1 ∨ (conf F + 1) i j = -1) ∧
    ((conf F - 1) i j = 1 ∨ (conf F - 1) i j = -1) := by
  by_cases h : i = j
  · subst j
    simp [conf_diagonal, Matrix.add_apply, Matrix.sub_apply]
  · simpa [Matrix.one_apply_ne h, Matrix.add_apply, Matrix.sub_apply] using
      (And.intro (conf_off (F := F) h) (conf_off (F := F) h))

theorem paley_one (hq : Fintype.card F % 4 = 3) : PaleyHas (Fintype.card F + 1) := by
  have hF : ringChar F ≠ 2 := fun e => by have := FiniteField.even_card_of_char_two e; omega
  have hsg : (quadraticChar F (-1) : ℝ) = -1 := by
    have := quadraticChar_neg_one_iff_not_isSquare.mpr (fun hs => (FiniteField.isSquare_neg_one_iff.mp hs) hq)
    exact_mod_cast this
  have ht : (conf F).transpose = -conf F := by rw [paley_transpose, hsg, neg_one_smul]
  apply movePaley (ι := Option F) (by simp) (conf F + 1) (fun i j => (confEntry i j).1)
  have hg : (conf F).transpose * conf F = (Fintype.card F : ℕ) := paley_gram hF
  simp only [transpose_add, transpose_one, add_mul, mul_add, one_mul, mul_one, Nat.cast_add, Nat.cast_one]
  rw [hg, ht]
  abel

theorem paley_two (hq : Fintype.card F % 4 = 1) : PaleyHas (2*(Fintype.card F + 1)) := by
  have hF : ringChar F ≠ 2 := fun e => by have := FiniteField.even_card_of_char_two e; omega
  have hsg : (quadraticChar F (-1) : ℝ) = 1 := by
    have := (quadraticChar_one_iff_isSquare (neg_ne_zero.mpr (one_ne_zero' F))).mpr
      (FiniteField.isSquare_neg_one_iff.mpr (by omega))
    exact_mod_cast this
  let C := conf F
  have ht : C.transpose = C := by
    change (conf F).transpose = conf F
    rw [paley_transpose, hsg, one_smul]
  have hg : C * C = (Fintype.card F : ℕ) := by
    have h : C.transpose * C = (Fintype.card F : ℕ) := paley_gram hF
    rwa [ht] at h
  let A := C + 1
  let B := C - 1
  apply movePaley (ι := Option F ⊕ Option F) (by simp; omega) (fromBlocks A B B (-A))
  · intro i j
    cases i <;> cases j
    · exact (confEntry _ _).1
    · exact (confEntry _ _).2
    · exact (confEntry _ _).2
    · rename_i i j
      rcases (confEntry i j).1 with h | h
      · right; change -(A i j) = -1; rw [show A i j = 1 from h]
      · left; change -(A i j) = 1; rw [show A i j = -1 from h, neg_neg]
  · have tA : A.transpose = A := by simp [A, ht]
    have tB : B.transpose = B := by simp [B, ht]
    have d : A*A + B*B = ((2*(Fintype.card F + 1) : ℕ) : Matrix (Option F) (Option F) ℝ) := by
      simp only [A,B,add_mul,mul_add,sub_mul,mul_sub,one_mul,mul_one,hg,Nat.cast_add,Nat.cast_ofNat,two_mul]
      noncomm_ring
      norm_num [two_zsmul, two_nsmul]
    have eq : A*B = B*A := by simp only [A,B,add_mul,mul_add,sub_mul,mul_sub,one_mul,mul_one]; abel
    rw [fromBlocks_transpose, transpose_neg, tA, tB, fromBlocks_multiply]
    simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg, ← eq, add_neg_cancel,
      d, show B*B+A*A = A*A+B*B by abel]
    exact (fromBlocks_diagonal _ _).trans (by congr 1; funext i; cases i <;> rfl)
end OMA.Had

namespace OMA.Had

def word {t : ℕ} (w : ℕ) (i : Fin t) : Bool := w.testBit i.val
def wordPair {u v : ℕ} (w : ℕ) (i : Fin u × Fin v) : Bool := w.testBit (i.1.val * v + i.2.val)

private theorem hm4 : Has 4 := times two two

private theorem hm12 : Has 12 := by
  classical
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have z := paley_two (F := ZMod 5) (by rw [ZMod.card])
  rw [ZMod.card] at z
  exact z

private theorem hm20 : Has 20 := by
  classical
  have : Fact (Nat.Prime 19) := ⟨by norm_num⟩
  have z := paley_one (F := ZMod 19) (by rw [ZMod.card])
  rw [ZMod.card] at z
  exact z

private theorem hm28 : Has 28 := by
  classical
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  have z := paley_two (F := ZMod 13) (by rw [ZMod.card])
  rw [ZMod.card] at z
  exact z

private theorem hm36 : Has 36 := by
  classical
  have : Fact (Nat.Prime 17) := ⟨by norm_num⟩
  have z := paley_two (F := ZMod 17) (by rw [ZMod.card])
  rw [ZMod.card] at z
  exact z

private theorem hm44 : Has 44 := by
  classical
  have : Fact (Nat.Prime 43) := ⟨by norm_num⟩
  have z := paley_one (F := ZMod 43) (by rw [ZMod.card])
  rw [ZMod.card] at z
  exact z

private theorem hm52 : Has 52 := by
  classical
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  letI : Fintype (GaloisField 5 2) := Fintype.ofFinite _
  have cardF : Fintype.card (GaloisField 5 2) = 25 := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 5 2 (by decide : 2 ≠ 0)] <;> norm_num
  have z := paley_two (F := GaloisField 5 2) (by rw [cardF])
  rw [cardF] at z
  exact z

private theorem hm60 : Has 60 := by
  classical
  have : Fact (Nat.Prime 29) := ⟨by norm_num⟩
  have z := paley_two (F := ZMod 29) (by rw [ZMod.card])
  rw [ZMod.card] at z
  exact z

private theorem hm68 : Has 68 := by
  classical
  have : Fact (Nat.Prime 67) := ⟨by norm_num⟩
  have z := paley_one (F := ZMod 67) (by rw [ZMod.card])
  rw [ZMod.card] at z
  exact z

private theorem hm76 : Has 76 := by
  classical
  have : Fact (Nat.Prime 37) := ⟨by norm_num⟩
  have z := paley_two (F := ZMod 37) (by rw [ZMod.card])
  rw [ZMod.card] at z
  exact z

private theorem hm84 : Has 84 := by
  classical
  have : Fact (Nat.Prime 41) := ⟨by norm_num⟩
  have z := paley_two (F := ZMod 41) (by rw [ZMod.card])
  rw [ZMod.card] at z
  exact z

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 10000 in
private theorem hm92 : Has 92 := by
  simpa using gs_has (word (t:=23) 0x3ba5dc) (word (t:=23) 0x498192) (word (t:=23) 0x1ca538) (word (t:=23) 0x117e88) (by decide +kernel)

private theorem hm100 : Has 100 := by
  classical
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  letI : Fintype (GaloisField 7 2) := Fintype.ofFinite _
  have cardF : Fintype.card (GaloisField 7 2) = 49 := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 7 2 (by decide : 2 ≠ 0)] <;> norm_num
  have z := paley_two (F := GaloisField 7 2) (by rw [cardF])
  rw [cardF] at z
  exact z

private theorem hm108 : Has 108 := by
  classical
  have : Fact (Nat.Prime 53) := ⟨by norm_num⟩
  have z := paley_two (F := ZMod 53) (by rw [ZMod.card])
  rw [ZMod.card] at z
  exact z

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 10000 in
private theorem hm116 : Has 116 := by
  simpa using gs_has (word (t:=29) 0x735eb38) (word (t:=29) 0x17340b3a) (word (t:=29) 0x25c0e90) (word (t:=29) 0xda2116c) (by decide +kernel)

private theorem hm124 : Has 124 := by
  classical
  have : Fact (Nat.Prime 61) := ⟨by norm_num⟩
  have z := paley_two (F := ZMod 61) (by rw [ZMod.card])
  rw [ZMod.card] at z
  exact z

private theorem hm132 : Has 132 := by
  classical
  have : Fact (Nat.Prime 131) := ⟨by norm_num⟩
  have z := paley_one (F := ZMod 131) (by rw [ZMod.card])
  rw [ZMod.card] at z
  exact z

private theorem hm148 : Has 148 := by
  classical
  have : Fact (Nat.Prime 73) := ⟨by norm_num⟩
  have z := paley_two (F := ZMod 73) (by rw [ZMod.card])
  rw [ZMod.card] at z
  exact z

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 10000 in
private theorem hm156 : Has 156 := by
  simpa using gs_has (word (t:=39) 0x1afb3cdf58) (word (t:=39) 0x1975bdae98) (word (t:=39) 0xecf5af370) (word (t:=39) 0x72be247d4e) (by decide +kernel)

private theorem hm164 : Has 164 := by
  classical
  have : Fact (Nat.Prime 163) := ⟨by norm_num⟩
  have z := paley_one (F := ZMod 163) (by rw [ZMod.card])
  rw [ZMod.card] at z
  exact z

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 10000 in
private theorem hm172 : Has 172 := by
  simpa using gs_has (word (t:=43) 0x385b3fcda1c) (word (t:=43) 0x14d42f42b28) (word (t:=43) 0x207ac935e04) (word (t:=43) 0x730a26450ce) (by decide +kernel)

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 10000 in
private theorem hm188 : Has 188 := by
  simpa using gs_has (word (t:=47) 0x4351b2753de) (word (t:=47) 0x1deaca7e7eec) (word (t:=47) 0x7a824938e9ca) (word (t:=47) 0x260dcfb05d48) (by decide +kernel)

private theorem hm196 : Has 196 := by
  classical
  have : Fact (Nat.Prime 97) := ⟨by norm_num⟩
  have z := paley_two (F := ZMod 97) (by rw [ZMod.card])
  rw [ZMod.card] at z
  exact z

private theorem hm204 : Has 204 := by
  classical
  have : Fact (Nat.Prime 101) := ⟨by norm_num⟩
  have z := paley_two (F := ZMod 101) (by rw [ZMod.card])
  rw [ZMod.card] at z
  exact z

private theorem hm220 : Has 220 := by
  classical
  have : Fact (Nat.Prime 109) := ⟨by norm_num⟩
  have z := paley_two (F := ZMod 109) (by rw [ZMod.card])
  rw [ZMod.card] at z
  exact z

private theorem hm228 : Has 228 := by
  classical
  have : Fact (Nat.Prime 113) := ⟨by norm_num⟩
  have z := paley_two (F := ZMod 113) (by rw [ZMod.card])
  rw [ZMod.card] at z
  exact z

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 10000 in
private theorem hm236 : Has 236 := by
  simpa using gs_has (word (t:=59) 0x22b62183e7b92ba) (word (t:=59) 0x22b62183e7b92ba) (word (t:=59) 0x7bb5beefcd8a3c8) (word (t:=59) 0x7ed3487aea9d8c0) (by decide +kernel)

private theorem hm244 : Has 244 := by
  classical
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  letI : Fintype (GaloisField 11 2) := Fintype.ofFinite _
  have cardF : Fintype.card (GaloisField 11 2) = 121 := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 11 2 (by decide : 2 ≠ 0)] <;> norm_num
  have z := paley_two (F := GaloisField 11 2) (by rw [cardF])
  rw [cardF] at z
  exact z

private theorem hm252 : Has 252 := by
  classical
  have : Fact (Nat.Prime 251) := ⟨by norm_num⟩
  have z := paley_one (F := ZMod 251) (by rw [ZMod.card])
  rw [ZMod.card] at z
  exact z

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 10000 in
private theorem hm260 : Has 260 := by
  simpa using gs_has (word (t:=65) 0x1c14ab632ce4ab5f0) (word (t:=65) 0xb044dc6208f92982) (word (t:=65) 0xae1f72dcb68acec) (word (t:=65) 0x5d1c4e54fbf67e40) (by decide +kernel)

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 10000 in
private theorem hm268 : Has 268 := by
  simpa using gs_has (word (t:=67) 0x359c281ba27ebc652) (word (t:=67) 0x6d155eb4b811318e) (word (t:=67) 0x638064fd84d627650) (word (t:=67) 0x65db500c0a514cbc) (by decide +kernel)

private theorem hm276 : Has 276 := by
  classical
  have : Fact (Nat.Prime 137) := ⟨by norm_num⟩
  have z := paley_two (F := ZMod 137) (by rw [ZMod.card])
  rw [ZMod.card] at z
  exact z

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 10000 in
private theorem hm292 : Has 292 := by
  simpa using gs_has (word (t:=73) 0x1ea334697985a74cea0) (word (t:=73) 0x5cfc7ebc0eee62a800) (word (t:=73) 0x1b6cf382b96b41666a0) (word (t:=73) 0x144994861a589315f) (by decide +kernel)

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 10000 in
private theorem hm324 : Has 324 := by
  simpa using gs_has (wordPair (u:=3) (v:=27) 0x3ebd7c49733a46d198b6) (wordPair (u:=3) (v:=27) 0x1c1428389733a492e6748) (wordPair (u:=3) (v:=27) 0x1b4662db8285077050a0e) (wordPair (u:=3) (v:=27) 0x1b4662dc7d7af8f050a0e) (by decide +kernel)

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 10000 in
private theorem hm356 : Has 356 := by
  simpa using gs_has (word (t:=89) 0x114e1f1639006b24d40a62e) (word (t:=89) 0xeb1e0e9b9006b24d40a62e) (word (t:=89) 0x16052dc746ff94d8d40a62e) (word (t:=89) 0x9fad238c6ff94d8d40a62e) (by decide +kernel)

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 10000 in
private theorem hm372 : Has 372 := by
  simpa using gs_has (word (t:=93) 0x86545dfad0f43d28117567a) (word (t:=93) 0xcea843264a1f82d8502194c) (word (t:=93) 0x1fa332a03451e2097bd8b1ec) (word (t:=93) 0x121de88c92e31fa6edb09c68) (by decide +kernel)

private theorem hm388 : Has 388 := by
  classical
  have : Fact (Nat.Prime 193) := ⟨by norm_num⟩
  have z := paley_two (F := ZMod 193) (by rw [ZMod.card])
  rw [ZMod.card] at z
  exact z

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 10000 in
private theorem hm404 : Has 404 := by
  simpa using gs_has (word (t:=101) 0x1f516263c64ec304bc04a90ea6) (word (t:=101) 0xae9d9c3e4ec304bc04a90ea6) (word (t:=101) 0x19ce0b6551b13cfb4004a90ea6) (word (t:=101) 0x631f49aa9b13cfb4004a90ea6) (by decide +kernel)

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 10000 in
private theorem hm412 : Has 412 := by
  simpa using gs_has (word (t:=103) 0x62605a55228ef08ebb55a5f9b8) (word (t:=103) 0x5978ca149b8153994bebbe7c4) (word (t:=103) 0x637e497806a79fed8e16ba6e8e) (word (t:=103) 0x71ddd7483fb36edcec863e5a1e) (by decide +kernel)

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 10000 in
private theorem hm428 : Has 428 := by
  simpa using gs_has (word (t:=107) 0x5e121f53c21158b3e8768c88682) (word (t:=107) 0x21ede0ac3a1158b3e8768c88682) (word (t:=107) 0x4e10cdac15eea74c17768c88682) (word (t:=107) 0x31ef3253edeea74c17768c88682) (by decide +kernel)

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 10000 in
private theorem hm436 : Has 436 := by
  simpa using gs_has (word (t:=109) 0x61647ba0c54915db573e88765e6) (word (t:=109) 0x694209d8fc81f4609cda6a0a818) (word (t:=109) 0x15c88a4a6087e79bf10c3b553252) (word (t:=109) 0xb603a57bf9ef099ba461c3d915a) (by decide +kernel)

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 10000 in
private theorem hm452 : Has 452 := by
  simpa using gs_has (word (t:=113) 0xa4e1b61369dc2aaf11a4de49e36a) (word (t:=113) 0x189c302ae2efd8ee4fdd08502cfd0) (word (t:=113) 0xf60c6043d6021362886b78b9d526) (word (t:=113) 0x1ca1f0b2a809b57b0660121a6d1d4) (by decide +kernel)

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 10000 in
private theorem hm476 : Has 476 := by
  simpa using gs_has (word (t:=119) 0x3dba4bd595ffd4784f6fdc4a98d9e2) (word (t:=119) 0x4ad40508473a7bb7ca3d703667b130) (word (t:=119) 0x7ced25e318906b1c3f93790ebc9222) (word (t:=119) 0x747cd4c115aa2b2c4d3e2e8dbe050e) (by decide +kernel)

private theorem hm484 : Has 484 := by
  classical
  have : Fact (Nat.Prime 241) := ⟨by norm_num⟩
  have z := paley_two (F := ZMod 241) (by rw [ZMod.card])
  rw [ZMod.card] at z
  exact z

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 10000 in
private theorem hm508 : Has 508 := by
  simpa using gs_has (word (t:=127) 0x172a099c419697f17016967dc66fab16) (word (t:=127) 0x7bcbf1deab02b2e9d9de1049de49e996) (word (t:=127) 0x7feaf8c8ea95a595f8c88737c8378736) (word (t:=127) 0x6ce5f876fb953e2cabced7621af84ca0) (by decide +kernel)

private theorem hm516 : Has 516 := by
  classical
  have : Fact (Nat.Prime 257) := ⟨by norm_num⟩
  have z := paley_two (F := ZMod 257) (by rw [ZMod.card])
  rw [ZMod.card] at z
  exact z

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 10000 in
private theorem hm532 : Has 532 := by
  simpa using gs_has (word (t:=133) 0x175762530f4f72d7f8052c4343cd6e4544) (word (t:=133) 0x12c03cbac499d449e27b99f9b628e4fe08) (word (t:=133) 0x41fcdc51be7e66791e68ae608d74700d2) (word (t:=133) 0x17cbbfbe1ca8b6b46bf7a6a56b7a29c596) (by decide +kernel)

private theorem hm580 : Has 580 := by
  classical
  have : Fact (Nat.Prime 17) := ⟨by norm_num⟩
  letI : Fintype (GaloisField 17 2) := Fintype.ofFinite _
  have cardF : Fintype.card (GaloisField 17 2) = 289 := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 17 2 (by decide : 2 ≠ 0)] <;> norm_num
  have z := paley_two (F := GaloisField 17 2) (by rw [cardF])
  rw [cardF] at z
  exact z

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 10000 in
private theorem hm604 : Has 604 := by
  simpa using gs_has (word (t:=151) 0x334f8af4227afacb7196712ca0a1bbd0ae0d32) (word (t:=151) 0x2050cf57623e742b729250e46c3c4f70818814) (word (t:=151) 0x6f80b34ce6bae892ac596f3b31436b4d9d03fe) (word (t:=151) 0x52ce18bc3479bd5fd7e77006b7b2b077503e48) (by decide +kernel)

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 10000 in
private theorem hm612 : Has 612 := by
  simpa using gs_has (word (t:=153) 0x1432ccbc56fe69da2bc6c1c0d798a78ab8dce6e) (word (t:=153) 0xebbc40a2bd9e916c4377cddfbef4d0f12b1a40) (word (t:=153) 0x102eb52f65493583f321057c968755c06fc0c2) (word (t:=153) 0x4740c1b7c8ce86b2d3c53b51a606066534eb12) (by decide +kernel)

private theorem hm628 : Has 628 := by
  classical
  have : Fact (Nat.Prime 313) := ⟨by norm_num⟩
  have z := paley_two (F := ZMod 313) (by rw [ZMod.card])
  rw [ZMod.card] at z
  exact z

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 10000 in
private theorem hm652 : Has 652 := by
  simpa using gs_has (word (t:=163) 0x12383f66986b2a5fea77311a805ab29e69903e3b6) (word (t:=163) 0x440d219387a8b53138934cc55ed78035f659d0602) (word (t:=163) 0x71b161aa93c41733287bce9fe9e3ac94163fc4052) (word (t:=163) 0x25e4f8bdfc449a87bab9aad1ff2cdd6b98f64b460) (by decide +kernel)


private theorem hm140 : Has 140 := by
  classical
  have : Fact (Nat.Prime 139) := ⟨by norm_num⟩
  have z := paley_one (F := ZMod 139) (by rw [ZMod.card])
  rw [ZMod.card] at z
  exact z

private theorem hm180 : Has 180 := by
  classical
  have : Fact (Nat.Prime 179) := ⟨by norm_num⟩
  have z := paley_one (F := ZMod 179) (by rw [ZMod.card])
  rw [ZMod.card] at z
  exact z

private theorem hm212 : Has 212 := by
  classical
  have : Fact (Nat.Prime 211) := ⟨by norm_num⟩
  have z := paley_one (F := ZMod 211) (by rw [ZMod.card])
  rw [ZMod.card] at z
  exact z

private theorem hm284 : Has 284 := by
  classical
  have : Fact (Nat.Prime 283) := ⟨by norm_num⟩
  have z := paley_one (F := ZMod 283) (by rw [ZMod.card])
  rw [ZMod.card] at z
  exact z

private theorem hm300 : Has 300 := by
  classical
  have : Fact (Nat.Prime 149) := ⟨by norm_num⟩
  have z := paley_two (F := ZMod 149) (by rw [ZMod.card])
  rw [ZMod.card] at z
  exact z

private theorem hm308 : Has 308 := by
  classical
  have : Fact (Nat.Prime 307) := ⟨by norm_num⟩
  have z := paley_one (F := ZMod 307) (by rw [ZMod.card])
  rw [ZMod.card] at z
  exact z

private theorem hm316 : Has 316 := by
  classical
  have : Fact (Nat.Prime 157) := ⟨by norm_num⟩
  have z := paley_two (F := ZMod 157) (by rw [ZMod.card])
  rw [ZMod.card] at z
  exact z

private theorem hm332 : Has 332 := by
  classical
  have : Fact (Nat.Prime 331) := ⟨by norm_num⟩
  have z := paley_one (F := ZMod 331) (by rw [ZMod.card])
  rw [ZMod.card] at z
  exact z

private theorem hm340 : Has 340 := by
  classical
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  letI : Fintype (GaloisField 13 2) := Fintype.ofFinite _
  have cardF : Fintype.card (GaloisField 13 2) = 169 := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 13 2 (by decide : 2 ≠ 0)] <;> norm_num
  have z := paley_two (F := GaloisField 13 2) (by rw [cardF])
  rw [cardF] at z
  exact z

private theorem hm348 : Has 348 := by
  classical
  have : Fact (Nat.Prime 347) := ⟨by norm_num⟩
  have z := paley_one (F := ZMod 347) (by rw [ZMod.card])
  rw [ZMod.card] at z
  exact z

private theorem hm364 : Has 364 := by
  classical
  have : Fact (Nat.Prime 181) := ⟨by norm_num⟩
  have z := paley_two (F := ZMod 181) (by rw [ZMod.card])
  rw [ZMod.card] at z
  exact z

private theorem hm380 : Has 380 := by
  classical
  have : Fact (Nat.Prime 379) := ⟨by norm_num⟩
  have z := paley_one (F := ZMod 379) (by rw [ZMod.card])
  rw [ZMod.card] at z
  exact z

private theorem hm396 : Has 396 := by
  classical
  have : Fact (Nat.Prime 197) := ⟨by norm_num⟩
  have z := paley_two (F := ZMod 197) (by rw [ZMod.card])
  rw [ZMod.card] at z
  exact z

private theorem hm420 : Has 420 := by
  classical
  have : Fact (Nat.Prime 419) := ⟨by norm_num⟩
  have z := paley_one (F := ZMod 419) (by rw [ZMod.card])
  rw [ZMod.card] at z
  exact z

private theorem hm444 : Has 444 := by
  classical
  have : Fact (Nat.Prime 443) := ⟨by norm_num⟩
  have z := paley_one (F := ZMod 443) (by rw [ZMod.card])
  rw [ZMod.card] at z
  exact z

private theorem hm460 : Has 460 := by
  classical
  have : Fact (Nat.Prime 229) := ⟨by norm_num⟩
  have z := paley_two (F := ZMod 229) (by rw [ZMod.card])
  rw [ZMod.card] at z
  exact z

private theorem hm468 : Has 468 := by
  classical
  have : Fact (Nat.Prime 467) := ⟨by norm_num⟩
  have z := paley_one (F := ZMod 467) (by rw [ZMod.card])
  rw [ZMod.card] at z
  exact z

private theorem hm492 : Has 492 := by
  classical
  have : Fact (Nat.Prime 491) := ⟨by norm_num⟩
  have z := paley_one (F := ZMod 491) (by rw [ZMod.card])
  rw [ZMod.card] at z
  exact z

private theorem hm500 : Has 500 := by
  classical
  have : Fact (Nat.Prime 499) := ⟨by norm_num⟩
  have z := paley_one (F := ZMod 499) (by rw [ZMod.card])
  rw [ZMod.card] at z
  exact z

private theorem hm524 : Has 524 := by
  classical
  have : Fact (Nat.Prime 523) := ⟨by norm_num⟩
  have z := paley_one (F := ZMod 523) (by rw [ZMod.card])
  rw [ZMod.card] at z
  exact z

private theorem hm540 : Has 540 := by
  classical
  have : Fact (Nat.Prime 269) := ⟨by norm_num⟩
  have z := paley_two (F := ZMod 269) (by rw [ZMod.card])
  rw [ZMod.card] at z
  exact z

private theorem hm548 : Has 548 := by
  classical
  have : Fact (Nat.Prime 547) := ⟨by norm_num⟩
  have z := paley_one (F := ZMod 547) (by rw [ZMod.card])
  rw [ZMod.card] at z
  exact z

private theorem hm556 : Has 556 := by
  classical
  have : Fact (Nat.Prime 277) := ⟨by norm_num⟩
  have z := paley_two (F := ZMod 277) (by rw [ZMod.card])
  rw [ZMod.card] at z
  exact z

private theorem hm564 : Has 564 := by
  classical
  have : Fact (Nat.Prime 563) := ⟨by norm_num⟩
  have z := paley_one (F := ZMod 563) (by rw [ZMod.card])
  rw [ZMod.card] at z
  exact z

private theorem hm572 : Has 572 := by
  classical
  have : Fact (Nat.Prime 571) := ⟨by norm_num⟩
  have z := paley_one (F := ZMod 571) (by rw [ZMod.card])
  rw [ZMod.card] at z
  exact z

private theorem hm588 : Has 588 := by
  classical
  have : Fact (Nat.Prime 587) := ⟨by norm_num⟩
  have z := paley_one (F := ZMod 587) (by rw [ZMod.card])
  rw [ZMod.card] at z
  exact z

private theorem hm620 : Has 620 := by
  classical
  have : Fact (Nat.Prime 619) := ⟨by norm_num⟩
  have z := paley_one (F := ZMod 619) (by rw [ZMod.card])
  rw [ZMod.card] at z
  exact z

private theorem hm636 : Has 636 := by
  classical
  have : Fact (Nat.Prime 317) := ⟨by norm_num⟩
  have z := paley_two (F := ZMod 317) (by rw [ZMod.card])
  rw [ZMod.card] at z
  exact z

private theorem hm644 : Has 644 := by
  classical
  have : Fact (Nat.Prime 643) := ⟨by norm_num⟩
  have z := paley_one (F := ZMod 643) (by rw [ZMod.card])
  rw [ZMod.card] at z
  exact z

private theorem hm660 : Has 660 := by
  classical
  have : Fact (Nat.Prime 659) := ⟨by norm_num⟩
  have z := paley_one (F := ZMod 659) (by rw [ZMod.card])
  rw [ZMod.card] at z
  exact z


theorem matrix_of_gram {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hentries : ∀ i j, M i j = 1 ∨ M i j = -1)
    (hg : M.transpose * M = Matrix.diagonal (fun _ => (n : ℝ))) :
    Hadamard.IsHadamard M := by
  refine ⟨fun i j => by simpa using hentries i j, ?_⟩
  have hd := congrArg Matrix.det hg
  simp only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, ← sq] at hd
  rw [← Real.sqrt_sq_eq_abs, hd, Real.sqrt_eq_rpow, ← Real.rpow_natCast,
    ← Real.rpow_mul (Nat.cast_nonneg n)]
  congr 1
  ring


open Matrix
variable {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]

set_option maxHeartbeats 4000000 in
theorem gram_blocks (a b c d : G → ℝ) (W : Matrix G G ℝ)
  (h : C (rev a)*C a + C (rev b)*C b + C (rev c)*C c + C (rev d)*C d =
    W) :
  ((gs a b c d).transpose.map (·.transpose)) * gs a b c d =
    Matrix.diagonal (fun _ => W) := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_four, gs, Matrix.diagonal_apply] <;>
    simp only [Matrix.transpose_neg, ct, st, neg_mul, mul_neg, neg_neg, ss, cs, cc, rev_rev,
      neg_one_smul] at * <;>
    first | exact h | (rw [← h]; abel_nf) | abel_nf
  all_goals
    simp only [neg_one_zsmul, Matrix.transpose_neg, ct, st, neg_mul, mul_neg, neg_neg, ss, cs, cc, rev_rev]
    try abel

private def t4z (i j : Fin 4) : ℤ :=
  if i=0 ∨ j=0 ∨ i=j ∧ i≠1 ∧ i≠2 ∨ i=1 ∧ j=2 ∨ i=2 ∧ j=1 then 1 else -1
private def r4z (i j : Fin 4) : ℤ := if i=0 then -1 else t4z i j
private def l4z (i j : Fin 4) : ℤ := if i=j then -1 else 1

private def T4 (i j : Fin 4) : ℝ := t4z i j
private def R4 (i j : Fin 4) : ℝ := r4z i j
private def L4 (i j : Fin 4) : ℝ := l4z i j

private theorem colsT (i j : Fin 4) : ∑ k, T4 k i * T4 k j = if i=j then 4 else 0 := by
  have h : ∀ i j : Fin 4, ∑ k, t4z k i * t4z k j = if i=j then 4 else 0 := by decide +kernel
  have e := h i j
  unfold T4
  by_cases he : i=j <;> simp only [he, if_true, if_false] at e ⊢ <;> exact_mod_cast e
private theorem colsR (i j : Fin 4) : ∑ k, R4 k i * R4 k j = if i=j then 4 else 0 := by
  have h : ∀ i j : Fin 4, ∑ k, r4z k i * r4z k j = if i=j then 4 else 0 := by decide +kernel
  have e := h i j
  unfold R4
  by_cases he : i=j <;> simp only [he, if_true, if_false] at e ⊢ <;> exact_mod_cast e
private theorem colsL (i j : Fin 4) : ∑ k, L4 k i * L4 k j = if i=j then 4 else 0 := by
  have h : ∀ i j : Fin 4, ∑ k, l4z k i * l4z k j = if i=j then 4 else 0 := by decide +kernel
  have e := h i j
  unfold L4
  by_cases he : i=j <;> simp only [he, if_true, if_false] at e ⊢ <;> exact_mod_cast e
private theorem colsTR (i j : Fin 4) : ∑ k, T4 k i * R4 k j = -(2*L4 j i) := by
  have h : ∀ i j : Fin 4, ∑ k, t4z k i * r4z k j = -(2*l4z j i) := by decide +kernel
  have e := h i j
  unfold T4 R4 L4
  exact_mod_cast e
private theorem colsRT (i j : Fin 4) : ∑ k, R4 k i * T4 k j = -(2*L4 i j) := by
  simpa only [mul_comm] using colsTR j i

def bordered (B : Matrix (Fin 4 × G) (Fin 4 × G) ℝ) :
    Matrix (Fin 4 ⊕ Fin 4 × G) (Fin 4 ⊕ Fin 4 × G) ℝ :=
  Matrix.fromBlocks T4 (fun i j => R4 i j.1) (fun i j => L4 i.1 j) B

theorem border_check (B : Matrix (Fin 4 × G) (Fin 4 × G) ℝ)
    (hcol : ∀ p j y, ∑ z, B (p,z) (j,y) = if p=j then 2 else 0)
    (hbb : ∀ (i j : Fin 4 × G), ∑ z, B z i * B z j =
      if i.1=j.1 then (if i.2=j.2 then (4 * Fintype.card G : ℝ) else -4) else 0) :
    (bordered B).transpose * bordered B =
      Matrix.diagonal (fun _ => (4*(Fintype.card G+1) : ℝ)) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fintype.sum_sum_type]
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      change (∑ k, T4 k i * T4 k j) + (∑ k : Fin 4 × G, L4 k.1 i * L4 k.1 j) = _
      simp only [Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        ← Finset.mul_sum, colsL, colsT]
      by_cases h : i=j <;> simp [Matrix.diagonal_apply,h] <;> ring
    | inr jy =>
      rcases jy with ⟨j,y⟩
      change (∑ k, T4 k i * R4 k j) + (∑ k : Fin 4 × G, L4 k.1 i * B k (j,y)) = _
      simp only [Fintype.sum_prod_type, ← Finset.mul_sum, hcol, colsTR,
        Matrix.diagonal_apply_ne _ Sum.inl_ne_inr]
      simp [mul_ite] <;> ring
  | inr ix =>
    rcases ix with ⟨i,x⟩
    cases j with
    | inl j =>
      change (∑ k, R4 k i * T4 k j) + (∑ k : Fin 4 × G, B k (i,x) * L4 k.1 j) = _
      simp only [Fintype.sum_prod_type, ← Finset.sum_mul, hcol, colsRT,
        Matrix.diagonal_apply_ne _ Sum.inr_ne_inl]
      simp [ite_mul] <;> ring
    | inr jy =>
      rcases jy with ⟨j,y⟩
      change (∑ k, R4 k i * R4 k j) + (∑ k : Fin 4 × G, B k (i,x) * B k (j,y)) = _
      simp only [colsR, hbb]
      by_cases hx : i=j <;> by_cases hy : x=y <;>
        simp [Matrix.diagonal_apply,Prod.ext_iff,hx,hy] <;> ring

def spence (a b c d : G → Bool) : Prop :=
  (∑ x, zi (a x)) = 2 ∧ (∑ x, zi (b x)) = 0 ∧
    (∑ x, zi (c x)) = 0 ∧ (∑ x, zi (d x)) = 0 ∧
    ∀ i, corr a i + corr b i + corr c i + corr d i =
      if i=0 then ((4*Fintype.card G : ℕ) : ℤ) else -4
instance (a b c d : G → Bool) : Decidable (spence a b c d) := by unfold spence; infer_instance
private theorem sumC (f : G → ℝ) (y : G) : (∑ z, C f z y) = ∑ z, f z := by
  simpa [Matrix.circulant_apply] using (Equiv.subRight y).sum_comp f
private theorem sumS (f : G → ℝ) (y : G) : (∑ z, S f z y) = ∑ z, f z := by
  simp only [s_apply]
  exact Fintype.sum_equiv (Equiv.addRight y) _ _ fun _ => rfl
private theorem sumRev (f : G → ℝ) : (∑ z, rev f z) = ∑ z, f z := by
  exact Fintype.sum_equiv (Equiv.neg G) _ _ fun _ => rfl
private theorem sumRS (f : G → Bool) : (∑ z, rs f z) = ((∑ z, zi (f z) : ℤ) : ℝ) := by simp [rs]

theorem spence_has (a b c d : G → Bool) (hs : spence a b c d) : Has (4*(Fintype.card G+1)) := by
  let A := gs (rs a) (rs b) (rs c) (rs d)
  let B := Matrix.comp (Fin 4) (Fin 4) G G ℝ A
  let W : Matrix G G ℝ := fun x y => if x=y then (4 * Fintype.card G : ℝ) else -4
  rcases hs with ⟨ha,hb,hc,hd,hco⟩
  have h : C (rev (rs a))*C (rs a) + C (rev (rs b))*C (rs b) +
      C (rev (rs c))*C (rs c) + C (rev (rs d))*C (rs d) = W := by
    ext i j
    simp only [Matrix.add_apply,autocorr]
    have hh := hco (i-j)
    by_cases hij : i=j
    · subst j
      simp [W] at hh ⊢
      exact_mod_cast hh
    · simp [sub_ne_zero.mpr hij] at hh
      simp only [W,if_neg hij]
      exact_mod_cast hh
  have gram : B.transpose * B = Matrix.comp (Fin 4) (Fin 4) G G ℝ
      (Matrix.diagonal fun _ => W) := by
    dsimp only [B]
    rw [Matrix.transpose_comp]
    change Matrix.compRingEquiv (Fin 4) G ℝ _ * Matrix.compRingEquiv (Fin 4) G ℝ _ = _
    rw [← map_mul]
    exact congrArg (Matrix.comp (Fin 4) (Fin 4) G G ℝ) (gram_blocks _ _ _ _ W h)
  have hcol (p j : Fin 4) (y : G) :
      (∑ x, B (p,x) (j,y)) = if p=j then 2 else 0 := by
    change (∑ x, A p j x y) = _
    fin_cases p <;> fin_cases j <;>
      norm_num [A,gs,Finset.sum_neg_distrib,sumC,sumS,sumRev,sumRS,ha,hb,hc,hd] <;>
      exact (sumC (rs a) y).trans (by simp [sumRS,ha])
  have hbb (i j : Fin 4 × G) : (∑ z, B z i * B z j) =
      if i.1=j.1 then (if i.2=j.2 then (4 * Fintype.card G : ℝ) else -4) else 0 := by
    change (B.transpose * B) i j = _
    rw [gram]
    change (Matrix.diagonal (fun _ : Fin 4 => W) i.1 j.1) i.2 j.2 = _
    by_cases he : i.1=j.1
    · rw [if_pos he]
      have heq : (Matrix.diagonal (fun _ : Fin 4 => W)) i.1 j.1 = W := by
        rw [he,Matrix.diagonal_apply_eq]
      rw [heq]
    · rw [if_neg he,Matrix.diagonal_apply_ne _ he]
      rfl
  apply of_index (X := Fin 4 ⊕ Fin 4 × G) (by simp; omega) (bordered B)
  · intro i j
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        change T4 i j = 1 ∨ T4 i j = -1
        unfold T4 t4z; split <;> norm_num
      | inr j =>
        change R4 i j.1 = 1 ∨ R4 i j.1 = -1
        unfold R4 r4z t4z
        split
        · norm_num
        · split <;> norm_num
    | inr ix =>
      rcases ix with ⟨i,x⟩
      cases j with
      | inl j =>
        change L4 i j = 1 ∨ L4 i j = -1
        unfold L4 l4z; split <;> norm_num
      | inr jy =>
        rcases jy with ⟨j,y⟩
        change A i j x y = 1 ∨ A i j x y = -1
        have sig (f : G → Bool) (x : G) : rs f x = 1 ∨ rs f x = -1 := by
          cases h : f x <;> simp [rs,zi,h]
        fin_cases i <;> fin_cases j <;>
          norm_num [A, gs, s_apply, Matrix.circulant_apply, rev] <;>
          first | apply sig | (simpa only [neg_eq_iff_eq_neg] using (sig _ _)) |
            (apply Or.symm; simpa only [neg_eq_iff_eq_neg] using (sig _ _))
  · simpa using border_check B hcol hbb

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 10000 in
private theorem hm596 : Has 596 := by
  simpa using spence_has (word (t:=148) 0x2b368e74361738b66a4acda39d0d85ce2d9a8) (word (t:=148) 0xfd48608d174ef9ed407f52182345d3be7b501) (word (t:=148) 0x11c362e55fe4272dba7b8f2746a806f634916) (word (t:=148) 0x11c362e55fe4272dbafb8f2746a806f634914) (by decide +kernel)

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 10000 in
private theorem hm668 : Has 668 := by
  simpa using spence_has (word (t:=166) 0x2da6ac01d3b04261b92abdb4d5a03a71f7b3c8daa8) (word (t:=166) 0x7c1cd56ea4a0496b5bb80f839aadd4b3f6d21488f) (word (t:=166) 0x38e789eed00889f10d1a871cf13dda026ec1de5caf) (word (t:=166) 0x2b3b9b166807032e90ca3d677372cd031f9a2de6b8) (by decide +kernel)

private theorem hm8 : Has 8 := times two hm4
private theorem hm16 : Has 16 := times two hm8
private theorem hm24 : Has 24 := times two hm12
private theorem hm32 : Has 32 := times two hm16
private theorem hm40 : Has 40 := times two hm20
private theorem hm48 : Has 48 := times two hm24
private theorem hm56 : Has 56 := times two hm28
private theorem hm64 : Has 64 := times two hm32
private theorem hm72 : Has 72 := times two hm36
private theorem hm80 : Has 80 := times two hm40
private theorem hm88 : Has 88 := times two hm44
private theorem hm96 : Has 96 := times two hm48
private theorem hm104 : Has 104 := times two hm52
private theorem hm112 : Has 112 := times two hm56
private theorem hm120 : Has 120 := times two hm60
private theorem hm128 : Has 128 := times two hm64
private theorem hm136 : Has 136 := times two hm68
private theorem hm144 : Has 144 := times two hm72
private theorem hm152 : Has 152 := times two hm76
private theorem hm160 : Has 160 := times two hm80
private theorem hm168 : Has 168 := times two hm84
private theorem hm176 : Has 176 := times two hm88
private theorem hm184 : Has 184 := times two hm92
private theorem hm192 : Has 192 := times two hm96
private theorem hm200 : Has 200 := times two hm100
private theorem hm208 : Has 208 := times two hm104
private theorem hm216 : Has 216 := times two hm108
private theorem hm224 : Has 224 := times two hm112
private theorem hm232 : Has 232 := times two hm116
private theorem hm240 : Has 240 := times two hm120
private theorem hm248 : Has 248 := times two hm124
private theorem hm256 : Has 256 := times two hm128
private theorem hm264 : Has 264 := times two hm132
private theorem hm272 : Has 272 := times two hm136
private theorem hm280 : Has 280 := times two hm140
private theorem hm288 : Has 288 := times two hm144
private theorem hm296 : Has 296 := times two hm148
private theorem hm304 : Has 304 := times two hm152
private theorem hm312 : Has 312 := times two hm156
private theorem hm320 : Has 320 := times two hm160
private theorem hm328 : Has 328 := times two hm164
private theorem hm336 : Has 336 := times two hm168
private theorem hm344 : Has 344 := times two hm172
private theorem hm352 : Has 352 := times two hm176
private theorem hm360 : Has 360 := times two hm180
private theorem hm368 : Has 368 := times two hm184
private theorem hm376 : Has 376 := times two hm188
private theorem hm384 : Has 384 := times two hm192
private theorem hm392 : Has 392 := times two hm196
private theorem hm400 : Has 400 := times two hm200
private theorem hm408 : Has 408 := times two hm204
private theorem hm416 : Has 416 := times two hm208
private theorem hm424 : Has 424 := times two hm212
private theorem hm432 : Has 432 := times two hm216
private theorem hm440 : Has 440 := times two hm220
private theorem hm448 : Has 448 := times two hm224
private theorem hm456 : Has 456 := times two hm228
private theorem hm464 : Has 464 := times two hm232
private theorem hm472 : Has 472 := times two hm236
private theorem hm480 : Has 480 := times two hm240
private theorem hm488 : Has 488 := times two hm244
private theorem hm496 : Has 496 := times two hm248
private theorem hm504 : Has 504 := times two hm252
private theorem hm512 : Has 512 := times two hm256
private theorem hm520 : Has 520 := times two hm260
private theorem hm528 : Has 528 := times two hm264
private theorem hm536 : Has 536 := times two hm268
private theorem hm544 : Has 544 := times two hm272
private theorem hm552 : Has 552 := times two hm276
private theorem hm560 : Has 560 := times two hm280
private theorem hm568 : Has 568 := times two hm284
private theorem hm576 : Has 576 := times two hm288
private theorem hm584 : Has 584 := times two hm292
private theorem hm592 : Has 592 := times two hm296
private theorem hm600 : Has 600 := times two hm300
private theorem hm608 : Has 608 := times two hm304
private theorem hm616 : Has 616 := times two hm308
private theorem hm624 : Has 624 := times two hm312
private theorem hm632 : Has 632 := times two hm316
private theorem hm640 : Has 640 := times two hm320
private theorem hm648 : Has 648 := times two hm324
private theorem hm656 : Has 656 := times two hm328
private theorem hm664 : Has 664 := times two hm332

private theorem finiteCases (k : ℕ) (hk : k < 167) : Has (4*k) := by
  interval_cases k
  · refine ⟨0, (fun i => Fin.elim0 i), ?_⟩
    ext i
    exact Fin.elim0 i
  · exact hm4
  · exact hm8
  · exact hm12
  · exact hm16
  · exact hm20
  · exact hm24
  · exact hm28
  · exact hm32
  · exact hm36
  · exact hm40
  · exact hm44
  · exact hm48
  · exact hm52
  · exact hm56
  · exact hm60
  · exact hm64
  · exact hm68
  · exact hm72
  · exact hm76
  · exact hm80
  · exact hm84
  · exact hm88
  · exact hm92
  · exact hm96
  · exact hm100
  · exact hm104
  · exact hm108
  · exact hm112
  · exact hm116
  · exact hm120
  · exact hm124
  · exact hm128
  · exact hm132
  · exact hm136
  · exact hm140
  · exact hm144
  · exact hm148
  · exact hm152
  · exact hm156
  · exact hm160
  · exact hm164
  · exact hm168
  · exact hm172
  · exact hm176
  · exact hm180
  · exact hm184
  · exact hm188
  · exact hm192
  · exact hm196
  · exact hm200
  · exact hm204
  · exact hm208
  · exact hm212
  · exact hm216
  · exact hm220
  · exact hm224
  · exact hm228
  · exact hm232
  · exact hm236
  · exact hm240
  · exact hm244
  · exact hm248
  · exact hm252
  · exact hm256
  · exact hm260
  · exact hm264
  · exact hm268
  · exact hm272
  · exact hm276
  · exact hm280
  · exact hm284
  · exact hm288
  · exact hm292
  · exact hm296
  · exact hm300
  · exact hm304
  · exact hm308
  · exact hm312
  · exact hm316
  · exact hm320
  · exact hm324
  · exact hm328
  · exact hm332
  · exact hm336
  · exact hm340
  · exact hm344
  · exact hm348
  · exact hm352
  · exact hm356
  · exact hm360
  · exact hm364
  · exact hm368
  · exact hm372
  · exact hm376
  · exact hm380
  · exact hm384
  · exact hm388
  · exact hm392
  · exact hm396
  · exact hm400
  · exact hm404
  · exact hm408
  · exact hm412
  · exact hm416
  · exact hm420
  · exact hm424
  · exact hm428
  · exact hm432
  · exact hm436
  · exact hm440
  · exact hm444
  · exact hm448
  · exact hm452
  · exact hm456
  · exact hm460
  · exact hm464
  · exact hm468
  · exact hm472
  · exact hm476
  · exact hm480
  · exact hm484
  · exact hm488
  · exact hm492
  · exact hm496
  · exact hm500
  · exact hm504
  · exact hm508
  · exact hm512
  · exact hm516
  · exact hm520
  · exact hm524
  · exact hm528
  · exact hm532
  · exact hm536
  · exact hm540
  · exact hm544
  · exact hm548
  · exact hm552
  · exact hm556
  · exact hm560
  · exact hm564
  · exact hm568
  · exact hm572
  · exact hm576
  · exact hm580
  · exact hm584
  · exact hm588
  · exact hm592
  · exact hm596
  · exact hm600
  · exact hm604
  · exact hm608
  · exact hm612
  · exact hm616
  · exact hm620
  · exact hm624
  · exact hm628
  · exact hm632
  · exact hm636
  · exact hm640
  · exact hm644
  · exact hm648
  · exact hm652
  · exact hm656
  · exact hm660
  · exact hm664

end OMA.Had

theorem OMA.solution : type_of% @Hadamard.HadamardConjecture.variants.«167» := by
  suffices hbound : 672 ≤ Hadamard.hadamardConstant from lt_of_lt_of_le (by norm_num) hbound
  unfold Hadamard.hadamardConstant
  refine le_iInf fun k => le_iInf fun hk => ?_
  by_cases h : 168 ≤ k
  · have hn : 672 ≤ 4*k := by omega
    exact_mod_cast hn
  · have hw : OMA.Had.Has (4*k) := by
      by_cases hsmall : k < 167
      · exact OMA.Had.finiteCases k hsmall
      · have hk' : k = 167 := by omega
        subst k
        exact OMA.Had.hm668
    obtain ⟨M,he,hg⟩ := hw
    exact (hk ⟨M, OMA.Had.matrix_of_gram M he hg⟩).elim
