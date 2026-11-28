import OMAStatements.S_oeis_a227433
import Mathlib

-- Problem: OEIS A227433, Resta's conjecture: the number of ordered pairs of 2 X 2 matrices
-- over Z/pZ that do not commute is p^3 (p^3 - 1) (p^2 - 1) for every prime p
-- Statement: statements/oeis-a227433.lean (declaration OMA.S_oeis_a227433.main)
-- Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)
--
-- Proof. Let F = Z/pZ, a field with p elements. A scalar matrix commutes with all p^4
-- matrices, and there are p scalar matrices. Let A be not scalar. The map (x, y) -> x I + y A
-- is injective, and each matrix that commutes with A is of this form (solve the three linear
-- equations of A B = B A in each of the cases A01 /= 0, A10 /= 0, A00 /= A11). So the
-- centralizer of A has p^2 elements. The number of commuting pairs is thus
-- p * p^4 + (p^4 - p) * p^2, and p^8 minus this number is p^3 (p^3 - 1) (p^2 - 1).

namespace OMA.A227433

open Matrix

variable {F : Type*} [Field F]

/-- The matrix is a multiple of the identity. -/
def IsScalar (A : Matrix (Fin 2) (Fin 2) F) : Prop :=
  A 0 1 = 0 ∧ A 1 0 = 0 ∧ A 0 0 = A 1 1

lemma comm_iff (A B : Matrix (Fin 2) (Fin 2) F) :
    A * B = B * A ↔ (A 0 1 * B 1 0 = B 0 1 * A 1 0 ∧
      B 0 1 * (A 0 0 - A 1 1) = A 0 1 * (B 0 0 - B 1 1) ∧
      A 1 0 * (B 0 0 - B 1 1) = B 1 0 * (A 0 0 - A 1 1)) := by
  rw [← Matrix.ext_iff]
  simp only [Fin.forall_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  constructor
  · rintro ⟨⟨h00, h01⟩, h10, h11⟩
    exact ⟨by linear_combination h00, by linear_combination h01, by linear_combination h10⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨by linear_combination h1, by linear_combination h2⟩, by linear_combination h3,
      by linear_combination -h1⟩

lemma comm_of_scalar (A : Matrix (Fin 2) (Fin 2) F) (hA : IsScalar A)
    (B : Matrix (Fin 2) (Fin 2) F) : A * B = B * A := by
  obtain ⟨h1, h2, h3⟩ := hA
  rw [comm_iff, h1, h2, h3]
  simp

lemma entries (x y : F) (A : Matrix (Fin 2) (Fin 2) F) (i j : Fin 2) :
    (x • (1 : Matrix (Fin 2) (Fin 2) F) + y • A) i j = x * (1 : Matrix (Fin 2) (Fin 2) F) i j + y * A i j := by
  simp

lemma eq_of_mul (x y : F) (A B : Matrix (Fin 2) (Fin 2) F) (h1 : y * A 0 1 = B 0 1)
    (h2 : y * A 1 0 = B 1 0) (h3 : y * (A 0 0 - A 1 1) = B 0 0 - B 1 1)
    (hx : x = B 0 0 - y * A 0 0) :
    x • (1 : Matrix (Fin 2) (Fin 2) F) + y • A = B := by
  rw [← Matrix.ext_iff]
  simp only [Fin.forall_fin_two, entries]
  subst hx
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · simp
  · simpa using h1
  · simpa using h2
  · simp
    linear_combination -h3

lemma exists_of_comm (A B : Matrix (Fin 2) (Fin 2) F) (hA : ¬ IsScalar A) (hB : A * B = B * A) :
    ∃ xy : F × F, xy.1 • (1 : Matrix (Fin 2) (Fin 2) F) + xy.2 • A = B := by
  obtain ⟨h1, h2, h3⟩ := (comm_iff A B).mp hB
  by_cases hb : A 0 1 = 0
  · by_cases hc : A 1 0 = 0
    · have hd : A 0 0 - A 1 1 ≠ 0 := fun h => hA ⟨hb, hc, sub_eq_zero.mp h⟩
      rw [hb, zero_mul] at h2
      rw [hc, zero_mul] at h3
      have hf : B 0 1 = 0 := by
        rcases mul_eq_zero.mp h2 with h | h
        · exact h
        · exact absurd h hd
      have hg : B 1 0 = 0 := by
        rcases mul_eq_zero.mp h3.symm with h | h
        · exact h
        · exact absurd h hd
      refine ⟨(B 0 0 - (B 0 0 - B 1 1) / (A 0 0 - A 1 1) * A 0 0,
        (B 0 0 - B 1 1) / (A 0 0 - A 1 1)), eq_of_mul _ _ A B ?_ ?_ ?_ rfl⟩
      · rw [hb, hf, mul_zero]
      · rw [hc, hg, mul_zero]
      · exact div_mul_cancel₀ _ hd
    · rw [hb, zero_mul] at h1
      have hf : B 0 1 = 0 := by
        rcases mul_eq_zero.mp h1.symm with h | h
        · exact h
        · exact absurd h hc
      refine ⟨(B 0 0 - B 1 0 / A 1 0 * A 0 0, B 1 0 / A 1 0), eq_of_mul _ _ A B ?_ ?_ ?_ rfl⟩
      · rw [hb, hf, mul_zero]
      · exact div_mul_cancel₀ _ hc
      · rw [div_mul_eq_mul_div, div_eq_iff hc]
        linear_combination -h3
  · refine ⟨(B 0 0 - B 0 1 / A 0 1 * A 0 0, B 0 1 / A 0 1), eq_of_mul _ _ A B ?_ ?_ ?_ rfl⟩
    · exact div_mul_cancel₀ _ hb
    · rw [div_mul_eq_mul_div, div_eq_iff hb]
      linear_combination -h1
    · rw [div_mul_eq_mul_div, div_eq_iff hb]
      linear_combination h2

lemma card_centralizer [Fintype F] [DecidableEq F] (A : Matrix (Fin 2) (Fin 2) F)
    (hA : ¬ IsScalar A) :
    Fintype.card {B : Matrix (Fin 2) (Fin 2) F // A * B = B * A} = Fintype.card F ^ 2 := by
  have hc : Fintype.card (F × F) = Fintype.card F ^ 2 := by rw [Fintype.card_prod, sq]
  rw [← hc]
  symm
  apply Fintype.card_of_bijective
    (f := fun xy : F × F => (⟨xy.1 • 1 + xy.2 • A, by simp [mul_add, add_mul]⟩ :
      {B : Matrix (Fin 2) (Fin 2) F // A * B = B * A}))
  constructor
  · rintro ⟨x, y⟩ ⟨x', y'⟩ h
    have h' : x • (1 : Matrix (Fin 2) (Fin 2) F) + y • A = x' • 1 + y' • A := congrArg Subtype.val h
    rw [← Matrix.ext_iff] at h'
    simp only [Fin.forall_fin_two, entries] at h'
    obtain ⟨⟨h00, h01⟩, h10, h11⟩ := h'
    simp at h00 h01 h10 h11
    have hy : y = y' := by
      by_contra hne
      have hne' : y - y' ≠ 0 := sub_ne_zero.mpr hne
      apply hA
      refine ⟨?_, ?_, ?_⟩
      · rcases h01 with h | h
        · exact absurd h hne
        · exact h
      · rcases h10 with h | h
        · exact absurd h hne
        · exact h
      · have : (y - y') * (A 0 0 - A 1 1) = 0 := by linear_combination h00 - h11
        rcases mul_eq_zero.mp this with h | h
        · exact absurd h hne'
        · exact sub_eq_zero.mp h
    subst hy
    have hx : x = x' := by linear_combination h00
    rw [hx]
  · rintro ⟨B, hB⟩
    obtain ⟨xy, h⟩ := exists_of_comm A B hA hB
    exact ⟨xy, Subtype.ext h⟩

lemma card_scalar [Fintype F] [DecidableEq F]
    [Fintype {A : Matrix (Fin 2) (Fin 2) F // IsScalar A}] :
    Fintype.card {A : Matrix (Fin 2) (Fin 2) F // IsScalar A} = Fintype.card F := by
  symm
  apply Fintype.card_of_bijective
    (f := fun a : F => (⟨a • 1, by simp [IsScalar]⟩ :
      {A : Matrix (Fin 2) (Fin 2) F // IsScalar A}))
  constructor
  · intro a b h
    have h' : a • (1 : Matrix (Fin 2) (Fin 2) F) = b • 1 := congrArg Subtype.val h
    have := congrFun (congrFun h' 0) 0
    simpa using this
  · rintro ⟨A, h1, h2, h3⟩
    refine ⟨A 0 0, Subtype.ext ?_⟩
    show A 0 0 • (1 : Matrix (Fin 2) (Fin 2) F) = A
    rw [← Matrix.ext_iff]
    simp only [Fin.forall_fin_two]
    simp [h1, h2, h3]

lemma card_mat [Fintype F] [DecidableEq F] :
    Fintype.card (Matrix (Fin 2) (Fin 2) F) = Fintype.card F ^ 4 := by
  rw [Fintype.card_congr (Matrix.of (m := Fin 2) (n := Fin 2) (α := F)).symm, Fintype.card_fun,
    Fintype.card_fun, Fintype.card_fin, ← pow_mul]

theorem count_comm [Fintype F] [DecidableEq F] :
    Fintype.card {P : Matrix (Fin 2) (Fin 2) F × Matrix (Fin 2) (Fin 2) F // P.1 * P.2 = P.2 * P.1}
      = Fintype.card F * Fintype.card F ^ 4
        + (Fintype.card F ^ 4 - Fintype.card F) * Fintype.card F ^ 2 := by
  classical
  rw [Fintype.card_congr (Equiv.subtypeProdEquivSigmaSubtype
    (fun A B : Matrix (Fin 2) (Fin 2) F => A * B = B * A)), Fintype.card_sigma]
  have hf : ∀ A : Matrix (Fin 2) (Fin 2) F,
      Fintype.card {B : Matrix (Fin 2) (Fin 2) F // A * B = B * A}
        = if IsScalar A then Fintype.card F ^ 4 else Fintype.card F ^ 2 := by
    intro A
    split_ifs with h
    · rw [Fintype.card_congr (Equiv.subtypeUnivEquiv (comm_of_scalar A h)), card_mat]
    · exact card_centralizer A h
  rw [Finset.sum_congr rfl (fun A _ => hf A), Finset.sum_ite, Finset.sum_const, Finset.sum_const,
    smul_eq_mul, smul_eq_mul]
  have hs : (Finset.univ.filter (fun A : Matrix (Fin 2) (Fin 2) F => IsScalar A)).card
      = Fintype.card F := by
    rw [← Fintype.card_subtype]
    exact card_scalar
  have hn' : (Finset.univ.filter (fun A : Matrix (Fin 2) (Fin 2) F => ¬ IsScalar A)).card
      = Fintype.card F ^ 4 - Fintype.card F := by
    rw [← Fintype.card_subtype, Fintype.card_subtype_compl, card_mat, card_scalar]
  rw [hs, hn']

theorem result (p : ℕ) (hp : p.Prime) :
    Nat.card {P : Matrix (Fin 2) (Fin 2) (ZMod p) × Matrix (Fin 2) (Fin 2) (ZMod p) //
      P.1 * P.2 ≠ P.2 * P.1} = p ^ 3 * (p ^ 3 - 1) * (p ^ 2 - 1) := by
  have : Fact p.Prime := ⟨hp⟩
  classical
  rw [Nat.card_eq_fintype_card]
  have h := Fintype.card_subtype_compl
    (fun P : Matrix (Fin 2) (Fin 2) (ZMod p) × Matrix (Fin 2) (Fin 2) (ZMod p) =>
      P.1 * P.2 = P.2 * P.1)
  rw [count_comm, Fintype.card_prod, card_mat, ZMod.card] at h
  rw [h]
  have h1 : 1 ≤ p ^ 3 := Nat.one_le_pow _ _ hp.pos
  have h2 : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ hp.pos
  have h3 : p ≤ p ^ 4 := Nat.le_self_pow (by norm_num) p
  apply Nat.sub_eq_of_eq_add
  zify [h1, h2, h3]
  ring

end OMA.A227433

theorem OMA.solution : type_of% @OMA.S_oeis_a227433.main :=
  fun p hp => OMA.A227433.result p hp
