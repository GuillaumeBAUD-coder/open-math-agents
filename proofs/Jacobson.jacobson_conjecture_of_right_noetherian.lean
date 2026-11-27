import FormalConjectures.Wikipedia.Jacobson

-- Problem: Jacobson Conjecture — jacobson conjecture of right noetherian
-- Upstream: formal-conjectures FormalConjectures/Wikipedia/Jacobson.lean:66 (declaration Jacobson.jacobson_conjecture_of_right_noetherian)
-- Credit: @senamakel (the owner of the agent is credited as the solver)

/-!
# Proof of `Jacobson.jacobson_conjecture_of_right_noetherian`

Herstein's counterexample [He1965], with the `2`-adic integers in place of `ℤ_(p)`.
`R` is the ring of upper triangular `2 × 2` matrices over `ℚ_[2]` whose top-left entry lies in
`ℤ_[2]`.
1. `R` is right Noetherian: a right ideal `N` is determined, among the right ideals it contains,
   by its ideal of top-left entries in `ℤ_[2]` (`P N`) and by the `ℚ_[2]`-subspace of right
   columns of its elements with top-left entry `0` (`Q N`). The map `N ↦ (P N, Q N)` is strictly
   monotone into a product of two Noetherian lattices.
2. Any element with top-left entry in `2ℤ_[2]` and bottom-right entry `0` is in the Jacobson
   radical `J`: `1 + y * M` has an explicit left inverse in `R`.
3. With `x = diag(2, 0)` and `e(β)` the matrix with `β` in the top-right corner,
   `e(β) = x * e(β / 2)`, so by induction every `e(β)` lies in every `J ^ n`, and
   `⨅ n, J ^ n ≠ 0`.
-/

namespace HersteinRing

open Matrix

/-- Upper triangular 2x2 matrices over `ℚ_[2]` whose top-left entry is a `2`-adic integer. -/
noncomputable def S : Subring (Matrix (Fin 2) (Fin 2) ℚ_[2]) where
  carrier := {M | M 1 0 = 0 ∧ ‖M 0 0‖ ≤ 1}
  mul_mem' := by
    rintro A B ⟨hA1, hA2⟩ ⟨hB1, hB2⟩
    refine ⟨?_, ?_⟩
    · simp [Matrix.mul_apply, Fin.sum_univ_two, hA1, hB1]
    · simp only [Matrix.mul_apply, Fin.sum_univ_two, hB1, mul_zero, add_zero, norm_mul]
      exact mul_le_one₀ hA2 (norm_nonneg _) hB2
  one_mem' := by simp
  add_mem' := by
    rintro A B ⟨hA1, hA2⟩ ⟨hB1, hB2⟩
    refine ⟨by simp [hA1, hB1], ?_⟩
    simp only [Matrix.add_apply]
    exact (Padic.nonarchimedean _ _).trans (max_le hA2 hB2)
  zero_mem' := by simp
  neg_mem' := by
    rintro A ⟨hA1, hA2⟩
    exact ⟨by simp [hA1], by simpa using hA2⟩

abbrev R := ↥S

lemma mem_S {M : Matrix (Fin 2) (Fin 2) ℚ_[2]} : M ∈ S ↔ M 1 0 = 0 ∧ ‖M 0 0‖ ≤ 1 := Iff.rfl


lemma two_norm_lt : ‖(2 : ℚ_[2])‖ < 1 := by
  simpa using Padic.norm_p_lt_one (p := 2)

/-- Every element with top-left entry in `2ℤ_[2]` and bottom-right entry `0` lies in the
Jacobson radical: `1 + y * M` has an explicit left inverse in `R`. -/
lemma mem_jac (M : R) (h0 : ‖M.1 0 0‖ < 1) (h11 : M.1 1 1 = 0) : M ∈ Ring.jacobson R := by
  rw [← Ideal.jacobson_bot, Ideal.mem_jacobson_iff]
  intro y
  have hy10 : y.1 1 0 = 0 := y.2.1
  have hy00 : ‖y.1 0 0‖ ≤ 1 := y.2.2
  have hM10 : M.1 1 0 = 0 := M.2.1
  set t := y.1 0 0 * M.1 0 0 with ht_def
  have ht : ‖t‖ < 1 := by
    rw [ht_def, norm_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_right hy00 (norm_nonneg _) h0
  have h1t : ‖1 + t‖ = 1 := by
    rw [Padic.add_eq_max_of_ne] <;> simp [ht.le, ht.ne']
  have hne : 1 + t ≠ 0 := by
    intro h; rw [h] at h1t; simp at h1t
  refine ⟨⟨!![(1 + t)⁻¹, -((1 + t)⁻¹ * (y.1 0 0 * M.1 0 1)); 0, 1], by
    simp [mem_S, norm_inv, h1t]⟩, ?_⟩
  rw [Submodule.mem_bot]
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, hy10, hM10, h11, -Matrix.cons_mul]
  all_goals first
    | ring1
    | (rw [mul_assoc, ← ht_def]; field_simp; ring)

/-- The element with a single entry `β` in the top-right corner. -/
noncomputable def e (β : ℚ_[2]) : R := ⟨!![0, β; 0, 0], by simp [mem_S]⟩

noncomputable def x2 : R := ⟨!![2, 0; 0, 0], by simp [mem_S, two_norm_lt.le]⟩

lemma e_mem_succ (n : ℕ) : ∀ β, e β ∈ Ring.jacobson R ^ (n + 1) := by
  induction n with
  | zero =>
    intro β
    rw [Submodule.pow_one]
    exact mem_jac _ (by simp [e]) (by simp [e])
  | succ n ih =>
    intro β
    rw [Submodule.pow_succ' _ (Nat.succ_ne_zero n)]
    have hx : x2 ∈ Ring.jacobson R := mem_jac _ (by simpa [x2] using two_norm_lt) (by simp [x2])
    have := Submodule.mul_mem_mul hx (ih (β / 2))
    convert this using 1
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [e, x2, Matrix.mul_apply, Fin.sum_univ_two]
    field_simp

lemma e_mem (n : ℕ) (β : ℚ_[2]) : e β ∈ Ring.jacobson R ^ n := by
  cases n with
  | zero => rw [Submodule.pow_zero, Ideal.one_eq_top]; trivial
  | succ n => exact e_mem_succ n β

lemma not_jac : ¬ Jacobson.JacobsonConjectureFor R := by
  intro h
  have he : e 1 ∈ ⨅ n : ℕ, Ring.jacobson R ^ n := Submodule.mem_iInf _ |>.mpr fun n => e_mem n 1
  unfold Jacobson.JacobsonConjectureFor at h
  rw [h, Submodule.zero_eq_bot, Submodule.mem_bot] at he
  have := congrArg (fun M : R => M.1 0 1) he
  simp [e] at this

section Noetherian

lemma smul_eq (N : Submodule Rᵐᵒᵖ R) {m : R} (hm : m ∈ N) (r : R) : m * r ∈ N := by
  have := N.smul_mem (MulOpposite.op r) hm
  rwa [op_smul_eq_mul] at this

/-- The top-left entries of a right ideal, as an ideal of `ℤ_[2]`. -/
noncomputable def P (N : Submodule Rᵐᵒᵖ R) : Ideal ℤ_[2] where
  carrier := {a | ∃ m ∈ N, m.1 0 0 = (a : ℚ_[2])}
  add_mem' := by
    rintro a b ⟨m, hm, ha⟩ ⟨n, hn, hb⟩
    exact ⟨m + n, N.add_mem hm hn, by simp [ha, hb]⟩
  zero_mem' := ⟨0, N.zero_mem, by simp⟩
  smul_mem' := by
    rintro s a ⟨m, hm, ha⟩
    refine ⟨m * ⟨!![(s : ℚ_[2]), 0; 0, 0], by simp [mem_S, PadicInt.norm_le_one]⟩,
      smul_eq N hm _, ?_⟩
    have h10 : m.1 1 0 = 0 := m.2.1
    simp [Matrix.mul_apply, Fin.sum_univ_two, ha, mul_comm, -Matrix.cons_mul]

/-- The right column of the elements of a right ideal with top-left entry `0`. -/
noncomputable def Q (N : Submodule Rᵐᵒᵖ R) : Submodule ℚ_[2] (ℚ_[2] × ℚ_[2]) where
  carrier := {v | ∃ m ∈ N, m.1 0 0 = 0 ∧ m.1 0 1 = v.1 ∧ m.1 1 1 = v.2}
  add_mem' := by
    rintro v w ⟨m, hm, h1, h2, h3⟩ ⟨n, hn, k1, k2, k3⟩
    exact ⟨m + n, N.add_mem hm hn, by simp [h1, k1], by simp [h2, k2], by simp [h3, k3]⟩
  zero_mem' := ⟨0, N.zero_mem, by simp, by simp, by simp⟩
  smul_mem' := by
    rintro t v ⟨m, hm, h1, h2, h3⟩
    refine ⟨m * ⟨!![0, 0; 0, t], by simp [mem_S]⟩, smul_eq N hm _, ?_, ?_, ?_⟩
    all_goals
      have h10 : m.1 1 0 = 0 := m.2.1
      simp [Matrix.mul_apply, Fin.sum_univ_two, h1, h2, h3, h10, mul_comm, -Matrix.cons_mul]

lemma PQ_strictMono : StrictMono (fun N : Submodule Rᵐᵒᵖ R => (P N, Q N)) := by
  intro N N' hlt
  have hle := hlt.le
  refine lt_of_le_of_ne ⟨?_, ?_⟩ ?_
  · rintro a ⟨m, hm, ha⟩; exact ⟨m, hle hm, ha⟩
  · rintro v ⟨m, hm, h⟩; exact ⟨m, hle hm, h⟩
  · intro heq
    apply hlt.ne
    apply le_antisymm hle
    intro m' hm'
    have hP : P N = P N' := congrArg Prod.fst heq
    have hQ : Q N = Q N' := congrArg Prod.snd heq
    have ha : (⟨m'.1 0 0, m'.2.2⟩ : ℤ_[2]) ∈ P N' := ⟨m', hm', rfl⟩
    rw [← hP] at ha
    obtain ⟨m, hm, hmm⟩ := ha
    have hd : m' - m ∈ N' := N'.sub_mem hm' (hle hm)
    have hv : ((m' - m).1 0 1, (m' - m).1 1 1) ∈ Q N' :=
      ⟨m' - m, hd, by simp [hmm], rfl, rfl⟩
    rw [← hQ] at hv
    obtain ⟨d, hdN, d1, d2, d3⟩ := hv
    have hdeq : d = m' - m := by
      apply Subtype.ext
      have e10 : d.1 1 0 = 0 := d.2.1
      have f10 : (m' - m).1 1 0 = 0 := (m' - m).2.1
      ext i j
      fin_cases i <;> fin_cases j
      · simpa [hmm] using d1
      · exact d2
      · exact e10.trans f10.symm
      · exact d3
    have : m' = d + m := by rw [hdeq]; abel
    rw [this]
    exact N.add_mem hdN hm

theorem noeth : IsRightNoetherianRing R :=
  isNoetherian_iff'.mpr PQ_strictMono.wellFoundedGT

end Noetherian

end HersteinRing

theorem OMA.solution : type_of% @Jacobson.jacobson_conjecture_of_right_noetherian := by
  intro h
  haveI := HersteinRing.noeth
  exact HersteinRing.not_jac (h HersteinRing.R)
