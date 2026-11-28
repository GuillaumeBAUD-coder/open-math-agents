import OMAStatements.S_mo_353633
import Mathlib

theorem OMA.solution : type_of% @OMA.S_mo_353633.main := by
  intro K _instField _instDec n k x hrank
  classical
  let vals : Finset K := Finset.univ.image x
  let m : ℕ := vals.card
  have hm_le : m ≤ n := by
    have hcard : vals.card ≤ Fintype.card (Fin n) := by
      simpa [vals, Finset.card_univ] using
        (Finset.card_image_le (s := (Finset.univ : Finset (Fin n))) (f := x))
    simpa [m, Fintype.card_fin] using hcard
  let e : {a // a ∈ vals} ≃ Fin m := vals.equivFin
  let val : Fin m → K := fun j => (e.symm j).1
  have hval_inj : Function.Injective val := by
    intro i j hij
    apply e.symm.injective
    exact Subtype.ext hij
  have hval_mem : ∀ j, val j ∈ vals := fun j => (e.symm j).2
  have hx_in : ∀ i, x i ∈ vals := fun i => by
    simpa [vals] using Finset.mem_image_of_mem x (Finset.mem_univ i)
  have hexists : ∀ j, ∃ i : Fin n, x i = val j := by
    intro j
    rcases Finset.mem_image.mp (hval_mem j) with ⟨i, _, hi⟩
    exact ⟨i, hi⟩
  let rep : Fin m → Fin n := fun j => Classical.choose (hexists j)
  have hrep : ∀ j, x (rep j) = val j := fun j => Classical.choose_spec (hexists j)
  have hrep_inj : Function.Injective rep := by
    intro i j hij
    apply hval_inj
    rw [← hrep i, ← hrep j, hij]
  let A : Matrix (Fin n) (Fin n) K := Matrix.vandermonde x
  let B : Matrix (Fin n) (Fin m) K :=
    Matrix.of fun i j => if x i = val j then (1 : K) else 0
  let C : Matrix (Fin m) (Fin n) K :=
    Matrix.of fun t j => val t ^ (j : ℕ)
  let C0 : Matrix (Fin m) (Fin m) K := Matrix.vandermonde val
  have hdet : C0.det ≠ 0 :=
    (Matrix.det_vandermonde_ne_zero_iff).2 hval_inj
  have hrow : ∀ (i : Fin n) (t0 : Fin m), val t0 = x i →
      ∀ t : Fin m, t ≠ t0 → x i ≠ val t := by
    intro i t0 ht0 t ht h
    apply ht
    apply hval_inj
    rw [ht0, h]
  have hA : A = B * C := by
    ext i j
    rw [Matrix.mul_apply]
    let t0 : Fin m := e ⟨x i, hx_in i⟩
    have ht0 : val t0 = x i := by
      simp [val, t0, Equiv.symm_apply_apply]
    rw [Finset.sum_eq_single (s := Finset.univ) t0]
    · simp [A, B, C, Matrix.vandermonde_apply, Matrix.of_apply, ht0]
    · intro t _ ht
      have hne : x i ≠ val t := hrow i t0 ht0 t ht
      simp [B, C, Matrix.of_apply, hne]
    · intro h
      exact False.elim (h (Finset.mem_univ t0))
  let emb : Fin m → Fin n := fun j => ⟨j.1, Nat.lt_of_lt_of_le j.isLt hm_le⟩
  have hA0 : A.submatrix id emb = B * C0 := by
    ext i j
    rw [Matrix.submatrix_apply, Matrix.mul_apply]
    let t0 : Fin m := e ⟨x i, hx_in i⟩
    have ht0 : val t0 = x i := by
      simp [val, t0, Equiv.symm_apply_apply]
    rw [Finset.sum_eq_single (s := Finset.univ) t0]
    · simp [A, B, C0, Matrix.vandermonde_apply, Matrix.of_apply, ht0, emb]
    · intro t _ ht
      have hne : x i ≠ val t := hrow i t0 ht0 t ht
      simp [B, Matrix.of_apply, hne]
    · intro h
      exact False.elim (h (Finset.mem_univ t0))
  have hBrow : B.submatrix rep id = 1 := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [Matrix.submatrix_apply, Matrix.one_apply, B, Matrix.of_apply, hrep]
    · have hne : val i ≠ val j := fun h => hij (hval_inj h)
      simp [Matrix.submatrix_apply, Matrix.one_apply, B, Matrix.of_apply, hrep, hij, hne]
  have hBrank : (B.submatrix rep id).rank = m := by
    have hdet1 : ((1 : Matrix (Fin m) (Fin m) K)).det ≠ 0 := by simp
    have := Matrix.rank_of_det_ne_zero (A := B.submatrix rep id)
      (by simpa [hBrow] using hdet1)
    simpa [Fintype.card_fin] using this
  have hBge : m ≤ B.rank := by
    have hle : (B.submatrix rep id).rank ≤ B.rank :=
      Matrix.rank_submatrix_le B rep (id : Fin m → Fin m)
    simpa [hBrank] using hle
  have hBle : B.rank ≤ m := Matrix.rank_le_width B
  have hBr : B.rank = m := le_antisymm hBle hBge
  have hA0rank : (A.submatrix id emb).rank = m := by
    rw [hA0, Matrix.rank_mul_eq_left_of_det_ne_zero C0 B hdet, hBr]
  have hAge : m ≤ A.rank := by
    have hle : (A.submatrix id emb).rank ≤ A.rank :=
      Matrix.rank_submatrix_le A (id : Fin n → Fin n) emb
    simpa [hA0rank] using hle
  have hAle : A.rank ≤ m := by
    rw [hA]
    calc (B * C).rank ≤ B.rank := Matrix.rank_mul_le_left B C
      _ = m := hBr
  have hAr : A.rank = m := le_antisymm hAle hAge
  have hgoal : (Matrix.vandermonde x).rank = vals.card := by
    simpa [A, m, vals] using hAr
  simpa [vals] using hgoal.symm.trans hrank

