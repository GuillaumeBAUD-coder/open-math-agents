import OMAStatements.S_mo_128018
import Mathlib

open Polynomial

open OMA.S_mo_128018



theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_128018.main) := by
  intro h
  let P : ℤ[X] := C 2 * X
  let Q : ℤ[X] := C 4 * X
  let D : ℤ[X] := X
  have hP : integerImage P = C (2 : ℚ) * X := by simp [integerImage, P]; rfl
  have hQ : integerImage Q = C (4 : ℚ) * X := by simp [integerImage, Q]; rfl
  have hG : monicGCD (integerImage P) (integerImage Q) X := by
    rw [hP,hQ]
    refine ⟨monic_X, ⟨C 2, mul_comm _ _⟩, ⟨C 4, mul_comm _ _⟩, ?_⟩
    intro H hH _
    apply hH.trans
    refine ⟨C (1/2 : ℚ), ?_⟩
    calc
      (X : ℚ[X]) = (C (2 : ℚ) * C (1/2 : ℚ)) * X := by
        rw [← Polynomial.C_mul]
        norm_num
      _ = C 2 * X * C (1/2 : ℚ) := by ring
  have hD : leastIntegralMultiple X D := by
    refine ⟨1, by decide, ?_, fun m hm _ => hm⟩
    simp [D, integerImage]
  let x : ℂ := 1 / 2
  have hp : complexValue P x = ((1 : ℤ) : ℂ) := by norm_num [complexValue, P, x]
  have hq : complexValue Q x = ((2 : ℤ) : ℂ) := by norm_num [complexValue, Q, x]
  obtain ⟨_, _, d, _, _, hd, _, _⟩ := h P Q D X hG hD x ⟨1,hp⟩ ⟨2,hq⟩
  have hh : (1:ℂ) / 2 = d := by simpa [complexValue, D, x] using hd
  have hi : (1:ℂ) = (d:ℂ) * 2 := (div_eq_iff (by norm_num)).mp hh
  have he : (1:ℤ) = d * 2 := by exact_mod_cast hi
  omega
