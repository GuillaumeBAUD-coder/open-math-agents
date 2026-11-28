import FormalConjectures.ErdosProblems.«1107»
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Group.GeometryOfNumbers
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic
import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-! Fixed levels for the sum of three powerful numbers, following B. Z. Moroz,
Astérisque 209 (1992), Theorems 1 and 2. Credit: @sturdy4days. -/

section
/-!
Legendre–Gauss three squares, sufficiency. The squarefree reduction, auxiliary primes, and Minkowski argument are from Kenta Kitamura, KitaKen1/lean-eval-conway-schneeberger-fifteen, Submission/ConwayFifteen.lean at commit 4fafb6bb0d8fb1129b11e348b7ede02330da8b5c. Copyright 2026 Kenta Kitamura. Used under the Apache License, Version 2.0. The source project includes benchmark scaffolding copyright 2026 Lean FRO, LLC under the same license. This extraction uses only the proof and adds the natural-number and zero cases.
-/
/- The three-square extraction was contributed by @marcusbuffett in open-math-agents #4995.
The reduction outside residue 7 is from @JaviSoto's #4744. -/

namespace PowerfulLegendre
open Matrix Finset Function
open scoped NumberTheorySymbols
theorem exists_prime_delta (m₀ : ℕ) (hm₀ : 0 < m₀) (hodd : ¬ 2 ∣ m₀)
    (δ : ℕ) (hδ : δ = 1 ∨ δ = 2) (r : ℕ) (hr : r = 1 ∨ r = 5) (N₀ : ℕ) :
    ∃ q : ℕ, q.Prime ∧ N₀ < q ∧ q % 8 = r ∧ (m₀ : ℤ) ∣ (δ : ℤ) * q + 1 := by
  have : NeZero m₀ := ⟨hm₀.ne'⟩
  have : NeZero (8 * m₀) := ⟨by positivity⟩
  have h8m : Nat.Coprime 8 m₀ := by
    have h2 : Nat.Coprime 2 m₀ := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd
    have h8 := h2.pow_left 3
    norm_num at h8
    exact h8
  have hδu : IsUnit ((δ : ℕ) : ZMod m₀) := by
    rcases hδ with h1 | h1 <;> subst h1
    · simp
    · rw [Nat.cast_ofNat]
      refine (ZMod.isUnit_iff_coprime 2 m₀).mpr ?_
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd
  have hru : IsUnit ((r : ℕ) : ZMod 8) := by
    rcases hr with h1 | h1 <;> subst h1
    · simp
    · exact ⟨⟨5, 5, by decide, by decide⟩, by rfl⟩
  set w : ZMod m₀ := -(((δ : ℕ) : ZMod m₀))⁻¹ with hw
  have hwu : IsUnit w := by
    rw [hw]
    have hmul : (-((((δ : ℕ) : ZMod m₀)))⁻¹) * (-(((δ : ℕ) : ZMod m₀))) = 1 := by
      rw [neg_mul_neg, mul_comm]
      exact ZMod.mul_inv_of_unit _ hδu
    exact ⟨⟨_, _, hmul, by rwa [mul_comm] at hmul⟩, rfl⟩
  set e2 := ZMod.chineseRemainder h8m with he2
  set α : ZMod (8 * m₀) := e2.symm (((r : ℕ) : ZMod 8), w) with hα
  have hunitα : IsUnit α := by
    refine IsUnit.map e2.symm ?_
    rw [Prod.isUnit_iff]
    exact ⟨hru, hwu⟩
  obtain ⟨q, hqgt, hqp, hqeq⟩ := Nat.forall_exists_prime_gt_and_eq_mod hunitα N₀
  have hsplit : ((q : ZMod 8), (q : ZMod m₀)) = (((r : ℕ) : ZMod 8), w) := by
    have h1 : e2 ((q : ℕ) : ZMod (8 * m₀)) = (((r : ℕ) : ZMod 8), w) := by
      rw [hqeq, hα, RingEquiv.apply_symm_apply]
    rw [map_natCast] at h1
    rw [← h1, Prod.ext_iff]
    exact ⟨(Prod.fst_natCast q).symm, (Prod.snd_natCast q).symm⟩
  have hq8 : q % 8 = r := by
    have h1 : (q : ZMod 8) = ((r : ℕ) : ZMod 8) := (Prod.mk.injEq _ _ _ _).mp hsplit |>.1
    have h2 : q % 8 = r % 8 := (ZMod.natCast_eq_natCast_iff' q r 8).mp h1
    rcases hr with h3 | h3 <;> omega
  have hqm₀ : (m₀ : ℤ) ∣ (δ : ℤ) * q + 1 := by
    have h1 : (q : ZMod m₀) = w := (Prod.mk.injEq _ _ _ _).mp hsplit |>.2
    have h2 : (((δ : ℤ) * q + 1 : ℤ) : ZMod m₀) = 0 := by
      push_cast
      rw [h1, hw]
      have := ZMod.mul_inv_of_unit _ hδu
      ring_nf
      ring_nf at this
      linear_combination -this
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ m₀).mp h2
  exact ⟨q, hqp, hqgt, hq8, hqm₀⟩

theorem jacobi_chain_odd {m : ℕ} (hm2 : m % 2 = 1)
    {δ q : ℕ} (hq4 : q % 4 = 1) (hqodd : q % 2 = 1)
    (hδcase : (δ = 1 ∧ m % 4 = 1) ∨ (δ = 2 ∧ m % 8 = 3))
    (hres : (m : ℤ) ∣ (δ : ℤ) * q + 1) :
    J((-(m : ℤ)) | q) = 1 := by
  have hoddm : Odd m := Nat.odd_iff.mpr hm2
  have hoddq : Odd q := Nat.odd_iff.mpr hqodd
  have h1 : J((-(m : ℤ)) | q) = J((-1 : ℤ) | q) * J(((m : ℕ) : ℤ) | q) := by
    rw [← jacobiSym.mul_left]
    congr 1
    ring
  have h2 : J((-1 : ℤ) | q) = 1 := by
    rw [jacobiSym.at_neg_one hoddq, ZMod.χ₄_nat_eq_if_mod_four]
    simp [hqodd, hq4]
  have h3 : J(((m : ℕ) : ℤ) | q) = J(((q : ℕ) : ℤ) | m) :=
    (jacobiSym.quadratic_reciprocity_one_mod_four hq4 hoddm).symm
  have hδm : Int.gcd ((δ : ℕ) : ℤ) m = 1 := by
    rcases hδcase with ⟨h6, _⟩ | ⟨h6, _⟩ <;> subst h6
    · simp
    · have hcop : Nat.Coprime 2 m :=
        (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (by omega)
      simpa [Int.gcd] using hcop
  have h4 : J(((δ : ℕ) : ℤ) | m) * J(((q : ℕ) : ℤ) | m) = J((-1 : ℤ) | m) := by
    rw [← jacobiSym.mul_left]
    refine jacobiSym.mod_left' ?_
    have hmodeq : (((δ : ℕ) : ℤ) * ((q : ℕ) : ℤ)) ≡ (-1 : ℤ) [ZMOD (m : ℕ)] :=
      Int.ModEq.symm (Int.modEq_iff_dvd.mpr (by
        rw [show (((δ : ℕ) : ℤ) * ((q : ℕ) : ℤ)) - (-1) = (δ : ℤ) * q + 1 by ring]
        exact hres))
    exact hmodeq
  have hsq := jacobiSym.sq_one hδm
  have h5 : J(((q : ℕ) : ℤ) | m)
      = J(((δ : ℕ) : ℤ) | m) * J((-1 : ℤ) | m) := by
    calc J(((q : ℕ) : ℤ) | m)
        = J(((δ : ℕ) : ℤ) | m) ^ 2 * J(((q : ℕ) : ℤ) | m) := by rw [hsq, one_mul]
      _ = J(((δ : ℕ) : ℤ) | m)
          * (J(((δ : ℕ) : ℤ) | m) * J(((q : ℕ) : ℤ) | m)) := by ring
      _ = J(((δ : ℕ) : ℤ) | m) * J((-1 : ℤ) | m) := by rw [h4]
  rcases hδcase with ⟨h6, hm4⟩ | ⟨h6, hm8⟩ <;> subst h6
  · have e1 : J(((1 : ℕ) : ℤ) | m) = 1 := by
      norm_num [jacobiSym.one_left]
    have e2 : J((-1 : ℤ) | m) = 1 := by
      rw [jacobiSym.at_neg_one hoddm, ZMod.χ₄_nat_eq_if_mod_four]
      simp [hm2, hm4]
    rw [h1, h2, h3, h5, e1, e2]
    norm_num
  · have hm4 : m % 4 = 3 := by omega
    have e1 : J(((2 : ℕ) : ℤ) | m) = -1 := by
      rw [show ((2 : ℕ) : ℤ) = (2 : ℤ) by norm_num,
        jacobiSym.at_two hoddm, ZMod.χ₈_nat_eq_if_mod_eight]
      simp [hm2, hm8]
    have e2 : J((-1 : ℤ) | m) = -1 := by
      rw [jacobiSym.at_neg_one hoddm, ZMod.χ₄_nat_eq_if_mod_four]
      simp [hm2, hm4]
    rw [h1, h2, h3, h5, e1, e2]
    norm_num

theorem jacobi_chain_even {m₀ : ℕ} (hm₀2 : m₀ % 2 = 1)
    {q : ℕ} (hqodd : q % 2 = 1) (hq4 : q % 4 = 1)
    (hcase : (m₀ % 4 = 1 ∧ q % 8 = 1) ∨ (m₀ % 4 = 3 ∧ q % 8 = 5))
    (hres : (m₀ : ℤ) ∣ (q : ℤ) + 1) :
    J((-((2 * m₀ : ℕ) : ℤ)) | q) = 1 := by
  have hoddm : Odd m₀ := Nat.odd_iff.mpr hm₀2
  have hoddq : Odd q := Nat.odd_iff.mpr hqodd
  have h1 : J((-((2 * m₀ : ℕ) : ℤ)) | q)
      = J((-1 : ℤ) | q) * (J((2 : ℤ) | q) * J(((m₀ : ℕ) : ℤ) | q)) := by
    rw [← jacobiSym.mul_left, ← jacobiSym.mul_left]
    congr 1
    push_cast
    ring
  have h2 : J((-1 : ℤ) | q) = 1 := by
    rw [jacobiSym.at_neg_one hoddq, ZMod.χ₄_nat_eq_if_mod_four]
    simp [hqodd, hq4]
  have h3 : J(((m₀ : ℕ) : ℤ) | q) = J(((q : ℕ) : ℤ) | m₀) :=
    (jacobiSym.quadratic_reciprocity_one_mod_four hq4 hoddm).symm
  have h4 : J(((q : ℕ) : ℤ) | m₀) = J((-1 : ℤ) | m₀) := by
    refine jacobiSym.mod_left' ?_
    have hmodeq : (((q : ℕ) : ℤ)) ≡ (-1 : ℤ) [ZMOD (m₀ : ℕ)] :=
      Int.ModEq.symm (Int.modEq_iff_dvd.mpr (by
        rw [show (((q : ℕ) : ℤ)) - (-1) = (q : ℤ) + 1 by ring]
        exact hres))
    exact hmodeq
  rcases hcase with ⟨hm4, hq8⟩ | ⟨hm4, hq8⟩
  · have e1 : J((2 : ℤ) | q) = 1 := by
      rw [jacobiSym.at_two hoddq, ZMod.χ₈_nat_eq_if_mod_eight]
      simp [hqodd, hq8]
    have e2 : J((-1 : ℤ) | m₀) = 1 := by
      rw [jacobiSym.at_neg_one hoddm, ZMod.χ₄_nat_eq_if_mod_four]
      simp [hm₀2, hm4]
    rw [h1, h2, h3, h4, e1, e2]
    norm_num
  · have e1 : J((2 : ℤ) | q) = -1 := by
      rw [jacobiSym.at_two hoddq, ZMod.χ₈_nat_eq_if_mod_eight]
      simp [hqodd, hq8]
    have e2 : J((-1 : ℤ) | m₀) = -1 := by
      rw [jacobiSym.at_neg_one hoddm, ZMod.χ₄_nat_eq_if_mod_four]
      simp [hm₀2, hm4]
    rw [h1, h2, h3, h4, e1, e2]
    norm_num

theorem exists_b_h' {m q : ℕ} [Fact q.Prime] (hqodd : q % 2 = 1)
    {δ : ℕ} (hδ : δ = 1 ∨ δ = 2) (hmδ : δ = 2 → m % 2 = 1)
    (hsq : IsSquare (-((m : ℕ) : ZMod q))) :
    ∃ b h' : ℤ, ((δ : ℤ) * q) * h' = b ^ 2 + (m : ℤ) := by
  obtain ⟨r, hr⟩ := hsq
  have hb₀ : (q : ℤ) ∣ ((r.val : ℤ)) ^ 2 + m := by
    refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp ?_
    push_cast at hr ⊢
    rw [ZMod.natCast_rightInverse r]
    linear_combination -hr
  rcases hδ with h1 | h1 <;> subst h1
  · obtain ⟨h', hh'⟩ := hb₀
    refine ⟨(r.val : ℤ), h', ?_⟩
    push_cast
    linarith [hh']
  · have hm2 := hmδ rfl
    set b : ℤ := if 2 ∣ (r.val : ℤ) then (r.val : ℤ) + q else (r.val : ℤ) with hb
    have hqb : (q : ℤ) ∣ b ^ 2 + m := by
      rw [hb]
      split_ifs with h
      · have hexp : ((r.val : ℤ) + q) ^ 2 + m
            = ((r.val : ℤ) ^ 2 + m) + (q : ℤ) * (2 * r.val + q) := by ring
        rw [hexp]
        exact dvd_add hb₀ (Dvd.intro _ rfl)
      · exact hb₀
    have hbodd : ¬ (2 : ℤ) ∣ b := by
      rw [hb]
      split_ifs with h
      · intro h2
        omega
      · exact h
    have h2b : (2 : ℤ) ∣ b ^ 2 + m := by
      obtain ⟨k, hk⟩ : ∃ k, b = 2 * k + 1 := ⟨(b - 1) / 2, by omega⟩
      obtain ⟨j, hj⟩ : ∃ j, (m : ℤ) = 2 * j + 1 := ⟨((m : ℤ) - 1) / 2, by omega⟩
      exact ⟨2 * k ^ 2 + 2 * k + j + 1, by rw [hk, hj]; ring⟩
    have hcop : IsCoprime (2 : ℤ) (q : ℤ) := by
      rw [Int.isCoprime_iff_gcd_eq_one]
      have hc : Nat.Coprime 2 q :=
        (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (by omega)
      simpa [Int.gcd] using hc
    obtain ⟨h', hh'⟩ := hcop.mul_dvd h2b hqb
    refine ⟨b, h', ?_⟩
    push_cast
    linarith [hh']

theorem exists_ankeny_data {m : ℕ} (hm : 0 < m)
    (hmod : m % 8 = 1 ∨ m % 8 = 2 ∨ m % 8 = 3 ∨ m % 8 = 5 ∨ m % 8 = 6) :
    ∃ (q : ℕ) (δ c b h' t : ℤ),
      q.Prime ∧ q % 4 = 1 ∧ (δ = 1 ∨ δ = 2) ∧ c = δ * q ∧
      c * h' = b ^ 2 + (m : ℤ) ∧ ((m : ℤ) ∣ c * t ^ 2 + 1) ∧
      IsCoprime c (m : ℤ) ∧
      (∀ p : ℕ, p.Prime → p ∣ m → p ≠ 2 → IsSquare ((-c : ℤ) : ZMod p)) := by
  by_cases hpar : m % 2 = 1
  · -- odd case
    set δN : ℕ := if m % 8 = 3 then 2 else 1 with hδN
    have hδN12 : δN = 1 ∨ δN = 2 := by rw [hδN]; split_ifs <;> simp
    obtain ⟨q, hqp, hqgt, hq8, hres⟩ :=
      exists_prime_delta m hm (by omega) δN hδN12 1 (Or.inl rfl) m
    have : Fact q.Prime := ⟨hqp⟩
    have hq4 : q % 4 = 1 := by omega
    have hqodd : q % 2 = 1 := by omega
    have hδcase : (δN = 1 ∧ m % 4 = 1) ∨ (δN = 2 ∧ m % 8 = 3) := by
      rw [hδN]
      split_ifs with h
      · exact Or.inr ⟨rfl, h⟩
      · exact Or.inl ⟨rfl, by omega⟩
    have hJ := jacobi_chain_odd hpar hq4 hqodd hδcase hres
    have hsq : IsSquare (-((m : ℕ) : ZMod q)) := by
      have hs := ZMod.isSquare_of_jacobiSym_eq_one hJ
      push_cast at hs
      exact hs
    obtain ⟨b, h', hch⟩ := exists_b_h' hqodd hδN12 (fun _ => hpar) hsq
    have hqm : Nat.Coprime q m := by
      have hd1 : (Nat.gcd q m : ℤ) ∣ (δN : ℤ) * q + 1 :=
        dvd_trans (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right q m)) hres
      have hd2 : (Nat.gcd q m : ℤ) ∣ (δN : ℤ) * q :=
        Dvd.dvd.mul_left (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left q m)) _
      have hd3 : (Nat.gcd q m : ℤ) ∣ 1 := by
        have hsub := dvd_sub hd1 hd2
        simpa using hsub
      have hd4 : (Nat.gcd q m : ℤ) = 1 :=
        Int.eq_one_of_dvd_one (by positivity) hd3
      exact_mod_cast hd4
    have hδm : Nat.Coprime δN m := by
      rcases hδN12 with h1 | h1 <;> rw [h1]
      · exact Nat.coprime_one_left m
      · exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (by omega)
    have hcm : IsCoprime ((δN : ℤ) * q) ((m : ℕ) : ℤ) := by
      rw [Int.isCoprime_iff_gcd_eq_one]
      have hcast : ((δN : ℤ) * q) = (((δN * q : ℕ)) : ℤ) := by push_cast; ring
      rw [hcast, Int.gcd_natCast_natCast]
      exact Nat.Coprime.mul_left hδm hqm
    refine ⟨q, (δN : ℤ), (δN : ℤ) * q, b, h', 1, hqp, hq4, ?_, rfl, hch, ?_, hcm, ?_⟩
    · rcases hδN12 with h1 | h1
      · exact Or.inl (by rw [h1]; norm_num)
      · exact Or.inr (by rw [h1]; norm_num)
    · rw [one_pow, mul_one]
      exact hres
    · intro p hpp hpm hp2
      have hpd : ((p : ℕ) : ℤ) ∣ (δN : ℤ) * q + 1 :=
        dvd_trans (Int.natCast_dvd_natCast.mpr hpm) hres
      have h0 : (((δN : ℤ) * q + 1 : ℤ) : ZMod p) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hpd
      refine ⟨1, ?_⟩
      push_cast at h0 ⊢
      linear_combination -h0
  · -- even case
    have hm₀odd : (m / 2) % 2 = 1 := by omega
    have hm₀pos : 0 < m / 2 := by omega
    have hm2 : m = 2 * (m / 2) := by omega
    set r : ℕ := if m % 8 = 2 then 1 else 5 with hrdef
    have hr15 : r = 1 ∨ r = 5 := by rw [hrdef]; split_ifs <;> simp
    obtain ⟨q, hqp, hqgt, hq8, hres⟩ :=
      exists_prime_delta (m / 2) hm₀pos (by omega) 1 (Or.inl rfl) r hr15 m
    have : Fact q.Prime := ⟨hqp⟩
    have hq4 : q % 4 = 1 := by rcases hr15 with h | h <;> omega
    have hqodd : q % 2 = 1 := by rcases hr15 with h | h <;> omega
    have hres' : ((m / 2 : ℕ) : ℤ) ∣ (q : ℤ) + 1 := by
      have hres2 := hres
      rw [Nat.cast_one, one_mul] at hres2
      exact hres2
    have hcase : ((m / 2) % 4 = 1 ∧ q % 8 = 1) ∨ ((m / 2) % 4 = 3 ∧ q % 8 = 5) := by
      rw [hrdef] at hq8
      split_ifs at hq8 with h
      · exact Or.inl ⟨by omega, hq8⟩
      · exact Or.inr ⟨by omega, hq8⟩
    have hJ := jacobi_chain_even hm₀odd hqodd hq4 hcase hres'
    have hJm : jacobiSym (-(m : ℤ)) q = 1 := by
      have hmcast : ((m : ℕ) : ℤ) = ((2 * (m / 2) : ℕ) : ℤ) := by
        exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) hm2
      rw [hmcast]
      exact hJ
    have hsq : IsSquare (-((m : ℕ) : ZMod q)) := by
      have hs := ZMod.isSquare_of_jacobiSym_eq_one hJm
      push_cast at hs
      exact hs
    obtain ⟨b, h', hch⟩ :=
      exists_b_h' hqodd (Or.inl rfl) (fun h => absurd h (by norm_num)) hsq
    have hmdvd : (m : ℤ) ∣ (q : ℤ) + 1 := by
      have h2d : (2 : ℤ) ∣ (q : ℤ) + 1 := by omega
      have hcop2 : IsCoprime (2 : ℤ) ((m / 2 : ℕ) : ℤ) := by
        rw [Int.isCoprime_iff_gcd_eq_one,
          show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, Int.gcd_natCast_natCast]
        exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (by omega)
      have hmul := hcop2.mul_dvd h2d hres'
      have hmcast : ((m : ℕ) : ℤ) = 2 * ((m / 2 : ℕ) : ℤ) := by
        push_cast
        omega
      rw [hmcast]
      exact hmul
    have hqm : Nat.Coprime q m := by
      have hd1 : (Nat.gcd q m : ℤ) ∣ (q : ℤ) + 1 :=
        dvd_trans (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right q m)) hmdvd
      have hd2 : (Nat.gcd q m : ℤ) ∣ (q : ℤ) :=
        Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left q m)
      have hd3 : (Nat.gcd q m : ℤ) ∣ 1 := by
        have hsub := dvd_sub hd1 hd2
        simpa using hsub
      have hd4 : (Nat.gcd q m : ℤ) = 1 :=
        Int.eq_one_of_dvd_one (by positivity) hd3
      exact_mod_cast hd4
    have hcm : IsCoprime ((1 : ℤ) * q) ((m : ℕ) : ℤ) := by
      rw [Int.isCoprime_iff_gcd_eq_one, one_mul, Int.gcd_natCast_natCast]
      exact hqm
    refine ⟨q, 1, (1 : ℤ) * q, b, h', 1, hqp, hq4, Or.inl rfl, rfl, ?_, ?_, hcm, ?_⟩
    · have hch2 := hch
      rw [Nat.cast_one] at hch2
      exact hch2
    · rw [one_pow, mul_one, one_mul]
      exact hmdvd
    · intro p hpp hpm hp2
      have hpm₀ : p ∣ m / 2 := by
        rcases (Nat.Prime.dvd_mul hpp).mp (hm2 ▸ hpm) with h | h
        · exact absurd ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp h) hp2
        · exact h
      have hpd : ((p : ℕ) : ℤ) ∣ (q : ℤ) + 1 :=
        dvd_trans (Int.natCast_dvd_natCast.mpr hpm₀) hres'
      have h0 : (((q : ℤ) + 1 : ℤ) : ZMod p) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hpd
      refine ⟨1, ?_⟩
      push_cast at h0 ⊢
      linear_combination -h0
private lemma gamma_five_half : Real.Gamma ((3 : ℝ) / 2 + 1) = 3 / 4 * Real.sqrt Real.pi := by
  rw [Real.Gamma_add_one (by norm_num), show ((3 : ℝ) / 2) = 1 / 2 + 1 by norm_num,
    Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]
  ring

private lemma sqrt_pi_pos : 0 < Real.sqrt Real.pi :=
  Real.sqrt_pos.mpr Real.pi_pos

private lemma volume_const_gt {m : ℝ} (hm : 0 < m) :
    8 * (m * Real.sqrt m)
      < Real.sqrt (2 * m) ^ 3
        * (Real.sqrt Real.pi ^ 3 / Real.Gamma ((3 : ℝ) / 2 + 1)) := by
  have hsm : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm
  have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsπ := sqrt_pi_pos
  have h2m : Real.sqrt (2 * m) = Real.sqrt 2 * Real.sqrt m :=
    Real.sqrt_mul (by norm_num) m
  have hmm : Real.sqrt m * Real.sqrt m = m := Real.mul_self_sqrt hm.le
  have h22 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hππ : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi :=
    Real.mul_self_sqrt Real.pi_pos.le
  have hπ3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hs21 : (1 : ℝ) < Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hgam : Real.sqrt Real.pi ^ 3 / (3 / 4 * Real.sqrt Real.pi)
      = 4 / 3 * Real.pi := by
    rw [div_eq_iff (by positivity)]
    linear_combination Real.sqrt Real.pi * hππ
  have hcube : (Real.sqrt 2 * Real.sqrt m) ^ 3
      = 2 * Real.sqrt 2 * (m * Real.sqrt m) := by
    linear_combination (Real.sqrt 2 * Real.sqrt m ^ 3) * h22
      + (2 * Real.sqrt 2 * Real.sqrt m) * hmm
  rw [gamma_five_half, h2m, hgam, hcube,
    show 2 * Real.sqrt 2 * (m * Real.sqrt m) * (4 / 3 * Real.pi)
      = 2 * Real.sqrt 2 * (4 / 3 * Real.pi) * (m * Real.sqrt m) by ring]
  refine mul_lt_mul_of_pos_right ?_ (mul_pos hm hsm)
  nlinarith [hπ3, hs21, hs2]
open MeasureTheory in
set_option maxHeartbeats 2000000 in
theorem geometry : ∀ m c b h' t : ℤ, 0 < m → 0 < c → c * h' = b ^ 2 + m →
    ∃ x y z : ℤ, ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧
      (t*(c*x+b*y)+m*z)^2+(c*x^2+2*b*x*y+h'*y^2)<2*m := by
  let formR (m c b t x y z : ℤ) : ℤ := t * (c * x + b * y) + m * z

  let formPsi (c b h' x y : ℤ) : ℤ := c * x ^ 2 + 2 * b * x * y + h' * y ^ 2

  let formQ (m c b h' t x y z : ℤ) : ℤ :=
    formR m c b t x y z ^ 2 + formPsi c b h' x y
  let matM (m c b t : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
    !![t * c, t * b, m;
       Real.sqrt c, b / Real.sqrt c, 0;
       0, Real.sqrt (m / c), 0]

  have matM_entries (m c b t : ℝ) (w : Fin 3 → ℝ) :
      (matM m c b t).mulVec w 0 = t * c * w 0 + t * b * w 1 + m * w 2
      ∧ (matM m c b t).mulVec w 1
          = Real.sqrt c * w 0 + b / Real.sqrt c * w 1
      ∧ (matM m c b t).mulVec w 2 = Real.sqrt (m / c) * w 1 := by
    refine ⟨?_, ?_, ?_⟩ <;>
      simp [matM, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

  have matM_det {m c b t : ℝ} (hc : 0 < c) :
      (matM m c b t).det = m * Real.sqrt m := by
    have h1 : Real.sqrt c * Real.sqrt (m / c) = Real.sqrt m := by
      rw [← Real.sqrt_mul hc.le, mul_div_cancel₀ _ hc.ne']
    dsimp only [matM]
    rw [Matrix.det_fin_three]
    simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_fin_const,
      Matrix.cons_val_fin_one, Matrix.of_apply]
    linear_combination m * h1

  have matM_normsq {m c b h' t : ℝ} (hm : 0 < m) (hc : 0 < c)
      (hch : c * h' = b ^ 2 + m) (w : Fin 3 → ℝ) :
      ((matM m c b t).mulVec w 0) ^ 2 + ((matM m c b t).mulVec w 1) ^ 2
        + ((matM m c b t).mulVec w 2) ^ 2
        = (t * (c * w 0 + b * w 1) + m * w 2) ^ 2
          + (c * w 0 ^ 2 + 2 * b * w 0 * w 1 + h' * w 1 ^ 2) := by
    obtain ⟨e0, e1, e2⟩ := matM_entries m c b t w
    rw [e0, e1, e2]
    set sc : ℝ := Real.sqrt c with hscdef
    set u : ℝ := Real.sqrt (m / c) with hudef
    have hscpos : 0 < sc := Real.sqrt_pos.mpr hc
    have hscne : sc ≠ 0 := hscpos.ne'
    have hsc : sc * sc = c := Real.mul_self_sqrt hc.le
    have hu : u * u * c = m := by
      rw [hudef, Real.mul_self_sqrt (by positivity)]
      exact div_mul_cancel₀ m hc.ne'
    have hbs : b / sc = b * sc / c := by
      rw [div_eq_div_iff hscne hc.ne']
      linear_combination (-b) * hsc
    rw [hbs]
    field_simp
    ring_nf
    linear_combination (w 1 ^ 2 * c) * hu + ((c * w 0 + b * w 1) ^ 2) * hsc
      + (-(c * w 1 ^ 2)) * hch
  have exists_int_point {m c b h' t : ℝ} (hm : 0 < m) (hc : 0 < c)
      (hch : c * h' = b ^ 2 + m) :
      ∃ n : Fin 3 → ℤ, ¬(n 0 = 0 ∧ n 1 = 0 ∧ n 2 = 0) ∧
        (t * (c * (n 0 : ℝ) + b * (n 1 : ℝ)) + m * (n 2 : ℝ)) ^ 2
          + (c * (n 0 : ℝ) ^ 2 + 2 * b * (n 0 : ℝ) * (n 1 : ℝ)
              + h' * (n 1 : ℝ) ^ 2) < 2 * m := by
    classical
    have hsqm : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm
    have h2m : (0 : ℝ) < 2 * m := by linarith
    have hrpos : (0 : ℝ) < Real.sqrt (2 * m) := Real.sqrt_pos.mpr h2m
    have hdet : LinearMap.det (Matrix.toLin' (matM m c b t)) = m * Real.sqrt m := by
      rw [LinearMap.det_toLin']
      exact matM_det hc
    have hdetpos : (0 : ℝ) < m * Real.sqrt m := mul_pos hm hsqm
    have hdetne : LinearMap.det (Matrix.toLin' (matM m c b t)) ≠ 0 := by
      rw [hdet]
      exact hdetpos.ne'
    have hs₀ball : {v : Fin 3 → ℝ | v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 < 2 * m}
        = (WithLp.toLp 2 : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)) ⁻¹'
            Metric.ball 0 (Real.sqrt (2 * m)) := by
      ext v
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, Metric.mem_ball, dist_zero_right]
      rw [EuclideanSpace.norm_eq]
      have hcoords : ∀ i : Fin 3,
          ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin 3)) i‖ = |v i| := fun i => rfl
      simp only [hcoords, Fin.sum_univ_three, sq_abs]
      rw [Real.sqrt_lt_sqrt_iff (by positivity)]
    have hs₀vol : volume {v : Fin 3 → ℝ | v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 < 2 * m}
        = volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) (Real.sqrt (2 * m))) := by
      rw [hs₀ball]
      exact (PiLp.volume_preserving_toLp (Fin 3)).measure_preimage
        measurableSet_ball.nullMeasurableSet
    have hs₀conv : Convex ℝ {v : Fin 3 → ℝ | v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 < 2 * m} := by
      rw [hs₀ball]
      exact Convex.linear_preimage
        (f := (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).symm.toLinearMap)
        (convex_ball 0 _)
    set S : Set (Fin 3 → ℝ) :=
      ⇑(Matrix.toLin' (matM m c b t)) ⁻¹'
        {v : Fin 3 → ℝ | v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 < 2 * m} with hSdef
    have hSconv : Convex ℝ S :=
      Convex.linear_preimage hs₀conv (Matrix.toLin' (matM m c b t))
    have hSsymm : ∀ x ∈ S, -x ∈ S := by
      intro x hx
      simp only [hSdef, Set.mem_preimage, map_neg, Set.mem_ofPred_eq, Pi.neg_apply,
        neg_sq] at hx ⊢
      exact hx
    have hSvol : volume S
        = ENNReal.ofReal ((m * Real.sqrt m)⁻¹)
          * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) (Real.sqrt (2 * m))) := by
      rw [hSdef, Measure.addHaar_preimage_linearMap volume hdetne, hdet,
        hs₀vol, abs_of_pos (inv_pos.mpr hdetpos)]
    have hfund := ZSpan.isAddFundamentalDomain' (Pi.basisFun ℝ (Fin 3)) volume
    have hvolF : volume (ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin 3))) = 1 := by
      rw [ZSpan.volume_fundamentalDomain]
      have hone : (Matrix.of ⇑(Pi.basisFun ℝ (Fin 3)))
          = (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
        ext i j
        simp [Pi.basisFun_apply, Pi.single_apply, Matrix.one_apply, eq_comm]
      rw [hone, Matrix.det_one]
      simp
    have hballvol : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 3))
          (Real.sqrt (2 * m)))
        = ENNReal.ofReal (Real.sqrt (2 * m) ^ 3
            * (Real.sqrt Real.pi ^ 3 / Real.Gamma ((3 : ℝ) / 2 + 1))) := by
      rw [EuclideanSpace.volume_ball]
      rw [← ENNReal.ofReal_pow hrpos.le, ← ENNReal.ofReal_mul (by positivity)]
      norm_num [Fintype.card_fin]
    have hineq : volume (ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin 3)))
        * 2 ^ Module.finrank ℝ (Fin 3 → ℝ) < volume S := by
      rw [hvolF, one_mul, hSvol, hballvol, ← ENNReal.ofReal_mul (by positivity)]
      have hrank : Module.finrank ℝ (Fin 3 → ℝ) = 3 := by
        simp
      rw [hrank, show ((2 : ENNReal) ^ 3) = ENNReal.ofReal 8 by
        rw [show (8 : ℝ) = 2 ^ 3 by norm_num, ENNReal.ofReal_pow (by norm_num)]
        norm_num]
      rw [ENNReal.ofReal_lt_ofReal_iff (by positivity)]
      have hkey := volume_const_gt hm
      rw [lt_inv_mul_iff₀ hdetpos]
      linarith
    have : Countable
        ↥(Submodule.span ℤ (Set.range ⇑(Pi.basisFun ℝ (Fin 3)))).toAddSubgroup :=
      (inferInstance :
        Countable ↥(Submodule.span ℤ (Set.range ⇑(Pi.basisFun ℝ (Fin 3)))))
    obtain ⟨x, hx0, hxS⟩ :=
      exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
        hfund hSsymm hSconv hineq
    have hxmem : (x : Fin 3 → ℝ)
        ∈ Submodule.span ℤ (Set.range ⇑(Pi.basisFun ℝ (Fin 3))) := by
      have := x.2
      rwa [Submodule.mem_toAddSubgroup] at this
    obtain ⟨n, hn⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hxmem
    have hxfun : ∀ j, (x : Fin 3 → ℝ) j = (n j : ℝ) := by
      intro j
      rw [← hn]
      simp [Pi.basisFun_apply, Pi.single_apply, zsmul_eq_mul]
    refine ⟨n, ?_, ?_⟩
    · rintro ⟨h0, h1, h2⟩
      apply hx0
      have hcoe : (x : Fin 3 → ℝ) = 0 := by
        funext j
        rw [hxfun j]
        fin_cases j <;> simp [h0, h1, h2]
      exact (ZeroMemClass.coe_eq_zero).mp hcoe
    · have hxS' := hxS
      rw [hSdef, Set.mem_preimage, Matrix.toLin'_apply, Set.mem_ofPred_eq] at hxS'
      rw [matM_normsq hm hc hch] at hxS'
      rw [hxfun 0, hxfun 1, hxfun 2] at hxS'
      exact hxS'
  intro m c b h' t hm hc hch
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hcR : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  have hchR : (c : ℝ) * (h' : ℝ) = (b : ℝ) ^ 2 + (m : ℝ) := by exact_mod_cast hch
  obtain ⟨n, hn0, hnlt⟩ := exists_int_point (t := (t : ℝ)) hmR hcR hchR
  refine ⟨n 0, n 1, n 2, hn0, ?_⟩
  have hcast : ((formQ m c b h' t (n 0) (n 1) (n 2) : ℤ) : ℝ)
      < (((2 : ℤ) * m : ℤ) : ℝ) := by
    unfold formQ formR formPsi
    push_cast
    ring_nf
    ring_nf at hnlt
    linarith
  exact_mod_cast hcast

set_option maxHeartbeats 2000000 in
theorem sum_of_geometry (point : ∀ m c b h' t : ℤ, 0 < m → 0 < c → c * h' = b ^ 2 + m →
    ∃ x y z : ℤ, ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧
      (t*(c*x+b*y)+m*z)^2+(c*x^2+2*b*x*y+h'*y^2)<2*m) :
    ∀ n : ℕ, 0 < n → (∀ a b : ℕ, n ≠ 4 ^ a * (8 * b + 7)) →
     ∃ x y z : ℤ, x^2+y^2+z^2=(n:ℤ) := by
  let IsSum3Sq (n : ℤ) : Prop := ∃ x y z : ℤ, x ^ 2 + y ^ 2 + z ^ 2 = n

  have mul_square {n : ℤ} (k : ℤ) (h : IsSum3Sq n) :
      IsSum3Sq (k ^ 2 * n) := by
    obtain ⟨x, y, z, hxyz⟩ := h
    exact ⟨k * x, k * y, k * z, by linear_combination (k ^ 2) * hxyz⟩

  have odd_sq_mod8 {k : ℕ} (hk : ¬ 2 ∣ k) : k ^ 2 % 8 = 1 := by
    obtain ⟨j, hj⟩ : ∃ j, k = 2 * j + 1 := ⟨k / 2, by omega⟩
    obtain ⟨t, ht⟩ : ∃ t, j * (j + 1) = 2 * t := (Nat.even_mul_succ_self j).exists_two_nsmul _
    have : k ^ 2 = 8 * t + 1 := by subst hj; ring_nf; nlinarith [ht]
    omega

  have isSum3Sq_of_core
      (core : ∀ m : ℕ, Squarefree m →
        (m % 8 = 1 ∨ m % 8 = 2 ∨ m % 8 = 3 ∨ m % 8 = 5 ∨ m % 8 = 6) →
        IsSum3Sq (m : ℤ)) :
      ∀ n : ℕ, 0 < n → (∀ a b : ℕ, n ≠ 4 ^ a * (8 * b + 7)) →
        IsSum3Sq (n : ℤ) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n IH =>
      intro hn hform
      by_cases h4 : 4 ∣ n
      · obtain ⟨m, rfl⟩ := h4
        have hm : IsSum3Sq (m : ℤ) :=
          IH m (by omega) (by omega)
            (fun a b hab => hform (a + 1) b (by rw [hab]; ring))
        obtain ⟨x, y, z, hxyz⟩ := hm
        exact ⟨2 * x, 2 * y, 2 * z, by push_cast; linear_combination (4 : ℤ) * hxyz⟩
      · by_cases h8 : n % 8 = 7
        · exact absurd (by omega : n = 4 ^ 0 * (8 * (n / 8) + 7))
            (hform 0 (n / 8))
        · -- strip the square part
          obtain ⟨m, k, hmk, hsf⟩ := Nat.sq_mul_squarefree n
          have hk2 : ¬ 2 ∣ k := by
            intro ⟨j, hj⟩
            exact h4 ⟨j ^ 2 * m, by subst hj; rw [← hmk]; ring⟩
          have hkodd : k ^ 2 % 8 = 1 := odd_sq_mod8 hk2
          have hmmod : m % 8 = n % 8 := by
            have h1 : n % 8 = k ^ 2 % 8 * (m % 8) % 8 := by
              rw [← Nat.mul_mod, hmk]
            rw [hkodd, one_mul] at h1
            omega
          have hcore : IsSum3Sq (m : ℤ) := by
            refine core m hsf ?_
            have hmod4 : ¬ n % 4 = 0 := fun hc => h4 (Nat.dvd_of_mod_eq_zero hc)
            omega
          have := mul_square (k : ℤ) hcore
          rwa [show ((k : ℤ)) ^ 2 * (m : ℤ) = ((n : ℕ) : ℤ) by
            rw [← hmk]; push_cast; ring] at this
  let formR (m c b t x y z : ℤ) : ℤ := t * (c * x + b * y) + m * z

  let formPsi (c b h' x y : ℤ) : ℤ := c * x ^ 2 + 2 * b * x * y + h' * y ^ 2

  let formQ (m c b h' t x y z : ℤ) : ℤ :=
    formR m c b t x y z ^ 2 + formPsi c b h' x y
  have c_mul_formPsi {m c b h' : ℤ} (hch : c * h' = b ^ 2 + m) (x y : ℤ) :
      c * formPsi c b h' x y = (c * x + b * y) ^ 2 + m * y ^ 2 := by
    unfold formPsi
    linear_combination y ^ 2 * hch

  have formPsi_nonneg {m c b h' : ℤ} (hc : 0 < c) (hm : 0 < m)
      (hch : c * h' = b ^ 2 + m) (x y : ℤ) : 0 ≤ formPsi c b h' x y := by
    have h := c_mul_formPsi hch x y
    nlinarith [sq_nonneg (c * x + b * y), sq_nonneg y]

  have formPsi_pos {m c b h' : ℤ} (hc : 0 < c) (hm : 0 < m)
      (hch : c * h' = b ^ 2 + m) {x y : ℤ} (hxy : x ≠ 0 ∨ y ≠ 0) :
      0 < formPsi c b h' x y := by
    have h := c_mul_formPsi hch x y
    by_cases hy : y = 0
    · subst hy
      have hx : x ≠ 0 := by
        rcases hxy with h' | h'
        · exact h'
        · exact absurd rfl h'
      have hcx : c * x ≠ 0 := mul_ne_zero hc.ne' hx
      have h2 : 0 < (c * x) ^ 2 := by
        rcases lt_or_gt_of_ne hcx with h' | h' <;> nlinarith
      nlinarith [h]
    · have hy2 : 0 < y ^ 2 := by
        rcases lt_or_gt_of_ne hy with h' | h' <;> nlinarith
      nlinarith [h, sq_nonneg (c * x + b * y), mul_pos hm hy2]

  have formQ_pos {m c b h' t : ℤ} (hc : 0 < c) (hm : 0 < m)
      (hch : c * h' = b ^ 2 + m) {x y z : ℤ}
      (hxyz : ¬(x = 0 ∧ y = 0 ∧ z = 0)) :
      0 < formQ m c b h' t x y z := by
    by_cases hxy : x = 0 ∧ y = 0
    · obtain ⟨rfl, rfl⟩ := hxy
      have hz : z ≠ 0 := fun hz => hxyz ⟨rfl, rfl, hz⟩
      have hQ : formQ m c b h' t 0 0 z = (m * z) ^ 2 := by
        unfold formQ formR formPsi
        ring
      rw [hQ]
      have hmz : m * z ≠ 0 := mul_ne_zero hm.ne' hz
      rcases lt_or_gt_of_ne hmz with h' | h' <;> nlinarith
    · have hxy' : x ≠ 0 ∨ y ≠ 0 := by tauto
      have h1 := formPsi_pos hc hm hch hxy'
      have h2 := sq_nonneg (formR m c b t x y z)
      unfold formQ
      linarith

  have m_dvd_formQ {m c b h' t : ℤ} (hch : c * h' = b ^ 2 + m)
      (hmt : m ∣ c * t ^ 2 + 1) (hcm : IsCoprime c m) (x y z : ℤ) :
      m ∣ formQ m c b h' t x y z := by
    obtain ⟨k, hk⟩ := hmt
    have hdvd : m ∣ c * formQ m c b h' t x y z := by
      refine ⟨k * (c * x + b * y) ^ 2 + 2 * c * t * (c * x + b * y) * z
        + c * m * z ^ 2 + y ^ 2, ?_⟩
      unfold formQ formR formPsi
      linear_combination ((c * x + b * y) ^ 2) * hk + y ^ 2 * hch
    exact hcm.symm.dvd_of_dvd_mul_left hdvd

  have eq_of_dvd_of_lt_two_mul {m v : ℤ} (hm : 0 < m) (hv : m ∣ v)
      (h0 : 0 < v) (h2 : v < 2 * m) : v = m := by
    obtain ⟨k, rfl⟩ := hv
    have h1 : 1 ≤ k := by nlinarith
    have hk2 : k < 2 := by nlinarith
    have hk : k = 1 := by omega
    rw [hk, mul_one]

  have formQ_eq_m {m c b h' t : ℤ} (hc : 0 < c) (hm : 0 < m)
      (hch : c * h' = b ^ 2 + m) (hmt : m ∣ c * t ^ 2 + 1) (hcm : IsCoprime c m)
      {x y z : ℤ} (hne : ¬(x = 0 ∧ y = 0 ∧ z = 0))
      (hlt : formQ m c b h' t x y z < 2 * m) :
      formQ m c b h' t x y z = m :=
    eq_of_dvd_of_lt_two_mul hm (m_dvd_formQ hch hmt hcm x y z)
      (formQ_pos hc hm hch hne) hlt

  have even_padicValNat_of_not_isSquare {p m : ℕ} [hp : Fact p.Prime]
      (hns : ¬ IsSquare (-(m : ZMod p))) :
      ∀ N a b : ℕ, N = a ^ 2 + m * b ^ 2 → N ≠ 0 → Even (padicValNat p N) := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N IH =>
      intro a b hN hN0
      by_cases hpN : p ∣ N
      · have hpb : p ∣ b := by
          by_contra hpb
          apply hns
          have hb0 : (b : ZMod p) ≠ 0 := fun hb0 =>
            hpb ((CharP.cast_eq_zero_iff (ZMod p) p b).mp hb0)
          have hzero : ((a : ZMod p)) ^ 2 + (m : ZMod p) * ((b : ZMod p)) ^ 2 = 0 := by
            have h1 : ((N : ℕ) : ZMod p) = 0 := (CharP.cast_eq_zero_iff _ p N).mpr hpN
            rw [hN] at h1
            push_cast at h1
            exact h1
          refine ⟨(a : ZMod p) * ((b : ZMod p))⁻¹, ?_⟩
          field_simp
          linear_combination -hzero
        have hpa : p ∣ a := by
          have hmb : p ∣ m * b ^ 2 := Dvd.dvd.mul_left (dvd_pow hpb two_ne_zero) m
          have ha2 : p ∣ a ^ 2 := by
            have hsub := Nat.dvd_sub hpN hmb
            have heq : N - m * b ^ 2 = a ^ 2 := by omega
            rwa [heq] at hsub
          exact hp.out.dvd_of_dvd_pow ha2
        obtain ⟨a', rfl⟩ := hpa
        obtain ⟨b', rfl⟩ := hpb
        have hNfac : N = p ^ 2 * (a' ^ 2 + m * b' ^ 2) := by rw [hN]; ring
        have hN'0 : a' ^ 2 + m * b' ^ 2 ≠ 0 := by
          intro h0
          rw [h0, mul_zero] at hNfac
          exact hN0 hNfac
        have hplt : 2 ≤ p := hp.out.two_le
        have hlt : a' ^ 2 + m * b' ^ 2 < N := by
          have h1 : 0 < a' ^ 2 + m * b' ^ 2 := Nat.pos_of_ne_zero hN'0
          have hp4 : 4 ≤ p ^ 2 := by nlinarith
          nlinarith [hNfac, h1, hp4]
        have hp2 : p ^ 2 ≠ 0 := pow_ne_zero 2 hp.out.pos.ne'
        have hval : padicValNat p N
            = 2 + padicValNat p (a' ^ 2 + m * b' ^ 2) := by
          rw [hNfac, padicValNat.mul hp2 hN'0, padicValNat.prime_pow]
        rw [hval]
        exact Even.add ⟨1, rfl⟩ (IH _ hlt a' b' rfl hN'0)
      · rw [padicValNat.eq_zero_of_not_dvd hpN]
        exact Even.zero

  have core_of_minkowski_point
      {m : ℕ} (hm : 0 < m) (hsf : Squarefree m)
      {q : ℕ} (hq : q.Prime) (hq4 : q % 4 = 1)
      {δ c b h' t : ℤ} (hδ : δ = 1 ∨ δ = 2) (hcδ : c = δ * q)
      (hch : c * h' = b ^ 2 + (m : ℤ))
      (hmt : (m : ℤ) ∣ c * t ^ 2 + 1)
      (hcm : IsCoprime c (m : ℤ))
      (hC1 : ∀ p : ℕ, p.Prime → p ∣ m → p ≠ 2 → IsSquare ((-c : ℤ) : ZMod p))
      {x y z : ℤ} (hne : ¬(x = 0 ∧ y = 0 ∧ z = 0))
      (hlt : formQ (m : ℤ) c b h' t x y z < 2 * m) :
      IsSum3Sq (m : ℤ) := by
    have hqZ : (0 : ℤ) < (q : ℤ) := by exact_mod_cast hq.pos
    have hc : 0 < c := by
      rcases hδ with h1 | h1 <;> rw [hcδ, h1] <;> linarith
    have hmZ : (0 : ℤ) < (m : ℤ) := by exact_mod_cast hm
    have hQm := formQ_eq_m hc hmZ hch hmt hcm hne hlt
    have hcpsi := c_mul_formPsi hch x y
    have hv0 : 0 ≤ formPsi c b h' x y := formPsi_nonneg hc hmZ hch x y
    set v : ℤ := formPsi c b h' x y with hvd
    set R₁ : ℤ := formR (m : ℤ) c b t x y z with hRd
    have hv : R₁ ^ 2 + v = (m : ℤ) := by rw [hRd, hvd]; exact hQm
    have hVv : ((v.toNat : ℕ) : ℤ) = v := Int.toNat_of_nonneg hv0
    have h2sq : ∃ X Y : ℕ, v.toNat = X ^ 2 + Y ^ 2 := by
      rw [Nat.eq_sq_add_sq_iff]
      intro p hpmem hp43
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors hpmem
      have : Fact p.Prime := ⟨hpp⟩
      have hpV : p ∣ v.toNat := Nat.dvd_of_mem_primeFactors hpmem
      have hV0 : v.toNat ≠ 0 := (Nat.mem_primeFactors.mp hpmem).2.2
      have hp2 : p ≠ 2 := by omega
      have hpq : p ≠ q := by intro h; rw [h] at hp43; omega
      have hppZ : Prime ((p : ℕ) : ℤ) := Nat.prime_iff_prime_int.mp hpp
      have hpvZ : ((p : ℕ) : ℤ) ∣ v := by
        have h := Int.natCast_dvd_natCast.mpr hpV
        rwa [hVv] at h
      have hpc : ¬ ((p : ℕ) : ℤ) ∣ c := by
        rw [hcδ]
        intro hdvd
        rcases hppZ.dvd_mul.mp hdvd with hdδ | hdq
        · rcases hδ with h1 | h1 <;> rw [h1] at hdδ
          · exact hppZ.not_isUnit (isUnit_of_dvd_one hdδ)
          · have h2' : p ∣ 2 := by exact_mod_cast hdδ
            exact hp2 ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp h2')
        · have hq' : p ∣ q := by exact_mod_cast hdq
          exact hpq ((Nat.prime_dvd_prime_iff_eq hpp hq).mp hq')
      have hpcZ : ((c : ℤ) : ZMod p) ≠ 0 := by
        intro h0
        exact hpc ((ZMod.intCast_zmod_eq_zero_iff_dvd c p).mp h0)
      by_cases hpm : p ∣ m
      · -- impossible branch
        exfalso
        have hpmZ : ((p : ℕ) : ℤ) ∣ (m : ℤ) := Int.natCast_dvd_natCast.mpr hpm
        have hpR : ((p : ℕ) : ℤ) ∣ R₁ := by
          refine hppZ.dvd_of_dvd_pow (n := 2) ?_
          have hRe : R₁ ^ 2 = (m : ℤ) - v := by rw [← hv]; ring
          rw [hRe]
          exact dvd_sub hpmZ hpvZ
        have hpA : ((p : ℕ) : ℤ) ∣ (c * x + b * y) := by
          refine hppZ.dvd_of_dvd_pow (n := 2) ?_
          have hAe : (c * x + b * y) ^ 2 = c * v - (m : ℤ) * y ^ 2 := by
            rw [hvd, hcpsi]; ring
          rw [hAe]
          exact dvd_sub (Dvd.dvd.mul_left hpvZ c) (Dvd.dvd.mul_right hpmZ (y ^ 2))
        obtain ⟨m₁, hm₁⟩ := hpm
        have hpm₁ : ¬ p ∣ m₁ := by
          rintro ⟨k, hk⟩
          have hu := Nat.isUnit_iff.mp (hsf p ⟨k, by rw [hm₁, hk]; ring⟩)
          have h2le := hpp.two_le
          omega
        obtain ⟨R', hR'⟩ := hpR
        obtain ⟨A', hA'⟩ := hpA
        have hmZcast : (m : ℤ) = ((p : ℕ) : ℤ) * ((m₁ : ℕ) : ℤ) := by
          exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) hm₁
        have hpne : ((p : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hpp.pos.ne'
        have hcancel : (c - y ^ 2) * ((m₁ : ℕ) : ℤ)
            = ((p : ℕ) : ℤ) * (c * R' ^ 2 + A' ^ 2) := by
          refine mul_left_cancel₀ hpne ?_
          linear_combination (-c) * hv + hcpsi + (c * (R₁ + ((p : ℕ) : ℤ) * R')) * hR'
            + ((c * x + b * y) + ((p : ℕ) : ℤ) * A') * hA'
            + (-(c - y ^ 2)) * hmZcast
        have hdvd2 : ((p : ℕ) : ℤ) ∣ (c - y ^ 2) := by
          rcases hppZ.dvd_mul.mp ⟨c * R' ^ 2 + A' ^ 2, hcancel⟩ with h | h
          · exact h
          · exact absurd (Int.natCast_dvd_natCast.mp h) hpm₁
        have hsqc : IsSquare ((c : ℤ) : ZMod p) := by
          have h0 : ((c - y ^ 2 : ℤ) : ZMod p) = 0 :=
            (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hdvd2
          push_cast at h0
          exact ⟨((y : ℤ) : ZMod p), by linear_combination h0⟩
        have hsqnc : IsSquare ((-c : ℤ) : ZMod p) := hC1 p hpp ⟨m₁, hm₁⟩ hp2
        have hsqneg : IsSquare (-1 : ZMod p) := by
          have hmul := hsqnc.mul hsqc.inv
          have he : ((-c : ℤ) : ZMod p) * ((c : ℤ) : ZMod p)⁻¹ = -1 := by
            push_cast
            field_simp
          rwa [he] at hmul
        rw [ZMod.exists_sq_eq_neg_one_iff] at hsqneg
        exact hsqneg hp43
      · -- descent branch
        have hmp0 : ((m : ℕ) : ZMod p) ≠ 0 := by
          intro h0
          exact hpm ((CharP.cast_eq_zero_iff (ZMod p) p m).mp h0)
        have hnsm : ¬ IsSquare (-((m : ℕ)) : ZMod p) := by
          intro hsq
          have hsqm : IsSquare ((m : ℕ) : ZMod p) := by
            have hveq : ((v : ℤ) : ZMod p) = 0 :=
              (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hpvZ
            have hcast := congrArg (fun w : ℤ => (w : ZMod p)) hv
            push_cast at hcast
            rw [hveq] at hcast  -- placeholder; fixed below if needed
            exact ⟨((R₁ : ℤ) : ZMod p), by linear_combination -hcast⟩
          have hone : IsSquare (-1 : ZMod p) := by
            have hmul := hsq.mul hsqm.inv
            have he : (-((m : ℕ)) : ZMod p) * ((m : ℕ) : ZMod p)⁻¹ = -1 := by
              field_simp
            rwa [he] at hmul
          rw [ZMod.exists_sq_eq_neg_one_iff] at hone
          exact hone hp43
        -- ℕ-side equation `c·v = A² + m·y²`
        have hcN : ((c.natAbs : ℕ) : ℤ) = c := Int.natAbs_of_nonneg hc.le
        have hEqN : c.natAbs * v.toNat
            = (c * x + b * y).natAbs ^ 2 + m * y.natAbs ^ 2 := by
          have hcast : ((c.natAbs * v.toNat : ℕ) : ℤ)
              = (((c * x + b * y).natAbs ^ 2 + m * y.natAbs ^ 2 : ℕ) : ℤ) := by
            push_cast
            rw [abs_of_nonneg hc.le, sq_abs, sq_abs, hVv]
            linarith [hcpsi]
          exact_mod_cast hcast
        have hcabs0 : c.natAbs ≠ 0 := by
          intro h0
          rw [Int.natAbs_eq_zero] at h0
          exact hc.ne' h0
        have hprod0 : c.natAbs * v.toNat ≠ 0 := Nat.mul_ne_zero hcabs0 hV0
        have heven := even_padicValNat_of_not_isSquare hnsm
          (c.natAbs * v.toNat) (c * x + b * y).natAbs y.natAbs hEqN hprod0
        have hpcabs : ¬ p ∣ c.natAbs := by
          intro hdvd
          exact hpc (Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr hdvd))
        rw [padicValNat.mul hcabs0 hV0,
          padicValNat.eq_zero_of_not_dvd hpcabs, zero_add] at heven
        exact heven
    obtain ⟨X, Y, hXY⟩ := h2sq
    refine ⟨R₁, X, Y, ?_⟩
    have hvXY : v = (X : ℤ) ^ 2 + (Y : ℤ) ^ 2 := by
      rw [← hVv]
      exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) hXY
    linarith [hv, hvXY]
  let MinkowskiPoint : Prop :=
    ∀ m c b h' t : ℤ, 0 < m → 0 < c → c * h' = b ^ 2 + m →
      ∃ x y z : ℤ, ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧ formQ m c b h' t x y z < 2 * m

  have isSum3Sq_of_minkowskiPoint (W3 : MinkowskiPoint) :
      ∀ n : ℕ, 0 < n → (∀ a b : ℕ, n ≠ 4 ^ a * (8 * b + 7)) →
        IsSum3Sq (n : ℤ) := by
    refine isSum3Sq_of_core ?_
    intro m hsf hmod
    have hm : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; omega)
    obtain ⟨q, δ, c, b, h', t, hqp, hq4, hδ, hcδ, hch, hmt, hcm, hC1⟩ :=
      exists_ankeny_data hm hmod
    have hqZ : (0 : ℤ) < (q : ℤ) := by exact_mod_cast hqp.pos
    have hc : 0 < c := by
      rcases hδ with h1 | h1 <;> rw [hcδ, h1] <;> linarith
    obtain ⟨x, y, z, hne, hlt⟩ :=
      W3 ((m : ℕ) : ℤ) c b h' t (by exact_mod_cast hm) hc hch
    exact core_of_minkowski_point hm hsf hqp hq4 hδ hcδ hch hmt hcm hC1 hne hlt
  exact isSum3Sq_of_minkowskiPoint point

theorem natural940 (n : ℕ) (h : ∀ a b : ℕ, n ≠ 4 ^ a * (8 * b + 7)) :
    ∃ x y z : ℕ, n = x^2 + y^2 + z^2 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨0,0,0,by decide⟩
  obtain ⟨x,y,z,he⟩ := sum_of_geometry geometry n hn h
  refine ⟨x.natAbs,y.natAbs,z.natAbs,?_⟩
  zify [Int.natCast_natAbs, sq_abs]
  exact he.symm

lemma sq_full (x : ℕ) : Nat.Full 2 (x ^ 2) := by
  intro p hp
  have h := Nat.mem_primeFactors.mp hp
  exact pow_dvd_pow_of_dvd (h.1.dvd_of_dvd_pow h.2.1) 2

lemma eight_sq_full (z : ℕ) : Nat.Full 2 (8 * z ^ 2) := by
  intro p hp
  have h := Nat.mem_primeFactors.mp hp
  rcases h.1.dvd_mul.mp h.2.1 with hd | hd
  · have h8 : (8 : ℕ) = 2 ^ 3 := by norm_num
    rw [h8] at hd
    have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq h.1 Nat.prime_two).1 (h.1.dvd_of_dvd_pow hd)
    rw [hp2]
    exact dvd_mul_of_dvd_left (by norm_num) _
  · exact dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd (h.1.dvd_of_dvd_pow hd) 2) _

lemma of_triple {n x y z : ℕ} (hx : Nat.Full 2 x) (hy : Nat.Full 2 y) (hz : Nat.Full 2 z)
    (h : n = x + y + z) : Erdos1107.SumOfRPowerful 2 n := by
  refine ⟨[x,y,z], by simp, ?_, ?_⟩
  · intro s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl <;> assumption
  · simpa [Nat.add_assoc] using h.symm

/-- A number with odd `2`-adic valuation is not of the form `4 ^ c * v` with `v` odd. -/
lemma val_parity : ∀ (a c u v : ℕ), u % 2 = 1 → v % 2 = 1 → 2 * (4 ^ a * u) ≠ 4 ^ c * v := by
  intro a
  induction a with
  | zero =>
    intro c u v hu hv h
    rcases c with _ | c
    · simp only [pow_zero, one_mul] at h
      omega
    · simp only [pow_zero, one_mul] at h
      have h' : 2 * u = 4 * (4 ^ c * v) := by
        rw [h, pow_succ]
        ring
      omega
  | succ a ih =>
    intro c u v hu hv h
    rcases c with _ | c
    · simp only [pow_zero, one_mul] at h
      omega
    · apply ih c u v hu hv
      have h' : 4 * (2 * (4 ^ a * u)) = 4 * (4 ^ c * v) := by
        calc 4 * (2 * (4 ^ a * u)) = 2 * (4 ^ (a + 1) * u) := by
              rw [pow_succ]
              ring
          _ = 4 ^ (c + 1) * v := h
          _ = 4 * (4 ^ c * v) := by
              rw [pow_succ]
              ring
      exact Nat.eq_of_mul_eq_mul_left (by norm_num) h'

lemma sq_mod_two (t : ℕ) : t ^ 2 % 2 = t % 2 := by
  obtain ⟨k, hk | hk⟩ : ∃ k, t = 2 * k ∨ t = 2 * k + 1 := ⟨t / 2, by omega⟩
  · rw [hk]
    have h : (2 * k) ^ 2 = 2 * (2 * k ^ 2) := by ring
    omega
  · rw [hk]
    have h : (2 * k + 1) ^ 2 = 2 * (2 * k ^ 2 + 2 * k) + 1 := by ring
    omega

/-- From a three-square representation of `2 * m` with `P ≡ Q (mod 2)` and `R` even. -/
lemma rep_of_parity (m P Q R : ℕ) (h : 2 * m = P ^ 2 + Q ^ 2 + R ^ 2) (hle : Q ≤ P)
    (hPQ : P % 2 = Q % 2) (hR : R % 2 = 0) :
    ∃ x y z : ℕ, m = x ^ 2 + y ^ 2 + 2 * z ^ 2 := by
  obtain ⟨y, hy⟩ : ∃ y, P = Q + 2 * y := ⟨(P - Q) / 2, by omega⟩
  obtain ⟨z, hz⟩ : ∃ z, R = 2 * z := ⟨R / 2, by omega⟩
  refine ⟨Q + y, y, z, ?_⟩
  have h2 : 2 * m = 2 * ((Q + y) ^ 2 + y ^ 2 + 2 * z ^ 2) := by
    rw [h, hy, hz]
    ring
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) h2

lemma rep_of_parity' (m P Q R : ℕ) (h : 2 * m = P ^ 2 + Q ^ 2 + R ^ 2)
    (hPQ : P % 2 = Q % 2) (hR : R % 2 = 0) :
    ∃ x y z : ℕ, m = x ^ 2 + y ^ 2 + 2 * z ^ 2 := by
  rcases le_total Q P with hle | hle
  · exact rep_of_parity m P Q R h hle hPQ hR
  · refine rep_of_parity m Q P R ?_ hle hPQ.symm hR
    rw [h]
    ring

/-- Legendre's theorem gives representations by `x ^ 2 + y ^ 2 + 2 * z ^ 2`. -/
lemma rep_one_one_two (h1 : ∀ n : ℕ, (∀ a b : ℕ, n ≠ 4^a*(8*b+7)) → ∃ x y z : ℕ, n = x^2+y^2+z^2) (m : ℕ) (hm : ∀ a b : ℕ, 2 * m ≠ 4 ^ a * (8 * b + 7)) :
    ∃ x y z : ℕ, m = x ^ 2 + y ^ 2 + 2 * z ^ 2 := by
  obtain ⟨A, B, C, hABC⟩ := h1 (2 * m) hm
  have hA := sq_mod_two A
  have hB := sq_mod_two B
  have hC := sq_mod_two C
  rcases Nat.mod_two_eq_zero_or_one C with hc | hc
  · exact rep_of_parity' m A B C hABC (by omega) hc
  · rcases Nat.mod_two_eq_zero_or_one B with hb | hb
    · refine rep_of_parity' m A C B ?_ (by omega) hb
      rw [hABC]
      ring
    · refine rep_of_parity' m B C A ?_ (by omega) (by omega)
      rw [hABC]
      ring

theorem eventual_of_seven
    (h2 : ∀ᶠ n : ℕ in Filter.atTop, n % 8 = 7 → ∃ x y z : ℕ, Nat.Full 2 x ∧ Nat.Full 2 y ∧ Nat.Full 2 z ∧ n = x + y + z) :
    ∀ᶠ n : ℕ in Filter.atTop, Erdos1107.SumOfRPowerful 2 n := by
  have h1 := natural940
  have h2' : ∀ᶠ n : ℕ in Filter.atTop, n % 8 = 7 →
      ∃ x y z : ℕ, Nat.Full 2 x ∧ Nat.Full 2 y ∧ Nat.Full 2 z ∧ n = x + y + z := h2
  refine h2'.mono fun n hn => ?_
  by_cases h7 : n % 8 = 7
  · obtain ⟨x, y, z, hx, hy, hz, hsum⟩ := hn h7
    exact of_triple hx hy hz hsum
  · by_cases h4 : n % 4 = 0
    · obtain ⟨m, hm⟩ : ∃ m, n = 4 * m := ⟨n / 4, by omega⟩
      by_cases hB : ∀ a b : ℕ, 2 * m ≠ 4 ^ a * (8 * b + 7)
      · obtain ⟨x, y, z, hxyz⟩ := rep_one_one_two h1 m hB
        refine of_triple (sq_full (2 * x)) (sq_full (2 * y)) (eight_sq_full z) ?_
        rw [hm, hxyz]
        ring
      · obtain ⟨a, ha⟩ := not_forall.1 hB
        obtain ⟨b, hb⟩ := not_forall.1 ha
        have hab : 2 * m = 4 ^ a * (8 * b + 7) := not_not.1 hb
        have hno : ∀ c d : ℕ, n ≠ 4 ^ c * (8 * d + 7) := by
          intro c d hcd
          refine val_parity a c (8 * b + 7) (8 * d + 7) (by omega) (by omega) ?_
          rw [← hab, ← hcd, hm]
          ring
        obtain ⟨x, y, z, hxyz⟩ := h1 n hno
        exact of_triple (sq_full x) (sq_full y) (sq_full z) hxyz
    · have hno : ∀ a b : ℕ, n ≠ 4 ^ a * (8 * b + 7) := by
        intro a b h
        rcases a with _ | a
        · simp only [pow_zero, one_mul] at h
          omega
        · have h' : n = 4 * (4 ^ a * (8 * b + 7)) := by
            rw [h, pow_succ]
            ring
          omega
      obtain ⟨x, y, z, hxyz⟩ := h1 n hno
      exact of_triple (sq_full x) (sq_full y) (sq_full z) hxyz

theorem three_squares_mod_three (m : ℕ) (three : m % 8 = 3) :
    ∃ x y z : ℕ, m=x^2+y^2+z^2 := by
  apply natural940
  intro a b eq
  cases a with
  | zero => simp only [pow_zero,one_mul] at eq; omega
  | succ a =>
    have div : 4 ∣ m := by
      rw [eq,pow_succ]
      exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _
    omega
theorem eventual_of_fixed125 (seven : ∀ᶠ n : ℕ in Filter.atTop, n % 8 = 7 →
    ∃ x y z : ℕ, n = x^2+y^2+125*z^2) : type_of% @Erdos1107.erdos_1107.variants.two := by
  apply eventual_of_seven
  filter_upwards [seven] with n hn h7
  obtain ⟨x,y,z,h⟩ := hn h7
  refine ⟨x^2,y^2,125*z^2,sq_full x,sq_full y,?_,h⟩
  intro p hp
  have v := Nat.mem_primeFactors.mp hp
  rcases v.1.dvd_mul.mp v.2.1 with h5 | hz
  · rw [show (125:ℕ) = 5^3 by decide] at h5
    have eq := (Nat.prime_dvd_prime_iff_eq v.1 (by decide : Nat.Prime 5)).mp (v.1.dvd_of_dvd_pow h5)
    subst p
    exact dvd_mul_of_dvd_left (by decide : 5^2 ∣ 125) _
  · exact dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd (v.1.dvd_of_dvd_pow hz) 2) _

end PowerfulLegendre
end

section
open Filter

namespace PowerfulMoroz

/-- Twice the determinant of the integral Gram matrix for x²+y²+cz²
in the convention f(x)=xᵀAx/2. -/
theorem twice_det (c : ℕ) :
    2*(Matrix.diagonal (![2,2,(2:ℤ)*c] : Fin 3 → ℤ)).det=16*c := by
  rw [Matrix.det_diagonal,Fin.prod_univ_three]
  simp
  ring

/-- Strip the common factors of five from n and the coefficient 125.
The two possible residue classes are exactly 7 for odd e and 3 for even e. -/
theorem strip (n : ℕ) (hn : n%8=7) :
    ∃ (e : ℕ) (m:ℕ), e≤3 ∧ n=5^(3-e)*m ∧ m.Coprime (16*5^e) ∧
      m%8=(if e%2=1 then 7 else 3) := by
  have cop (m e : ℕ) (odd : ¬ 2∣m) (unit : ¬5∣m) : m.Coprime (16*5^e) := by
    have two := (Nat.prime_two.coprime_iff_not_dvd.mpr odd).symm.pow_right 4
    have five := ((by decide : Nat.Prime 5).coprime_iff_not_dvd.mpr unit).symm.pow_right e
    exact Nat.Coprime.mul_right two five
  by_cases h₁ : 5∣n
  · obtain ⟨x,rfl⟩ := h₁
    by_cases h₂ : 5∣x
    · obtain ⟨y,rfl⟩ := h₂
      by_cases h₃ : 5∣y
      · obtain ⟨z,rfl⟩ := h₃
        refine ⟨0,z,by decide,by ring,?_,?_⟩
        · have hz : ¬2∣z := by omega
          simpa using (Nat.prime_two.coprime_iff_not_dvd.mpr hz).symm.pow_right 4
        · simp; omega
      · exact ⟨1,y,by decide,by ring,cop _ _ (by omega) h₃,by simp; omega⟩
    · exact ⟨2,x,by decide,by ring,cop _ _ (by omega) h₂,by simp; omega⟩
  · exact ⟨3,n,by decide,by simp,cop _ _ (by omega) h₁,by simpa using hn⟩

/-- If a stripped form represents its input, multiply the first two squares
by the removed power of five via the two-square product identity. -/
theorem reassemble {n m e : ℕ} (he : e≤3) (stripEq : n=5^(3-e)*m)
    {x y z : ℕ} (rep : m=x^2+y^2+5^e*z^2) :
    ∃ X Y Z : ℕ, n=X^2+Y^2+125*Z^2 := by
  have power (k : ℕ) : ∃ a b : ℕ, 5^k=a^2+b^2 := by
    induction k with
    | zero => exact ⟨1,0,by decide⟩
    | succ k ih =>
      obtain ⟨a,b,eq⟩ := ih
      simpa only [pow_succ] using Nat.sq_add_sq_mul eq (by decide : 5=(1:ℕ)^2+2^2)
  obtain ⟨a,b,eq⟩ := power (3-e)
  obtain ⟨X,Y,eq'⟩ := Nat.sq_add_sq_mul eq (rfl : x^2+y^2=x^2+y^2)
  refine ⟨X,Y,z,?_⟩
  rw [stripEq,rep,mul_add,eq',←mul_assoc,←pow_add,Nat.sub_add_cancel he]
  norm_num

/-- Every eventual representation for the three exceptional coprime-level
forms suffices. For e=0, Legendre immediately represents the class 3 mod 8. -/
theorem of_coprime_forms
    (three : ∀ m : ℕ, m%8=3 → ∃ x y z : ℕ,m=x^2+y^2+z^2)
    (forms : ∀ᶠ m : ℕ in atTop, ∀ e : ℕ, 1≤e → e≤3 → m.Coprime (16*5^e) →
      m%8=(if e%2=1 then 7 else 3) → ∃ x y z : ℕ,m=x^2+y^2+5^e*z^2) :
    ∀ᶠ n : ℕ in atTop, n%8=7 → ∃ x y z : ℕ,n=x^2+y^2+125*z^2 := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp forms
  filter_upwards [eventually_ge_atTop (125*N)] with n hn
  intro seven
  obtain ⟨e,m,le,eq,cop,res⟩ := strip n seven
  have scale : 5^(3-e) ≤ 125 := by
    exact Nat.pow_le_pow_right (by decide : 0<5) (by omega : 3-e≤3)
  have mge : N ≤ m := by
    have := Nat.mul_le_mul_right m scale
    omega
  apply Exists.elim (p:=fun x => ∃ y z : ℕ, m=x^2+y^2+5^e*z^2) _ (fun x ⟨y,z,h⟩ => reassemble le eq h)
  by_cases zero : e=0
  · subst e
    simpa using three m (by simpa using res)
  · exact hN m mge e (by omega) le cop res

end PowerfulMoroz

open Filter

namespace PowerfulMoroz

/-- On the isotropic lines modulo five, division by one of the two Gaussian
integer factors of five leaves an integral pair. -/
theorem remove_five (x y : ℤ) (hz : (x:ZMod 5)^2+(y:ZMod 5)^2=0) :
    ∃ a b : ℤ, x^2+y^2=5*(a^2+b^2) := by
  have lines : ∀ X Y : ZMod 5, X^2+Y^2=0 →
      (X-2*Y=0 ∧ 2*X+Y=0) ∨ (X+2*Y=0 ∧ 2*X-Y=0) := by decide +kernel
  have div (v : ℤ) (h : (v:ZMod 5)=0) : 5∣v := (ZMod.intCast_zmod_eq_zero_iff_dvd v 5).mp h
  rcases lines x y hz with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
  · obtain ⟨a,ha⟩ := div (x-2*y) (by push_cast; exact h₁)
    obtain ⟨b,hb⟩ := div (2*x+y) (by push_cast; exact h₂)
    use a,b
    have key : (5*a)^2+(5*b)^2=5*(x^2+y^2) := by rw [←ha,←hb]; ring
    linarith only [key]
  · obtain ⟨a,ha⟩ := div (x+2*y) (by push_cast; exact h₁)
    obtain ⟨b,hb⟩ := div (2*x-y) (by push_cast; exact h₂)
    use a,b
    have key : (5*a)^2+(5*b)^2=5*(x^2+y^2) := by rw [←ha,←hb]; ring
    linarith only [key]

/-- A representation of 5m by three squares always descends to m by
the form x²+y²+5z². -/
theorem descend_three (m x y z : ℕ) (h : 5*m=x^2+y^2+z^2) :
    ∃ a b c : ℕ, m=a^2+b^2+5*c^2 := by
  have hm : (x:ZMod 5)^2+(y:ZMod 5)^2+(z:ZMod 5)^2=0 := by
    have e := congrArg (fun w : ℕ => (w:ZMod 5)) h
    push_cast at e
    simpa [show (5:ZMod 5)=0 by decide] using e.symm
  have axis : ∀ X Y Z : ZMod 5, X^2+Y^2+Z^2=0 → X=0 ∨ Y=0 ∨ Z=0 := by decide +kernel
  have finish (u v t : ℕ) (ht : (t:ZMod 5)=0) (e : 5*m=u^2+v^2+t^2) :
      ∃ a b c : ℕ, m=a^2+b^2+5*c^2 := by
    obtain ⟨c,rfl⟩ := (ZMod.natCast_eq_zero_iff t 5).mp ht
    have ev := congrArg (fun w : ℕ => (w:ZMod 5)) e
    push_cast at ev
    obtain ⟨a,b,eqn⟩ := remove_five (u:ℤ) (v:ℤ) (by simpa [show (5:ZMod 5)=0 by decide] using ev.symm)
    refine ⟨a.natAbs,b.natAbs,c,?_⟩
    zify at e ⊢
    rw [sq_abs,sq_abs]
    nlinarith only [e,eqn]
  rcases axis x y z hm with hx | hy | hz
  · exact finish y z x hx (by linarith only [h])
  · exact finish x z y hy (by linarith only [h])
  · exact finish x y z hz h

/-- The solely analytic cases are e=2 and e=3, since the e=1 case
already follows from the three-squares theorem applied to 5m. -/
theorem of_two_coprime_forms
    (three : ∀ m : ℕ, m%8=3 → ∃ x y z : ℕ,m=x^2+y^2+z^2)
    (forms : ∀ᶠ m : ℕ in atTop, ∀ e : ℕ, 2≤e → e≤3 → m.Coprime (16*5^e) →
      m%8=(if e%2=1 then 7 else 3) → ∃ x y z : ℕ,m=x^2+y^2+5^e*z^2) :
    ∀ᶠ n : ℕ in atTop, n%8=7 → ∃ x y z : ℕ,n=x^2+y^2+125*z^2 := by
  apply of_coprime_forms three
  filter_upwards [forms] with m hm
  intro e pos le cop res
  by_cases e2 : 2≤e
  · exact hm e e2 le cop res
  obtain rfl : e=1 := by omega
  obtain ⟨x,y,z,h⟩ := three (5*m) (by norm_num at res; omega)
  simpa using descend_three m x y z h

end PowerfulMoroz
end

section
/- The Hensel adjustment and lifting through Z/p^kZ adapt the three desk notes
by @jared-jasinski on Erdos1107. We allow an arbitrary coefficient q in
place of a prime cube and prove all the local hypotheses for the fixed forms. -/
namespace PowerfulLocal

open Polynomial

variable {p : ℕ} [Fact p.Prime]

theorem adjustSquare (a x t : ℤ_[p]) (hx : IsUnit x)
    (hclose : ‖a * x ^ 2 - t‖ < ‖2 * a‖ ^ 2) :
    ∃ z : ℤ_[p], a * z ^ 2 = t ∧ IsUnit z := by
  let f : Polynomial ℤ_[p] := C a * X ^ 2 - C t
  have value (z : ℤ_[p]) : f.aeval z = a * z ^ 2 - t := by simp [f]
  have derivative (z : ℤ_[p]) : f.derivative.aeval z = (2 * a) * z := by
    simp [f]
    ring
  have hnormx := PadicInt.isUnit_iff.mp hx
  have hstart : ‖f.aeval x‖ < ‖f.derivative.aeval x‖ ^ 2 := by
    simpa only [value, derivative, norm_mul, hnormx, mul_one] using hclose
  obtain ⟨z, hz, -, hnorm, -⟩ := hensels_lemma hstart
  have heq : ‖2 * a‖ * ‖z‖ = ‖2 * a‖ * 1 := by
    simpa only [derivative, norm_mul, hnormx] using hnorm
  have hpos : 0 < ‖2 * a‖ := by
    by_contra! h
    have hzero : ‖2 * a‖ = 0 := le_antisymm h (norm_nonneg _)
    rw [hzero, zero_pow (by decide : 2 ≠ 0)] at hclose
    exact (norm_nonneg _).not_gt hclose
  exact ⟨z, sub_eq_zero.mp (by simpa only [value] using hz),
    PadicInt.isUnit_iff.mpr (mul_left_cancel₀ hpos.ne' heq)⟩

theorem liftDiagonal (a b c x y z t : ℤ_[p])
    (h : let e := ‖a * x ^ 2 + b * y ^ 2 + c * z ^ 2 - t‖
      (IsUnit x ∧ e < ‖2 * a‖ ^ 2) ∨ (IsUnit y ∧ e < ‖2 * b‖ ^ 2) ∨
      (IsUnit z ∧ e < ‖2 * c‖ ^ 2)) :
    ∃ u v w : ℤ_[p], a * u ^ 2 + b * v ^ 2 + c * w ^ 2 = t ∧
      (IsUnit u ∨ IsUnit v ∨ IsUnit w) := by
  dsimp only at h
  rcases h with ⟨hx,h⟩ | ⟨hy,h⟩ | ⟨hz,h⟩
  · have he : a * x ^ 2 - (t - b * y ^ 2 - c * z ^ 2) =
        a * x ^ 2 + b * y ^ 2 + c * z ^ 2 - t := by ring
    obtain ⟨u, hu, hUnit⟩ := adjustSquare a x _ hx (by rwa [he])
    exact ⟨u, y, z, by linear_combination hu, Or.inl hUnit⟩
  · have he : b * y ^ 2 - (t - a * x ^ 2 - c * z ^ 2) =
        a * x ^ 2 + b * y ^ 2 + c * z ^ 2 - t := by ring
    obtain ⟨v, hv, hUnit⟩ := adjustSquare b y _ hy (by rwa [he])
    exact ⟨x, v, z, by linear_combination hv, Or.inr (Or.inl hUnit)⟩
  · have he : c * z ^ 2 - (t - a * x ^ 2 - b * y ^ 2) =
        a * x ^ 2 + b * y ^ 2 + c * z ^ 2 - t := by ring
    obtain ⟨w, hw, hUnit⟩ := adjustSquare c z _ hz (by rwa [he])
    exact ⟨x, y, w, by linear_combination hw, Or.inr (Or.inr hUnit)⟩

private theorem isUnit_of_toZMod_ne_zero {x : ℤ_[p]} (h : PadicInt.toZMod x ≠ 0) :
    IsUnit x := by
  by_contra hunit
  apply h
  change x ∈ RingHom.ker (PadicInt.toZMod (p := p))
  rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal]
  exact hunit

theorem liftTwo (q n : ℕ) (hq : q % 2 = 1) (x y z : ZMod 8)
    (h : (q : ZMod 8) * x ^ 2 + y ^ 2 + z ^ 2 = n)
    (hunit : x.val % 2 = 1 ∨ y.val % 2 = 1 ∨ z.val % 2 = 1) :
    ∃ a b c : ℤ_[2], (q : ℤ_[2]) * a ^ 2 + b ^ 2 + c ^ 2 = n ∧
      (IsUnit ((q : ℤ_[2]) * a) ∨ IsUnit b ∨ IsUnit c) := by
  have unitNat (m : ℕ) (hm : m % 2 = 1) : IsUnit (m : ℤ_[2]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    exact (Nat.prime_two.coprime_iff_not_dvd).mpr (by omega)
  have hqUnit := unitNat q hq
  let e := (q : ℤ_[2]) * (x.val : ℤ_[2]) ^ 2 +
    (y.val : ℤ_[2]) ^ 2 + (z.val : ℤ_[2]) ^ 2 - n
  have hr : PadicInt.toZModPow (p := 2) 3 e = 0 := by
    simp [e, h]
  have hb : ‖e‖ ≤ (2 : ℝ) ^ (-3 : ℤ) := by
    have hk := (PadicInt.norm_le_pow_iff_mem_span_pow e 3).mpr (by
      rw [← PadicInt.ker_toZModPow, RingHom.mem_ker]; exact hr)
    simpa using hk
  have ht : ‖(2 : ℤ_[2])‖ = (2 : ℝ)⁻¹ := PadicInt.norm_p (p := 2)
  have hl : ‖e‖ < ‖(2 : ℤ_[2])‖ ^ 2 := by
    rw [ht]
    exact hb.trans_lt (by norm_num)
  have haq : ‖2 * (q : ℤ_[2])‖ = ‖(2 : ℤ_[2])‖ := by
    simp only [norm_mul, PadicInt.isUnit_iff.mp hqUnit, mul_one]
  obtain ⟨a,b,c,he,hu⟩ := liftDiagonal (q : ℤ_[2]) 1 1 x.val y.val z.val n (by
    simp only [one_mul, mul_one, haq]
    rcases hunit with hx | hy | hz
    · exact Or.inl ⟨unitNat _ hx, hl⟩
    · exact Or.inr (Or.inl ⟨unitNat _ hy, hl⟩)
    · exact Or.inr (Or.inr ⟨unitNat _ hz, hl⟩))
  refine ⟨a,b,c,by simpa only [one_mul] using he,?_⟩
  exact hu.imp (hqUnit.mul) id

theorem liftOdd (q n : ℕ) (hp : p ≠ 2) (x y z : ZMod p)
    (h : (q : ZMod p) * x ^ 2 + y ^ 2 + z ^ 2 = n)
    (hunit : (q : ZMod p) * x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) :
    ∃ a b c : ℤ_[p], (q : ℤ_[p]) * a ^ 2 + b ^ 2 + c ^ 2 = n ∧
      (IsUnit ((q : ℤ_[p]) * a) ∨ IsUnit b ∨ IsUnit c) := by
  let x₀ : ℤ_[p] := x.val
  let y₀ : ℤ_[p] := y.val
  let z₀ : ℤ_[p] := z.val
  have hX : PadicInt.toZMod x₀ = x := by simp [x₀]
  have hY : PadicInt.toZMod y₀ = y := by simp [y₀]
  have hZ : PadicInt.toZMod z₀ = z := by simp [z₀]
  let e := (q : ℤ_[p]) * x₀ ^ 2 + y₀ ^ 2 + z₀ ^ 2 - n
  have hr : PadicInt.toZMod e = 0 := by simp [e, hX, hY, hZ, h]
  have hlt : ‖e‖ < 1 := by
    rw [PadicInt.norm_lt_one_iff_dvd, ← Ideal.mem_span_singleton, ← PadicInt.maximalIdeal_eq_span_p,
      ← PadicInt.ker_toZMod, RingHom.mem_ker]
    exact hr
  have htwo : IsUnit (2 : ℤ_[p]) := by
    apply isUnit_of_toZMod_ne_zero
    change PadicInt.toZMod ((2 : ℕ) : ℤ_[p]) ≠ 0
    rw [map_natCast, ne_eq, ZMod.natCast_eq_zero_iff]
    exact fun hd => hp ((Nat.prime_dvd_prime_iff_eq Fact.out (by decide)).mp hd)
  rcases hunit with hqX | hy | hz
  · have hq : IsUnit (q : ℤ_[p]) := isUnit_of_toZMod_ne_zero (by
      simpa only [map_natCast] using (fun h₀ => hqX (by rw [h₀, zero_mul]) : (q : ZMod p) ≠ 0))
    have hx : IsUnit x₀ := isUnit_of_toZMod_ne_zero (by
      rw [hX]; exact fun h₀ => hqX (by rw [h₀, mul_zero]))
    have hnorm := PadicInt.isUnit_iff.mp (htwo.mul hq)
    have hclose : ‖(q : ℤ_[p]) * x₀ ^ 2 - (n - y₀ ^ 2 - z₀ ^ 2)‖ <
        ‖2 * (q : ℤ_[p])‖ ^ 2 := by
      rw [hnorm, one_pow, show (q : ℤ_[p]) * x₀ ^ 2 - (n - y₀ ^ 2 - z₀ ^ 2) = e by dsimp [e]; ring]
      exact hlt
    obtain ⟨a, ha, haunit⟩ := adjustSquare _ x₀ _ hx hclose
    exact ⟨a, y₀, z₀, by linear_combination ha, Or.inl (hq.mul haunit)⟩
  · have hyUnit : IsUnit y₀ := isUnit_of_toZMod_ne_zero (hY.symm ▸ hy)
    have hclose : ‖1 * y₀ ^ 2 - (n - (q : ℤ_[p]) * x₀ ^ 2 - z₀ ^ 2)‖ <
        ‖2 * (1 : ℤ_[p])‖ ^ 2 := by
      rw [mul_one, PadicInt.isUnit_iff.mp htwo, one_pow,
        show 1 * y₀ ^ 2 - (n - (q : ℤ_[p]) * x₀ ^ 2 - z₀ ^ 2) = e by dsimp [e]; ring]
      exact hlt
    obtain ⟨b, hb, hbUnit⟩ := adjustSquare 1 y₀ _ hyUnit hclose
    exact ⟨x₀, b, z₀, by linear_combination hb, Or.inr (Or.inl hbUnit)⟩
  · have hzUnit : IsUnit z₀ := isUnit_of_toZMod_ne_zero (hZ.symm ▸ hz)
    have hclose : ‖1 * z₀ ^ 2 - (n - (q : ℤ_[p]) * x₀ ^ 2 - y₀ ^ 2)‖ <
        ‖2 * (1 : ℤ_[p])‖ ^ 2 := by
      rw [mul_one, PadicInt.isUnit_iff.mp htwo, one_pow,
        show 1 * z₀ ^ 2 - (n - (q : ℤ_[p]) * x₀ ^ 2 - y₀ ^ 2) = e by dsimp [e]; ring]
      exact hlt
    obtain ⟨c, hc, hcUnit⟩ := adjustSquare 1 z₀ _ hzUnit hclose
    exact ⟨x₀, y₀, c, by linear_combination hc, Or.inr (Or.inr hcUnit)⟩

end PowerfulLocal

namespace PowerfulLocal

/-- For odd primes, two squares prescribe the residue. If the target
vanishes modulo p, put one in the coefficient-q coordinate instead. -/
theorem odd_seed (q n : ℕ) (cop : n.Coprime q) (p : ℕ) [hp : Fact p.Prime] :
    ∃ x y z : ZMod p, (q : ZMod p)*x^2+y^2+z^2=n ∧
      ((q : ZMod p)*x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) := by
  by_cases hn : (n : ZMod p) = 0
  · have hq : (q : ZMod p) ≠ 0 := by
      intro hz
      have h := Nat.dvd_gcd ((ZMod.natCast_eq_zero_iff ..).mp hn)
        ((ZMod.natCast_eq_zero_iff ..).mp hz)
      rw [cop.gcd_eq_one, Nat.dvd_one] at h
      exact hp.out.ne_one h
    obtain ⟨y,z,eq⟩ := ZMod.sq_add_sq p (-(q : ZMod p))
    exact ⟨1,y,z,by rw [hn]; simp only [one_pow, mul_one]; linear_combination eq,
      Or.inl (by simpa using hq)⟩
  · obtain ⟨y,z,eq⟩ := ZMod.sq_add_sq p (n : ZMod p)
    refine ⟨0,y,z,by simpa using eq,Or.inr ?_⟩
    by_contra! hh
    simp [hh.1, hh.2] at eq
    exact hn eq.symm

/-- Primitive representations at every prime for either fixed Moroz form.
The coordinate multiplied by q is permitted only when q is itself a unit. -/
theorem everywhere (q n : ℕ) (hq : q%2=1) (cop : n.Coprime q)
    (res : n%8=(q+2)%8) (p : ℕ) [Fact p.Prime] :
    ∃ x y z : ℤ_[p], x^2+y^2+(q : ℤ_[p])*z^2=n ∧
      (IsUnit x ∨ IsUnit y ∨ IsUnit ((q : ℤ_[p])*z)) := by
  have rep : ∃ a b c : ℤ_[p], (q : ℤ_[p])*a^2+b^2+c^2=n ∧
      (IsUnit ((q : ℤ_[p])*a) ∨ IsUnit b ∨ IsUnit c) := by
    rcases eq_or_ne p 2 with rfl | hp
    · apply liftTwo q n hq 1 1 1 _ (Or.inl (by decide))
      have eq : (n : ZMod 8) = ((q+2:ℕ) : ZMod 8) := by
        rw [← ZMod.natCast_mod n 8, ← ZMod.natCast_mod (q+2) 8, res]
      rw [eq]
      push_cast
      ring
    · obtain ⟨x,y,z,eq,hu⟩ := odd_seed q n cop p
      exact liftOdd q n hp x y z eq hu
  obtain ⟨a,b,c,he,hu⟩ := rep
  exact ⟨b,c,a,by linear_combination he, by tauto⟩

end PowerfulLocal
end

section
open Filter Finset
namespace PowerfulMass

/-- Two effective powers suffice to turn the two independent analytic estimates
into an integral representation for each of the two coprime levels. -/
theorem bridge
    (lower : ∀ᶠ n : ℕ in atTop, ∀ c ∈ ({25, 125} : Finset ℕ), n.Coprime (16*c) →
    n%8=(c+2)%8 →
    (∀ (p : ℕ) (hp : p.Prime), letI : Fact p.Prime := ⟨hp⟩
      ∃ x y z : ℤ_[p], x^2 + y^2 + (c : ℤ_[p])*z^2 = n ∧
        (IsUnit x ∨ IsUnit y ∨ IsUnit ((c : ℤ_[p])*z))) →
    ∀ᶠ k : ℕ in atTop,
    let M := (k + 1).factorial
    let X := Finset.range M
    let A := ((X ×ˢ (X ×ˢ X)).filter (fun t ↦
      (t.1 ^ 2 + t.2.1 ^ 2 + c * t.2.2 ^ 2) % M = n % M)).card
    (n : ℝ) ^ ((49 : ℝ) / 100) ≤ 2 * Real.pi * Real.sqrt ((n : ℝ) / (c : ℝ)) * (A : ℝ) / (M : ℝ) ^ 2)
    (upper : ∀ᶠ n : ℕ in atTop, ∀ c ∈ ({25, 125} : Finset ℕ), n.Coprime (16*c) →
    let I := Finset.Icc (-(n : ℤ)) (n : ℤ)
    let R := ((I ×ˢ (I ×ˢ I)).filter (fun t ↦
      t.1 ^ 2 + t.2.1 ^ 2 + (c : ℤ) * t.2.2 ^ 2 = (n : ℤ))).card
    ∀ᶠ k : ℕ in atTop,
    let M := (k + 1).factorial
    let X := Finset.range M
    let A := ((X ×ˢ (X ×ˢ X)).filter (fun t ↦
      (t.1 ^ 2 + t.2.1 ^ 2 + c * t.2.2 ^ 2) % M = n % M)).card
    2 * Real.pi * Real.sqrt ((n : ℝ) / (c : ℝ)) * (A : ℝ) / (M : ℝ) ^ 2 ≤ (R : ℝ) + (n : ℝ) ^ ((48 : ℝ) / 100)) :
    ∀ᶠ n : ℕ in atTop, ∀ e : ℕ, 2 ≤ e → e ≤ 3 → n.Coprime (16*5^e) →
      n%8=(if e%2=1 then 7 else 3) → ∃ x y z : ℕ, n=x^2+y^2+5^e*z^2 := by
  filter_upwards [lower,upper,eventually_gt_atTop 1] with n lo hi hn
  intro e emin emax cop residue
  let c := 5 ^ e
  have cc : c ∈ ({25,125} : Finset ℕ) := by dsimp only [c]; interval_cases e <;> decide
  have odd : c % 2 = 1 := by dsimp only [c]; interval_cases e <;> decide
  have res : n%8=(c+2)%8 := by dsimp only [c]; interval_cases e <;> norm_num at residue ⊢ <;> assumption
  have oddcop : n.Coprime c := cop.coprime_dvd_right (dvd_mul_left _ _)
  have loc (p : ℕ) (hp : p.Prime) : letI : Fact p.Prime := ⟨hp⟩
      ∃ x y z : ℤ_[p], x^2+y^2+(c : ℤ_[p])*z^2=n ∧
        (IsUnit x ∨ IsUnit y ∨ IsUnit ((c : ℤ_[p])*z)) := by
    let : Fact p.Prime := ⟨hp⟩
    exact PowerfulLocal.everywhere c n odd oddcop res p
  obtain ⟨k,lk,uk⟩ := ((lo c cc cop res loc).and (hi c cc cop)).exists
  let I := Finset.Icc (-(n:ℤ)) (n:ℤ)
  let R := (I ×ˢ (I ×ˢ I)).filter (fun t ↦ t.1^2 + t.2.1^2 + (c:ℤ)*t.2.2^2 = (n:ℤ))
  have smaller : (n : ℝ) ^ ((48 : ℝ) / 100) < (n : ℝ) ^ ((49 : ℝ) / 100) :=
    Real.rpow_lt_rpow_of_exponent_lt (by exact_mod_cast hn) (by norm_num)
  have final : (n : ℝ) ^ ((49 : ℝ) / 100) ≤ (R.card:ℝ) + (n : ℝ) ^ ((48 : ℝ) / 100) := lk.trans uk
  have positive : 0 < R.card := by
    by_contra! hR
    rw [Nat.eq_zero_of_le_zero hR, Nat.cast_zero, zero_add] at final
    exact (not_le_of_gt smaller) final
  obtain ⟨⟨x,y,z⟩,hh⟩ := Finset.card_pos.mp positive
  have eq := (Finset.mem_filter.mp hh).2
  change x^2+y^2+(c:ℤ)*z^2=n at eq
  refine ⟨x.natAbs, y.natAbs, z.natAbs, ?_⟩
  zify
  simp only [sq_abs]
  exact eq.symm

end PowerfulMass
end

section
namespace PowerfulDyadic
open Finset

/-- Set two odd coordinates to 1 mod 8. Hensel's lemma adjusts the other
coordinate, uniformly for every choice of these two coordinates. -/
theorem choose_square (c n y z : ℕ) (hc : n%8=(c+2)%8)
    (hy : y%8=1) (hz : z%8=1) :
    ∃ x : ℤ_[2], x^2+(y:ℤ_[2])^2+(c:ℤ_[2])*z^2=n := by
  let t : ℤ_[2] := n-(y:ℤ_[2])^2-(c:ℤ_[2])*z^2
  have castone {u : ℕ} (h : u%8=1) : (u : ZMod 8) = 1 := by
    rw [← ZMod.natCast_mod u 8,h]; rfl
  have eq : (n : ZMod 8)=(c:ZMod 8)+2 := by
    rw [← Nat.cast_ofNat (R := ZMod 8) (n := 2), ← Nat.cast_add,
      ← ZMod.natCast_mod n 8, ← ZMod.natCast_mod (c+2) 8, hc]
  have hmod : PadicInt.toZModPow (p:=2) 3 (1-t) = 0 := by
    simp only [t,map_sub,map_one,map_pow,map_natCast,map_mul]
    change 1-((n:ZMod 8) - (y:ZMod 8)^2 - (c:ZMod 8)*(z:ZMod 8)^2)=0
    rw [eq,castone hy,castone hz]
    ring
  have bound : ‖1-t‖ ≤ (2:ℝ)^(-3:ℤ) := by
    have h := (PadicInt.norm_le_pow_iff_mem_span_pow (1-t) 3).mpr (by
      rw [← PadicInt.ker_toZModPow,RingHom.mem_ker]; exact hmod)
    simpa using h
  have small : ‖(1:ℤ_[2])*1^2-t‖ < ‖2*(1:ℤ_[2])‖^2 := by
    simp only [one_pow,mul_one]
    rw [show ‖(2:ℤ_[2])‖ = (2:ℝ)⁻¹ from PadicInt.norm_p (p:=2)]
    exact bound.trans_lt (by norm_num)
  obtain ⟨x,h,_⟩ := PowerfulLocal.adjustSquare 1 1 t isUnit_one small
  refine ⟨x,?_⟩
  dsimp [t] at h
  linear_combination h

theorem count_lower (c n k : ℕ) (hc : n%8=(c+2)%8) :
    let M := 2^(k+3)
    let X := range M
    (2^k)^2 ≤ ((X ×ˢ (X ×ˢ X)).filter (fun u ↦
      (u.1^2+u.2.1^2+c*u.2.2^2)%M=n%M)).card := by
  intro M X
  have eqM : M=8*2^k := by dsimp [M]; rw [pow_add]; ring
  have mpos : 0 < M := by dsimp [M]; positivity
  let choose (i j : ℕ) := (choose_square c n (8*i+1) (8*j+1) hc (by omega) (by omega)).choose
  let coord (i j : ℕ) := (PadicInt.toZModPow (p:=2) (k+3) (choose i j)).val
  let f (u : ℕ × ℕ) := (coord u.1 u.2,8*u.1+1,8*u.2+1)
  have inj : Function.Injective f := by
    intro u v he
    have h₁ := congrArg (fun w : ℕ × ℕ × ℕ ↦ w.2.1) he
    have h₂ := congrArg (fun w : ℕ × ℕ × ℕ ↦ w.2.2) he
    simp only [f] at h₁ h₂
    apply Prod.ext <;> omega
  have mem (u : ℕ × ℕ) (hu : u ∈ range (2^k) ×ˢ range (2^k)) :
      f u ∈ (X ×ˢ (X ×ˢ X)).filter
        (fun v ↦ (v.1^2+v.2.1^2+c*v.2.2^2)%M=n%M) := by
    obtain ⟨h₁,h₂⟩ := mem_product.mp hu
    rw [mem_range] at h₁ h₂
    apply mem_filter.mpr
    refine ⟨mem_product.mpr ⟨mem_range.mpr (ZMod.val_lt _),
      mem_product.mpr ⟨mem_range.mpr (by change 8*u.1+1< M; omega),
        mem_range.mpr (by change 8*u.2+1< M; omega)⟩⟩,?_⟩
    have he := congrArg (PadicInt.toZModPow (p:=2) (k+3))
      (choose_square c n (8*u.1+1) (8*u.2+1) hc (by omega) (by omega)).choose_spec
    simp only [map_add,map_pow,map_mul,map_natCast] at he
    apply (ZMod.natCast_eq_natCast_iff ..).mp
    change (((coord u.1 u.2)^2+(8*u.1+1)^2+c*(8*u.2+1)^2 : ℕ) : ZMod M) = n
    push_cast
    simpa only [coord,choose,ZMod.natCast_zmod_val,Nat.cast_add,Nat.cast_mul,
      Nat.cast_one,Nat.cast_ofNat] using he
  simpa only [card_product,card_range,pow_two] using
    (Finset.card_le_card_of_injOn f mem inj.injOn)

end PowerfulDyadic
end

section
open Filter

namespace PowerfulMass

/-- A lower bound for the Euler product with exponent −1/200 gives the
genus exponent 49/100, with room for the two fixed bad local factors. -/
theorem archimedean :
    ∀ᶠ n : ℕ in atTop, ∀ c ∈ ({25,125} : Finset ℕ), ∀ d P : ℝ,
      (n:ℝ)^(-(1:ℝ)/200) ≤ P → P/3200 ≤ d →
      (n:ℝ)^((49:ℝ)/100) ≤ 2*Real.pi*Real.sqrt ((n:ℝ)/c)*d := by
  have growth : Tendsto (fun n : ℕ ↦ (n:ℝ)^((1:ℝ)/200)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/200)).comp tendsto_natCast_atTop_atTop
  filter_upwards [growth.eventually_ge_atTop 40000,eventually_gt_atTop 0] with n big hn
  intro c hc d P product density
  have npos : (0:ℝ)<n := by exact_mod_cast hn
  have cp : (0:ℝ)<c := by simp only [Finset.mem_insert,Finset.mem_singleton] at hc; rcases hc with rfl|rfl <;> norm_num
  have small : Real.sqrt c ≤ 12 := by
    simp only [Finset.mem_insert,Finset.mem_singleton] at hc
    rcases hc with rfl|rfl <;> norm_num [Real.sqrt_le_iff]
  have Ppos : 0 < P := (Real.rpow_pos_of_pos npos _).trans_le product
  have dpos : 0 ≤ d := (by positivity : 0 ≤ P/3200).trans density
  have sq : Real.sqrt n ≤ 12 * Real.sqrt ((n:ℝ)/c) := by
    rw [Real.sqrt_div npos.le]
    rw [← mul_div_assoc]
    exact (le_div_iff₀ (Real.sqrt_pos.2 cp)).2 (by nlinarith [mul_nonneg (Real.sqrt_nonneg (n:ℝ)) (sub_nonneg.mpr small)])
  have coef : Real.sqrt n * P ≤ 40000 * (2*Real.pi*Real.sqrt ((n:ℝ)/c)*d) := by
    calc
      _ ≤ (12 * Real.sqrt ((n:ℝ)/c)) * (3200*d) :=
        mul_le_mul sq (by linarith : P ≤ 3200*d) (le_of_lt Ppos) (by positivity)
      _ ≤ _ := by
        have q : 0 ≤ (80000*Real.pi-38400)*(Real.sqrt ((n:ℝ)/c)*d) :=
          mul_nonneg (by linarith [Real.pi_gt_three]) (by positivity)
        linarith only [q]
  have expcmp : 40000 * (n:ℝ)^((49:ℝ)/100) ≤ Real.sqrt n * P := by
    calc
      _ ≤ (n:ℝ)^((1:ℝ)/200) * (n:ℝ)^((49:ℝ)/100) :=
        mul_le_mul_of_nonneg_right big (Real.rpow_nonneg npos.le _)
      _ = Real.sqrt n * (n:ℝ)^(-(1:ℝ)/200) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_add npos, ← Real.rpow_add npos]
        norm_num
      _ ≤ _ := mul_le_mul_of_nonneg_left product (Real.sqrt_nonneg _)
  linarith

end PowerfulMass
end

section
namespace PowerfulMass
open Filter Finset

/-- Apply the finite local factorization at (k+1)! and absorb the fixed
exceptional-prime and archimedean constants. -/
theorem jacobi_lower (arithmetic : ∀ᶠ n : ℕ in atTop, ∀ c ∈ ({25,125}:Finset ℕ),
    n.Coprime (16*c) → ∀ᶠ K : ℕ in atTop,
    (n:ℝ)^(-(1:ℝ)/200) ≤ ∏ p ∈ (range (K+1)).filter (fun p => p.Prime ∧ ¬p∣10*n),
      (1+(jacobiSym (-(c:ℤ)*n) p:ℝ)/p))
    (local_factors : ∀ c n K : ℕ, c ∈ ({25,125}:Finset ℕ) →
      n.Coprime (16*c) → n%8=(c+2)%8 → 8≤K →
      let M := K.factorial
      let X := range M
      (∏ p ∈ (range (K+1)).filter (fun p => p.Prime ∧ ¬p∣10*n),
        (1+(jacobiSym (-(c:ℤ)*n) p:ℝ)/p))/3200 ≤
      (((X ×ˢ (X ×ˢ X)).filter (fun t ↦
        (t.1^2+t.2.1^2+c*t.2.2^2)%M=n%M)).card:ℝ)/(M:ℝ)^2) :
    ∀ᶠ n : ℕ in atTop, ∀ c ∈ ({25,125} : Finset ℕ), n.Coprime (16*c) →
    n%8=(c+2)%8 →
    (∀ (p : ℕ) (hp : p.Prime), letI : Fact p.Prime := ⟨hp⟩
      ∃ x y z : ℤ_[p], x^2+y^2+(c:ℤ_[p])*z^2=n ∧
        (IsUnit x ∨ IsUnit y ∨ IsUnit ((c:ℤ_[p])*z))) →
    ∀ᶠ k : ℕ in atTop,
      let M := (k+1).factorial
      let X := range M
      let A := ((X ×ˢ (X ×ˢ X)).filter (fun t ↦
        (t.1^2+t.2.1^2+c*t.2.2^2)%M=n%M)).card
      (n:ℝ)^((49:ℝ)/100) ≤ 2 * Real.pi * Real.sqrt ((n:ℝ)/c) * (A:ℝ) / (M:ℝ)^2 := by
  filter_upwards [arithmetic, archimedean] with n primes arch
  intro c hc cop res _
  obtain ⟨K₀,hK₀⟩ := eventually_atTop.mp (primes c hc cop)
  filter_upwards [eventually_ge_atTop (max K₀ 8)] with k hk
  have hs := local_factors c n (k+1) hc cop res (by omega)
  have hg := arch c hc _ _ (hK₀ (k+1) (by omega)) hs
  simpa only [mul_div_assoc] using hg

end PowerfulMass
end

section
namespace PowerfulDensity
open Finset

/-- Identifying natural representatives with their residue classes preserves the exact
cardinality of the solution set of a diagonal ternary congruence. -/
theorem modular_count (M c n : ℕ) [NeZero M] :
    (((range M ×ˢ (range M ×ˢ range M)).filter fun t =>
      (t.1^2+t.2.1^2+c*t.2.2^2)%M=n%M).card) =
      Fintype.card {t : ZMod M × ZMod M × ZMod M //
        t.1^2+t.2.1^2+(c : ZMod M)*t.2.2^2=n} := by
  classical
  let B := (range M ×ˢ (range M ×ˢ range M)).filter fun t =>
      (t.1^2+t.2.1^2+c*t.2.2^2)%M=n%M
  have mem (x y z : ℕ) : (x,y,z) ∈ B ↔ x< M ∧ y< M ∧ z< M ∧
      ((x:ZMod M)^2+(y:ZMod M)^2+(c:ZMod M)*(z:ZMod M)^2=(n:ZMod M)) := by
    simp only [B,mem_filter,mem_product,mem_range, ←ZMod.natCast_eq_natCast_iff', Nat.cast_add,
      Nat.cast_pow,Nat.cast_mul]
    tauto
  let T := {t : ZMod M × ZMod M × ZMod M // t.1^2+t.2.1^2+(c:ZMod M)*t.2.2^2=n}
  change B.card = Fintype.card T
  rw [←Fintype.card_coe]
  apply Fintype.card_congr
  refine ⟨fun u => ⟨((u.1.1 : ZMod M),(u.1.2.1 : ZMod M),(u.1.2.2 : ZMod M)),
    ((mem ..).mp u.2).2.2.2⟩, fun v => ⟨(v.1.1.val,v.1.2.1.val,v.1.2.2.val), (mem ..).mpr
      ⟨ZMod.val_lt _,ZMod.val_lt _,ZMod.val_lt _,by simpa only [ZMod.natCast_zmod_val] using v.2⟩⟩,?_,?_⟩
  · rintro ⟨⟨x,y,z⟩,h⟩
    obtain ⟨hx,hy,hz,_⟩ := (mem ..).mp h
    apply Subtype.ext
    exact Prod.ext (ZMod.val_natCast_of_lt hx)
      (Prod.ext (ZMod.val_natCast_of_lt hy) (ZMod.val_natCast_of_lt hz))
  · rintro ⟨⟨x,y,z⟩,h⟩
    apply Subtype.ext
    exact Prod.ext (ZMod.natCast_zmod_val _) (Prod.ext (ZMod.natCast_zmod_val _) (ZMod.natCast_zmod_val _))

theorem range_eq_zmod (M c n : ℕ) [NeZero M] :
    (((range M ×ˢ (range M ×ˢ range M)).filter fun t =>
      (t.1^2+t.2.1^2+c*t.2.2^2)%M=n%M).card) =
       ((univ : Finset (ZMod M × ZMod M × ZMod M)).filter fun t =>
        t.1^2+t.2.1^2+(c : ZMod M)*t.2.2^2=n).card := by
  rw [modular_count]
  exact Fintype.card_subtype _

theorem zmod_count_mul (a b c n : ℕ) [NeZero a] [NeZero b] [NeZero (a*b)] (cop : a.Coprime b) :
    let N (M : ℕ) [NeZero M] := Fintype.card {t : ZMod M × ZMod M × ZMod M //
      t.1^2+t.2.1^2+(c : ZMod M)*t.2.2^2=n}
    N (a*b) = N a * N b := by
  intro N
  let Z (M : ℕ) := {t : ZMod M × ZMod M × ZMod M // t.1^2+t.2.1^2+(c:ZMod M)*t.2.2^2=n}
  let g := ZMod.chineseRemainder cop
  have compat (x y z : ZMod (a*b)) :
      x^2+y^2+(c:ZMod (a*b))*z^2=n ↔
      (g x).1^2+(g y).1^2+(c:ZMod a)*(g z).1^2=n ∧
      (g x).2^2+(g y).2^2+(c:ZMod b)*(g z).2^2=n := by
    rw [←g.injective.eq_iff]
    simp only [map_add,map_mul,map_natCast,Prod.ext_iff,Prod.fst_add,Prod.snd_add,
      Prod.fst_mul,Prod.snd_mul,sq,Prod.fst_natCast,Prod.snd_natCast]
  let e : Z (a*b) ≃ Z a × Z b := {
    toFun := fun ⟨⟨x,y,z⟩,h⟩ =>
      (⟨((g x).1,(g y).1,(g z).1),((compat x y z).mp h).1⟩,
       ⟨((g x).2,(g y).2,(g z).2),((compat x y z).mp h).2⟩)
    invFun := fun ⟨⟨⟨x,y,z⟩,h⟩,⟨⟨u,v,w⟩,k⟩⟩ =>
      ⟨(g.symm (x,u),g.symm (y,v),g.symm (z,w)), (compat ..).mpr
        (by simpa only [RingEquiv.apply_symm_apply] using And.intro h k)⟩
    left_inv := by
      rintro ⟨⟨x,y,z⟩,h⟩
      apply Subtype.ext
      simp
    right_inv := by
      rintro ⟨⟨⟨x,y,z⟩,h⟩,⟨⟨u,v,w⟩,k⟩⟩
      apply Prod.ext <;> apply Subtype.ext <;> simp }
  exact (Fintype.card_congr e).trans (Fintype.card_prod _ _)

theorem crt_count (c n a b : ℕ) (cop : a.Coprime b) (ha : 0<a) (hb : 0<b) :
    let S (M : ℕ) := ((range M ×ˢ (range M ×ˢ range M)).filter fun t =>
      (t.1^2+t.2.1^2+c*t.2.2^2)%M=n%M).card
    S (a*b) = S a * S b := by
  intro S
  have : NeZero a := ⟨ha.ne'⟩
  have : NeZero b := ⟨hb.ne'⟩
  have : NeZero (a*b) := ⟨(Nat.mul_pos ha hb).ne'⟩
  calc S (a*b) = _ := modular_count (a*b) c n
       _ = _ := zmod_count_mul a b c n cop
       _ = _ := congrArg₂ (· * ·) (modular_count a c n).symm (modular_count b c n).symm

end PowerfulDensity
end

section
namespace PowerfulDensity

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The character correction to the number of square roots in odd characteristic. -/
theorem count_roots (odd : ringChar F ≠ 2) (a : F) :
    (∑ x : F, (if x^2 = a then (1:ℤ) else 0)) = quadraticChar F a + 1 := by
  simpa [Finset.sum_boole, Set.toFinset_ofPred] using quadraticChar_card_sqrts odd a

/-- The quadratic character summed on a translated square. For a nonzero
translation the change of variables (x,y) ↦ (x+y,x−y) identifies the conic
with the multiplicative group. -/
theorem sum_character_square_sub (odd : ringChar F ≠ 2) (t : F) :
    ∑ x : F, quadraticChar F (x^2-t) = if t=0 then (Fintype.card F : ℤ)-1 else -1 := by
  classical
  by_cases z : t=0
  · subst t
    have chi (x : F) : quadraticChar F (x^2) = if x=0 then 0 else 1 := by
      split_ifs with h
      · simp [h]
      · rw [map_pow,quadraticChar_sq_one h]
    rw [if_pos rfl]
    simp only [sub_zero,chi]
    have h (x:F) : (if x=0 then (0:ℤ) else 1) = 1 - (if x=0 then 1 else 0) := by split_ifs <;> simp
    simp only [h,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
    simp
  rw [if_neg z]
  let X := Σ x : F, {y : F // y^2=x^2-t}
  have two : (2:F) ≠ 0 := Ring.two_ne_zero odd
  let a (u : X) : F := u.1+u.2.val
  have prod (u : X) : a u * (u.1-u.2.val) = t := by dsimp [a]; linear_combination -u.2.property
  have nz (u : X) : a u ≠ 0 := fun h => z (by simpa [h] using (prod u).symm)
  let p (w : Fˣ) := ((w:F)+t/(w:F))/2
  let q (w : Fˣ) := ((w:F)-t/(w:F))/2
  have pq (w : Fˣ) : (q w)^2=(p w)^2-t := by
    dsimp [p,q]
    field_simp [two,w.ne_zero]
    ring
  let e : X ≃ Fˣ := {
    toFun := fun u => Units.mk0 (a u) (nz u)
    invFun := fun w => ⟨p w, q w, pq w⟩
    left_inv := by
      intro u
      have ratio : t/(a u) = u.1-u.2.val := (div_eq_iff (nz _)).mpr (by simpa [mul_comm] using (prod u).symm)
      have first : p (Units.mk0 _ (nz u)) = u.1 := by
        change (a u + t/(a u))/2 = _
        rw [ratio, div_eq_iff two]
        dsimp [a]
        ring
      have second : q (Units.mk0 _ (nz u)) = u.2.val := by
        change (a u - t/(a u))/2 = _
        rw [ratio, div_eq_iff two]
        dsimp [a]
        ring
      apply Sigma.ext first
      apply (Subtype.heq_iff_coe_eq ?_).mpr second
      intro y
      change (y^2=(p (Units.mk0 _ (nz u)))^2-t) ↔ y^2=u.1^2-t
      rw [first]
    right_inv := by
      intro w
      apply Units.ext
      change p w + q w = w
      dsimp [p,q]
      field_simp [two]
      ring }
  have size := Fintype.card_congr e
  change Fintype.card (Σ x : F, {y : F // y^2=x^2-t}) = _ at size
  rw [Fintype.card_sigma] at size
  have roots (x : F) : (Fintype.card {y : F // y^2=x^2-t} : ℤ) = quadraticChar F (x^2-t)+1 := by
    rw [Fintype.card_subtype]
    simpa only [Finset.sum_boole] using count_roots odd (x^2-t)
  have card := congrArg (fun n : ℕ => (n:ℤ)) size
  simp only [Nat.cast_sum,roots,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] at card
  have u := Fintype.card_eq_card_units_add_one (α := F)
  omega

end PowerfulDensity

namespace PowerfulDensity

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem binary_count (odd : ringChar F ≠ 2) (t : F) :
    ∑ x : F, ∑ y : F, (if x^2+y^2=t then (1:ℤ) else 0) =
      Fintype.card F - quadraticChar F (-1) +
        (Fintype.card F * quadraticChar F (-1)) * (if t=0 then 1 else 0) := by
  have term (x : F) : (∑ y : F, if x^2+y^2=t then (1:ℤ) else 0) =
      quadraticChar F (-1) * quadraticChar F (x^2-t) + 1 := by
    have root := count_roots odd (t-x^2)
    have eq (y:F) : x^2+y^2=t ↔ y^2=t-x^2 := by constructor <;> intro h <;> linear_combination h
    simp_rw [eq]
    rw [root, show t-x^2 = (-1)*(x^2-t) by ring, map_mul]
  simp_rw [term]
  rw [Finset.sum_add_distrib, ←Finset.mul_sum, sum_character_square_sub odd]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
  split_ifs <;> ring

/-- The exact size of every level set of a nondegenerate diagonal ternary form
x²+y²+c z² over a finite field of odd characteristic. -/
theorem ternary_count (odd : ringChar F ≠ 2) (c n : F) (hc : c ≠ 0) :
    ∑ z : F, ∑ x : F, ∑ y : F, (if x^2+y^2+c*z^2=n then (1:ℤ) else 0) =
      (Fintype.card F : ℤ)^2 + Fintype.card F * quadraticChar F (-c*n) := by
  have eq (x y z:F) : x^2+y^2+c*z^2=n ↔ x^2+y^2=n-c*z^2 := by
    constructor <;> intro h <;> linear_combination h
  have perm (z:F) : n-c*z^2=0 ↔ z^2=n/c := by
    rw [eq_div_iff hc,sub_eq_zero,mul_comm]
    exact eq_comm
  simp_rw [eq, binary_count odd,perm]
  rw [Finset.sum_add_distrib,← Finset.mul_sum, count_roots odd, Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have mult : quadraticChar F (n/c) * quadraticChar F c = quadraticChar F n := by rw [← map_mul,div_mul_cancel₀ _ hc]
  have inv : quadraticChar F (n/c) = quadraticChar F c * quadraticChar F n := by
    rw [← mult, ← mul_assoc, mul_comm (quadraticChar F c),mul_assoc, ←sq,quadraticChar_sq_one hc,mul_one]
  rw [inv, show -c*n=(-1)*c*n by ring, map_mul, map_mul]
  ring

/-- Count as the cardinality of the actual set of solutions. -/
theorem card_ternary (odd : ringChar F ≠ 2) (c n : F) (hc : c ≠ 0) :
    ((Finset.univ.filter fun u : F × F × F => u.2.1^2+u.2.2^2+c*u.1^2=n).card : ℤ) =
      (Fintype.card F : ℤ)^2 + Fintype.card F * quadraticChar F (-c*n) := by
  rw [← Finset.sum_boole]
  simpa only [Fintype.sum_prod_type] using ternary_count odd c n hc

end PowerfulDensity

namespace PowerfulDensity

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem line_count (a b t : F) (hb : b ≠ 0) :
    ∑ x : F, (if a+b*x=t then (1:ℕ) else 0) = 1 := by
  have eq (x:F) : a+b*x=t ↔ x=(t-a)/b := by
    rw [eq_div_iff hb, mul_comm x]
    constructor <;> intro h <;> linear_combination h
  simp_rw [eq]
  simp

theorem plane_count (a b c t : F) (nz : a≠0 ∨ b≠0 ∨ c≠0) :
    ∑ x : F, ∑ y : F, ∑ z : F, (if a*x+b*y+c*z=t then (1:ℕ) else 0) =
      Fintype.card F ^ 2 := by
  rcases nz with ha | hb | hc
  · rw [Finset.sum_comm]
    have row (y:F) : ∑ x : F, ∑ z : F, (if a*x+b*y+c*z=t then (1:ℕ) else 0) = Fintype.card F := by
      rw [Finset.sum_comm]
      simp_rw [show ∀ x y z : F, a*x+b*y+c*z=(b*y+c*z)+a*x from fun _ _ _ => by ring,
        line_count _ _ _ ha]
      simp
    simp only [row, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id, pow_two]
  · have row (x:F) : ∑ y : F, ∑ z : F, (if a*x+b*y+c*z=t then (1:ℕ) else 0) = Fintype.card F := by
      rw [Finset.sum_comm]
      simp_rw [show ∀ x y z : F, a*x+b*y+c*z=(a*x+c*z)+b*y from fun _ _ _ => by ring,
        line_count _ _ _ hb]
      simp
    simp only [row, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id, pow_two]
  · simp_rw [line_count _ _ _ hc]
    simp [pow_two]

/-- A congruence modulo mp over a fixed solution modulo m imposes one affine
linear equation on the three new base-p digits, whenever p divides m. -/
theorem lift_criterion {p : ℕ} [Fact p.Prime] {m : ℕ} (hm : 0 < m) (pm : p ∣ m)
    (c n x y z t : ℤ) (old : x^2+y^2+c*z^2-n=(m:ℤ)*t) (i j k : ZMod p) :
    ((m:ℤ)*p) ∣ (x+m*i.val)^2+(y+m*j.val)^2+c*(z+m*k.val)^2-n ↔
    ((2*x : ℤ) : ZMod p)*i + ((2*y : ℤ) : ZMod p)*j + ((2*c*z : ℤ):ZMod p)*k = -(t:ZMod p) := by
  have expanded :
      (x+m*i.val)^2+(y+m*j.val)^2+c*(z+m*k.val)^2-n =
        m*(t+2*x*i.val+2*y*j.val+2*c*z*k.val+m*((i.val:ℤ)^2+j.val^2+c*k.val^2)) := by
    linear_combination old
  have mne : (m:ℤ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [expanded, mul_dvd_mul_iff_left mne, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have zm : (m:ZMod p) = 0 := (ZMod.natCast_eq_zero_iff m p).mpr pm
  push_cast
  simp only [ZMod.natCast_zmod_val,zm,zero_mul,add_zero]
  constructor <;> intro h <;> linear_combination h

theorem card_as_sum {V : Type*} [Fintype V] (P : V → Prop) [DecidablePred P] :
    (Finset.univ.filter P).card = ∑ v, if P v then (1:ℕ) else 0 := by
  simpa only [Nat.cast_id] using (Finset.sum_boole (R := ℕ) P Finset.univ).symm

/-- Each primitive level-m solution has exactly p² lifts with digits in
0,…,p−1, in the unshifted integral form of the congruence. -/
theorem lift_card {p : ℕ} [Fact p.Prime] {m : ℕ} (hm : 0 < m) (pm : p ∣ m)
    (c n x y z : ℤ) (old : (m:ℤ) ∣ x^2+y^2+c*z^2-n)
    (nonzero : ((2*x : ℤ) : ZMod p) ≠ 0 ∨ ((2*y : ℤ) : ZMod p) ≠ 0 ∨ ((2*c*z : ℤ) : ZMod p) ≠ 0) :
    (Finset.univ.filter (fun u : ZMod p × ZMod p × ZMod p =>
      ((m:ℤ)*p) ∣ (x+m*u.1.val)^2+(y+m*u.2.1.val)^2+c*(z+m*u.2.2.val)^2-n)).card = p^2 := by
  obtain ⟨t, ht⟩ := old
  have eq := plane_count (t := -(t:ZMod p)) _ _ _ nonzero
  rw [card_as_sum]
  simp only [Fintype.sum_prod_type, lift_criterion hm pm c n x y z t ht]
  simpa only [ZMod.card] using eq

end PowerfulDensity

namespace PowerfulDensity
open Finset
open scoped Classical

set_option maxHeartbeats 1700000 in
theorem odd_density_factors :
    (∀ (p e c n : ℕ) [Fact p.Prime] (_odd : p ≠ 2) (_unit : (c:ZMod p)≠0),
    let M := p^(e+1)
    let val := ((((range M ×ˢ (range M ×ˢ range M)).filter fun u =>
      (u.1^2+u.2.1^2+c*u.2.2^2)%M=n%M).card:ℝ) / (M:ℝ)^2)
    (if (n:ZMod p)=0 then 1-1/(p:ℝ)^2 else 1+(quadraticChar (ZMod p) (-(c:ZMod p)*n):ℝ)/p) ≤ val ∧
      ((n:ZMod p)≠0 → val = 1+(quadraticChar (ZMod p) (-(c:ZMod p)*n):ℝ)/p)) ∧
    (∀ (e c n : ℕ) (_hc : (c:ZMod 5)=0) (_hn : (n:ZMod 5)≠0),
    let M := 5^(e+1)
    ((((range M ×ˢ (range M ×ˢ range M)).filter fun u =>
      (u.1^2+u.2.1^2+c*u.2.2^2)%M=n%M).card:ℝ) / (M:ℝ)^2) = 4/5) := by
  classical
  let Cube (V : Type) := V × V × V

  let smooth (p : ℕ) (c x y z : ℤ) : Prop :=
    ((2*x:ℤ):ZMod p) ≠ 0 ∨ ((2*y:ℤ):ZMod p) ≠ 0 ∨ ((2*c*z:ℤ):ZMod p) ≠ 0

  let primitiveCount (p m : ℕ) (c n : ℤ) : ℕ :=
    ∑ u : Cube (Fin m),
      if ((m:ℤ) ∣ (u.1.val:ℤ)^2 + (u.2.1.val:ℤ)^2 + c*(u.2.2.val:ℤ)^2-n) ∧
        smooth p c u.1.val u.2.1.val u.2.2.val then 1 else 0

  let mixedDigits {α β γ : Type} (e : α × β ≃ γ) : Cube α × Cube β ≃ Cube γ := {
    toFun | ⟨⟨a,b,c⟩,⟨i,j,k⟩⟩ => (e (a,i), e (b,j), e (c,k))
    invFun | ⟨u,v,w⟩ => (((e.symm u).1,(e.symm v).1,(e.symm w).1),
      ((e.symm u).2,(e.symm v).2,(e.symm w).2))
    left_inv := by rintro ⟨⟨a,b,c⟩,⟨i,j,k⟩⟩; simp
    right_inv := by rintro ⟨u,v,w⟩; simp }

  let digitIndex (p m : ℕ) [NeZero p] : Fin m × ZMod p ≃ Fin (p*m) :=
    let z : ZMod p ≃ Fin p := {
      toFun := fun i => ⟨i.val, ZMod.val_lt i⟩
      invFun := fun i => (i.val:ZMod p)
      left_inv := ZMod.natCast_zmod_val
      right_inv := fun i => Fin.ext (ZMod.val_natCast_of_lt i.isLt) }
    ((Equiv.prodComm _ _).trans (z.prodCongr (Equiv.refl _))).trans finProdFinEquiv

  have digitIndex_val {p m : ℕ} [NeZero p] (a : Fin m) (i : ZMod p) :
      (digitIndex p m (a,i)).val = a.val+m*i.val := rfl

  have smooth_fiber {p : ℕ} [Fact p.Prime] {m : ℕ} (hm : 0< m) (pm : p∣m) (c n x y z : ℤ) :
      (∑ v : Cube (ZMod p), if
        ((m:ℤ)*p ∣ (x+m*v.1.val)^2+(y+m*v.2.1.val)^2+c*(z+m*v.2.2.val)^2-n) ∧
        smooth p c (x+m*v.1.val) (y+m*v.2.1.val) (z+m*v.2.2.val) then (1:ℕ) else 0)
      = p^2 * (if (m:ℤ) ∣ x^2+y^2+c*z^2-n ∧ smooth p c x y z then 1 else 0) := by
    have zm : (m:ZMod p) = 0 := (ZMod.natCast_eq_zero_iff m p).mpr pm
    have stays (v : Cube (ZMod p)) : smooth p c (x+m*v.1.val) (y+m*v.2.1.val) (z+m*v.2.2.val) ↔ smooth p c x y z := by
      simp [smooth,zm]
    simp_rw [stays]
    by_cases nonzero : smooth p c x y z
    · simp only [nonzero,and_true]
      by_cases old : (m:ℤ) ∣ x^2+y^2+c*z^2-n
      · rw [if_pos old,mul_one,← card_as_sum]
        exact lift_card hm pm c n x y z old nonzero
      · rw [if_neg old,mul_zero]
        apply Finset.sum_eq_zero
        intro v _
        apply if_neg
        intro h
        have dv := dvd_trans (dvd_mul_right (m:ℤ) (p:ℤ)) h
        have diff : (m:ℤ) ∣ ((x+m*v.1.val)^2+(y+m*v.2.1.val)^2+c*(z+m*v.2.2.val)^2-n)
              -(x^2+y^2+c*z^2-n) := ⟨2*x*v.1.val+2*y*v.2.1.val+2*c*z*v.2.2.val +
                m*((v.1.val:ℤ)^2+v.2.1.val^2+c*v.2.2.val^2), by ring⟩
        exact old (by simpa only [sub_sub_cancel] using dvd_sub dv diff)
    · simp [nonzero]

  have primitiveCount_step {p : ℕ} [Fact p.Prime] {m : ℕ} (hm : 0< m) (pm : p∣m) (c n : ℤ) :
      primitiveCount p (p*m) c n = p^2 * primitiveCount p m c n := by
    classical
    let e := mixedDigits (digitIndex p m)
    let hit (u : Cube (Fin (p*m))) : ℕ := if
      (((p*m:ℕ):ℤ) ∣ (u.1.val:ℤ)^2 + (u.2.1.val:ℤ)^2 + c*(u.2.2.val:ℤ)^2 - n) ∧
        smooth p c u.1.val u.2.1.val u.2.2.val then 1 else 0
    change (∑ u : Cube (Fin (p*m)), hit u) = _
    rw [← Equiv.sum_comp e hit, Fintype.sum_prod_type]
    unfold primitiveCount
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    obtain ⟨a,b,d⟩ := u
    simp only [e,mixedDigits,Equiv.coe_fn_mk,hit,Nat.cast_mul]
    rw [Int.mul_comm (p:ℤ) (m:ℤ)]
    exact smooth_fiber hm pm c n a.val b.val d.val

  have primitiveCount_pow (p : ℕ) [Fact p.Prime] (c n : ℤ) (e : ℕ) :
      primitiveCount p (p^(e+1)) c n = (p^2)^e * primitiveCount p p c n := by
    induction e with
    | zero => simp
    | succ e ih =>
      rw [pow_succ' p (e+1), primitiveCount_step (pow_pos (Fact.out : p.Prime).pos _)
        (dvd_pow_self p (Nat.succ_ne_zero e)), ih, pow_succ' (p^2), mul_assoc]

  have smooth_mod_prime {p : ℕ} [Fact p.Prime] (odd : p ≠ 2) {c : ℤ}
      (unit : (c:ZMod p) ≠ 0) (x y z : ℤ) :
      smooth p c x y z ↔ ((x:ZMod p),(y:ZMod p),(z:ZMod p)) ≠ (0 : Cube (ZMod p)) := by
    have two : (2:ZMod p) ≠ 0 := Ring.two_ne_zero (by rwa [ZMod.ringChar_zmod_n])
    simp [smooth,two,unit,Prod.ext_iff]
    tauto

  have reordered_count {F : Type} [Field F] [Fintype F] [DecidableEq F]
      (odd : ringChar F ≠ 2) (c n : F) (unit : c ≠ 0) :
      ∑ x:F, ∑ y:F, ∑ z:F, (if x^2+y^2+c*z^2=n then (1:ℤ) else 0) =
        (Fintype.card F:ℤ)^2 + Fintype.card F * quadraticChar F (-c*n) := by
    rw [← ternary_count odd c n unit, Finset.sum_comm (f := fun z x => ∑ y:F, (if x^2+y^2+c*z^2=n then (1:ℤ) else 0))]
    exact Finset.sum_congr rfl (fun x _ => Finset.sum_comm)

  have primitiveCount_prime (p : ℕ) [Fact p.Prime] (odd : p ≠ 2) (c n : ℤ)
      (unit : (c:ZMod p) ≠ 0) :
      (primitiveCount p p c n : ℤ) = (p:ℤ)^2+p * quadraticChar (ZMod p) (-(c:ZMod p)*n)
        - if (n:ZMod p) = 0 then 1 else 0 := by
    let Z := ZMod p
    let e : Fin p ≃ Z := {
      toFun := fun i => (i.val:ZMod p)
      invFun := fun a => ⟨a.val,ZMod.val_lt a⟩
      left_inv := fun i => Fin.ext (ZMod.val_natCast_of_lt i.isLt)
      right_inv := ZMod.natCast_zmod_val }
    let v := e.prodCongr (e.prodCongr e)
    let hit (q : Cube Z) := q.1^2+q.2.1^2+(c:Z)*q.2.2^2=(n:Z)
    let ind (q : Cube Z) : ℤ := if hit q ∧ q≠0 then 1 else 0
    have model : (primitiveCount p p c n : ℤ) = ∑ q:Cube Z, ind q := by
      rw [← Equiv.sum_comp v ind]
      simp only [primitiveCount,Nat.cast_sum]
      apply Finset.sum_congr rfl
      intro q _
      obtain ⟨x,y,z⟩ := q
      change ((if ((p:ℤ) ∣ (x.val:ℤ)^2 + (y.val:ℤ)^2+c*(z.val:ℤ)^2-n) ∧ smooth p c x.val y.val z.val then 1 else 0 : ℕ) : ℤ) =
        (if ((x.val:ZMod p)^2 + (y.val:ZMod p)^2+(c:ZMod p)*(z.val:ZMod p)^2=n) ∧ ((x.val:ZMod p),(y.val:ZMod p),(z.val:ZMod p))≠(0:Cube (ZMod p)) then 1 else 0)
      simp only [smooth_mod_prime odd unit, ← ZMod.intCast_zmod_eq_zero_iff_dvd,Int.cast_sub,Int.cast_add,Int.cast_pow,Int.cast_mul,Int.cast_natCast,sub_eq_zero]
      split_ifs <;> rfl
    have decomp (q : Cube Z) :
        (if hit q then (1:ℤ) else 0) = ind q + (if q=0 then (if (n:Z)=0 then 1 else 0) else 0) := by
      by_cases zero : q=0
      · subst q
        simp [ind,hit,eq_comm]
      · simp [ind,zero]
    have full : (∑ q:Cube Z, if hit q then (1:ℤ) else 0) =
        (p:ℤ)^2+p * quadraticChar (ZMod p) (-(c:ZMod p)*n) := by
      simpa only [Cube,Fintype.sum_prod_type,hit,ZMod.card] using
        reordered_count (F := ZMod p) (by rwa [ZMod.ringChar_zmod_n]) (c:ZMod p) n unit
    rw [← full,model]
    simp_rw [decomp]
    rw [Finset.sum_add_distrib]
    have single : (∑ q:Cube Z, if q=0 then (if (n:Z)=0 then (1:ℤ) else 0) else 0) = (if (n:Z)=0 then 1 else 0) := by
      rw [Finset.sum_eq_single (0:Cube Z)]
      · simp only [if_true]
      · intro b _ ne
        exact if_neg ne
      · simp
    rw [single,add_sub_cancel_right]

  have primitiveCount_prime_power (p : ℕ) [Fact p.Prime] (odd : p ≠ 2) (c n : ℤ)
      (unit : (c:ZMod p) ≠ 0) (e : ℕ) :
      (primitiveCount p (p^(e+1)) c n : ℤ) = (p:ℤ)^(2*e) *
        ((p:ℤ)^2+p * quadraticChar (ZMod p) (-(c:ZMod p)*n) -
          if (n:ZMod p)=0 then 1 else 0) := by
    rw [primitiveCount_pow, Nat.cast_mul, Nat.cast_pow,Nat.cast_pow,primitiveCount_prime p odd c n unit,pow_mul]

  have raw_eq_digits (m : ℕ) [NeZero m] (c n : ℤ) :
      ((univ : Finset (Cube (ZMod m))).filter fun u => u.1^2+u.2.1^2+(c:ZMod m)*u.2.2^2=n).card =
      ∑ u : Cube (Fin m), if (m:ℤ) ∣ (u.1.val:ℤ)^2+(u.2.1.val:ℤ)^2+c*(u.2.2.val:ℤ)^2-n then 1 else 0 := by
    let e : Fin m ≃ ZMod m := {
      toFun := fun i => (i.val:ZMod m)
      invFun := fun a => ⟨a.val,ZMod.val_lt a⟩
      left_inv := fun i => Fin.ext (ZMod.val_natCast_of_lt i.isLt)
      right_inv := ZMod.natCast_zmod_val }
    let v := e.prodCongr (e.prodCongr e)
    let h (u : Cube (ZMod m)) : ℕ := if u.1^2+u.2.1^2+(c:ZMod m)*u.2.2^2=n then 1 else 0
    rw [card_as_sum]
    change (∑ u:Cube (ZMod m), h u) = _
    rw [← Equiv.sum_comp v h]
    apply Finset.sum_congr rfl
    rintro ⟨x,y,z⟩ _
    change (if (x.val:ZMod m)^2+(y.val:ZMod m)^2+(c:ZMod m)*(z.val:ZMod m)^2=n then (1:ℕ) else 0) = _
    simp only [←ZMod.intCast_zmod_eq_zero_iff_dvd,Int.cast_sub,Int.cast_add,Int.cast_pow,Int.cast_mul,Int.cast_natCast,sub_eq_zero]

  have primitive_le_raw (p m : ℕ) [NeZero m] (c n : ℤ) :
      primitiveCount p m c n ≤ ((univ : Finset (Cube (ZMod m))).filter fun u => u.1^2+u.2.1^2+(c:ZMod m)*u.2.2^2=n).card := by
    rw [raw_eq_digits]
    dsimp only [primitiveCount]
    apply Finset.sum_le_sum
    intro u _
    split_ifs with a b <;> first | decide | exact (b a.1).elim

  have raw_eq_primitive_unit {p m : ℕ} [Fact p.Prime] [NeZero m] (odd : p≠2) (pm : p∣m)
      (c n : ℤ) (unit : (n:ZMod p)≠0) :
      ((univ : Finset (Cube (ZMod m))).filter fun u => u.1^2+u.2.1^2+(c:ZMod m)*u.2.2^2=n).card =
        primitiveCount p m c n := by
    rw [raw_eq_digits]
    dsimp only [primitiveCount]
    have two : (2:ZMod p)≠0 := Ring.two_ne_zero (by rwa [ZMod.ringChar_zmod_n])
    apply Finset.sum_congr rfl
    rintro ⟨x,y,z⟩ _
    have hs : (m:ℤ)∣(x.val:ℤ)^2+(y.val:ℤ)^2+c*(z.val:ℤ)^2-n → smooth p c x.val y.val z.val := by
      intro old
      have h : (p:ℤ)∣(x.val:ℤ)^2+(y.val:ℤ)^2+c*(z.val:ℤ)^2-n := dvd_trans (by exact_mod_cast pm) old
      have h' := (ZMod.intCast_zmod_eq_zero_iff_dvd ..).mpr h
      push_cast at h'
      by_contra hbad
      simp only [smooth,Int.cast_mul,Int.cast_ofNat,Int.cast_natCast,not_or,not_not,mul_eq_zero,two,false_or] at hbad
      obtain ⟨hx,hy,hcz⟩ := hbad
      rcases hcz with hc|hz
      · exact unit (by simpa [hx,hy,hc] using h')
      · exact unit (by simpa [hx,hy,hz] using h')
    by_cases ok : (m:ℤ)∣(x.val:ℤ)^2+(y.val:ℤ)^2+c*(z.val:ℤ)^2-n
    · simp [ok, hs ok]
    · simp [ok]

  have raw_five_base (c n : ℤ) (hc : (c:ZMod 5)=0) (hn : (n:ZMod 5)≠0) :
      primitiveCount 5 5 c n = 20 := by
    let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
    rw [← raw_eq_primitive_unit (p:=5) (m:=5) (by decide) (dvd_refl _) c n hn]
    have base : ∀ a : ZMod 5, a≠0 → ((univ : Finset (Cube (ZMod 5))).filter fun x => x.1^2+x.2.1^2=a).card=20 := by decide +kernel
    simpa [hc] using base (n:ZMod 5) hn

  have raw_prime_factors (p e c n : ℕ) [Fact p.Prime] (odd : p ≠ 2) (unit : (c:ZMod p)≠0) :
      let M := p^(e+1)
      let val := ((((range M ×ˢ (range M ×ˢ range M)).filter fun u =>
        (u.1^2+u.2.1^2+c*u.2.2^2)%M=n%M).card:ℝ) / (M:ℝ)^2)
      (if (n:ZMod p)=0 then 1-1/(p:ℝ)^2 else 1+(quadraticChar (ZMod p) (-(c:ZMod p)*n):ℝ)/p) ≤ val ∧
        ((n:ZMod p)≠0 → val = 1+(quadraticChar (ZMod p) (-(c:ZMod p)*n):ℝ)/p) := by
    dsimp only
    rw [range_eq_zmod]
    let M := p^(e+1)
    let N := ((univ : Finset (Cube (ZMod M))).filter fun u => u.1^2+u.2.1^2+(c:ZMod M)*u.2.2^2=n).card
    let W := primitiveCount p M c n
    let X := quadraticChar (ZMod p) (-(c:ZMod p)*n)
    change (if (n:ZMod p)=0 then 1-1/(p:ℝ)^2 else 1+(X:ℝ)/p) ≤ (N:ℝ)/(M:ℝ)^2 ∧
      ((n:ZMod p)≠0 → (N:ℝ)/(M:ℝ)^2 = 1+(X:ℝ)/p)
    have h := primitiveCount_prime_power p odd (c:ℤ) n (by exact_mod_cast unit) e
    simp only [Int.cast_natCast] at h
    have calcW : (W:ℝ)=(p:ℝ)^(2*e)*((p:ℝ)^2+p*(X:ℝ) - (if (n:ZMod p)=0 then 1 else 0)) := by
      change ((primitiveCount p (p^(e+1)) c n):ℝ)=_
      dsimp only [X]
      by_cases z : (n:ZMod p)=0 <;> simp only [z,if_true,if_false] at h ⊢ <;> exact_mod_cast h
    have le : (W:ℝ) ≤ N := by
      exact_mod_cast (by simpa only [Int.cast_natCast] using primitive_le_raw p M (c:ℤ) n : W≤N)
    have pp : (0:ℝ)<p := by exact_mod_cast (Fact.out : p.Prime).pos
    have pp0 := pp.ne'
    have normalized : (W:ℝ)/(M:ℝ)^2 = (if (n:ZMod p)=0 then 1-1/(p:ℝ)^2 else 1+(X:ℝ)/p) := by
      rw [calcW]
      simp only [M,Nat.cast_pow]
      rw [pow_succ]
      rw [Nat.mul_comm 2 e,pow_mul]
      by_cases zero : (n:ZMod p)=0
      · have x0 : X=0 := by simp [X,zero]
        simp only [zero,x0,if_true,Int.cast_zero,mul_zero,add_zero]
        field_simp
        ring
      · simp only [zero,if_false,sub_zero]
        field_simp
        ring
    refine ⟨normalized ▸ div_le_div_of_nonneg_right le (sq_nonneg _),?_⟩
    intro nonz
    have eq : N=W := by
      simpa only [Int.cast_natCast] using raw_eq_primitive_unit odd (dvd_pow_self p (Nat.succ_ne_zero e)) (c:ℤ) n (by exact_mod_cast nonz)
    rw [eq, normalized, if_neg nonz]

  have raw_five_factor (e c n : ℕ) (hc : (c:ZMod 5)=0) (hn : (n:ZMod 5)≠0) :
      let M := 5^(e+1)
      ((((range M ×ˢ (range M ×ˢ range M)).filter fun u =>
        (u.1^2+u.2.1^2+c*u.2.2^2)%M=n%M).card:ℝ) / (M:ℝ)^2) = 4/5 := by
    dsimp only
    let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
    rw [range_eq_zmod]
    have h := raw_eq_primitive_unit (p:=5) (m:=5^(e+1)) (by decide) (dvd_pow_self 5 (Nat.succ_ne_zero e)) (c:ℤ) n (by exact_mod_cast hn)
    simp only [Int.cast_natCast] at h
    rw [h, primitiveCount_pow, raw_five_base (c:ℤ) n (by exact_mod_cast hc) (by exact_mod_cast hn)]
    push_cast
    rw [pow_succ]
    have powers : (25:ℝ)^e = ((5:ℝ)^e)^2 := by rw [←pow_mul,Nat.mul_comm, pow_mul]; norm_num
    field_simp
    simp only [powers,pow_succ]; ring

  exact ⟨raw_prime_factors,raw_five_factor⟩

end PowerfulDensity
end

section
namespace PowerfulDensity
open Finset

/-- The product from 2 through n+1 is (n+2)/(2(n+1)). Dropping any of
its factors can only increase it. -/
theorem euler_product_half (P : Finset ℕ) (large : ∀ p ∈ P, 2 ≤ p) :
    (1/2:ℝ) ≤ ∏ p ∈ P,(1-1/(p:ℝ)^2) := by
  have interval (n : ℕ) :
      (∏ p ∈ Ico 2 (n+2), (1-1/(p:ℝ)^2)) = ((n:ℝ)+2)/(2*((n:ℝ)+1)) := by
    induction n with
    | zero => norm_num
    | succ n ih =>
      rw [show n+1+2=n+2+1 by omega,prod_Ico_succ_top (by omega),ih]
      push_cast
      field_simp
      ring
  let n := P.sup id
  have sub : P ⊆ Ico 2 (n+2) := by
    intro p hp; exact mem_Ico.mpr ⟨large p hp,by have := Finset.le_sup (f:=id) hp; change p≤n at this; omega⟩
  calc
    _ ≤ ((n:ℝ)+2)/(2*((n:ℝ)+1)) := by
      apply (le_div_iff₀ (by positivity)).mpr
      linarith
    _ = _ := (interval n).symm
    _ ≤ _ := prod_le_prod_of_subset_of_le_one sub (fun p hp => by
      have hp' : (2:ℝ)≤p := by exact_mod_cast (mem_Ico.mp hp).1
      have hh : (1:ℝ)/p^2≤1 := (div_le_one (by positivity)).mpr (by nlinarith)
      linarith) (fun p _ _ => sub_le_self _ (by positivity))

end PowerfulDensity

namespace PowerfulDensity
open Finset

/-- Separate the two exceptional primes, the remaining prime divisors of n,
and the primes carrying the good local factor. -/
theorem density_euler_lower (P : Finset ℕ) (n : ℕ) (F g : ℕ → ℝ)
    (hprime : ∀ p ∈ P, p.Prime) (two : 2 ∈ P) (five : 5 ∈ P)
    (nonneg : ∀ p ∈ P, 0 ≤ F p)
    (g_nonneg : ∀ p ∈ P, p≠2 → p≠5 → ¬p∣n → 0≤g p)
    (p2 : 1/64 ≤ F 2) (p5 : 1/25 ≤ F 5)
    (bad : ∀ p ∈ P, p≠2 → p≠5 → p∣n → 1-1/(p:ℝ)^2 ≤ F p)
    (good : ∀ p ∈ P, p≠2 → p≠5 → ¬p∣n → g p ≤ F p) :
    (∏ p∈P.filter (fun p => p≠2 ∧ p≠5 ∧ ¬p∣n),g p)/3200 ≤ ∏ p∈P,F p := by
  let S := (P.erase 2).erase 5
  let D := S.filter (· ∣ n)
  let U := S.filter (fun p => ¬p∣n)
  have memS {p:ℕ} : p∈S ↔ p∈P ∧ p≠2 ∧ p≠5 := by simp [S,and_comm,and_assoc]
  have eqU : P.filter (fun p => p≠2 ∧ p≠5 ∧ ¬p∣n)=U := by
    ext p
    simp only [U,mem_filter,memS]; tauto
  have eD : (1/2:ℝ) ≤ ∏p∈D,F p := by
    refine (euler_product_half D (fun p hp => (hprime p (memS.mp (mem_filter.mp hp).1).1).two_le)).trans ?_
    apply prod_le_prod
    · intro p hp
      have h : (2:ℝ)≤p := by exact_mod_cast (hprime p (memS.mp (mem_filter.mp hp).1).1).two_le
      exact sub_nonneg.mpr ((div_le_one (by positivity)).mpr (by nlinarith))
    · intro p hp
      obtain ⟨ps,pd⟩ := mem_filter.mp hp
      obtain ⟨pP,p2,p5⟩ := memS.mp ps
      exact bad p pP p2 p5 pd
  have eU : (∏p∈U,g p) ≤ ∏p∈U,F p := by
    apply prod_le_prod
    · intro p hp
      obtain ⟨pP,p2,p5⟩ := memS.mp (mem_filter.mp hp).1
      exact g_nonneg p pP p2 p5 (mem_filter.mp hp).2
    · intro p hp
      obtain ⟨pP,p2,p5⟩ := memS.mp (mem_filter.mp hp).1
      exact good p pP p2 p5 (mem_filter.mp hp).2
  have pU : 0 ≤ ∏p∈U,g p := prod_nonneg fun p hp =>
    g_nonneg p (memS.mp (mem_filter.mp hp).1).1 (memS.mp (mem_filter.mp hp).1).2.1
      (memS.mp (mem_filter.mp hp).1).2.2 (mem_filter.mp hp).2
  have fU : 0 ≤ ∏p∈U,F p := prod_nonneg fun p hp => nonneg p (memS.mp (mem_filter.mp hp).1).1
  have split : ∏p∈P,F p = (F 2*F 5)*((∏p∈D,F p)*(∏p∈U,F p)) := by
    rw [← mul_prod_erase P F two,← mul_prod_erase (P.erase 2) F (mem_erase.mpr ⟨by decide,five⟩)]
    rw [mul_assoc,prod_filter_mul_prod_filter_not]
  have exc : (1/64:ℝ)*(1/25) ≤ F 2*F 5 := mul_le_mul p2 p5 (by norm_num) (nonneg _ two)
  have rest := mul_le_mul eD eU pU (le_trans (by norm_num) eD)
  rw [eqU,split]
  calc
    _ = ((1/64:ℝ)*(1/25))*((1/2)*(∏p∈U,g p)) := by ring
    _ ≤ _ := mul_le_mul exc rest (by positivity) (mul_nonneg (nonneg _ two) (nonneg _ five))

end PowerfulDensity

namespace PowerfulDensity
open Finset

/-- A multiplicative density on positive moduli is the product of its prime-power factors. -/
theorem product_prime_powers {R : Type*} [CommMonoid R] (F : ℕ → R) (one : F 1=1)
    (mul : ∀ a b, a.Coprime b → 0<a → 0<b → F (a*b)=F a*F b) (M : ℕ) (pos : 0< M) :
    F M = ∏ p ∈ M.primeFactors, F (p^M.factorization p) := by
  have factor (s : Finset ℕ) (hs : ∀ p∈s, p.Prime) :
      F (∏ p ∈ s, p^M.factorization p) = ∏ p ∈ s, F (p^M.factorization p) := by
    induction s using Finset.induction_on with
    | empty => simpa using one
    | @insert p s np ih =>
      have pp := hs p (mem_insert_self ..)
      have sp : ∀ q∈s, q.Prime := fun q h => hs q (mem_insert_of_mem h)
      have allpos : 0 < ∏ q ∈ s, q^M.factorization q :=
        prod_pos fun q h => pow_pos (sp q h).pos _
      have cp : (p^M.factorization p).Coprime (∏ q ∈ s, q^M.factorization q) := by
        apply Nat.coprime_prod_right_iff.mpr
        intro q hq
        have ne : p≠q := by rintro rfl; exact np hq
        exact (((Nat.coprime_primes pp (sp q hq)).mpr ne).pow_left _).pow_right _
      rw [prod_insert np,prod_insert np,mul _ _ cp (pow_pos pp.pos _) allpos,ih sp]
  nth_rw 1 [Nat.prod_primeFactors_pow_factorization pos.ne']
  exact factor _ (fun _ h => Nat.prime_of_mem_primeFactors h)

theorem mass_factorization (c n M : ℕ) (pos : 0< M) :
    let S (m : ℕ) := ((range m ×ˢ (range m ×ˢ range m)).filter fun t =>
       (t.1^2+t.2.1^2+c*t.2.2^2)%m=n%m).card
    let D (m : ℕ) := (S m : ℝ)/(m:ℝ)^2
    D M = ∏ p ∈ M.primeFactors, D (p^M.factorization p) := by
  intro S D
  apply product_prime_powers D _ _ M pos
  · simp [D,S,Finset.range_one, Nat.mod_one]
  · intro a b cop ha hb
    have count : S (a*b) = S a*S b := crt_count c n a b cop ha hb
    simp only [D,count,Nat.cast_mul,mul_pow]
    ring

theorem primeFactors_factorial (K : ℕ) :
    K.factorial.primeFactors = (range (K+1)).filter Nat.Prime := by
  ext p
  simp only [Nat.mem_primeFactors,mem_filter,mem_range,Nat.lt_succ_iff]
  exact ⟨fun ⟨pp,d,_⟩ => ⟨pp.dvd_factorial.mp d,pp⟩,fun ⟨h,pp⟩ => ⟨pp,pp.dvd_factorial.mpr h,(Nat.factorial_pos _).ne'⟩⟩

end PowerfulDensity

namespace PowerfulDensity
open Finset Filter

/-- The normalized factorial congruence count dominates its good Euler product,
with explicit absolute loss from the two exceptional and all singular primes. -/
theorem factorial_euler (c n K : ℕ) (large : 5≤K) (g : ℕ → ℝ) :
    let M := K.factorial
    let D (m : ℕ) := (((range m ×ˢ (range m ×ˢ range m)).filter fun t =>
       (t.1^2+t.2.1^2+c*t.2.2^2)%m=n%m).card : ℝ) / (m:ℝ)^2
    (1/64 ≤ D (2^M.factorization 2)) →
    (1/25 ≤ D (5^M.factorization 5)) →
    (∀ p≤K, p.Prime → p≠2 → p≠5 → p∣n → 1-1/(p:ℝ)^2 ≤ D (p^M.factorization p)) →
    (∀ p≤K, p.Prime → ¬p∣10*n → 0≤g p ∧ g p≤D (p^M.factorization p)) →
    (∏ p ∈ (range (K+1)).filter (fun p => p.Prime ∧ ¬ p∣10*n), g p)/3200 ≤ D M := by
  intro M D htwo hfive hbad hgood
  let P := M.primeFactors
  have memP (p : ℕ) : p∈P ↔ p≤K ∧ p.Prime := by
    simp only [P,M,primeFactors_factorial,mem_filter,mem_range,Nat.lt_succ_iff]
  have gd (p : ℕ) (pp : p.Prime) : ¬p∣10*n ↔ p≠2 ∧ p≠5 ∧ ¬p∣n := by
    rw [pp.dvd_mul, show 10=2*5 by decide,pp.dvd_mul,Nat.prime_dvd_prime_iff_eq pp Nat.prime_two,
      Nat.prime_dvd_prime_iff_eq pp (by decide : Nat.Prime 5)]
    tauto
  have ident : (range (K+1)).filter (fun p => p.Prime ∧ ¬p∣10*n) =
      P.filter (fun p => p≠2 ∧ p≠5 ∧ ¬p∣n) := by
    ext p
    simp only [mem_filter,mem_range,memP,Nat.lt_succ_iff]
    constructor
    · rintro ⟨pk,pp,not_dvd⟩
      exact ⟨⟨pk,pp⟩,(gd p pp).mp not_dvd⟩
    · rintro ⟨⟨pk,pp⟩,h⟩
      exact ⟨pk,pp,(gd p pp).mpr h⟩
  have fac : D M = ∏ p ∈ P, D (p^M.factorization p) := mass_factorization c n M (Nat.factorial_pos K)
  rw [ident,fac]
  apply density_euler_lower P n (fun p => D (p^M.factorization p)) g
    (fun p h => ((memP p).mp h).2) ((memP 2).mpr ⟨by omega,Nat.prime_two⟩)
    ((memP 5).mpr ⟨large,by decide⟩)
  · intro p _
    dsimp [D]
    positivity
  · intro p h p2 p5 pn
    obtain ⟨pk,pp⟩ := (memP p).mp h
    exact (hgood p pk pp ((gd p pp).mpr ⟨p2,p5,pn⟩)).1
  · exact htwo
  · exact hfive
  · intro p h p2 p5 pn
    obtain ⟨pk,pp⟩ := (memP p).mp h
    exact hbad p pk pp p2 p5 pn
  · intro p h p2 p5 pn
    obtain ⟨pk,pp⟩ := (memP p).mp h
    exact (hgood p pk pp ((gd p pp).mpr ⟨p2,p5,pn⟩)).2

end PowerfulDensity

namespace PowerfulDensity
open Finset

/-- Every local factor of the ternary congruence count is accounted for. Only
the truncated quadratic Jacobi Euler product remains on the analytic side. -/
theorem jacobi_mass (c n K : ℕ) (hc : c ∈ ({25,125}:Finset ℕ)) (hn : n.Coprime (16*c))
    (res : n%8=(c+2)%8) (large : 8≤K) :
    let M := K.factorial
    let X := range M
    (∏ p ∈ (range (K+1)).filter (fun p => p.Prime ∧ ¬p∣10*n),
      (1+(jacobiSym (-(c:ℤ)*n) p : ℝ)/p))/3200 ≤
      (((X ×ˢ (X ×ˢ X)).filter fun t =>
       (t.1^2+t.2.1^2+c*t.2.2^2)%M=n%M).card : ℝ) / (M:ℝ)^2 := by
  intro M X
  let S (m : ℕ) := ((range m ×ˢ (range m ×ˢ range m)).filter fun t =>
       (t.1^2+t.2.1^2+c*t.2.2^2)%m=n%m).card
  let D (m : ℕ) := (S m:ℝ)/(m:ℝ)^2
  let g (p : ℕ) := 1+(jacobiSym (-(c:ℤ)*n) p:ℝ)/p
  have choice : c=25 ∨ c=125 := by simpa using hc
  have c5 : 5∣c := by rcases choice with rfl|rfl <;> decide
  have n5 : ¬5∣n := by
    intro dvd
    have eq := Nat.eq_one_of_dvd_coprimes hn dvd (dvd_mul_of_dvd_right c5 16)
    omega
  have hM : M≠0 := (Nat.factorial_pos _).ne'
  have pexp (p : ℕ) (pp : p.Prime) (pk : p≤K) : ∃ e, M.factorization p=e+1 :=
    Nat.exists_eq_succ_of_ne_zero (pp.factorization_pos_of_dvd hM (pp.dvd_factorial.mpr pk)).ne'
  have unit (p : ℕ) (pp : p.Prime) (p5 : p≠5) : (c:ZMod p)≠0 := by
    rw [ne_eq,ZMod.natCast_eq_zero_iff]
    have no5 : ¬p∣5 := fun d => p5 ((Nat.prime_dvd_prime_iff_eq pp (by decide : Nat.Prime 5)).mp d)
    rcases choice with rfl|rfl
    · intro dvd
      exact no5 (pp.dvd_of_dvd_pow (n:=2) (show p∣5^2 from dvd))
    · intro dvd
      exact no5 (pp.dvd_of_dvd_pow (n:=3) (show p∣5^3 from dvd))
  apply factorial_euler c n K (by omega) g
  · have div : 2^3 ∣ M := dvd_trans (by decide : 2^3 ∣ (8:ℕ).factorial) (Nat.factorial_dvd_factorial large)
    have ex : 3≤ M.factorization 2 := (Nat.prime_two.pow_dvd_iff_le_factorization hM).mp div
    obtain ⟨k,eq⟩ : ∃ k, M.factorization 2=k+3 := ⟨M.factorization 2-3,by omega⟩
    change 1/64 ≤ D (2^M.factorization 2)
    rw [eq]
    have lower : (2^k)^2 ≤ S (2^(k+3)) := PowerfulDyadic.count_lower c n k res
    have rr : ((2:ℝ)^k)^2 ≤ S (2^(k+3)) := by exact_mod_cast lower
    change 1/64 ≤ (S (2^(k+3)):ℝ)/((2^(k+3):ℕ):ℝ)^2
    rw [Nat.cast_pow,Nat.cast_ofNat]
    apply (le_div_iff₀ (by positivity)).mpr
    rw [pow_add]
    nlinarith
  · obtain ⟨e,eq⟩ := pexp 5 (by decide) (by omega)
    change 1/25 ≤ D (5^M.factorization 5)
    rw [eq]
    have five : D (5^(e+1))=4/5 := odd_density_factors.2 e c n
      ((ZMod.natCast_eq_zero_iff ..).mpr c5) (fun h => n5 ((ZMod.natCast_eq_zero_iff ..).mp h))
    rw [five]
    norm_num
  · intro p pk pp p2 p5 pn
    have : Fact p.Prime := ⟨pp⟩
    obtain ⟨e,eq⟩ := pexp p pp pk
    change 1-1/(p:ℝ)^2 ≤ D (p^M.factorization p)
    rw [eq]
    have z : (n:ZMod p)=0 := (ZMod.natCast_eq_zero_iff ..).mpr pn
    simpa only [z,if_true] using (odd_density_factors.1 p e c n p2 (unit p pp p5)).1
  · intro p pk pp pn
    have : Fact p.Prime := ⟨pp⟩
    have p2 : p≠2 := by rintro rfl; exact pn (dvd_mul_of_dvd_left (by decide) _)
    have p5 : p≠5 := by rintro rfl; exact pn (dvd_mul_of_dvd_left (by decide) _)
    have nz : (n:ZMod p)≠0 := fun h => pn (dvd_mul_of_dvd_right ((ZMod.natCast_eq_zero_iff ..).mp h) _)
    obtain ⟨e,eq⟩ := pexp p pp pk
    have id : jacobiSym (-(c:ℤ)*n) p = quadraticChar (ZMod p) (-(c:ZMod p)*n) := by
      rw [←jacobiSym.legendreSym.to_jacobiSym,legendreSym]
      push_cast
      rfl
    change 0≤g p ∧ g p ≤ D (p^M.factorization p)
    have eqD : D (p^(e+1)) = g p := by
      rw [show g p = 1+(quadraticChar (ZMod p) (-(c:ZMod p)*n):ℝ)/p by simp only [g,id]]
      exact (odd_density_factors.1 p e c n p2 (unit p pp p5)).2 nz
    rw [eq,←eqD]
    exact ⟨by dsimp [D]; positivity,le_rfl⟩

end PowerfulDensity
end

namespace OMA.R_Erdos1107_erdos_1107_variants_two_R2

open Filter

/-- A lower bound for partial Euler products of imaginary quadratic characters. -/
def H1 : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ c ∈ ({25,125}:Finset ℕ), n.Coprime (16*c) →
    ∀ᶠ K : ℕ in atTop, (n:ℝ)^(-(1:ℝ)/200) ≤
      ∏ p ∈ (Finset.range (K+1)).filter (fun p => p.Prime ∧ ¬p∣10*n),
        (1+(jacobiSym (-(c:ℤ)*n) p:ℝ)/p)

/-- The fixed ternary theta-series discrepancy at levels coprime to n. -/
def H2 : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ c ∈ ({25, 125} : Finset ℕ), n.Coprime (16*c) →
    let I := Finset.Icc (-(n : ℤ)) (n : ℤ)
    let R := ((I ×ˢ (I ×ˢ I)).filter (fun t ↦
      t.1 ^ 2 + t.2.1 ^ 2 + (c : ℤ) * t.2.2 ^ 2 = (n : ℤ))).card
    ∀ᶠ k : ℕ in atTop,
    let M := (k + 1).factorial
    let X := Finset.range M
    let A := ((X ×ˢ (X ×ˢ X)).filter (fun t ↦
      (t.1 ^ 2 + t.2.1 ^ 2 + c * t.2.2 ^ 2) % M = n % M)).card
    2 * Real.pi * Real.sqrt ((n : ℝ) / (c : ℝ)) * (A : ℝ) / (M : ℝ) ^ 2 ≤ (R : ℝ) + (n : ℝ) ^ ((48 : ℝ) / 100)

theorem main : H1 → H2 → type_of% @Erdos1107.erdos_1107.variants.two := by
  intro lo hi
  exact PowerfulLegendre.eventual_of_fixed125 (PowerfulMoroz.of_two_coprime_forms
    PowerfulLegendre.three_squares_mod_three (PowerfulMass.bridge
      (PowerfulMass.jacobi_lower lo PowerfulDensity.jacobi_mass) hi))

end OMA.R_Erdos1107_erdos_1107_variants_two_R2
