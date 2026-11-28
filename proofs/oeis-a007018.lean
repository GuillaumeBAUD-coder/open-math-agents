import OMAStatements.S_oeis_a007018

/-!
Each term from 6 onward is 6m with m coprime to 6. For each proper unitary
divisor q of m the four products q, 2q, 3q, 6q balance as 1 + 2 + 3 = 6.
For q = m the proper divisors only give q, 2q, 3q, and 1 + 2 = 3.
-/

namespace SylvesterUnitary
open Nat Finset OMA.S_oeis_a007018

private theorem a_factor (n : ℕ) : ∃ m, 0 < m ∧ a (n+2) = 6*m ∧ Coprime 6 m := by
  induction n with
  | zero => exact ⟨1, by decide, by decide, by decide⟩
  | succ n ih =>
    obtain ⟨m,hm,he,hc⟩ := ih
    refine ⟨m*(a (n+2)+1), Nat.mul_pos hm (Nat.succ_pos _), ?_, ?_⟩
    · have hs : a (n+1+2) = a (n+2)*(a (n+2)+1) := by
        rw [show n+1+2 = (n+2)+1 by omega, a, pow_two, Nat.mul_add, mul_one]
      change a (n+1+2) = _
      rw [hs]
      conv_lhs => lhs; rw [he]
      rw [mul_assoc]
    · exact Nat.coprime_mul_iff_right.mpr ⟨hc, by rw [he]; simp⟩

private theorem six_divisors : divisors 6 = {1,2,3,6} := by decide +kernel

private theorem unitary6 (i : ℕ) (hi : i ∈ divisors 6) : Coprime i (6/i) := by
  rw [six_divisors] at hi
  simp only [mem_insert, mem_singleton] at hi
  rcases hi with rfl|rfl|rfl|rfl <;> decide

private theorem coprime_product {m i q : ℕ} (hc : Coprime 6 m)
    (hi : i ∈ divisors 6) (hq : q ∈ divisors m) :
    Coprime (i*q) (6*m/(i*q)) ↔ Coprime q (m/q) := by
  have hid := (mem_divisors.mp hi).1
  have hqd := (mem_divisors.mp hq).1
  have h₁ : Coprime i (m/q) := hc.coprime_dvd_left hid |>.coprime_dvd_right (div_dvd_of_dvd hqd)
  have h₂ : Coprime q (6/i) := hc.symm.coprime_dvd_left hqd |>.coprime_dvd_right (div_dvd_of_dvd hid)
  rw [← Nat.div_mul_div_comm hid hqd, Nat.coprime_mul_iff_left,
    Nat.coprime_mul_iff_right, Nat.coprime_mul_iff_right]
  have hu := unitary6 i hi
  tauto

private theorem split_six {m : ℕ} (hm : 0 < m) (hc : Coprime 6 m) :
    IsUnitaryHalfZumkeller (6*m) := by
  let U := unitaryProperDivisors (6*m)
  let side (d : ℕ) := d.gcd 6 = 6 ∨ (d.gcd 6 = 3 ∧ d = 3*m)
  let g (d : ℕ) : ℤ := if side d then (d:ℤ) else -(d:ℤ)
  let f (d : ℕ) : ℤ := if d < 6*m ∧ Coprime d (6*m/d) then g d else 0
  have hU : U = (divisors (6*m)).filter (fun d => d < 6*m ∧ Coprime d (6*m/d)) := by
    ext d
    have hh : 6*m ≠ 0 := by positivity
    simp only [U, unitaryProperDivisors, mem_filter, mem_properDivisors, mem_divisors]
    tauto
  have hval {i q : ℕ} (hi : i ∈ divisors 6) (hq : q ∈ divisors m) :
      f (i*q) = if i*q < 6*m ∧ Coprime q (m/q) then
          if i = 6 ∨ (i = 3 ∧ i*q = 3*m) then (↑(i*q):ℤ) else -(↑(i*q):ℤ)
        else 0 := by
    have hg : (i*q).gcd 6 = i := by
      rw [mul_comm i q]
      exact gcd_mul_of_coprime_of_dvd (hc.symm.coprime_dvd_left (mem_divisors.mp hq).1)
        (mem_divisors.mp hi).1
    simp only [f,g,side,hg,coprime_product hc hi hq]
  have hrow (q : ℕ) (hq : q ∈ divisors m) : ∑ i ∈ divisors 6, f (i*q) = 0 := by
    rw [six_divisors]
    have hsum : ∑ i ∈ ({1,2,3,6} : Finset ℕ), f (i*q) =
        f (1*q) + f (2*q) + f (3*q) + f (6*q) := by
      simp [sum_insert, add_assoc]
    have hqle := Nat.le_of_dvd hm (mem_divisors.mp hq).1
    have h₁ : 1*q < 6*m := by omega
    have h₂ : 2*q < 6*m := by omega
    have h₃ : 3*q < 6*m := by omega
    by_cases hu : Coprime q (m/q)
    · have e1 : f (1*q) = -(q:ℤ) := by
        rw [hval (i := 1) (by decide) hq, if_pos ⟨h₁,hu⟩]
        norm_num
      have e2 : f (2*q) = -(2*(q:ℤ)) := by
        rw [hval (i := 2) (by decide) hq, if_pos ⟨h₂,hu⟩]
        norm_num
      rw [hsum,e1,e2,hval (i := 3) (by decide) hq, if_pos ⟨h₃,hu⟩,
        hval (i := 6) (by decide) hq]
      by_cases he : q = m
      · have h₆ : ¬ (6*q < 6*m ∧ Coprime q (m/q)) := by
          intro h
          have := h.1
          omega
        rw [if_neg h₆, if_pos (show (3:ℕ) = 6 ∨ (3:ℕ) = 3 ∧ 3*q = 3*m from Or.inr ⟨rfl, by omega⟩)]
        push_cast
        ring
      · have h₆ : 6*q < 6*m := by omega
        have hne : ¬ ((3:ℕ) = 6 ∨ (3:ℕ) = 3 ∧ 3*q = 3*m) := by omega
        have hpass : 6*q < 6*m ∧ Coprime q (m/q) := ⟨h₆,hu⟩
        have hside : (6:ℕ) = 6 ∨ (6:ℕ) = 3 ∧ 6*q = 3*m := Or.inl rfl
        rw [if_neg hne, if_pos hpass, if_pos hside]
        push_cast
        ring
    · rw [hsum]
      have e {i : ℕ} (hi : i ∈ divisors 6) : f (i*q) = 0 := by
        rw [hval hi hq, if_neg (fun h => hu h.2)]
      rw [e (i := 1) (by decide), e (i := 2) (by decide),
        e (i := 3) (by decide), e (i := 6) (by decide)]
      rfl
  have htotal : ∑ d ∈ U, g d = 0 := by
    rw [hU, sum_filter]
    change ∑ d ∈ divisors (6*m), f d = 0
    rw [hc.divisors_mul, sum_map]
    change (∑ p ∈ (divisors 6 ×ˢ divisors m).attach, f (p.val.1*p.val.2)) = 0
    rw [sum_attach (f := fun p : ℕ × ℕ => f (p.1*p.2))]
    change (∑ p ∈ divisors 6 ×ˢ divisors m, f (p.1*p.2)) = 0
    rw [sum_product, sum_comm]
    exact sum_eq_zero hrow
  let S := U.filter side
  have hcomp : U \ S = U.filter (fun d => ¬ side d) := by
    ext d
    simp only [S,mem_filter,mem_sdiff]
    tauto
  have hs : ∑ d ∈ U, g d = (∑ d ∈ S, (d:ℤ)) - ∑ d ∈ (U \ S), (d:ℤ) := by
    rw [hcomp]
    simp only [S,sum_filter,← sum_sub_distrib]
    exact sum_congr rfl (fun d _ => by by_cases hh : side d <;> simp [g,hh])
  refine ⟨S, filter_subset _ _, ?_⟩
  have hz := sub_eq_zero.mp (hs.symm.trans htotal)
  exact (Nat.cast_injective (R := ℤ)) (by simpa only [Nat.cast_sum] using hz)

end SylvesterUnitary

theorem OMA.solution : type_of% @OMA.S_oeis_a007018.main := by
  open SylvesterUnitary OMA.S_oeis_a007018 in
  intro n hn
  obtain ⟨k,hk⟩ : ∃ k, n = k+2 := ⟨n-2,by omega⟩
  subst n
  obtain ⟨m,hm,he,hc⟩ := a_factor k
  rw [he]
  exact split_six hm hc
