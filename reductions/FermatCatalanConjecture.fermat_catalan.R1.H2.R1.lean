import OMAReductions.R_FermatCatalanConjecture_fermat_catalan_R1

/-! The square case reduces to a signed equation with distinct odd prime exponents. -/

namespace OMA.R_FermatCatalanConjecture_fermat_catalan_R1_H2_R1

def H1 : Prop := ∀ p x y z : ℕ, p.Prime → 7 ≤ p → 0 < x → 0 < y → 0 < z →
  x.Coprime y → x^4 + y^2 ≠ z^p ∧ ∀ w : ℤ, w.natAbs = z → (y:ℤ)^2 + w^p ≠ (x:ℤ)^4

def H2 : Prop := ∀ (p : ℕ) (u v : ℤ) (z : ℕ), p.Prime → 7 ≤ p → 0 < z →
  u ≠ 0 → v ≠ 0 → u.natAbs.Coprime v.natAbs → u^p + v^p ≠ (z:ℤ)^2

def H3 : Prop := ∃ B : ℕ, ∀ (p q : ℕ) (u v : ℤ) (x : ℕ),
  p.Prime → q.Prime → 3 ≤ p → 3 ≤ q → p ≠ q → u ≠ 0 → v ≠ 0 → 0 < x →
  u.natAbs.Coprime v.natAbs → u^p + v^q = (x:ℤ)^2 → 1 < u.natAbs → p ≤ B

lemma arranged {v : Fin 3 → ℕ} (sum : v 0 + v 1 = v 2) {i j k : Fin 3}
    (ij : i ≠ j) (ik : i ≠ k) (jk : j ≠ k) :
    v i + v j = v k ∨ v i + v k = v j ∨ v j + v k = v i := by
  have back : v 1 + v 0 = v 2 := (Nat.add_comm ..).trans sum
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    first
    | contradiction
    | exact Or.inl sum
    | exact Or.inl back
    | exact Or.inr (Or.inl sum)
    | exact Or.inr (Or.inl back)
    | exact Or.inr (Or.inr sum)
    | exact Or.inr (Or.inr back)

lemma coprime_indices {v : Fin 3 → ℕ} (sum : v 0 + v 1 = v 2) (cop : (v 0).Coprime (v 1))
    {i j : Fin 3} (ij : i ≠ j) : (v i).Coprime (v j) := by
  have ac : (v 0).Coprime (v 2) := sum ▸ Nat.coprime_self_add_right.mpr cop
  have bc : (v 1).Coprime (v 2) := sum ▸ Nat.coprime_add_self_right.mpr cop.symm
  fin_cases i <;> fin_cases j <;>
    first | contradiction | exact cop | exact cop.symm | exact ac | exact ac.symm | exact bc | exact bc.symm

lemma signed_square {p q x y z : ℕ} (hp : Odd p) (hq : Odd q)
    (rel : x^p + y^q = z^2 ∨ x^p + z^2 = y^q ∨ y^q + z^2 = x^p) :
    ∃ u v : ℤ, u.natAbs = x ∧ v.natAbs = y ∧ u^p + v^q = (z:ℤ)^2 := by
  rcases rel with h | h | h
  · exact ⟨x,y,rfl,rfl,by exact_mod_cast h⟩
  · refine ⟨-(x:ℤ),y,by simp,rfl,?_⟩
    rw [hp.neg_pow]
    have e : (x:ℤ)^p + (z:ℤ)^2 = (y:ℤ)^q := by exact_mod_cast h
    omega
  · refine ⟨x,-(y:ℤ),rfl,by simp,?_⟩
    rw [hq.neg_pow]
    have e : (y:ℤ)^q + (z:ℤ)^2 = (x:ℤ)^p := by exact_mod_cast h
    omega

lemma no_fourth (known : H1) {p x y z : ℕ} (hp : p.Prime) (seven : 7 ≤ p)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (cop : x.Coprime y) :
    ¬ (x^4 + y^2 = z^p ∨ x^4 + z^p = y^2 ∨ y^2 + z^p = x^4) := by
  obtain ⟨sum,diff⟩ := known p x y z hp seven hx hy hz cop
  rintro (h | h | h)
  · exact sum h
  · apply diff (-(z:ℤ)) (by simp)
    rw [(hp.odd_of_ne_two (by omega)).neg_pow]
    have e : (x:ℤ)^4 + (z:ℤ)^p = (y:ℤ)^2 := by exact_mod_cast h
    omega
  · exact diff z rfl (by exact_mod_cast h)

theorem main : H1 → H2 → H3 → OMA.R_FermatCatalanConjecture_fermat_catalan_R1.H2 := by
  rintro fourth repeated ⟨B,distinct⟩
  refine ⟨max B 6,fun v e pos cop sum roots normal uniqueSquare i nonunit => ?_⟩
  by_cases small : e i ≤ 6
  · exact small.trans (le_max_right ..)
  have seven : 7 ≤ e i := by omega
  have prime : (e i).Prime := (normal i).resolve_right (by omega)
  have positive_exp j : 0 < e j := (normal j).elim Nat.Prime.pos (fun four => by omega)
  obtain ⟨s,hs,unique⟩ := uniqueSquare
  have is : i ≠ s := fun same => small (by simp [same,hs])
  have third : ∀ i s : Fin 3, i ≠ s → ∃ k : Fin 3, k ≠ s ∧ k ≠ i := by decide
  obtain ⟨k,ks,ki⟩ := third i s is
  choose a power using roots
  have positive j : 0 < a j := by
    by_contra! low
    have zero : a j = 0 := by omega
    have h := power j
    rw [zero,zero_pow (positive_exp j).ne'] at h
    have := pos j
    omega
  have basecop {j l : Fin 3} (ne : j ≠ l) : (a j).Coprime (a l) := by
    have h := coprime_indices sum cop ne
    rw [← power j,← power l] at h
    exact h.of_dvd (dvd_pow_self _ (positive_exp j).ne') (dvd_pow_self _ (positive_exp l).ne')
  rcases normal k with pk | four
  · have notTwo : e k ≠ 2 := fun h => ks (unique k h)
    have rel := arranged sum (Ne.symm ki) is ks
    rw [← power i,← power k,← power s,hs] at rel
    obtain ⟨u,w,hu,hw,eqn⟩ := signed_square (prime.odd_of_ne_two (by omega)) (pk.odd_of_ne_two notTwo) rel
    have un : u ≠ 0 := by rintro rfl; simp at hu; have := positive i; omega
    have wn : w ≠ 0 := by rintro rfl; simp at hw; have := positive k; omega
    have uw : u.natAbs.Coprime w.natAbs := hu ▸ hw ▸ basecop (Ne.symm ki)
    by_cases same : e i = e k
    · rw [← same] at eqn
      exact (repeated (e i) u w (a s) prime seven (positive s) un wn uw eqn).elim
    · have largeRoot : 1 < u.natAbs := by
        rw [hu]
        by_contra! low
        have h := Nat.pow_le_pow_left low (e i)
        simp only [one_pow,power] at h
        omega
      exact (distinct (e i) (e k) u w (a s) prime pk (by omega) (by have := pk.two_le; omega)
        same un wn (positive s) uw eqn largeRoot).trans (le_max_left ..)
  · have rel := arranged sum ks ki (Ne.symm is)
    rw [← power k,← power s,← power i,four,hs] at rel
    exact (no_fourth fourth prime seven (positive k) (positive s) (positive i) (basecop ks) rel).elim

end OMA.R_FermatCatalanConjecture_fermat_catalan_R1_H2_R1
