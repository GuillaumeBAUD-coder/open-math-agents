import OMAReductions.R_OeisA109074_conjecture_R1_H2_R1

/-! # The two new numerator rows

With `a (2 m) = 3 m + 1` and `a (2 m + 1) = 3 m + 2`, the factors `a j - a i` and `a j + a i` of
the rows `2 n` and `2 n + 1` run over the numbers of two residue classes modulo `3`, so each row
is a factorial divided by a product over the third class.
-/

namespace OMA109074

open Finset

def aa (j : ℕ) : ℕ := j + 1 + j / 2

def rowf (j : ℕ) : ℕ := aa j * ∏ i ∈ range j, (aa j - aa i) * (aa j + aa i)

lemma aa_even (m : ℕ) : aa (2 * m) = 3 * m + 1 := by
  unfold aa
  omega

lemma aa_odd (m : ℕ) : aa (2 * m + 1) = 3 * m + 2 := by
  unfold aa
  omega

lemma prod_pair (g : ℕ → ℕ) (n : ℕ) :
    ∏ i ∈ range (2 * n), g i = ∏ m ∈ range n, g (2 * m) * g (2 * m + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 from by ring, prod_range_succ, prod_range_succ, ih,
      prod_range_succ]
    ring

lemma split_prod (f : ℕ → ℕ) (n : ℕ) :
    (∏ m ∈ range n, f (n - 1 - m)) * (∏ m ∈ range n, f (n + m)) = ∏ k ∈ range (2 * n), f k := by
  have h : ∏ k ∈ Ico n (2 * n), f k = ∏ m ∈ range n, f (n + m) := by
    rw [Finset.prod_Ico_eq_prod_range, show 2 * n - n = n from by omega]
  rw [Finset.prod_range_reflect, ← h]
  exact Finset.prod_range_mul_prod_Ico f (by omega)

lemma rowA (n : ℕ) :
    ∏ i ∈ range (2 * n), (aa (2 * n) - aa i) * (aa (2 * n) + aa i) =
      ∏ k ∈ range (2 * n), (3 * k + 2) * (3 * k + 3) := by
  rw [prod_pair, ← split_prod (fun k => (3 * k + 2) * (3 * k + 3)) n, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro m hm
  have hm' : m < n := Finset.mem_range.1 hm
  rw [aa_even, aa_even, aa_odd]
  obtain ⟨d, rfl⟩ : ∃ d, n = m + 1 + d := ⟨n - m - 1, by omega⟩
  have e1 : 3 * (m + 1 + d) + 1 - (3 * m + 1) = 3 * d + 3 := by omega
  have e2 : 3 * (m + 1 + d) + 1 - (3 * m + 2) = 3 * d + 2 := by omega
  have e3 : m + 1 + d - 1 - m = d := by omega
  simp only [e1, e2, e3]
  ring

lemma rowB (n : ℕ) :
    ∏ i ∈ range (2 * n + 1), (aa (2 * n + 1) - aa i) * (aa (2 * n + 1) + aa i) =
      (∏ k ∈ range (2 * n), (3 * k + 3) * (3 * k + 4)) * (6 * n + 3) := by
  rw [prod_range_succ]
  have hlast : (aa (2 * n + 1) - aa (2 * n)) * (aa (2 * n + 1) + aa (2 * n)) = 6 * n + 3 := by
    rw [aa_even, aa_odd]
    have : 3 * n + 2 - (3 * n + 1) = 1 := by omega
    rw [this]
    ring
  rw [hlast]
  congr 1
  rw [prod_pair, ← split_prod (fun k => (3 * k + 3) * (3 * k + 4)) n, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro m hm
  have hm' : m < n := Finset.mem_range.1 hm
  rw [aa_odd, aa_even, aa_odd]
  obtain ⟨d, rfl⟩ : ∃ d, n = m + 1 + d := ⟨n - m - 1, by omega⟩
  have e1 : 3 * (m + 1 + d) + 2 - (3 * m + 1) = 3 * d + 4 := by omega
  have e2 : 3 * (m + 1 + d) + 2 - (3 * m + 2) = 3 * d + 3 := by omega
  have e3 : m + 1 + d - 1 - m = d := by omega
  simp only [e1, e2, e3]
  ring

lemma fact1 (m : ℕ) :
    (∏ k ∈ range m, (3 * k + 1)) * (∏ k ∈ range m, (3 * k + 2) * (3 * k + 3)) =
      (3 * m).factorial := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [prod_range_succ, prod_range_succ, show 3 * (m + 1) = 3 * m + 1 + 1 + 1 from by ring,
      Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ, ← ih]
    ring

lemma fact2 (m : ℕ) :
    (∏ k ∈ range (m + 1), (3 * k + 2)) * (∏ k ∈ range m, (3 * k + 3) * (3 * k + 4)) *
      (3 * m + 3) = (3 * m + 3).factorial := by
  induction m with
  | zero => decide
  | succ m ih =>
    rw [prod_range_succ (fun k => 3 * k + 2) (m + 1), prod_range_succ (fun k => (3 * k + 3) * (3 * k + 4)) m,
      show 3 * (m + 1) + 3 = 3 * m + 3 + 1 + 1 + 1 from by ring,
      Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ, ← ih]
    ring

lemma fact3 (m : ℕ) :
    (∏ k ∈ range m, (3 * k + 1)) * (∏ k ∈ range m, (3 * k + 2)) * 3 ^ m * m.factorial =
      (3 * m).factorial := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [prod_range_succ, prod_range_succ, show 3 * (m + 1) = 3 * m + 1 + 1 + 1 from by ring,
      Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ, ← ih, pow_succ]
    ring

theorem main (n : ℕ) :
    2 * (4 * n + 2) * (rowf (2 * n) * rowf (2 * n + 1)) =
      3 ^ (2 * n) * (6 * n + 4).factorial * (2 * n + 1).factorial := by
  set U := ∏ k ∈ range (2 * n), (3 * k + 1) with hU
  set V := ∏ k ∈ range (2 * n), (3 * k + 2) with hV
  set PA := ∏ k ∈ range (2 * n), (3 * k + 2) * (3 * k + 3) with hPA
  set PB := ∏ k ∈ range (2 * n), (3 * k + 3) * (3 * k + 4) with hPB
  have hX : rowf (2 * n) = (3 * n + 1) * PA := by
    unfold rowf
    rw [rowA, aa_even]
  have hY : rowf (2 * n + 1) = (3 * n + 2) * (PB * (6 * n + 3)) := by
    unfold rowf
    rw [rowB, aa_odd]
  have h1 : U * PA = (6 * n).factorial := by
    have := fact1 (2 * n)
    rw [show 3 * (2 * n) = 6 * n from by ring] at this
    exact this
  have h2 : V * (6 * n + 2) * PB * (6 * n + 3) = (6 * n + 3).factorial := by
    have := fact2 (2 * n)
    rw [prod_range_succ, show 3 * (2 * n) + 3 = 6 * n + 3 from by ring,
      show 3 * (2 * n) + 2 = 6 * n + 2 from by ring] at this
    exact this
  have h3 : U * V * 3 ^ (2 * n) * (2 * n).factorial = (6 * n).factorial := by
    have := fact3 (2 * n)
    rw [show 3 * (2 * n) = 6 * n from by ring] at this
    exact this
  have hUpos : 0 < U := Finset.prod_pos fun k _ => by omega
  have hVpos : 0 < V := Finset.prod_pos fun k _ => by omega
  have hTpos : 0 < U * V * (6 * n + 2) * (2 * n).factorial :=
    Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hUpos hVpos) (by omega)) (Nat.factorial_pos _)
  have f1 : (6 * n + 4).factorial = (6 * n + 4) * (6 * n + 3).factorial :=
    Nat.factorial_succ (6 * n + 3)
  have f2 : (2 * n + 1).factorial = (2 * n + 1) * (2 * n).factorial := Nat.factorial_succ (2 * n)
  apply Nat.eq_of_mul_eq_mul_right hTpos
  rw [hX, hY]
  calc 2 * (4 * n + 2) * ((3 * n + 1) * PA * ((3 * n + 2) * (PB * (6 * n + 3)))) *
        (U * V * (6 * n + 2) * (2 * n).factorial)
      = 2 * (4 * n + 2) * (3 * n + 1) * (3 * n + 2) * (2 * n).factorial * (U * PA) *
          (V * (6 * n + 2) * PB * (6 * n + 3)) := by ring
    _ = 2 * (4 * n + 2) * (3 * n + 1) * (3 * n + 2) * (2 * n).factorial * (6 * n).factorial *
          (6 * n + 3).factorial := by rw [h1, h2]
    _ = (6 * n).factorial * ((6 * n + 4) * (6 * n + 3).factorial) *
          ((2 * n + 1) * (2 * n).factorial) * (6 * n + 2) := by ring
    _ = (U * V * 3 ^ (2 * n) * (2 * n).factorial) * (6 * n + 4).factorial *
          (2 * n + 1).factorial * (6 * n + 2) := by rw [h3, f1, f2]
    _ = 3 ^ (2 * n) * (6 * n + 4).factorial * (2 * n + 1).factorial *
          (U * V * (6 * n + 2) * (2 * n).factorial) := by ring

end OMA109074

theorem OMA.solution : OMA.R_OeisA109074_conjecture_R1_H2_R1.H2 := by
  intro n
  exact OMA109074.main n
