import OMAStatements.S_oeis_a160850

open PowerSeries OMA.S_oeis_a160850

def OMA.L (f : ℕ → ℤ) (t : ℕ) : ℤ :=
  (-1) * f t + (-2) * f (t + 1) + (-4) * f (t + 2) + (-6) * f (t + 3) + (-8) * f (t + 4) + (-9) * f (t + 5) + (-9) * f (t + 6) + (-7) * f (t + 7) + (-4) * f (t + 8) + (4) * f (t + 10) + (7) * f (t + 11) + (9) * f (t + 12) + (9) * f (t + 13) + (8) * f (t + 14) + (6) * f (t + 15) + (4) * f (t + 16) + (2) * f (t + 17) + (1) * f (t + 18)

lemma OMA.ann (f : ℕ → ℤ) (p : ℕ) (hp : p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5 ∨ p = 6 ∨ p = 7)
    (hf : ∀ t, f (t + p) = f t) (t : ℕ) : OMA.L f t = 0 := by
  unfold OMA.L
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have e0 : f (t + 1) = f t := hf _
    have e1 : f (t + 2) = f (t + 1) := hf _
    have e2 : f (t + 3) = f (t + 2) := hf _
    have e3 : f (t + 4) = f (t + 3) := hf _
    have e4 : f (t + 5) = f (t + 4) := hf _
    have e5 : f (t + 6) = f (t + 5) := hf _
    have e6 : f (t + 7) = f (t + 6) := hf _
    have e7 : f (t + 8) = f (t + 7) := hf _
    have e8 : f (t + 9) = f (t + 8) := hf _
    have e9 : f (t + 10) = f (t + 9) := hf _
    have e10 : f (t + 11) = f (t + 10) := hf _
    have e11 : f (t + 12) = f (t + 11) := hf _
    have e12 : f (t + 13) = f (t + 12) := hf _
    have e13 : f (t + 14) = f (t + 13) := hf _
    have e14 : f (t + 15) = f (t + 14) := hf _
    have e15 : f (t + 16) = f (t + 15) := hf _
    have e16 : f (t + 17) = f (t + 16) := hf _
    have e17 : f (t + 18) = f (t + 17) := hf _
    linarith
  · have e0 : f (t + 2) = f t := hf _
    have e1 : f (t + 3) = f (t + 1) := hf _
    have e2 : f (t + 4) = f (t + 2) := hf _
    have e3 : f (t + 5) = f (t + 3) := hf _
    have e4 : f (t + 6) = f (t + 4) := hf _
    have e5 : f (t + 7) = f (t + 5) := hf _
    have e6 : f (t + 8) = f (t + 6) := hf _
    have e7 : f (t + 9) = f (t + 7) := hf _
    have e8 : f (t + 10) = f (t + 8) := hf _
    have e9 : f (t + 11) = f (t + 9) := hf _
    have e10 : f (t + 12) = f (t + 10) := hf _
    have e11 : f (t + 13) = f (t + 11) := hf _
    have e12 : f (t + 14) = f (t + 12) := hf _
    have e13 : f (t + 15) = f (t + 13) := hf _
    have e14 : f (t + 16) = f (t + 14) := hf _
    have e15 : f (t + 17) = f (t + 15) := hf _
    have e16 : f (t + 18) = f (t + 16) := hf _
    linarith
  · have e0 : f (t + 3) = f t := hf _
    have e1 : f (t + 4) = f (t + 1) := hf _
    have e2 : f (t + 5) = f (t + 2) := hf _
    have e3 : f (t + 6) = f (t + 3) := hf _
    have e4 : f (t + 7) = f (t + 4) := hf _
    have e5 : f (t + 8) = f (t + 5) := hf _
    have e6 : f (t + 9) = f (t + 6) := hf _
    have e7 : f (t + 10) = f (t + 7) := hf _
    have e8 : f (t + 11) = f (t + 8) := hf _
    have e9 : f (t + 12) = f (t + 9) := hf _
    have e10 : f (t + 13) = f (t + 10) := hf _
    have e11 : f (t + 14) = f (t + 11) := hf _
    have e12 : f (t + 15) = f (t + 12) := hf _
    have e13 : f (t + 16) = f (t + 13) := hf _
    have e14 : f (t + 17) = f (t + 14) := hf _
    have e15 : f (t + 18) = f (t + 15) := hf _
    linarith
  · have e0 : f (t + 4) = f t := hf _
    have e1 : f (t + 5) = f (t + 1) := hf _
    have e2 : f (t + 6) = f (t + 2) := hf _
    have e3 : f (t + 7) = f (t + 3) := hf _
    have e4 : f (t + 8) = f (t + 4) := hf _
    have e5 : f (t + 9) = f (t + 5) := hf _
    have e6 : f (t + 10) = f (t + 6) := hf _
    have e7 : f (t + 11) = f (t + 7) := hf _
    have e8 : f (t + 12) = f (t + 8) := hf _
    have e9 : f (t + 13) = f (t + 9) := hf _
    have e10 : f (t + 14) = f (t + 10) := hf _
    have e11 : f (t + 15) = f (t + 11) := hf _
    have e12 : f (t + 16) = f (t + 12) := hf _
    have e13 : f (t + 17) = f (t + 13) := hf _
    have e14 : f (t + 18) = f (t + 14) := hf _
    linarith
  · have e0 : f (t + 5) = f t := hf _
    have e1 : f (t + 6) = f (t + 1) := hf _
    have e2 : f (t + 7) = f (t + 2) := hf _
    have e3 : f (t + 8) = f (t + 3) := hf _
    have e4 : f (t + 9) = f (t + 4) := hf _
    have e5 : f (t + 10) = f (t + 5) := hf _
    have e6 : f (t + 11) = f (t + 6) := hf _
    have e7 : f (t + 12) = f (t + 7) := hf _
    have e8 : f (t + 13) = f (t + 8) := hf _
    have e9 : f (t + 14) = f (t + 9) := hf _
    have e10 : f (t + 15) = f (t + 10) := hf _
    have e11 : f (t + 16) = f (t + 11) := hf _
    have e12 : f (t + 17) = f (t + 12) := hf _
    have e13 : f (t + 18) = f (t + 13) := hf _
    linarith
  · have e0 : f (t + 6) = f t := hf _
    have e1 : f (t + 7) = f (t + 1) := hf _
    have e2 : f (t + 8) = f (t + 2) := hf _
    have e3 : f (t + 9) = f (t + 3) := hf _
    have e4 : f (t + 10) = f (t + 4) := hf _
    have e5 : f (t + 11) = f (t + 5) := hf _
    have e6 : f (t + 12) = f (t + 6) := hf _
    have e7 : f (t + 13) = f (t + 7) := hf _
    have e8 : f (t + 14) = f (t + 8) := hf _
    have e9 : f (t + 15) = f (t + 9) := hf _
    have e10 : f (t + 16) = f (t + 10) := hf _
    have e11 : f (t + 17) = f (t + 11) := hf _
    have e12 : f (t + 18) = f (t + 12) := hf _
    linarith
  · have e0 : f (t + 7) = f t := hf _
    have e1 : f (t + 8) = f (t + 1) := hf _
    have e2 : f (t + 9) = f (t + 2) := hf _
    have e3 : f (t + 10) = f (t + 3) := hf _
    have e4 : f (t + 11) = f (t + 4) := hf _
    have e5 : f (t + 12) = f (t + 5) := hf _
    have e6 : f (t + 13) = f (t + 6) := hf _
    have e7 : f (t + 14) = f (t + 7) := hf _
    have e8 : f (t + 15) = f (t + 8) := hf _
    have e9 : f (t + 16) = f (t + 9) := hf _
    have e10 : f (t + 17) = f (t + 10) := hf _
    have e11 : f (t + 18) = f (t + 11) := hf _
    linarith

def OMA.F (y c t : ℕ) : ℤ := if Nat.Coprime y (t % y) then (c : ℤ) else 0

def OMA.G (y c t : ℕ) : ℤ := if t % 2 = 0 ∧ Nat.Coprime y ((t/2) % y) then (c : ℤ) else 0

lemma OMA.perF (y c t : ℕ) : OMA.F y c (t + y) = OMA.F y c t := by
  simp only [OMA.F, Nat.add_mod_right]

lemma OMA.perG1 (c t : ℕ) : OMA.G 1 c (t + 2) = OMA.G 1 c t := by
  simp only [OMA.G, show (t + 2) % 2 = t % 2 by omega, show (t + 2) / 2 % 1 = t / 2 % 1 by omega]

lemma OMA.perG2 (c t : ℕ) : OMA.G 2 c (t + 4) = OMA.G 2 c t := by
  simp only [OMA.G, show (t + 4) % 2 = t % 2 by omega, show (t + 4) / 2 % 2 = t / 2 % 2 by omega]

lemma OMA.perG3 (c t : ℕ) : OMA.G 3 c (t + 6) = OMA.G 3 c t := by
  simp only [OMA.G, show (t + 6) % 2 = t % 2 by omega, show (t + 6) / 2 % 3 = t / 2 % 3 by omega]

lemma OMA.perG0 (y t : ℕ) : OMA.G y 0 (t + 1) = OMA.G y 0 t := by
  simp [OMA.G]

lemma OMA.perF8 (c t : ℕ) : OMA.F 8 c (t + 2) = OMA.F 8 c t := by
  have h : ∀ r : ℕ, r < 8 → (Nat.Coprime 8 ((r + 2) % 8) ↔ Nat.Coprime 8 r) := by decide
  simp only [OMA.F, show (t + 2) % 8 = (t % 8 + 2) % 8 by omega, h (t % 8) (Nat.mod_lt _ (by norm_num))]

lemma OMA.perF9 (c t : ℕ) : OMA.F 9 c (t + 3) = OMA.F 9 c t := by
  have h : ∀ r : ℕ, r < 9 → (Nat.Coprime 9 ((r + 3) % 9) ↔ Nat.Coprime 9 r) := by decide
  simp only [OMA.F, show (t + 3) % 9 = (t % 9 + 3) % 9 by omega, h (t % 9) (Nat.mod_lt _ (by norm_num))]

lemma OMA.perG4 (c t : ℕ) : OMA.G 4 c (t + 4) = OMA.G 4 c t := by
  have h : ∀ r : ℕ, r < 4 → (Nat.Coprime 4 ((r + 2) % 4) ↔ Nat.Coprime 4 r) := by decide
  simp only [OMA.G, show (t + 4) % 2 = t % 2 by omega, show (t + 4) / 2 % 4 = (t / 2 % 4 + 2) % 4 by omega,
    h (t / 2 % 4) (Nat.mod_lt _ (by norm_num))]

lemma OMA.hsd : secondDiff = fun t => 2 * ∑ i : Fin 9, (OMA.F (i.val + 1) (10 - (i.val + 1)) t -
    OMA.G (i.val + 1) (10 - 2 * (i.val + 1)) t) := rfl

lemma OMA.sE (t : ℕ) : OMA.L secondDiff t = 0 := by
  have hF : ∀ (i : Fin 9) (t : ℕ), OMA.L (OMA.F (i.val + 1) (10 - (i.val + 1))) t = 0 := by
    intro i t
    fin_cases i
    · exact OMA.ann _ 1 (by decide) (OMA.perF 1 _) t
    · exact OMA.ann _ 2 (by decide) (OMA.perF 2 _) t
    · exact OMA.ann _ 3 (by decide) (OMA.perF 3 _) t
    · exact OMA.ann _ 4 (by decide) (OMA.perF 4 _) t
    · exact OMA.ann _ 5 (by decide) (OMA.perF 5 _) t
    · exact OMA.ann _ 6 (by decide) (OMA.perF 6 _) t
    · exact OMA.ann _ 7 (by decide) (OMA.perF 7 _) t
    · exact OMA.ann _ 2 (by decide) (OMA.perF8 _) t
    · exact OMA.ann _ 3 (by decide) (OMA.perF9 _) t
  have hG : ∀ (i : Fin 9) (t : ℕ), OMA.L (OMA.G (i.val + 1) (10 - 2 * (i.val + 1))) t = 0 := by
    intro i t
    fin_cases i
    · exact OMA.ann _ 2 (by decide) (OMA.perG1 _) t
    · exact OMA.ann _ 4 (by decide) (OMA.perG2 _) t
    · exact OMA.ann _ 6 (by decide) (OMA.perG3 _) t
    · exact OMA.ann _ 4 (by decide) (OMA.perG4 _) t
    · exact OMA.ann _ 1 (by decide) (OMA.perG0 _) t
    · exact OMA.ann _ 1 (by decide) (OMA.perG0 _) t
    · exact OMA.ann _ 1 (by decide) (OMA.perG0 _) t
    · exact OMA.ann _ 1 (by decide) (OMA.perG0 _) t
    · exact OMA.ann _ 1 (by decide) (OMA.perG0 _) t
  rw [OMA.hsd]
  simp only [OMA.L, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun i _ => ?_
  have h1 := hF i t
  have h2 := hG i t
  simp only [OMA.L] at h1 h2
  linarith

lemma OMA.hA (k : ℕ) : a (k + 4) = 2 * a (k + 3) - a (k + 2) + secondDiff (k + 3) := by
  show (counts (k + 2)).1 = 2 * (counts (k + 1)).1 - (counts k).1 + secondDiff (k + 3)
  first | rfl | simp only [counts]

lemma OMA.hrec : ∀ n : ℕ, 21 < n → a n = - a (n-2) + a (n-5) + a (n-6) + 2*a (n-7) + a (n-8) + a (n-9) - a (n-11) - a (n-12) - 2*a (n-13) - a (n-14) - a (n-15) + a (n-18) + a (n-20) := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 22 := ⟨n - 22, by omega⟩
  simp only [show m + 22 - 2 = m + 20 from rfl,
    show m + 22 - 5 = m + 17 from rfl,
    show m + 22 - 6 = m + 16 from rfl,
    show m + 22 - 7 = m + 15 from rfl,
    show m + 22 - 8 = m + 14 from rfl,
    show m + 22 - 9 = m + 13 from rfl,
    show m + 22 - 11 = m + 11 from rfl,
    show m + 22 - 12 = m + 10 from rfl,
    show m + 22 - 13 = m + 9 from rfl,
    show m + 22 - 14 = m + 8 from rfl,
    show m + 22 - 15 = m + 7 from rfl,
    show m + 22 - 18 = m + 4 from rfl,
    show m + 22 - 20 = m + 2 from rfl]
  have hs := OMA.sE (m + 3)
  simp only [OMA.L, show m + 3 + 1 = m + 4 from rfl,
    show m + 3 + 2 = m + 5 from rfl,
    show m + 3 + 3 = m + 6 from rfl,
    show m + 3 + 4 = m + 7 from rfl,
    show m + 3 + 5 = m + 8 from rfl,
    show m + 3 + 6 = m + 9 from rfl,
    show m + 3 + 7 = m + 10 from rfl,
    show m + 3 + 8 = m + 11 from rfl,
    show m + 3 + 9 = m + 12 from rfl,
    show m + 3 + 10 = m + 13 from rfl,
    show m + 3 + 11 = m + 14 from rfl,
    show m + 3 + 12 = m + 15 from rfl,
    show m + 3 + 13 = m + 16 from rfl,
    show m + 3 + 14 = m + 17 from rfl,
    show m + 3 + 15 = m + 18 from rfl,
    show m + 3 + 16 = m + 19 from rfl,
    show m + 3 + 17 = m + 20 from rfl,
    show m + 3 + 18 = m + 21 from rfl] at hs
  have a0 : a (m + 4) = 2 * a (m + 3) - a (m + 2) + secondDiff (m + 3) := OMA.hA _
  have a1 : a (m + 5) = 2 * a (m + 4) - a (m + 3) + secondDiff (m + 4) := OMA.hA _
  have a2 : a (m + 6) = 2 * a (m + 5) - a (m + 4) + secondDiff (m + 5) := OMA.hA _
  have a3 : a (m + 7) = 2 * a (m + 6) - a (m + 5) + secondDiff (m + 6) := OMA.hA _
  have a4 : a (m + 8) = 2 * a (m + 7) - a (m + 6) + secondDiff (m + 7) := OMA.hA _
  have a5 : a (m + 9) = 2 * a (m + 8) - a (m + 7) + secondDiff (m + 8) := OMA.hA _
  have a6 : a (m + 10) = 2 * a (m + 9) - a (m + 8) + secondDiff (m + 9) := OMA.hA _
  have a7 : a (m + 11) = 2 * a (m + 10) - a (m + 9) + secondDiff (m + 10) := OMA.hA _
  have a8 : a (m + 12) = 2 * a (m + 11) - a (m + 10) + secondDiff (m + 11) := OMA.hA _
  have a9 : a (m + 13) = 2 * a (m + 12) - a (m + 11) + secondDiff (m + 12) := OMA.hA _
  have a10 : a (m + 14) = 2 * a (m + 13) - a (m + 12) + secondDiff (m + 13) := OMA.hA _
  have a11 : a (m + 15) = 2 * a (m + 14) - a (m + 13) + secondDiff (m + 14) := OMA.hA _
  have a12 : a (m + 16) = 2 * a (m + 15) - a (m + 14) + secondDiff (m + 15) := OMA.hA _
  have a13 : a (m + 17) = 2 * a (m + 16) - a (m + 15) + secondDiff (m + 16) := OMA.hA _
  have a14 : a (m + 18) = 2 * a (m + 17) - a (m + 16) + secondDiff (m + 17) := OMA.hA _
  have a15 : a (m + 19) = 2 * a (m + 18) - a (m + 17) + secondDiff (m + 18) := OMA.hA _
  have a16 : a (m + 20) = 2 * a (m + 19) - a (m + 18) + secondDiff (m + 19) := OMA.hA _
  have a17 : a (m + 21) = 2 * a (m + 20) - a (m + 19) + secondDiff (m + 20) := OMA.hA _
  have a18 : a (m + 22) = 2 * a (m + 21) - a (m + 20) + secondDiff (m + 21) := OMA.hA _
  linarith

theorem OMA.solution : type_of% @OMA.S_oeis_a160850.main := by
  refine ⟨?_, OMA.hrec⟩
  have v0 : a 0 = 0 := rfl
  have v1 : a 1 = 1 := rfl
  have v2 : a 2 = 102 := rfl
  have v3 : a 3 = 203 := rfl
  have v4 : a 4 = 370 := by
    have h : a 4 = 2 * a 3 - a 2 + secondDiff 3 := OMA.hA _
    have s : secondDiff 3 = 66 := by decide
    linarith
  have v5 : a 5 = 563 := by
    have h : a 5 = 2 * a 4 - a 3 + secondDiff 4 := OMA.hA _
    have s : secondDiff 4 = 26 := by decide
    linarith
  have v6 : a 6 = 836 := by
    have h : a 6 = 2 * a 5 - a 4 + secondDiff 5 := OMA.hA _
    have s : secondDiff 5 = 80 := by decide
    linarith
  have v7 : a 7 = 1111 := by
    have h : a 7 = 2 * a 6 - a 5 + secondDiff 6 := OMA.hA _
    have s : secondDiff 6 = 2 := by decide
    linarith
  have v8 : a 8 = 1470 := by
    have h : a 8 = 2 * a 7 - a 6 + secondDiff 7 := OMA.hA _
    have s : secondDiff 7 = 84 := by decide
    linarith
  have v9 : a 9 = 1855 := by
    have h : a 9 = 2 * a 8 - a 7 + secondDiff 8 := OMA.hA _
    have s : secondDiff 8 = 26 := by decide
    linarith
  have v10 : a 10 = 2306 := by
    have h : a 10 = 2 * a 9 - a 8 + secondDiff 9 := OMA.hA _
    have s : secondDiff 9 = 66 := by decide
    linarith
  have v11 : a 11 = 2757 := by
    have h : a 11 = 2 * a 10 - a 9 + secondDiff 10 := OMA.hA _
    have s : secondDiff 10 = 0 := by decide
    linarith
  have v12 : a 12 = 3298 := by
    have h : a 12 = 2 * a 11 - a 10 + secondDiff 11 := OMA.hA _
    have s : secondDiff 11 = 90 := by decide
    linarith
  have v13 : a 13 = 3857 := by
    have h : a 13 = 2 * a 12 - a 11 + secondDiff 12 := OMA.hA _
    have s : secondDiff 12 = 18 := by decide
    linarith
  have v14 : a 14 = 4506 := by
    have h : a 14 = 2 * a 13 - a 12 + secondDiff 13 := OMA.hA _
    have s : secondDiff 13 = 90 := by decide
    linarith
  have v15 : a 15 = 5159 := by
    have h : a 15 = 2 * a 14 - a 13 + secondDiff 14 := OMA.hA _
    have s : secondDiff 14 = 4 := by decide
    linarith
  have v16 : a 16 = 5868 := by
    have h : a 16 = 2 * a 15 - a 14 + secondDiff 15 := OMA.hA _
    have s : secondDiff 15 = 56 := by decide
    linarith
  have v17 : a 17 = 6603 := by
    have h : a 17 = 2 * a 16 - a 15 + secondDiff 16 := OMA.hA _
    have s : secondDiff 16 = 26 := by decide
    linarith
  have v18 : a 18 = 7428 := by
    have h : a 18 = 2 * a 17 - a 16 + secondDiff 17 := OMA.hA _
    have s : secondDiff 17 = 90 := by decide
    linarith
  have v19 : a 19 = 8255 := by
    have h : a 19 = 2 * a 18 - a 17 + secondDiff 18 := OMA.hA _
    have s : secondDiff 18 = 2 := by decide
    linarith
  have v20 : a 20 = 9172 := by
    have h : a 20 = 2 * a 19 - a 18 + secondDiff 19 := OMA.hA _
    have s : secondDiff 19 = 90 := by decide
    linarith
  have v21 : a 21 = 10105 := by
    have h : a 21 = 2 * a 20 - a 19 + secondDiff 20 := OMA.hA _
    have s : secondDiff 20 = 16 := by decide
    linarith
  ext k
  rw [show ((1-X)^3*(1+X)*(1-X+X^2)*(1+X^2)*(1+X+X^2)*(1+X+X^2+X^3+X^4)*(1+X+X^2+X^3+X^4+X^5+X^6) : PowerSeries ℤ) =
      1 + X ^ 2 - X ^ 5 - X ^ 6 - 2 • X ^ 7 - X ^ 8 - X ^ 9 + X ^ 11 + X ^ 12 + 2 • X ^ 13 + X ^ 14 + X ^ 15 - X ^ 18 - X ^ 20 by ring,
    show (X*(1 + 102*X + 204*X^2 + 472*X^3 + 766*X^4 + 1205*X^5 + 1571*X^6 + 1999*X^7 + 2188*X^8 + 2334*X^9 + 2168*X^10 + 1959*X^11 + 1531*X^12 + 1165*X^13 + 746*X^14 + 462*X^15 + 214*X^16 + 112*X^17 + 21*X^18 + 10*X^19 + 10*X^20) : PowerSeries ℤ) =
      X ^ 1 + 102 • X ^ 2 + 204 • X ^ 3 + 472 • X ^ 4 + 766 • X ^ 5 + 1205 • X ^ 6 + 1571 • X ^ 7 + 1999 • X ^ 8 + 2188 • X ^ 9 + 2334 • X ^ 10 + 2168 • X ^ 11 + 1959 • X ^ 12 + 1531 • X ^ 13 + 1165 • X ^ 14 + 746 • X ^ 15 + 462 • X ^ 16 + 214 • X ^ 17 + 112 • X ^ 18 + 21 • X ^ 19 + 10 • X ^ 20 + 10 • X ^ 21 by ring]
  simp only [mul_add, mul_sub, mul_one, mul_smul_comm, map_add, map_sub, map_nsmul,
    coeff_mul_X_pow', coeff_mk, coeff_X_pow]
  by_cases hk : k < 22
  · interval_cases k <;> norm_num [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21]
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + 22 := ⟨k - 22, by omega⟩
    have h := OMA.hrec (m + 22) (by omega)
    simp only [show m + 22 - 2 = m + 20 from rfl,
      show m + 22 - 5 = m + 17 from rfl,
      show m + 22 - 6 = m + 16 from rfl,
      show m + 22 - 7 = m + 15 from rfl,
      show m + 22 - 8 = m + 14 from rfl,
      show m + 22 - 9 = m + 13 from rfl,
      show m + 22 - 11 = m + 11 from rfl,
      show m + 22 - 12 = m + 10 from rfl,
      show m + 22 - 13 = m + 9 from rfl,
      show m + 22 - 14 = m + 8 from rfl,
      show m + 22 - 15 = m + 7 from rfl,
      show m + 22 - 18 = m + 4 from rfl,
      show m + 22 - 20 = m + 2 from rfl] at h ⊢
    simp only [if_pos (show 2 ≤ m + 22 by omega),
      if_pos (show 5 ≤ m + 22 by omega),
      if_pos (show 6 ≤ m + 22 by omega),
      if_pos (show 7 ≤ m + 22 by omega),
      if_pos (show 8 ≤ m + 22 by omega),
      if_pos (show 9 ≤ m + 22 by omega),
      if_pos (show 11 ≤ m + 22 by omega),
      if_pos (show 12 ≤ m + 22 by omega),
      if_pos (show 13 ≤ m + 22 by omega),
      if_pos (show 14 ≤ m + 22 by omega),
      if_pos (show 15 ≤ m + 22 by omega),
      if_pos (show 18 ≤ m + 22 by omega),
      if_pos (show 20 ≤ m + 22 by omega),
      if_neg (show ¬ (m + 22 = 1) by omega),
      if_neg (show ¬ (m + 22 = 2) by omega),
      if_neg (show ¬ (m + 22 = 3) by omega),
      if_neg (show ¬ (m + 22 = 4) by omega),
      if_neg (show ¬ (m + 22 = 5) by omega),
      if_neg (show ¬ (m + 22 = 6) by omega),
      if_neg (show ¬ (m + 22 = 7) by omega),
      if_neg (show ¬ (m + 22 = 8) by omega),
      if_neg (show ¬ (m + 22 = 9) by omega),
      if_neg (show ¬ (m + 22 = 10) by omega),
      if_neg (show ¬ (m + 22 = 11) by omega),
      if_neg (show ¬ (m + 22 = 12) by omega),
      if_neg (show ¬ (m + 22 = 13) by omega),
      if_neg (show ¬ (m + 22 = 14) by omega),
      if_neg (show ¬ (m + 22 = 15) by omega),
      if_neg (show ¬ (m + 22 = 16) by omega),
      if_neg (show ¬ (m + 22 = 17) by omega),
      if_neg (show ¬ (m + 22 = 18) by omega),
      if_neg (show ¬ (m + 22 = 19) by omega),
      if_neg (show ¬ (m + 22 = 20) by omega),
      if_neg (show ¬ (m + 22 = 21) by omega),
      nsmul_eq_mul]
    push_cast
    linarith
