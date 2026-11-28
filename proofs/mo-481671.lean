import OMAStatements.S_mo_481671

/-!
Disproof. Let D be the circulant digraph on Z/13 with arcs i -> i + s, s in {1, 2, 4, 7}. The 26
objects are a_0, ..., a_12 (numbers 0 to 12) and b_0, ..., b_12 (numbers 13 to 25).

* A set I of vertices is acyclic in D exactly when some linear order puts a_i before b_j for every
  arc i -> j and puts b_i before a_i for every i in I.
* The set {0, 1, 2, 3, 5, 8, 11} is acyclic. Its 13 rotations cover every vertex 7 times. The 13 corresponding
  ballots order a_i before b_j unanimously for each arc i -> j, and order b_i before a_i in 7 of
  the 13 ballots. There are no ties.
* Two permutations that cover the multigraph give two acyclic sets that cover Z/13. Every
  2-colouring of Z/13 has a monochromatic directed 3-cycle or 4-cycle of D, which is a contradiction.
-/

namespace MO481671

def mk (f g : Fin 26 → Fin 26) (h1 : ∀ x, g (f x) = x) (h2 : ∀ x, f (g x) = x) :
    Equiv.Perm (Fin 26) := ⟨f, g, h1, h2⟩

def p0 : Equiv.Perm (Fin 26) := mk
  ![9, 11, 15, 17, 0, 20, 1, 2, 13, 3, 4, 7, 5, 8, 10, 14, 16, 18, 19, 21, 22, 12, 23, 24, 6, 25]
  ![4, 6, 7, 9, 10, 12, 24, 11, 13, 0, 14, 1, 21, 8, 15, 2, 16, 3, 17, 18, 5, 19, 20, 22, 23, 25]
  (by decide +kernel) (by decide +kernel)

def p1 : Equiv.Perm (Fin 26) := mk
  ![5, 9, 11, 15, 17, 0, 20, 1, 2, 13, 3, 4, 7, 25, 8, 10, 14, 16, 18, 19, 21, 22, 12, 23, 24, 6]
  ![5, 7, 8, 10, 11, 0, 25, 12, 14, 1, 15, 2, 22, 9, 16, 3, 17, 4, 18, 19, 6, 20, 21, 23, 24, 13]
  (by decide +kernel) (by decide +kernel)

def p2 : Equiv.Perm (Fin 26) := mk
  ![7, 5, 9, 11, 15, 17, 0, 20, 1, 2, 13, 3, 4, 6, 25, 8, 10, 14, 16, 18, 19, 21, 22, 12, 23, 24]
  ![6, 8, 9, 11, 12, 1, 13, 0, 15, 2, 16, 3, 23, 10, 17, 4, 18, 5, 19, 20, 7, 21, 22, 24, 25, 14]
  (by decide +kernel) (by decide +kernel)

def p3 : Equiv.Perm (Fin 26) := mk
  ![4, 7, 5, 9, 11, 15, 17, 0, 20, 1, 2, 13, 3, 24, 6, 25, 8, 10, 14, 16, 18, 19, 21, 22, 12, 23]
  ![7, 9, 10, 12, 0, 2, 14, 1, 16, 3, 17, 4, 24, 11, 18, 5, 19, 6, 20, 21, 8, 22, 23, 25, 13, 15]
  (by decide +kernel) (by decide +kernel)

def p4 : Equiv.Perm (Fin 26) := mk
  ![3, 4, 7, 5, 9, 11, 15, 17, 0, 20, 1, 2, 13, 23, 24, 6, 25, 8, 10, 14, 16, 18, 19, 21, 22, 12]
  ![8, 10, 11, 0, 1, 3, 15, 2, 17, 4, 18, 5, 25, 12, 19, 6, 20, 7, 21, 22, 9, 23, 24, 13, 14, 16]
  (by decide +kernel) (by decide +kernel)

def p5 : Equiv.Perm (Fin 26) := mk
  ![13, 3, 4, 7, 5, 9, 11, 15, 17, 0, 20, 1, 2, 12, 23, 24, 6, 25, 8, 10, 14, 16, 18, 19, 21, 22]
  ![9, 11, 12, 1, 2, 4, 16, 3, 18, 5, 19, 6, 13, 0, 20, 7, 21, 8, 22, 23, 10, 24, 25, 14, 15, 17]
  (by decide +kernel) (by decide +kernel)

def p6 : Equiv.Perm (Fin 26) := mk
  ![2, 13, 3, 4, 7, 5, 9, 11, 15, 17, 0, 20, 1, 22, 12, 23, 24, 6, 25, 8, 10, 14, 16, 18, 19, 21]
  ![10, 12, 0, 2, 3, 5, 17, 4, 19, 6, 20, 7, 14, 1, 21, 8, 22, 9, 23, 24, 11, 25, 13, 15, 16, 18]
  (by decide +kernel) (by decide +kernel)

def p7 : Equiv.Perm (Fin 26) := mk
  ![1, 2, 13, 3, 4, 7, 5, 9, 11, 15, 17, 0, 20, 21, 22, 12, 23, 24, 6, 25, 8, 10, 14, 16, 18, 19]
  ![11, 0, 1, 3, 4, 6, 18, 5, 20, 7, 21, 8, 15, 2, 22, 9, 23, 10, 24, 25, 12, 13, 14, 16, 17, 19]
  (by decide +kernel) (by decide +kernel)

def p8 : Equiv.Perm (Fin 26) := mk
  ![20, 1, 2, 13, 3, 4, 7, 5, 9, 11, 15, 17, 0, 19, 21, 22, 12, 23, 24, 6, 25, 8, 10, 14, 16, 18]
  ![12, 1, 2, 4, 5, 7, 19, 6, 21, 8, 22, 9, 16, 3, 23, 10, 24, 11, 25, 13, 0, 14, 15, 17, 18, 20]
  (by decide +kernel) (by decide +kernel)

def p9 : Equiv.Perm (Fin 26) := mk
  ![0, 20, 1, 2, 13, 3, 4, 7, 5, 9, 11, 15, 17, 18, 19, 21, 22, 12, 23, 24, 6, 25, 8, 10, 14, 16]
  ![0, 2, 3, 5, 6, 8, 20, 7, 22, 9, 23, 10, 17, 4, 24, 11, 25, 12, 13, 14, 1, 15, 16, 18, 19, 21]
  (by decide +kernel) (by decide +kernel)

def p10 : Equiv.Perm (Fin 26) := mk
  ![17, 0, 20, 1, 2, 13, 3, 4, 7, 5, 9, 11, 15, 16, 18, 19, 21, 22, 12, 23, 24, 6, 25, 8, 10, 14]
  ![1, 3, 4, 6, 7, 9, 21, 8, 23, 10, 24, 11, 18, 5, 25, 12, 13, 0, 14, 15, 2, 16, 17, 19, 20, 22]
  (by decide +kernel) (by decide +kernel)

def p11 : Equiv.Perm (Fin 26) := mk
  ![15, 17, 0, 20, 1, 2, 13, 3, 4, 7, 5, 9, 11, 14, 16, 18, 19, 21, 22, 12, 23, 24, 6, 25, 8, 10]
  ![2, 4, 5, 7, 8, 10, 22, 9, 24, 11, 25, 12, 19, 6, 13, 0, 14, 1, 15, 16, 3, 17, 18, 20, 21, 23]
  (by decide +kernel) (by decide +kernel)

def p12 : Equiv.Perm (Fin 26) := mk
  ![11, 15, 17, 0, 20, 1, 2, 13, 3, 4, 7, 5, 9, 10, 14, 16, 18, 19, 21, 22, 12, 23, 24, 6, 25, 8]
  ![3, 5, 6, 8, 9, 11, 23, 10, 25, 12, 13, 0, 20, 7, 14, 1, 15, 2, 16, 17, 4, 18, 19, 21, 22, 24]
  (by decide +kernel) (by decide +kernel)

def ballots : List (Equiv.Perm (Fin 26)) :=
  [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12]

/-- The arcs of the circulant digraph. -/
def arc (i j : Fin 13) : Bool :=
  [1, 2, 4, 7].contains ((j.val + 13 - i.val) % 13)

def a (i : Fin 13) : Fin 26 := ⟨i.val, by omega⟩

def b (i : Fin 13) : Fin 26 := ⟨i.val + 13, by omega⟩

theorem ab_ne : ∀ i j : Fin 13, a i ≠ b j := by
  intro i j h
  have := congrArg Fin.val h
  simp [a, b] at this
  omega

theorem ballots_arc : ∀ i j : Fin 13, arc i j = true →
    OMA.S_mo_481671.multiplicity ballots (a i) (b j) = 2 := by decide +kernel

theorem ballots_rev : ∀ i : Fin 13,
    OMA.S_mo_481671.multiplicity ballots (b i) (a i) = 1 := by decide +kernel

theorem two_of_mult {n : ℕ} (p q : Equiv.Perm (Fin n)) (x y : Fin n)
    (h : 2 ≤ OMA.S_mo_481671.multiplicity [p, q] x y) : p x < p y ∧ q x < q y := by
  unfold OMA.S_mo_481671.multiplicity at h
  by_cases hxy : x = y
  · simp [hxy] at h
  · by_cases hp : p x < p y <;> by_cases hq : q x < q y <;> simp [hxy, hp, hq] at h ⊢

theorem one_of_mult {n : ℕ} (p q : Equiv.Perm (Fin n)) (x y : Fin n)
    (h : 1 ≤ OMA.S_mo_481671.multiplicity [p, q] x y) : p x < p y ∨ q x < q y := by
  unfold OMA.S_mo_481671.multiplicity at h
  by_cases hxy : x = y
  · simp [hxy] at h
  · by_cases hp : p x < p y <;> by_cases hq : q x < q y <;> simp [hxy, hp, hq] at h ⊢

/-- Some listed directed cycle is monochromatic. -/
def goodB (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 : Bool) : Bool :=
  (c1 == c5 && c5 == c7) ||
  ((c2 == c9 && c9 == c11) ||
  ((c3 == c5 && c5 == c9) ||
  ((c0 == c7 && c7 == c9) ||
  ((c0 == c2 && c2 == c6) ||
  ((c0 == c4 && c4 == c11) ||
  ((c2 == c4 && c4 == c8) ||
  ((c4 == c6 && c6 == c10) ||
  ((c6 == c8 && c8 == c12) ||
  ((c1 == c8 && c8 == c10) ||
  ((c3 == c10 && c10 == c12) ||
  ((c5 == c7 && c7 == c11) ||
  ((c1 == c3 && c3 == c7) ||
  ((c1 == c5 && c5 == c12) ||
  ((c0 == c4 && (c4 == c5 && c5 == c12)) ||
  ((c0 == c1 && (c1 == c5 && c5 == c6)) ||
  ((c0 == c1 && (c1 == c8 && c8 == c9)) ||
  ((c6 == c7 && (c7 == c11 && c11 == c12)) ||
  ((c3 == c4 && (c4 == c11 && c11 == c12)) ||
  ((c1 == c2 && (c2 == c6 && c6 == c7)) ||
  ((c2 == c3 && (c3 == c10 && c10 == c11)) ||
  ((c1 == c2 && (c2 == c9 && c9 == c10)) ||
  ((c0 == c7 && (c7 == c8 && c8 == c12)) ||
  ((c2 == c3 && (c3 == c7 && c7 == c8)) ||
  ((c4 == c5 && (c5 == c9 && c9 == c10)) ||
  ((c5 == c6 && (c6 == c10 && c10 == c11)) ||
  ((c3 == c4 && (c4 == c8 && c8 == c9))))))))))))))))))))))))))))

theorem good_all : ∀ c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 : Bool,
    goodB c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 = true := by decide +kernel

end MO481671

open MO481671 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_481671.main) := by
  intro h
  obtain ⟨p, q, hpq⟩ := h 26 (by norm_num) ballots (by simp [ballots])
  have hA : ∀ i j, arc i j = true → p (a i) < p (b j) ∧ q (a i) < q (b j) := by
    intro i j hij
    apply two_of_mult
    have := hpq (a i) (b j)
    rw [ballots_arc i j hij] at this
    exact this
  have hB : ∀ i, p (b i) < p (a i) ∨ q (b i) < q (a i) := by
    intro i
    apply one_of_mult
    have := hpq (b i) (a i)
    rw [ballots_rev i] at this
    exact this
  let c : Fin 13 → Bool := fun i => decide (p (b i) < p (a i))
  have step : ∀ i j, arc i j = true → c i = c j →
      (c i = true ∧ p (a i) < p (a j)) ∨ (c i = false ∧ q (a i) < q (a j)) := by
    intro i j hij hc
    by_cases hi : p (b i) < p (a i)
    · have hj : p (b j) < p (a j) := by
        have : c j = true := by rw [← hc]; simp [c, hi]
        simpa [c] using this
      exact Or.inl ⟨by simp [c, hi], lt_trans (hA i j hij).1 hj⟩
    · have hj : ¬ p (b j) < p (a j) := by
        have : c j = false := by rw [← hc]; simp [c, hi]
        simpa [c] using this
      have hj' := (hB j).resolve_left hj
      exact Or.inr ⟨by simp [c, hi], lt_trans (hA i j hij).2 hj'⟩
  have tri : ∀ x y z, arc x y = true → arc y z = true → arc z x = true →
      c x = c y → c y = c z → False := by
    intro x y z h1 h2 h3 e1 e2
    have s1 := step x y h1 e1
    have s2 := step y z h2 e2
    have s3 := step z x h3 (by rw [e1, e2])
    rw [e1, e2] at s1
    rw [e2] at s2
    rcases s1 with ⟨k1, s1⟩ | ⟨k1, s1⟩ <;> rcases s2 with ⟨k2, s2⟩ | ⟨k2, s2⟩ <;>
      rcases s3 with ⟨k3, s3⟩ | ⟨k3, s3⟩ <;>
      first
        | exact absurd (lt_trans s1 (lt_trans s2 s3)) (lt_irrefl _)
        | (rw [k1] at k2; exact absurd k2 (by decide))
        | (rw [k1] at k3; exact absurd k3 (by decide))
  have quad : ∀ x y z w, arc x y = true → arc y z = true → arc z w = true → arc w x = true →
      c x = c y → c y = c z → c z = c w → False := by
    intro x y z w h1 h2 h3 h4 e1 e2 e3
    have s1 := step x y h1 e1
    have s2 := step y z h2 e2
    have s3 := step z w h3 e3
    have s4 := step w x h4 (by rw [e1, e2, e3])
    rw [e1, e2, e3] at s1
    rw [e2, e3] at s2
    rw [e3] at s3
    rcases s1 with ⟨k1, s1⟩ | ⟨k1, s1⟩ <;> rcases s2 with ⟨k2, s2⟩ | ⟨k2, s2⟩ <;>
      rcases s3 with ⟨k3, s3⟩ | ⟨k3, s3⟩ <;> rcases s4 with ⟨k4, s4⟩ | ⟨k4, s4⟩ <;>
      first
        | exact absurd (lt_trans s1 (lt_trans s2 (lt_trans s3 s4))) (lt_irrefl _)
        | (rw [k1] at k2; exact absurd k2 (by decide))
        | (rw [k1] at k3; exact absurd k3 (by decide))
        | (rw [k1] at k4; exact absurd k4 (by decide))
  have hg := good_all (c 0) (c 1) (c 2) (c 3) (c 4) (c 5) (c 6) (c 7) (c 8) (c 9) (c 10) (c 11) (c 12)
  unfold goodB at hg
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hg
  rcases hg with ⟨e1, e2⟩ |
    ⟨e1, e2⟩ |
    ⟨e1, e2⟩ |
    ⟨e1, e2⟩ |
    ⟨e1, e2⟩ |
    ⟨e1, e2⟩ |
    ⟨e1, e2⟩ |
    ⟨e1, e2⟩ |
    ⟨e1, e2⟩ |
    ⟨e1, e2⟩ |
    ⟨e1, e2⟩ |
    ⟨e1, e2⟩ |
    ⟨e1, e2⟩ |
    ⟨e1, e2⟩ |
    ⟨e1, e2, e3⟩ |
    ⟨e1, e2, e3⟩ |
    ⟨e1, e2, e3⟩ |
    ⟨e1, e2, e3⟩ |
    ⟨e1, e2, e3⟩ |
    ⟨e1, e2, e3⟩ |
    ⟨e1, e2, e3⟩ |
    ⟨e1, e2, e3⟩ |
    ⟨e1, e2, e3⟩ |
    ⟨e1, e2, e3⟩ |
    ⟨e1, e2, e3⟩ |
    ⟨e1, e2, e3⟩ |
    ⟨e1, e2, e3⟩
  · exact tri 1 5 7 (by decide) (by decide) (by decide) e1 e2
  · exact tri 2 9 11 (by decide) (by decide) (by decide) e1 e2
  · exact tri 3 5 9 (by decide) (by decide) (by decide) e1 e2
  · exact tri 0 7 9 (by decide) (by decide) (by decide) e1 e2
  · exact tri 0 2 6 (by decide) (by decide) (by decide) e1 e2
  · exact tri 0 4 11 (by decide) (by decide) (by decide) e1 e2
  · exact tri 2 4 8 (by decide) (by decide) (by decide) e1 e2
  · exact tri 4 6 10 (by decide) (by decide) (by decide) e1 e2
  · exact tri 6 8 12 (by decide) (by decide) (by decide) e1 e2
  · exact tri 1 8 10 (by decide) (by decide) (by decide) e1 e2
  · exact tri 3 10 12 (by decide) (by decide) (by decide) e1 e2
  · exact tri 5 7 11 (by decide) (by decide) (by decide) e1 e2
  · exact tri 1 3 7 (by decide) (by decide) (by decide) e1 e2
  · exact tri 1 5 12 (by decide) (by decide) (by decide) e1 e2
  · exact quad 0 4 5 12 (by decide) (by decide) (by decide) (by decide) e1 e2 e3
  · exact quad 0 1 5 6 (by decide) (by decide) (by decide) (by decide) e1 e2 e3
  · exact quad 0 1 8 9 (by decide) (by decide) (by decide) (by decide) e1 e2 e3
  · exact quad 6 7 11 12 (by decide) (by decide) (by decide) (by decide) e1 e2 e3
  · exact quad 3 4 11 12 (by decide) (by decide) (by decide) (by decide) e1 e2 e3
  · exact quad 1 2 6 7 (by decide) (by decide) (by decide) (by decide) e1 e2 e3
  · exact quad 2 3 10 11 (by decide) (by decide) (by decide) (by decide) e1 e2 e3
  · exact quad 1 2 9 10 (by decide) (by decide) (by decide) (by decide) e1 e2 e3
  · exact quad 0 7 8 12 (by decide) (by decide) (by decide) (by decide) e1 e2 e3
  · exact quad 2 3 7 8 (by decide) (by decide) (by decide) (by decide) e1 e2 e3
  · exact quad 4 5 9 10 (by decide) (by decide) (by decide) (by decide) e1 e2 e3
  · exact quad 5 6 10 11 (by decide) (by decide) (by decide) (by decide) e1 e2 e3
  · exact quad 3 4 8 9 (by decide) (by decide) (by decide) (by decide) e1 e2 e3
