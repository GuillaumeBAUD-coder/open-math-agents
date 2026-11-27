import OMAStatements.S_mo_228227
import Mathlib

/- The order-pattern coloring is from the answer by domotorp, MathOverflow 516757. -/

namespace OMA.P228227

def F3 {n : ℕ} (A : Finset (Fin n)) (a1 a2 a3 : Fin n) : Prop :=
  a1 ∈ A ∧ a2 ∈ A ∧ a3 ∈ A ∧ a1 < a2 ∧ a2 < a3 ∧ ∀ x ∈ A, x = a1 ∨ x = a2 ∨ a3 ≤ x

lemma F3_unique {n : ℕ} {A : Finset (Fin n)} {a1 a2 a3 b1 b2 b3 : Fin n}
    (h : F3 A a1 a2 a3) (g : F3 A b1 b2 b3) : a1 = b1 ∧ a2 = b2 ∧ a3 = b3 := by
  obtain ⟨m1, m2, m3, l1, l2, hA⟩ := h
  obtain ⟨p1, p2, p3, q1, q2, hB⟩ := g
  have e1 := hA b1 p1
  have e2 := hA b2 p2
  have e3 := hA b3 p3
  have e4 := hB a1 m1
  have e5 := hB a2 m2
  have e6 := hB a3 m3
  simp only [Fin.lt_def, Fin.le_def, Fin.ext_iff] at l1 l2 q1 q2 e1 e2 e3 e4 e5 e6 ⊢
  omega

def P {n : ℕ} (A B : Finset (Fin n)) : Prop :=
  ∃ a1 a2 a3 b1 b2 b3 : Fin n, F3 A a1 a2 a3 ∧ F3 B b1 b2 b3 ∧ a2 < b1 ∧ b1 < a3 ∧ a3 < b2

lemma P_spec {n : ℕ} {A B : Finset (Fin n)} {a1 a2 a3 b1 b2 b3 : Fin n}
    (h : P A B) (hA : F3 A a1 a2 a3) (hB : F3 B b1 b2 b3) : a2 < b1 ∧ b1 < a3 ∧ a3 < b2 := by
  obtain ⟨x1, x2, x3, y1, y2, y3, hx, hy, c1, c2, c3⟩ := h
  obtain ⟨r1, r2, r3⟩ := F3_unique hx hA
  obtain ⟨s1, s2, s3⟩ := F3_unique hy hB
  subst r1 r2 r3 s1 s2 s3
  exact ⟨c1, c2, c3⟩

lemma P_left {n : ℕ} {A B : Finset (Fin n)} (h : P A B) : ∃ a1 a2 a3, F3 A a1 a2 a3 := by
  obtain ⟨x1, x2, x3, y1, y2, y3, hx, hy, c1, c2, c3⟩ := h
  exact ⟨x1, x2, x3, hx⟩

lemma P_right {n : ℕ} {A B : Finset (Fin n)} (h : P A B) : ∃ b1 b2 b3, F3 B b1 b2 b3 := by
  obtain ⟨x1, x2, x3, y1, y2, y3, hx, hy, c1, c2, c3⟩ := h
  exact ⟨y1, y2, y3, hy⟩

lemma pair_spec {n : ℕ} {A B : Finset (Fin n)} {a1 a2 a3 b1 b2 b3 : Fin n}
    (h : P A B ∨ P B A) (hA : F3 A a1 a2 a3) (hB : F3 B b1 b2 b3) :
    (a2 < b1 ∧ b1 < a3 ∧ a3 < b2) ∨ (b2 < a1 ∧ a1 < b3 ∧ b3 < a2) := by
  rcases h with h | h
  · exact Or.inl (P_spec h hA hB)
  · exact Or.inr (P_spec h hB hA)

lemma no_red_triangle {n : ℕ} {A B C : Finset (Fin n)}
    (hAB : P A B ∨ P B A) (hBC : P B C ∨ P C B) (hAC : P A C ∨ P C A) : False := by
  have hA : ∃ a1 a2 a3, F3 A a1 a2 a3 := by
    rcases hAB with h | h
    · exact P_left h
    · exact P_right h
  have hB : ∃ b1 b2 b3, F3 B b1 b2 b3 := by
    rcases hAB with h | h
    · exact P_right h
    · exact P_left h
  have hC : ∃ c1 c2 c3, F3 C c1 c2 c3 := by
    rcases hBC with h | h
    · exact P_right h
    · exact P_left h
  obtain ⟨a1, a2, a3, hA⟩ := hA
  obtain ⟨b1, b2, b3, hB⟩ := hB
  obtain ⟨c1, c2, c3, hC⟩ := hC
  have t1 := pair_spec hAB hA hB
  have t2 := pair_spec hBC hB hC
  have t3 := pair_spec hAC hA hC
  have u1 := hA.2.2.2.1
  have u2 := hA.2.2.2.2.1
  have v1 := hB.2.2.2.1
  have v2 := hB.2.2.2.2.1
  have w1 := hC.2.2.2.1
  have w2 := hC.2.2.2.2.1
  simp only [Fin.lt_def] at t1 t2 t3 u1 u2 v1 v2 w1 w2
  omega

def gN (i : ℕ) : ℕ := if i = 0 then 0 else if i = 1 then 1 else if i = 2 then 3 else i + 3

def hN (k i : ℕ) : ℕ := if i = 0 then 2 else if i = 1 then 4 else if i = 2 then 5 else i + k

lemma gN_lt {k i : ℕ} (hk : 3 ≤ k) (hi : i < k) : gN i < 3 * k := by
  unfold gN; split_ifs <;> omega

lemma hN_lt {k i : ℕ} (hk : 3 ≤ k) (hi : i < k) : hN k i < 3 * k := by
  unfold hN; split_ifs <;> omega

lemma gN_inj {i j : ℕ} (h : gN i = gN j) : i = j := by
  unfold gN at h; split_ifs at h <;> omega

lemma hN_inj {k i j : ℕ} (hk : 3 ≤ k) (h : hN k i = hN k j) : i = j := by
  unfold hN at h; split_ifs at h <;> omega

lemma gN_ne_hN {k i j : ℕ} (hk : 3 ≤ k) (hi : i < k) : gN i ≠ hN k j := by
  unfold gN hN; split_ifs <;> omega

lemma gN_cases (i : ℕ) : gN i = 0 ∨ gN i = 1 ∨ 3 ≤ gN i := by
  unfold gN; split_ifs <;> omega

lemma hN_cases {k : ℕ} (hk : 3 ≤ k) (i : ℕ) : hN k i = 2 ∨ hN k i = 4 ∨ 5 ≤ hN k i := by
  unfold hN; split_ifs <;> omega

def fa {n k : ℕ} (hk : 3 ≤ k) (e : Fin (3 * k) ↪o Fin n) (i : Fin k) : Fin n :=
  e ⟨gN i.val, gN_lt hk i.isLt⟩

def fb {n k : ℕ} (hk : 3 ≤ k) (e : Fin (3 * k) ↪o Fin n) (i : Fin k) : Fin n :=
  e ⟨hN k i.val, hN_lt hk i.isLt⟩

lemma fa_inj {n k : ℕ} (hk : 3 ≤ k) (e : Fin (3 * k) ↪o Fin n) : Function.Injective (fa hk e) := by
  intro i j h
  have h1 := e.injective h
  exact Fin.ext (gN_inj (Fin.mk.inj h1))

lemma fb_inj {n k : ℕ} (hk : 3 ≤ k) (e : Fin (3 * k) ↪o Fin n) : Function.Injective (fb hk e) := by
  intro i j h
  have h1 := e.injective h
  exact Fin.ext (hN_inj hk (Fin.mk.inj h1))

lemma fa_ne_fb {n k : ℕ} (hk : 3 ≤ k) (e : Fin (3 * k) ↪o Fin n) (i j : Fin k) :
    fa hk e i ≠ fb hk e j := by
  intro h
  have h1 := e.injective h
  exact gN_ne_hN hk i.isLt (Fin.mk.inj h1)

lemma F3_A {n k : ℕ} (hk : 3 ≤ k) (e : Fin (3 * k) ↪o Fin n) :
    F3 (Finset.univ.image (fa hk e)) (e ⟨0, by omega⟩) (e ⟨1, by omega⟩) (e ⟨3, by omega⟩) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨⟨0, by omega⟩, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨⟨1, by omega⟩, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨⟨2, by omega⟩, Finset.mem_univ _, rfl⟩
  · exact e.lt_iff_lt.mpr (Fin.mk_lt_mk.mpr (by omega))
  · exact e.lt_iff_lt.mpr (Fin.mk_lt_mk.mpr (by omega))
  · intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    rcases gN_cases i.val with h | h | h
    · left; exact congrArg e (Fin.ext h)
    · right; left; exact congrArg e (Fin.ext h)
    · right; right; exact e.le_iff_le.mpr (Fin.mk_le_mk.mpr h)

lemma F3_B {n k : ℕ} (hk : 3 ≤ k) (e : Fin (3 * k) ↪o Fin n) :
    F3 (Finset.univ.image (fb hk e)) (e ⟨2, by omega⟩) (e ⟨4, by omega⟩) (e ⟨5, by omega⟩) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨⟨0, by omega⟩, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨⟨1, by omega⟩, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨⟨2, by omega⟩, Finset.mem_univ _, rfl⟩
  · exact e.lt_iff_lt.mpr (Fin.mk_lt_mk.mpr (by omega))
  · exact e.lt_iff_lt.mpr (Fin.mk_lt_mk.mpr (by omega))
  · intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    rcases hN_cases hk i.val with h | h | h
    · left; exact congrArg e (Fin.ext h)
    · right; left; exact congrArg e (Fin.ext h)
    · right; right; exact e.le_iff_le.mpr (Fin.mk_le_mk.mpr h)

lemma exists_red {n k : ℕ} (hk : 3 ≤ k) (S : Finset (Fin n)) (hS : S.card = 3 * k) :
    ∃ A B : Finset (Fin n), A ⊆ S ∧ B ⊆ S ∧ A.card = k ∧ B.card = k ∧ Disjoint A B ∧ P A B := by
  refine ⟨Finset.univ.image (fa hk (S.orderEmbOfFin hS)),
    Finset.univ.image (fb hk (S.orderEmbOfFin hS)), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.orderEmbOfFin_mem S hS _
  · intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.orderEmbOfFin_mem S hS _
  · rw [Finset.card_image_of_injective _ (fa_inj hk _)]
    simp
  · rw [Finset.card_image_of_injective _ (fb_inj hk _)]
    simp
  · rw [Finset.disjoint_left]
    intro x hx hy
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hy
    exact fa_ne_fb hk _ i j hj.symm
  · exact ⟨_, _, _, _, _, _, F3_A hk _, F3_B hk _,
      (S.orderEmbOfFin hS).lt_iff_lt.mpr (Fin.mk_lt_mk.mpr (by omega)),
      (S.orderEmbOfFin hS).lt_iff_lt.mpr (Fin.mk_lt_mk.mpr (by omega)),
      (S.orderEmbOfFin hS).lt_iff_lt.mpr (Fin.mk_lt_mk.mpr (by omega))⟩

end OMA.P228227

theorem OMA.solution : type_of% @OMA.S_mo_228227.main := by
  intro k hk N
  refine ⟨N, le_rfl, fun A B => OMA.P228227.P A B ∨ OMA.P228227.P B A, ?_, ?_, ?_⟩
  · intro A B
    exact Or.comm
  · intro S hS
    obtain ⟨A, B, h1, h2, h3, h4, h5, h6⟩ := OMA.P228227.exists_red hk S hS
    exact ⟨A, B, h1, h2, h3, h4, h5, Or.inl h6⟩
  · intro A B C _ _ _ _ _ _ h
    exact OMA.P228227.no_red_triangle h.1 h.2.1 h.2.2
