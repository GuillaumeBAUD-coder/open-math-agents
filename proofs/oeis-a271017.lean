import OMAStatements.S_oeis_a271017

-- Problem: A271017: Number of active (ON, black) cells at stage 2^n-1 of the two-dimensional cellular automaton defined by Rule 251, based on the 5-celled von Neumann neighborhood.
-- Upstream: formal-conjectures statements/oeis-a271017.lean:0 (declaration OMA.S_oeis_a271017.main)
-- Credit: @DevinWatson (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.E271017

open OMA.S_oeis_a271017

-- Rule 251 truth table: bit (c + 2*s) of 251 is false iff (c,s) in {(0,1), (0,4), (1,4)}.
private lemma testBit_251 (c : Bool) (n1 n2 n3 n4 : Bool) :
    (251 : ℕ).testBit (c.toNat + 2 * (n1.toNat + n2.toNat + n3.toNat + n4.toNat)) =
      !((n1 && n2 && n3 && n4) ||
        (!c && decide (n1.toNat + n2.toNat + n3.toNat + n4.toNat = 1))) := by
  cases c <;> cases n1 <;> cases n2 <;> cases n3 <;> cases n4 <;> rfl

-- Rotated 2-step sublattice CA on Z^2.
private def blockActive (S : ℤ → ℤ → Bool) (a b : ℤ) : Bool :=
  let s := (S a b).toNat + (S (a + 1) b).toNat + (S a (b + 1)).toNat + (S (a + 1) (b + 1)).toNat
  decide (s = 1 ∨ s = 4)

private def uvStep (S : ℤ → ℤ → Bool) (u v : ℤ) : Bool :=
  blockActive S u v || blockActive S (u - 1) v ||
    blockActive S u (v - 1) || blockActive S (u - 1) (v - 1)

private def S_iter : ℕ → ℤ → ℤ → Bool
  | 0 => fun u v => decide (u = 0 ∧ v = 0)
  | m + 1 => uvStep (S_iter m)

private def B_iter : ℕ → ℤ → ℤ → Bool
  | 0 => fun u v => decide (0 ≤ u ∧ u ≤ 1 ∧ 0 ≤ v ∧ v ≤ 1)
  | r + 1 => uvStep (B_iter r)

private def rect (a b c d u v : ℤ) : Bool :=
  decide (a ≤ u ∧ u ≤ b ∧ c ≤ v ∧ v ≤ d)

private def rectUnion (a b c d : ℤ) (F : ℤ → ℤ → Bool) (u v : ℤ) : Bool :=
  rect a b c d u v || F (u - b) (v - d) || F (u - (a - 1)) (v - d) ||
    F (u - b) (v - (c - 1)) || F (u - (a - 1)) (v - (c - 1))

private lemma blockActive_congr {S T : ℤ → ℤ → Bool} {a b : ℤ}
    (h00 : S a b = T a b) (h10 : S (a + 1) b = T (a + 1) b)
    (h01 : S a (b + 1) = T a (b + 1)) (h11 : S (a + 1) (b + 1) = T (a + 1) (b + 1)) :
    blockActive S a b = blockActive T a b := by
  simp only [blockActive, h00, h10, h01, h11]

private lemma cell_succ (t : ℕ) (i j : ℤ) :
    cell 251 (t + 1) i j =
      !((cell 251 t (i + 1) j && cell 251 t (i - 1) j && cell 251 t i (j + 1) && cell 251 t i (j - 1)) ||
        (!(cell 251 t i j) &&
          decide ((cell 251 t (i + 1) j).toNat + (cell 251 t (i - 1) j).toNat +
                  (cell 251 t i (j + 1)).toNat + (cell 251 t i (j - 1)).toNat = 1))) :=
  testBit_251 _ _ _ _ _

private lemma bool_251_odd (b00 b10 b01 b11 : Bool) :
    (!((b11 && b00 && b10 && b01) ||
      (!false && decide (b11.toNat + b00.toNat + b10.toNat + b01.toNat = 1)))) =
    (!decide (b00.toNat + b10.toNat + b01.toNat + b11.toNat = 1 ∨
              b00.toNat + b10.toNat + b01.toNat + b11.toNat = 4)) := by
  cases b00 <;> cases b10 <;> cases b01 <;> cases b11 <;> rfl

-- Exact correspondence between cell 251 and S_iter.
private lemma cell_even_odd (m : ℕ) :
    (∀ x y : ℤ, cell 251 (2 * m) x y =
      if (x + y) % 2 = 0 then S_iter m ((x + y) / 2) ((x - y) / 2) else false) ∧
    (∀ x y : ℤ, cell 251 (2 * m + 1) x y =
      if (x + y) % 2 = 0 then true
      else !blockActive (S_iter m) ((x + y - 1) / 2) ((x - y - 1) / 2)) := by
  induction m with
  | zero =>
    constructor
    · intro x y
      simp only [cell, S_iter]
      by_cases h : (x + y) % 2 = 0
      · rw [if_pos h]
        by_cases h0 : x = 0 ∧ y = 0
        · rcases h0 with ⟨rfl, rfl⟩; rfl
        · have hne : ¬((x + y) / 2 = 0 ∧ (x - y) / 2 = 0) := by omega
          simp [h0, hne]
      · rw [if_neg h]
        have hne : ¬(x = 0 ∧ y = 0) := by omega
        simp [hne]
    · intro x y
      simp only [Nat.mul_zero, zero_add]
      rw [cell_succ]
      simp only [cell, S_iter]
      by_cases h : (x + y) % 2 = 0
      · rw [if_pos h]
        have h1 : ¬(x + 1 = 0 ∧ y = 0) := by omega
        have h2 : ¬(x - 1 = 0 ∧ y = 0) := by omega
        have h3 : ¬(x = 0 ∧ y + 1 = 0) := by omega
        have h4 : ¬(x = 0 ∧ y - 1 = 0) := by omega
        simp [h1, h2, h3, h4]
      · rw [if_neg h]
        have h0 : ¬(x = 0 ∧ y = 0) := by omega
        set a := (x + y - 1) / 2
        set b := (x - y - 1) / 2
        have e1 : decide (x + 1 = 0 ∧ y = 0) = decide (a + 1 = 0 ∧ b + 1 = 0) :=
          decide_eq_decide.mpr (by omega)
        have e2 : decide (x - 1 = 0 ∧ y = 0) = decide (a = 0 ∧ b = 0) :=
          decide_eq_decide.mpr (by omega)
        have e3 : decide (x = 0 ∧ y + 1 = 0) = decide (a + 1 = 0 ∧ b = 0) :=
          decide_eq_decide.mpr (by omega)
        have e4 : decide (x = 0 ∧ y - 1 = 0) = decide (a = 0 ∧ b + 1 = 0) :=
          decide_eq_decide.mpr (by omega)
        simp only [h0, decide_false, e1, e2, e3, e4]
        dsimp only [blockActive]
        exact bool_251_odd (decide (a = 0 ∧ b = 0)) (decide (a + 1 = 0 ∧ b = 0))
          (decide (a = 0 ∧ b + 1 = 0)) (decide (a + 1 = 0 ∧ b + 1 = 0))
  | succ m ih =>
    rcases ih with ⟨ih_even, ih_odd⟩
    have h_even_next : ∀ x y : ℤ, cell 251 (2 * (m + 1)) x y =
        if (x + y) % 2 = 0 then S_iter (m + 1) ((x + y) / 2) ((x - y) / 2) else false := by
      intro x y
      rw [show 2 * (m + 1) = (2 * m + 1) + 1 by omega, cell_succ]
      simp only [ih_odd]
      by_cases h : (x + y) % 2 = 0
      · rw [if_pos h, if_pos h]
        have h1 : (x + 1 + y) % 2 ≠ 0 := by omega
        have h2 : (x - 1 + y) % 2 ≠ 0 := by omega
        have h3 : (x + (y + 1)) % 2 ≠ 0 := by omega
        have h4 : (x + (y - 1)) % 2 ≠ 0 := by omega
        rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4]
        set u := (x + y) / 2
        set v := (x - y) / 2
        have q1a : (x + 1 + y - 1) / 2 = u := by omega
        have q1b : (x + 1 - y - 1) / 2 = v := by omega
        have q2a : (x - 1 + y - 1) / 2 = u - 1 := by omega
        have q2b : (x - 1 - y - 1) / 2 = v - 1 := by omega
        have q3a : (x + (y + 1) - 1) / 2 = u := by omega
        have q3b : (x - (y + 1) - 1) / 2 = v - 1 := by omega
        have q4a : (x + (y - 1) - 1) / 2 = u - 1 := by omega
        have q4b : (x - (y - 1) - 1) / 2 = v := by omega
        rw [q1a, q1b, q2a, q2b, q3a, q3b, q4a, q4b]
        simp only [S_iter, uvStep]
        cases blockActive (S_iter m) u v <;>
          cases blockActive (S_iter m) (u - 1) (v - 1) <;>
          cases blockActive (S_iter m) u (v - 1) <;>
          cases blockActive (S_iter m) (u - 1) v <;> rfl
      · rw [if_neg h, if_neg h]
        have h1 : (x + 1 + y) % 2 = 0 := by omega
        have h2 : (x - 1 + y) % 2 = 0 := by omega
        have h3 : (x + (y + 1)) % 2 = 0 := by omega
        have h4 : (x + (y - 1)) % 2 = 0 := by omega
        rw [if_pos h1, if_pos h2, if_pos h3, if_pos h4]
        simp
    refine ⟨h_even_next, ?_⟩
    intro x y
    rw [cell_succ]
    simp only [h_even_next]
    by_cases h : (x + y) % 2 = 0
    · rw [if_pos h, if_pos h]
      have h1 : (x + 1 + y) % 2 ≠ 0 := by omega
      have h2 : (x - 1 + y) % 2 ≠ 0 := by omega
      have h3 : (x + (y + 1)) % 2 ≠ 0 := by omega
      have h4 : (x + (y - 1)) % 2 ≠ 0 := by omega
      rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4]
      cases S_iter (m + 1) ((x + y) / 2) ((x - y) / 2) <;> rfl
    · rw [if_neg h, if_neg h]
      have h1 : (x + 1 + y) % 2 = 0 := by omega
      have h2 : (x - 1 + y) % 2 = 0 := by omega
      have h3 : (x + (y + 1)) % 2 = 0 := by omega
      have h4 : (x + (y - 1)) % 2 = 0 := by omega
      rw [if_pos h1, if_pos h2, if_pos h3, if_pos h4]
      set a := (x + y - 1) / 2
      set b := (x - y - 1) / 2
      have q1a : (x + 1 + y) / 2 = a + 1 := by omega
      have q1b : (x + 1 - y) / 2 = b + 1 := by omega
      have q2a : (x - 1 + y) / 2 = a := by omega
      have q2b : (x - 1 - y) / 2 = b := by omega
      have q3a : (x + (y + 1)) / 2 = a + 1 := by omega
      have q3b : (x - (y + 1)) / 2 = b := by omega
      have q4a : (x + (y - 1)) / 2 = a := by omega
      have q4b : (x - (y - 1)) / 2 = b + 1 := by omega
      rw [q1a, q1b, q2a, q2b, q3a, q3b, q4a, q4b]
      dsimp only [blockActive]
      exact bool_251_odd (S_iter (m + 1) a b) (S_iter (m + 1) (a + 1) b)
        (S_iter (m + 1) a (b + 1)) (S_iter (m + 1) (a + 1) (b + 1))

-- Basic invariants of B_iter: bounding box, reflection symmetries, core preservation.
private lemma B_iter_support (r : ℕ) :
    ∀ u v : ℤ, B_iter r u v = true →
      -(r : ℤ) ≤ u ∧ u ≤ (r : ℤ) + 1 ∧ -(r : ℤ) ≤ v ∧ v ≤ (r : ℤ) + 1 := by
  induction r with
  | zero =>
    intro u v h
    simp only [B_iter, decide_eq_true_eq] at h
    omega
  | succ r ih =>
    intro u v h
    have hblk : ∀ a b : ℤ, blockActive (B_iter r) a b = true →
        -(r : ℤ) - 1 ≤ a ∧ a ≤ (r : ℤ) + 1 ∧ -(r : ℤ) - 1 ≤ b ∧ b ≤ (r : ℤ) + 1 := by
      intro a b hb
      by_contra hnot
      have h00 : B_iter r a b = false := by
        cases h' : B_iter r a b with
        | false => rfl
        | true => have := ih a b h'; omega
      have h10 : B_iter r (a + 1) b = false := by
        cases h' : B_iter r (a + 1) b with
        | false => rfl
        | true => have := ih (a + 1) b h'; omega
      have h01 : B_iter r a (b + 1) = false := by
        cases h' : B_iter r a (b + 1) with
        | false => rfl
        | true => have := ih a (b + 1) h'; omega
      have h11 : B_iter r (a + 1) (b + 1) = false := by
        cases h' : B_iter r (a + 1) (b + 1) with
        | false => rfl
        | true => have := ih (a + 1) (b + 1) h'; omega
      simp [blockActive, h00, h10, h01, h11] at hb
    simp only [B_iter, uvStep, Bool.or_eq_true] at h
    rcases h with ((h1 | h2) | h3) | h4
    · have := hblk u v h1; omega
    · have := hblk (u - 1) v h2; omega
    · have := hblk u (v - 1) h3; omega
    · have := hblk (u - 1) (v - 1) h4; omega

private lemma blockActive_B_false_of_outside (r : ℕ) {a b : ℤ}
    (h : a < -(r : ℤ) - 1 ∨ (r : ℤ) + 1 < a ∨ b < -(r : ℤ) - 1 ∨ (r : ℤ) + 1 < b) :
    blockActive (B_iter r) a b = false := by
  have h00 : B_iter r a b = false := by
    cases h' : B_iter r a b with
    | false => rfl
    | true => have := B_iter_support r a b h'; omega
  have h10 : B_iter r (a + 1) b = false := by
    cases h' : B_iter r (a + 1) b with
    | false => rfl
    | true => have := B_iter_support r (a + 1) b h'; omega
  have h01 : B_iter r a (b + 1) = false := by
    cases h' : B_iter r a (b + 1) with
    | false => rfl
    | true => have := B_iter_support r a (b + 1) h'; omega
  have h11 : B_iter r (a + 1) (b + 1) = false := by
    cases h' : B_iter r (a + 1) (b + 1) with
    | false => rfl
    | true => have := B_iter_support r (a + 1) (b + 1) h'; omega
  simp [blockActive, h00, h10, h01, h11]

private lemma B_iter_symm_u (r : ℕ) : ∀ u v : ℤ, B_iter r (1 - u) v = B_iter r u v := by
  induction r with
  | zero =>
    intro u v
    simp only [B_iter]
    exact decide_eq_decide.mpr (by omega)
  | succ r ih =>
    have hblk : ∀ a b : ℤ, blockActive (B_iter r) (-a) b = blockActive (B_iter r) a b := by
      intro a b
      simp only [blockActive]
      have e1 : B_iter r (-a) b = B_iter r (a + 1) b := by
        rw [← ih (a + 1) b]; congr 1; omega
      have e2 : B_iter r (-a + 1) b = B_iter r a b := by
        rw [← ih a b]; congr 1; omega
      have e3 : B_iter r (-a) (b + 1) = B_iter r (a + 1) (b + 1) := by
        rw [← ih (a + 1) (b + 1)]; congr 1; omega
      have e4 : B_iter r (-a + 1) (b + 1) = B_iter r a (b + 1) := by
        rw [← ih a (b + 1)]; congr 1; omega
      rw [e1, e2, e3, e4]
      exact decide_eq_decide.mpr (by omega)
    intro u v
    simp only [B_iter, uvStep]
    have h1 : blockActive (B_iter r) (1 - u) v = blockActive (B_iter r) (u - 1) v := by
      rw [← hblk (u - 1) v]; congr 1; omega
    have h2 : blockActive (B_iter r) (1 - u - 1) v = blockActive (B_iter r) u v := by
      rw [← hblk u v]; congr 1; omega
    have h3 : blockActive (B_iter r) (1 - u) (v - 1) = blockActive (B_iter r) (u - 1) (v - 1) := by
      rw [← hblk (u - 1) (v - 1)]; congr 1; omega
    have h4 : blockActive (B_iter r) (1 - u - 1) (v - 1) = blockActive (B_iter r) u (v - 1) := by
      rw [← hblk u (v - 1)]; congr 1; omega
    rw [h1, h2, h3, h4]
    cases blockActive (B_iter r) u v <;>
      cases blockActive (B_iter r) (u - 1) v <;>
      cases blockActive (B_iter r) u (v - 1) <;>
      cases blockActive (B_iter r) (u - 1) (v - 1) <;> rfl

private lemma B_iter_symm_v (r : ℕ) : ∀ u v : ℤ, B_iter r u (1 - v) = B_iter r u v := by
  induction r with
  | zero =>
    intro u v
    simp only [B_iter]
    exact decide_eq_decide.mpr (by omega)
  | succ r ih =>
    have hblk : ∀ a b : ℤ, blockActive (B_iter r) a (-b) = blockActive (B_iter r) a b := by
      intro a b
      simp only [blockActive]
      have e1 : B_iter r a (-b) = B_iter r a (b + 1) := by
        rw [← ih a (b + 1)]; congr 1; omega
      have e2 : B_iter r (a + 1) (-b) = B_iter r (a + 1) (b + 1) := by
        rw [← ih (a + 1) (b + 1)]; congr 1; omega
      have e3 : B_iter r a (-b + 1) = B_iter r a b := by
        rw [← ih a b]; congr 1; omega
      have e4 : B_iter r (a + 1) (-b + 1) = B_iter r (a + 1) b := by
        rw [← ih (a + 1) b]; congr 1; omega
      rw [e1, e2, e3, e4]
      exact decide_eq_decide.mpr (by omega)
    intro u v
    simp only [B_iter, uvStep]
    have h1 : blockActive (B_iter r) u (1 - v) = blockActive (B_iter r) u (v - 1) := by
      rw [← hblk u (v - 1)]; congr 1; omega
    have h2 : blockActive (B_iter r) (u - 1) (1 - v) = blockActive (B_iter r) (u - 1) (v - 1) := by
      rw [← hblk (u - 1) (v - 1)]; congr 1; omega
    have h3 : blockActive (B_iter r) u (1 - v - 1) = blockActive (B_iter r) u v := by
      rw [← hblk u v]; congr 1; omega
    have h4 : blockActive (B_iter r) (u - 1) (1 - v - 1) = blockActive (B_iter r) (u - 1) v := by
      rw [← hblk (u - 1) v]; congr 1; omega
    rw [h1, h2, h3, h4]
    cases blockActive (B_iter r) u v <;>
      cases blockActive (B_iter r) (u - 1) v <;>
      cases blockActive (B_iter r) u (v - 1) <;>
      cases blockActive (B_iter r) (u - 1) (v - 1) <;> rfl

private lemma B_iter_core (r : ℕ) :
    ∀ u v : ℤ, 0 ≤ u → u ≤ 1 → 0 ≤ v → v ≤ 1 → B_iter r u v = true := by
  induction r with
  | zero =>
    intro u v hu0 hu1 hv0 hv1
    simp [B_iter, hu0, hu1, hv0, hv1]
  | succ r ih =>
    intro u v hu0 hu1 hv0 hv1
    have h00 : blockActive (B_iter r) 0 0 = true := by
      simp [blockActive, ih 0 0 (by omega) (by omega) (by omega) (by omega),
        ih 1 0 (by omega) (by omega) (by omega) (by omega),
        ih 0 1 (by omega) (by omega) (by omega) (by omega),
        ih 1 1 (by omega) (by omega) (by omega) (by omega)]
    simp only [B_iter, uvStep]
    have hu : u = 0 ∨ u = 1 := by omega
    have hv : v = 0 ∨ v = 1 := by omega
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;> simp [h00]

private lemma blockActive_reflect_u (F : ℤ → ℤ → Bool) (p q : ℤ) :
    blockActive (fun u v => F (1 - u) v) (-p) q = blockActive F p q := by
  simp only [blockActive]
  have e1 : 1 - (-p) = p + 1 := by omega
  have e2 : 1 - (-p + 1) = p := by omega
  simp only [e1, e2]
  exact decide_eq_decide.mpr (by omega)

private lemma blockActive_reflect_v (F : ℤ → ℤ → Bool) (p q : ℤ) :
    blockActive (fun u v => F u (1 - v)) p (-q) = blockActive F p q := by
  simp only [blockActive]
  have e1 : 1 - (-q) = q + 1 := by omega
  have e2 : 1 - (-q + 1) = q := by omega
  simp only [e1, e2]
  exact decide_eq_decide.mpr (by omega)

-- Local superposition lemma: union of a quarter-plane with B_iter r.
private lemma blockActive_quad_TR (r : ℕ) (p q : ℤ) :
    blockActive (fun u v => decide (u ≤ 0 ∧ v ≤ 0) || B_iter r u v) p q =
      (decide (p + 1 ≤ 0 ∧ q + 1 ≤ 0) || blockActive (B_iter r) p q) := by
  by_cases h1 : p + 1 ≤ 0 ∧ q + 1 ≤ 0
  · simp only [h1, decide_true, Bool.true_or, blockActive]
    have c1 : p ≤ 0 ∧ q ≤ 0 := by omega
    have c2 : p + 1 ≤ 0 ∧ q ≤ 0 := by omega
    have c3 : p ≤ 0 ∧ q + 1 ≤ 0 := by omega
    simp [c1, c2, c3, h1]
  · simp only [h1, decide_false, Bool.false_or]
    by_cases h2 : p + 1 ≤ 0 ∧ q = 0
    · rcases h2 with ⟨hp, rfl⟩
      simp only [blockActive]
      have c1 : p ≤ 0 ∧ (0 : ℤ) ≤ 0 := by omega
      have c2 : p + 1 ≤ 0 ∧ (0 : ℤ) ≤ 0 := by omega
      have c3 : ¬(p ≤ 0 ∧ (0 : ℤ) + 1 ≤ 0) := by omega
      have c4 : ¬(p + 1 ≤ 0 ∧ (0 : ℤ) + 1 ≤ 0) := by omega
      have s1 : B_iter r p 0 = B_iter r p 1 := by
        simpa using B_iter_symm_v r p 1
      have s2 : B_iter r (p + 1) 0 = B_iter r (p + 1) 1 := by
        simpa using B_iter_symm_v r (p + 1) 1
      simp only [c1, c2, c3, c4, decide_true, decide_false, Bool.true_or, Bool.false_or,
        zero_add, s1, s2]
      cases B_iter r p 1 <;> cases B_iter r (p + 1) 1 <;> rfl
    · by_cases h3 : p = 0 ∧ q + 1 ≤ 0
      · rcases h3 with ⟨rfl, hq⟩
        simp only [blockActive]
        have c1 : (0 : ℤ) ≤ 0 ∧ q ≤ 0 := by omega
        have c2 : ¬((0 : ℤ) + 1 ≤ 0 ∧ q ≤ 0) := by omega
        have c3 : (0 : ℤ) ≤ 0 ∧ q + 1 ≤ 0 := by omega
        have c4 : ¬((0 : ℤ) + 1 ≤ 0 ∧ q + 1 ≤ 0) := by omega
        have s1 : B_iter r 0 q = B_iter r 1 q := by
          simpa using B_iter_symm_u r 1 q
        have s2 : B_iter r 0 (q + 1) = B_iter r 1 (q + 1) := by
          simpa using B_iter_symm_u r 1 (q + 1)
        simp only [c1, c2, c3, c4, decide_true, decide_false, Bool.true_or, Bool.false_or,
          zero_add, s1, s2]
        cases B_iter r 1 q <;> cases B_iter r 1 (q + 1) <;> rfl
      · by_cases h4 : p = 0 ∧ q = 0
        · rcases h4 with ⟨rfl, rfl⟩
          apply blockActive_congr
          · simp [B_iter_core r 0 0 (by omega) (by omega) (by omega) (by omega)]
          · simp [B_iter_core r 1 0 (by omega) (by omega) (by omega) (by omega)]
          · simp [B_iter_core r 0 1 (by omega) (by omega) (by omega) (by omega)]
          · simp [B_iter_core r 1 1 (by omega) (by omega) (by omega) (by omega)]
        · apply blockActive_congr
          · have : ¬(p ≤ 0 ∧ q ≤ 0) := by omega
            simp only [this, decide_false, Bool.false_or]
          · have : ¬(p + 1 ≤ 0 ∧ q ≤ 0) := by omega
            simp only [this, decide_false, Bool.false_or]
          · have : ¬(p ≤ 0 ∧ q + 1 ≤ 0) := by omega
            simp only [this, decide_false, Bool.false_or]
          · have : ¬(p + 1 ≤ 0 ∧ q + 1 ≤ 0) := by omega
            simp only [this, decide_false, Bool.false_or]

private lemma blockActive_quad_TL (r : ℕ) (p q : ℤ) :
    blockActive (fun u v => decide (1 ≤ u ∧ v ≤ 0) || B_iter r u v) p q =
      (decide (1 ≤ p ∧ q + 1 ≤ 0) || blockActive (B_iter r) p q) := by
  have h1 := blockActive_reflect_u (fun u v => decide (1 ≤ u ∧ v ≤ 0) || B_iter r u v) p q
  have h2 : blockActive (fun u v => decide (1 ≤ 1 - u ∧ v ≤ 0) || B_iter r (1 - u) v) (-p) q =
      blockActive (fun u v => decide (u ≤ 0 ∧ v ≤ 0) || B_iter r u v) (-p) q := by
    apply blockActive_congr <;> (rw [B_iter_symm_u]; congr 1; exact decide_eq_decide.mpr (by omega))
  have h3 := blockActive_quad_TR r (-p) q
  have h4 := blockActive_reflect_u (B_iter r) p q
  have h5 : blockActive (fun u v => B_iter r (1 - u) v) (-p) q = blockActive (B_iter r) (-p) q := by
    apply blockActive_congr <;> rw [B_iter_symm_u]
  rw [← h1, h2, h3, ← h5, h4]
  congr 1; exact decide_eq_decide.mpr (by omega)

private lemma blockActive_quad_BR (r : ℕ) (p q : ℤ) :
    blockActive (fun u v => decide (u ≤ 0 ∧ 1 ≤ v) || B_iter r u v) p q =
      (decide (p + 1 ≤ 0 ∧ 1 ≤ q) || blockActive (B_iter r) p q) := by
  have h1 := blockActive_reflect_v (fun u v => decide (u ≤ 0 ∧ 1 ≤ v) || B_iter r u v) p q
  have h2 : blockActive (fun u v => decide (u ≤ 0 ∧ 1 ≤ 1 - v) || B_iter r u (1 - v)) p (-q) =
      blockActive (fun u v => decide (u ≤ 0 ∧ v ≤ 0) || B_iter r u v) p (-q) := by
    apply blockActive_congr <;> (rw [B_iter_symm_v]; congr 1; exact decide_eq_decide.mpr (by omega))
  have h3 := blockActive_quad_TR r p (-q)
  have h4 := blockActive_reflect_v (B_iter r) p q
  have h5 : blockActive (fun u v => B_iter r u (1 - v)) p (-q) = blockActive (B_iter r) p (-q) := by
    apply blockActive_congr <;> rw [B_iter_symm_v]
  rw [← h1, h2, h3, ← h5, h4]
  congr 1; exact decide_eq_decide.mpr (by omega)

private lemma blockActive_quad_BL (r : ℕ) (p q : ℤ) :
    blockActive (fun u v => decide (1 ≤ u ∧ 1 ≤ v) || B_iter r u v) p q =
      (decide (1 ≤ p ∧ 1 ≤ q) || blockActive (B_iter r) p q) := by
  have h1 := blockActive_reflect_u (fun u v => decide (1 ≤ u ∧ 1 ≤ v) || B_iter r u v) p q
  have h2 : blockActive (fun u v => decide (1 ≤ 1 - u ∧ 1 ≤ v) || B_iter r (1 - u) v) (-p) q =
      blockActive (fun u v => decide (u ≤ 0 ∧ 1 ≤ v) || B_iter r u v) (-p) q := by
    apply blockActive_congr <;> (rw [B_iter_symm_u]; congr 1; exact decide_eq_decide.mpr (by omega))
  have h3 := blockActive_quad_BR r (-p) q
  have h4 := blockActive_reflect_u (B_iter r) p q
  have h5 : blockActive (fun u v => B_iter r (1 - u) v) (-p) q = blockActive (B_iter r) (-p) q := by
    apply blockActive_congr <;> rw [B_iter_symm_u]
  rw [← h1, h2, h3, ← h5, h4]
  congr 1; exact decide_eq_decide.mpr (by omega)

-- Exact blockActive formula for a solid rectangle.
private lemma blockActive_rect {a b c d : ℤ} (hab : a + 1 ≤ b) (hcd : c + 1 ≤ d) (p q : ℤ) :
    blockActive (rect a b c d) p q =
      (decide (a ≤ p ∧ p + 1 ≤ b ∧ c ≤ q ∧ q + 1 ≤ d) ||
       decide (p = b ∧ q = d) || decide (p = a - 1 ∧ q = d) ||
       decide (p = b ∧ q = c - 1) || decide (p = a - 1 ∧ q = c - 1)) := by
  have hcases :
      (a ≤ p ∧ p + 1 ≤ b ∧ c ≤ q ∧ q + 1 ≤ d) ∨
      (p = b ∧ q = d) ∨ (p = a - 1 ∧ q = d) ∨ (p = b ∧ q = c - 1) ∨ (p = a - 1 ∧ q = c - 1) ∨
      (p + 1 < a ∨ b < p ∨ q + 1 < c ∨ d < q) ∨
      ((p = a - 1 ∨ p = b) ∧ c ≤ q ∧ q + 1 ≤ d) ∨
      (a ≤ p ∧ p + 1 ≤ b ∧ (q = c - 1 ∨ q = d)) := by omega
  rcases hcases with h | h | h | h | h | h | h | h
  · simp only [blockActive, rect]
    have e1 : a ≤ p ∧ p ≤ b ∧ c ≤ q ∧ q ≤ d := by omega
    have e2 : a ≤ p + 1 ∧ p + 1 ≤ b ∧ c ≤ q ∧ q ≤ d := by omega
    have e3 : a ≤ p ∧ p ≤ b ∧ c ≤ q + 1 ∧ q + 1 ≤ d := by omega
    have e4 : a ≤ p + 1 ∧ p + 1 ≤ b ∧ c ≤ q + 1 ∧ q + 1 ≤ d := by omega
    simp [h, e1, e2, e3, e4]
  · rcases h with ⟨hp, hq⟩
    rw [hp, hq]
    have e1 : rect a b c d b d = true := by unfold rect; exact decide_eq_true (by omega)
    have e2 : rect a b c d (b + 1) d = false := by unfold rect; exact decide_eq_false (by omega)
    have e3 : rect a b c d b (d + 1) = false := by unfold rect; exact decide_eq_false (by omega)
    have e4 : rect a b c d (b + 1) (d + 1) = false := by unfold rect; exact decide_eq_false (by omega)
    simp only [blockActive, e1, e2, e3, e4]; simp
  · rcases h with ⟨hp, hq⟩
    rw [hp, hq]
    have e1 : rect a b c d (a - 1) d = false := by unfold rect; exact decide_eq_false (by omega)
    have e2 : rect a b c d (a - 1 + 1) d = true := by unfold rect; exact decide_eq_true (by omega)
    have e3 : rect a b c d (a - 1) (d + 1) = false := by unfold rect; exact decide_eq_false (by omega)
    have e4 : rect a b c d (a - 1 + 1) (d + 1) = false := by unfold rect; exact decide_eq_false (by omega)
    simp only [blockActive, e1, e2, e3, e4]; simp
  · rcases h with ⟨hp, hq⟩
    rw [hp, hq]
    have e1 : rect a b c d b (c - 1) = false := by unfold rect; exact decide_eq_false (by omega)
    have e2 : rect a b c d (b + 1) (c - 1) = false := by unfold rect; exact decide_eq_false (by omega)
    have e3 : rect a b c d b (c - 1 + 1) = true := by unfold rect; exact decide_eq_true (by omega)
    have e4 : rect a b c d (b + 1) (c - 1 + 1) = false := by unfold rect; exact decide_eq_false (by omega)
    simp only [blockActive, e1, e2, e3, e4]; simp
  · rcases h with ⟨hp, hq⟩
    rw [hp, hq]
    have e1 : rect a b c d (a - 1) (c - 1) = false := by unfold rect; exact decide_eq_false (by omega)
    have e2 : rect a b c d (a - 1 + 1) (c - 1) = false := by unfold rect; exact decide_eq_false (by omega)
    have e3 : rect a b c d (a - 1) (c - 1 + 1) = false := by unfold rect; exact decide_eq_false (by omega)
    have e4 : rect a b c d (a - 1 + 1) (c - 1 + 1) = true := by unfold rect; exact decide_eq_true (by omega)
    simp only [blockActive, e1, e2, e3, e4]; simp
  · have e1 : rect a b c d p q = false := by unfold rect; exact decide_eq_false (by omega)
    have e2 : rect a b c d (p + 1) q = false := by unfold rect; exact decide_eq_false (by omega)
    have e3 : rect a b c d p (q + 1) = false := by unfold rect; exact decide_eq_false (by omega)
    have e4 : rect a b c d (p + 1) (q + 1) = false := by unfold rect; exact decide_eq_false (by omega)
    have r1 : decide (a ≤ p ∧ p + 1 ≤ b ∧ c ≤ q ∧ q + 1 ≤ d) = false := decide_eq_false (by omega)
    have r2 : decide (p = b ∧ q = d) = false := decide_eq_false (by omega)
    have r3 : decide (p = a - 1 ∧ q = d) = false := decide_eq_false (by omega)
    have r4 : decide (p = b ∧ q = c - 1) = false := decide_eq_false (by omega)
    have r5 : decide (p = a - 1 ∧ q = c - 1) = false := decide_eq_false (by omega)
    simp only [blockActive, e1, e2, e3, e4, r1, r2, r3, r4, r5]; rfl
  · rcases h with ⟨hp | hp, hqc, hqd⟩
    · rw [hp]
      have e1 : rect a b c d (a - 1) q = false := by unfold rect; exact decide_eq_false (by omega)
      have e2 : rect a b c d (a - 1 + 1) q = true := by unfold rect; exact decide_eq_true (by omega)
      have e3 : rect a b c d (a - 1) (q + 1) = false := by unfold rect; exact decide_eq_false (by omega)
      have e4 : rect a b c d (a - 1 + 1) (q + 1) = true := by unfold rect; exact decide_eq_true (by omega)
      have r1 : decide (a ≤ a - 1 ∧ a - 1 + 1 ≤ b ∧ c ≤ q ∧ q + 1 ≤ d) = false := decide_eq_false (by omega)
      have r2 : decide (a - 1 = b ∧ q = d) = false := decide_eq_false (by omega)
      have r4 : decide (a - 1 = b ∧ q = c - 1) = false := decide_eq_false (by omega)
      simp only [blockActive, e1, e2, e3, e4, r1, r2, r4,
        show q ≠ d by omega, show q ≠ c - 1 by omega, and_false, decide_false]; rfl
    · rw [hp]
      have e1 : rect a b c d b q = true := by unfold rect; exact decide_eq_true (by omega)
      have e2 : rect a b c d (b + 1) q = false := by unfold rect; exact decide_eq_false (by omega)
      have e3 : rect a b c d b (q + 1) = true := by unfold rect; exact decide_eq_true (by omega)
      have e4 : rect a b c d (b + 1) (q + 1) = false := by unfold rect; exact decide_eq_false (by omega)
      have r1 : decide (a ≤ b ∧ b + 1 ≤ b ∧ c ≤ q ∧ q + 1 ≤ d) = false := decide_eq_false (by omega)
      have r3 : decide (b = a - 1 ∧ q = d) = false := decide_eq_false (by omega)
      have r5 : decide (b = a - 1 ∧ q = c - 1) = false := decide_eq_false (by omega)
      simp only [blockActive, e1, e2, e3, e4, r1, r3, r5,
        show q ≠ d by omega, show q ≠ c - 1 by omega, and_false, decide_false]; rfl
  · rcases h with ⟨hpa, hpb, hq | hq⟩
    · rw [hq]
      have e1 : rect a b c d p (c - 1) = false := by unfold rect; exact decide_eq_false (by omega)
      have e2 : rect a b c d (p + 1) (c - 1) = false := by unfold rect; exact decide_eq_false (by omega)
      have e3 : rect a b c d p (c - 1 + 1) = true := by unfold rect; exact decide_eq_true (by omega)
      have e4 : rect a b c d (p + 1) (c - 1 + 1) = true := by unfold rect; exact decide_eq_true (by omega)
      have r1 : decide (a ≤ p ∧ p + 1 ≤ b ∧ c ≤ c - 1 ∧ c - 1 + 1 ≤ d) = false := decide_eq_false (by omega)
      have r2 : decide (p = b ∧ c - 1 = d) = false := decide_eq_false (by omega)
      have r3 : decide (p = a - 1 ∧ c - 1 = d) = false := decide_eq_false (by omega)
      simp only [blockActive, e1, e2, e3, e4, r1, r2, r3,
        show p ≠ b by omega, show p ≠ a - 1 by omega, false_and, decide_false]; rfl
    · rw [hq]
      have e1 : rect a b c d p d = true := by unfold rect; exact decide_eq_true (by omega)
      have e2 : rect a b c d (p + 1) d = true := by unfold rect; exact decide_eq_true (by omega)
      have e3 : rect a b c d p (d + 1) = false := by unfold rect; exact decide_eq_false (by omega)
      have e4 : rect a b c d (p + 1) (d + 1) = false := by unfold rect; exact decide_eq_false (by omega)
      have r1 : decide (a ≤ p ∧ p + 1 ≤ b ∧ c ≤ d ∧ d + 1 ≤ d) = false := decide_eq_false (by omega)
      have r4 : decide (p = b ∧ d = c - 1) = false := decide_eq_false (by omega)
      have r5 : decide (p = a - 1 ∧ d = c - 1) = false := decide_eq_false (by omega)
      simp only [blockActive, e1, e2, e3, e4, r1, r4, r5,
        show p ≠ b by omega, show p ≠ a - 1 by omega, false_and, decide_false]; rfl

-- One step from a solid rectangle produces rectUnion with B_iter 0.
private lemma uvStep_rect {a b c d : ℤ} (hab : a + 1 ≤ b) (hcd : c + 1 ≤ d) (u v : ℤ) :
    uvStep (rect a b c d) u v = rectUnion a b c d (B_iter 0) u v := by
  simp only [uvStep, blockActive_rect hab hcd, rectUnion, rect, B_iter]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · rintro (((h | h) | h) | h) <;> rcases h with ((((h | h) | h) | h) | h)
    all_goals omega
  · rintro ((((h | h) | h) | h) | h)
    · by_cases hu : u + 1 ≤ b
      · by_cases hv : v + 1 ≤ d
        · left; left; left; left; left; left; left; omega
        · left; right; left; left; left; left; omega
      · by_cases hv : v + 1 ≤ d
        · left; left; right; left; left; left; left; omega
        · right; left; left; left; left; omega
    · by_cases hu : u = b
      · by_cases hv : v = d
        · left; left; left; left; left; left; right; omega
        · left; right; left; left; left; right; omega
      · by_cases hv : v = d
        · left; left; right; left; left; left; right; omega
        · right; left; left; left; right; omega
    · by_cases hu : u = a - 1
      · by_cases hv : v = d
        · left; left; left; left; left; right; omega
        · left; right; left; left; right; omega
      · by_cases hv : v = d
        · left; left; right; left; left; right; omega
        · right; left; left; right; omega
    · by_cases hu : u = b
      · by_cases hv : v = c - 1
        · left; left; left; left; right; omega
        · left; right; left; right; omega
      · by_cases hv : v = c - 1
        · left; left; right; left; right; omega
        · right; left; right; omega
    · by_cases hu : u = a - 1
      · by_cases hv : v = c - 1
        · left; left; left; right; omega
        · left; right; right; omega
      · by_cases hv : v = c - 1
        · left; left; right; right; omega
        · right; right; omega

-- Exact blockActive formula for rectUnion with B_iter r when corners stay separated.
private lemma blockActive_rectUnion {a b c d : ℤ} {r : ℕ}
    (hab : 2 * (r : ℤ) + 2 ≤ b - a) (hcd : 2 * (r : ℤ) + 2 ≤ d - c) (p q : ℤ) :
    blockActive (rectUnion a b c d (B_iter r)) p q =
      (decide (a ≤ p ∧ p + 1 ≤ b ∧ c ≤ q ∧ q + 1 ≤ d) ||
       blockActive (B_iter r) (p - b) (q - d) ||
       blockActive (B_iter r) (p - (a - 1)) (q - d) ||
       blockActive (B_iter r) (p - b) (q - (c - 1)) ||
       blockActive (B_iter r) (p - (a - 1)) (q - (c - 1))) := by
  have hBfalse : ∀ u v : ℤ,
      (u < -(r : ℤ) ∨ (r : ℤ) + 1 < u ∨ v < -(r : ℤ) ∨ (r : ℤ) + 1 < v) →
      B_iter r u v = false := by
    intro u v hout
    cases h' : B_iter r u v with
    | false => rfl
    | true => have := B_iter_support r u v h'; omega
  by_cases hp : a + (r : ℤ) < p
  · by_cases hq : c + (r : ℤ) < q
    · -- Top-Right quadrant
      have hTL := blockActive_B_false_of_outside r (a := p - (a - 1)) (b := q - d) (by omega)
      have hBR := blockActive_B_false_of_outside r (a := p - b) (b := q - (c - 1)) (by omega)
      have hBL := blockActive_B_false_of_outside r (a := p - (a - 1)) (b := q - (c - 1)) (by omega)
      rw [hTL, hBR, hBL, Bool.or_false, Bool.or_false, Bool.or_false]
      have hloc : blockActive (rectUnion a b c d (B_iter r)) p q =
          blockActive (fun u v => decide (u ≤ 0 ∧ v ≤ 0) || B_iter r u v) (p - b) (q - d) := by
        simp only [blockActive, rectUnion, rect]
        have f1 : ∀ u v : ℤ, a + (r : ℤ) < u → c + (r : ℤ) < v →
            (decide (a ≤ u ∧ u ≤ b ∧ c ≤ v ∧ v ≤ d) || B_iter r (u - b) (v - d) ||
             B_iter r (u - (a - 1)) (v - d) || B_iter r (u - b) (v - (c - 1)) ||
             B_iter r (u - (a - 1)) (v - (c - 1))) =
            (decide (u - b ≤ 0 ∧ v - d ≤ 0) || B_iter r (u - b) (v - d)) := by
          intro u v hu hv
          rw [hBfalse (u - (a - 1)) (v - d) (by omega),
              hBfalse (u - b) (v - (c - 1)) (by omega),
              hBfalse (u - (a - 1)) (v - (c - 1)) (by omega)]
          simp only [Bool.or_false]
          congr 1; exact decide_eq_decide.mpr (by omega)
        simp only [f1 p q hp hq, f1 (p + 1) q (by omega) hq, f1 p (q + 1) hp (by omega),
            f1 (p + 1) (q + 1) (by omega) (by omega)]
        have e1 : p + 1 - b = p - b + 1 := by omega
        have e2 : q + 1 - d = q - d + 1 := by omega
        simp only [e1, e2]
      rw [hloc, blockActive_quad_TR]
      congr 1; exact decide_eq_decide.mpr (by omega)
    · -- Bot-Right quadrant (a + r < p, q ≤ c + r)
      have hTR := blockActive_B_false_of_outside r (a := p - b) (b := q - d) (by omega)
      have hTL := blockActive_B_false_of_outside r (a := p - (a - 1)) (b := q - d) (by omega)
      have hBL := blockActive_B_false_of_outside r (a := p - (a - 1)) (b := q - (c - 1)) (by omega)
      rw [hTR, hTL, hBL, Bool.or_false, Bool.or_false, Bool.or_false]
      have hloc : blockActive (rectUnion a b c d (B_iter r)) p q =
          blockActive (fun u v => decide (u ≤ 0 ∧ 1 ≤ v) || B_iter r u v) (p - b) (q - (c - 1)) := by
        simp only [blockActive, rectUnion, rect]
        have f1 : ∀ u v : ℤ, a + (r : ℤ) < u → v ≤ c + (r : ℤ) + 1 →
            (decide (a ≤ u ∧ u ≤ b ∧ c ≤ v ∧ v ≤ d) || B_iter r (u - b) (v - d) ||
             B_iter r (u - (a - 1)) (v - d) || B_iter r (u - b) (v - (c - 1)) ||
             B_iter r (u - (a - 1)) (v - (c - 1))) =
            (decide (u - b ≤ 0 ∧ 1 ≤ v - (c - 1)) || B_iter r (u - b) (v - (c - 1))) := by
          intro u v hu hv
          rw [hBfalse (u - b) (v - d) (by omega),
              hBfalse (u - (a - 1)) (v - d) (by omega),
              hBfalse (u - (a - 1)) (v - (c - 1)) (by omega)]
          simp only [Bool.or_false]
          congr 1; exact decide_eq_decide.mpr (by omega)
        simp only [f1 p q hp (by omega), f1 (p + 1) q (by omega) (by omega),
            f1 p (q + 1) hp (by omega), f1 (p + 1) (q + 1) (by omega) (by omega)]
        have e1 : p + 1 - b = p - b + 1 := by omega
        have e2 : q + 1 - (c - 1) = q - (c - 1) + 1 := by omega
        simp only [e1, e2]
      rw [hloc, blockActive_quad_BR]
      congr 1; exact decide_eq_decide.mpr (by omega)
  · by_cases hq : c + (r : ℤ) < q
    · -- Top-Left quadrant (p ≤ a + r, c + r < q)
      have hTR := blockActive_B_false_of_outside r (a := p - b) (b := q - d) (by omega)
      have hBR := blockActive_B_false_of_outside r (a := p - b) (b := q - (c - 1)) (by omega)
      have hBL := blockActive_B_false_of_outside r (a := p - (a - 1)) (b := q - (c - 1)) (by omega)
      rw [hTR, hBR, hBL, Bool.or_false, Bool.or_false, Bool.or_false]
      have hloc : blockActive (rectUnion a b c d (B_iter r)) p q =
          blockActive (fun u v => decide (1 ≤ u ∧ v ≤ 0) || B_iter r u v) (p - (a - 1)) (q - d) := by
        simp only [blockActive, rectUnion, rect]
        have f1 : ∀ u v : ℤ, u ≤ a + (r : ℤ) + 1 → c + (r : ℤ) < v →
            (decide (a ≤ u ∧ u ≤ b ∧ c ≤ v ∧ v ≤ d) || B_iter r (u - b) (v - d) ||
             B_iter r (u - (a - 1)) (v - d) || B_iter r (u - b) (v - (c - 1)) ||
             B_iter r (u - (a - 1)) (v - (c - 1))) =
            (decide (1 ≤ u - (a - 1) ∧ v - d ≤ 0) || B_iter r (u - (a - 1)) (v - d)) := by
          intro u v hu hv
          rw [hBfalse (u - b) (v - d) (by omega),
              hBfalse (u - b) (v - (c - 1)) (by omega),
              hBfalse (u - (a - 1)) (v - (c - 1)) (by omega)]
          simp only [Bool.or_false]
          congr 1; exact decide_eq_decide.mpr (by omega)
        simp only [f1 p q (by omega) hq, f1 (p + 1) q (by omega) hq,
            f1 p (q + 1) (by omega) (by omega), f1 (p + 1) (q + 1) (by omega) (by omega)]
        have e1 : p + 1 - (a - 1) = p - (a - 1) + 1 := by omega
        have e2 : q + 1 - d = q - d + 1 := by omega
        simp only [e1, e2]
      rw [hloc, blockActive_quad_TL]
      congr 1; exact decide_eq_decide.mpr (by omega)
    · -- Bot-Left quadrant (p ≤ a + r, q ≤ c + r)
      have hTR := blockActive_B_false_of_outside r (a := p - b) (b := q - d) (by omega)
      have hTL := blockActive_B_false_of_outside r (a := p - (a - 1)) (b := q - d) (by omega)
      have hBR := blockActive_B_false_of_outside r (a := p - b) (b := q - (c - 1)) (by omega)
      rw [hTR, hTL, hBR, Bool.or_false, Bool.or_false, Bool.or_false]
      have hloc : blockActive (rectUnion a b c d (B_iter r)) p q =
          blockActive (fun u v => decide (1 ≤ u ∧ 1 ≤ v) || B_iter r u v)
            (p - (a - 1)) (q - (c - 1)) := by
        simp only [blockActive, rectUnion, rect]
        have f1 : ∀ u v : ℤ, u ≤ a + (r : ℤ) + 1 → v ≤ c + (r : ℤ) + 1 →
            (decide (a ≤ u ∧ u ≤ b ∧ c ≤ v ∧ v ≤ d) || B_iter r (u - b) (v - d) ||
             B_iter r (u - (a - 1)) (v - d) || B_iter r (u - b) (v - (c - 1)) ||
             B_iter r (u - (a - 1)) (v - (c - 1))) =
            (decide (1 ≤ u - (a - 1) ∧ 1 ≤ v - (c - 1)) || B_iter r (u - (a - 1)) (v - (c - 1))) := by
          intro u v hu hv
          rw [hBfalse (u - b) (v - d) (by omega),
              hBfalse (u - (a - 1)) (v - d) (by omega),
              hBfalse (u - b) (v - (c - 1)) (by omega)]
          simp only [Bool.or_false]
          congr 1; exact decide_eq_decide.mpr (by omega)
        simp only [f1 p q (by omega) (by omega), f1 (p + 1) q (by omega) (by omega),
            f1 p (q + 1) (by omega) (by omega), f1 (p + 1) (q + 1) (by omega) (by omega)]
        have e1 : p + 1 - (a - 1) = p - (a - 1) + 1 := by omega
        have e2 : q + 1 - (c - 1) = q - (c - 1) + 1 := by omega
        simp only [e1, e2]
      rw [hloc, blockActive_quad_BL]
      congr 1; exact decide_eq_decide.mpr (by omega)

-- Step theorem: uvStep commutes with rectUnion while corners stay separated.
private lemma uvStep_rectUnion {a b c d : ℤ} {r : ℕ}
    (hab : 2 * (r : ℤ) + 2 ≤ b - a) (hcd : 2 * (r : ℤ) + 2 ≤ d - c) (u v : ℤ) :
    uvStep (rectUnion a b c d (B_iter r)) u v = rectUnion a b c d (B_iter (r + 1)) u v := by
  simp only [uvStep, blockActive_rectUnion hab hcd, rectUnion, B_iter, rect]
  have e1 : u - 1 - b = u - b - 1 := by omega
  have e2 : v - 1 - d = v - d - 1 := by omega
  have e3 : u - 1 - (a - 1) = u - (a - 1) - 1 := by omega
  have e4 : v - 1 - (c - 1) = v - (c - 1) - 1 := by omega
  rw [e1, e2, e3, e4]
  have hrect :
      (decide (a ≤ u ∧ u + 1 ≤ b ∧ c ≤ v ∧ v + 1 ≤ d) ||
       decide (a ≤ u - 1 ∧ u - 1 + 1 ≤ b ∧ c ≤ v ∧ v + 1 ≤ d) ||
       decide (a ≤ u ∧ u + 1 ≤ b ∧ c ≤ v - 1 ∧ v - 1 + 1 ≤ d) ||
       decide (a ≤ u - 1 ∧ u - 1 + 1 ≤ b ∧ c ≤ v - 1 ∧ v - 1 + 1 ≤ d)) =
      decide (a ≤ u ∧ u ≤ b ∧ c ≤ v ∧ v ≤ d) := by
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    omega
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.or_eq_true]
  constructor
  · intro h
    rcases h with (((h | h) | h) | h)
    · rcases h with ((((h | h) | h) | h) | h)
      · left; left; left; left
        have := Bool.eq_iff_iff.mp hrect; simp only [Bool.or_eq_true] at this
        exact this.mp (Or.inl (Or.inl (Or.inl h)))
      · left; left; left; right; exact Or.inl (Or.inl (Or.inl h))
      · left; left; right; exact Or.inl (Or.inl (Or.inl h))
      · left; right; exact Or.inl (Or.inl (Or.inl h))
      · right; exact Or.inl (Or.inl (Or.inl h))
    · rcases h with ((((h | h) | h) | h) | h)
      · left; left; left; left
        have := Bool.eq_iff_iff.mp hrect; simp only [Bool.or_eq_true] at this
        exact this.mp (Or.inl (Or.inl (Or.inr h)))
      · left; left; left; right; exact Or.inl (Or.inl (Or.inr h))
      · left; left; right; exact Or.inl (Or.inl (Or.inr h))
      · left; right; exact Or.inl (Or.inl (Or.inr h))
      · right; exact Or.inl (Or.inl (Or.inr h))
    · rcases h with ((((h | h) | h) | h) | h)
      · left; left; left; left
        have := Bool.eq_iff_iff.mp hrect; simp only [Bool.or_eq_true] at this
        exact this.mp (Or.inl (Or.inr h))
      · left; left; left; right; exact Or.inl (Or.inr h)
      · left; left; right; exact Or.inl (Or.inr h)
      · left; right; exact Or.inl (Or.inr h)
      · right; exact Or.inl (Or.inr h)
    · rcases h with ((((h | h) | h) | h) | h)
      · left; left; left; left
        have := Bool.eq_iff_iff.mp hrect; simp only [Bool.or_eq_true] at this
        exact this.mp (Or.inr h)
      · left; left; left; right; exact Or.inr h
      · left; left; right; exact Or.inr h
      · left; right; exact Or.inr h
      · right; exact Or.inr h
  · intro h
    rcases h with ((((h | h) | h) | h) | h)
    · have := Bool.eq_iff_iff.mp hrect; simp only [Bool.or_eq_true] at this
      rcases this.mpr h with ((h | h) | h) | h
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h))))))
      · exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl h))))))
      · exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl h)))))
      · exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl h))))
    · rcases h with ((h | h) | h) | h
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))))
      · exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr h))))))
      · exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr h)))))
      · exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr h))))
    · rcases h with ((h | h) | h) | h
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h)))))
      · exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr h)))))
      · exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inr h))))
      · exact Or.inr (Or.inl (Or.inl (Or.inr h)))
    · rcases h with ((h | h) | h) | h
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))
      · exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inr h))))
      · exact Or.inl (Or.inr (Or.inl (Or.inr h)))
      · exact Or.inr (Or.inl (Or.inr h))
    · rcases h with ((h | h) | h) | h
      · exact Or.inl (Or.inl (Or.inl (Or.inr h)))
      · exact Or.inl (Or.inl (Or.inr (Or.inr h)))
      · exact Or.inl (Or.inr (Or.inr h))
      · exact Or.inr (Or.inr h)

-- Multi-step evolution from a solid rectangle.
private lemma uvStep_iterate_rect {a b c d : ℤ} {F : ℕ → ℤ → ℤ → Bool}
    (hstep : ∀ t, F (t + 1) = uvStep (F t))
    {t0 : ℕ} (hinit : F t0 = rect a b c d)
    (r : ℕ) (hab : 2 * (r : ℤ) ≤ b - a) (hcd : 2 * (r : ℤ) ≤ d - c)
    (hab1 : a + 1 ≤ b) (hcd1 : c + 1 ≤ d) :
    F (t0 + 1 + r) = rectUnion a b c d (B_iter r) := by
  induction r with
  | zero =>
    funext u v
    rw [Nat.add_zero, hstep t0, hinit]
    exact uvStep_rect hab1 hcd1 u v
  | succ r ih =>
    funext u v
    rw [show t0 + 1 + (r + 1) = (t0 + 1 + r) + 1 by omega, hstep, ih (by omega) (by omega)]
    exact uvStep_rectUnion (by omega) (by omega) u v

-- B_iter (2^k - 1) is the solid square [-(2^k - 1), 2^k]^2.
private lemma B_iter_pow2 (k : ℕ) :
    B_iter (2 ^ k - 1) = rect (-((2 ^ k : ℤ) - 1)) (2 ^ k : ℤ) (-((2 ^ k : ℤ) - 1)) (2 ^ k : ℤ) := by
  induction k with
  | zero =>
    funext u v
    simp [B_iter, rect]
  | succ k ih =>
    by_cases hk : k = 0
    · subst hk
      funext u v
      have h0 : B_iter 0 = rect 0 1 0 1 := by funext x y; simp [B_iter, rect]
      have h1 : B_iter 1 = uvStep (rect 0 1 0 1) := by rw [← h0]; rfl
      rw [show 2 ^ 1 - 1 = 1 by decide, h1, uvStep_rect (by omega) (by omega)]
      simp only [rectUnion, rect, B_iter]
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      omega
    · set a : ℤ := -((2 ^ k : ℤ) - 1)
      set b : ℤ := (2 ^ k : ℤ)
      have hb2 : 2 ≤ b := by
        have h1 : 2 ^ 1 ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) (by omega)
        have h2 : (2 : ℤ) ≤ (2 ^ k : ℤ) := by exact_mod_cast h1
        exact h2
      have hidx : 2 ^ (k + 1) - 1 = (2 ^ k - 1) + 1 + (2 ^ k - 1) := by
        have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
        rw [pow_succ']; omega
      have hcast : ((2 ^ k - 1 : ℕ) : ℤ) = b - 1 := by
        rw [Nat.cast_sub (Nat.one_le_two_pow)]; push_cast; rfl
      rw [hidx]
      have hev := uvStep_iterate_rect (F := B_iter) (fun _ => rfl) ih (2 ^ k - 1)
        (by rw [hcast]; omega) (by rw [hcast]; omega) (by omega) (by omega)
      rw [hev, ih]
      funext u v
      simp only [rectUnion, rect]
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      have h2k : (2 ^ (k + 1) : ℤ) = 2 * b := by simp only [b]; push_cast; ring
      rw [h2k]
      omega

-- S_iter (2^k - 1) is the solid square [-(2^k - 1), 2^k - 1]^2 for k ≥ 1.
private lemma S_iter_pow2 (k : ℕ) (hk : 1 ≤ k) :
    S_iter (2 ^ k - 1) =
      rect (-((2 ^ k : ℤ) - 1)) ((2 ^ k : ℤ) - 1) (-((2 ^ k : ℤ) - 1)) ((2 ^ k : ℤ) - 1) := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases hk0 : k = 0
    · subst hk0
      funext u v
      rw [show 2 ^ 1 - 1 = 1 by decide]
      have hcases :
          (-1 ≤ u ∧ u ≤ 1 ∧ -1 ≤ v ∧ v ≤ 1) ∨ (u < -1 ∨ 1 < u ∨ v < -1 ∨ 1 < v) := by omega
      rcases hcases with h | h
      · have hu : u = -1 ∨ u = 0 ∨ u = 1 := by omega
        have hv : v = -1 ∨ v = 0 ∨ v = 1 := by omega
        rcases hu with hu | hu | hu <;> rcases hv with hv | hv | hv <;> (rw [hu, hv]; rfl)
      · have hfalse : ∀ p q : ℤ, (p < -1 ∨ 0 < p ∨ q < -1 ∨ 0 < q) →
            blockActive (S_iter 0) p q = false := by
          intro p q hpq
          have c1 : S_iter 0 p q = false := by simp [S_iter]; omega
          have c2 : S_iter 0 (p + 1) q = false := by simp [S_iter]; omega
          have c3 : S_iter 0 p (q + 1) = false := by simp [S_iter]; omega
          have c4 : S_iter 0 (p + 1) (q + 1) = false := by simp [S_iter]; omega
          simp only [blockActive, c1, c2, c3, c4]; rfl
        change uvStep (S_iter 0) u v = _
        rw [uvStep, hfalse u v (by omega), hfalse (u - 1) v (by omega),
            hfalse u (v - 1) (by omega), hfalse (u - 1) (v - 1) (by omega)]
        simp only [Bool.or_false]
        have h21 : (2 ^ (0 + 1) : ℤ) = 2 := by norm_num
        rw [h21]
        unfold rect
        have hnot : ¬(-(2 - 1 : ℤ) ≤ u ∧ u ≤ (2 - 1 : ℤ) ∧ -(2 - 1 : ℤ) ≤ v ∧ v ≤ (2 - 1 : ℤ)) := by
          omega
        exact (decide_eq_false hnot).symm
    · have hk1 : 1 ≤ k := by omega
      have hprev := ih hk1
      set M : ℤ := (2 ^ k : ℤ) - 1
      have hM1 : 1 ≤ M := by
        have : 2 ^ 1 ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hk1
        have : (2 : ℤ) ≤ (2 ^ k : ℤ) := by exact_mod_cast this
        omega
      have hidx : 2 ^ (k + 1) - 1 = (2 ^ k - 1) + 1 + (2 ^ k - 1) := by
        have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
        rw [pow_succ']; omega
      have hcast : ((2 ^ k - 1 : ℕ) : ℤ) = M := by
        rw [Nat.cast_sub (Nat.one_le_two_pow)]; push_cast; rfl
      rw [hidx]
      have hev := uvStep_iterate_rect (F := S_iter) (fun _ => rfl) hprev (2 ^ k - 1)
        (by rw [hcast]; omega) (by rw [hcast]; omega) (by omega) (by omega)
      rw [hev, B_iter_pow2 k]
      funext u v
      simp only [rectUnion, rect]
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      have h2k : (2 ^ (k + 1) : ℤ) - 1 = 2 * M + 1 := by simp only [M]; push_cast; ring
      rw [h2k]
      omega

-- Counting ON cells at t = 2 * M + 1 when S_iter M = rect (-M) M (-M) M (for M ≥ 1).
private lemma onCount_odd_solid (M : ℕ) (hM : 1 ≤ M)
    (hS : S_iter M = rect (-(M : ℤ)) (M : ℤ) (-(M : ℤ)) (M : ℤ)) :
    onCount 251 (2 * M + 1) = 12 * M ^ 2 + 24 * M + 5 := by
  set t : ℕ := 2 * M + 1
  set S_sq : Finset (ℤ × ℤ) := Finset.Icc (-(t : ℤ)) (t : ℤ) ×ˢ Finset.Icc (-(t : ℤ)) (t : ℤ)
  have hon : onCount 251 t =
      ∑ p ∈ S_sq, if cell 251 t p.1 p.2 then 1 else 0 := by
    unfold onCount
    rw [Finset.sum_product]
    have h1d : ∀ f : ℤ → ℕ,
        (∑ i ∈ Finset.range (2 * t + 1), f ((i : ℤ) - (t : ℤ))) =
          ∑ x ∈ Finset.Icc (-(t : ℤ)) (t : ℤ), f x := by
      intro f
      refine Finset.sum_bij (fun i _ => (i : ℤ) - (t : ℤ)) ?_ ?_ ?_ ?_
      · intro i hi
        rw [Finset.mem_range] at hi
        rw [Finset.mem_Icc]; omega
      · intro i1 _ i2 _ h; omega
      · intro x hx
        rw [Finset.mem_Icc] at hx
        refine ⟨(x + (t : ℤ)).toNat, ?_, ?_⟩
        · rw [Finset.mem_range]; omega
        · omega
      · intro i _; rfl
    rw [h1d (fun x => ∑ j ∈ Finset.range (2 * t + 1), if cell 251 t x ((j : ℤ) - (t : ℤ)) then 1 else 0)]
    apply Finset.sum_congr rfl
    intro x _
    exact h1d (fun y => if cell 251 t x y then 1 else 0)
  have hpart :
      (∑ p ∈ S_sq, if cell 251 t p.1 p.2 then 1 else 0) +
        (S_sq.filter (fun p => cell 251 t p.1 p.2 = false)).card = S_sq.card := by
    have h1 : (∑ p ∈ S_sq, if cell 251 t p.1 p.2 then 1 else 0) =
        (S_sq.filter (fun p => cell 251 t p.1 p.2 = true)).card := by
      rw [Finset.card_filter]
    rw [h1]
    have hdisj : Disjoint (S_sq.filter (fun p => cell 251 t p.1 p.2 = true))
                          (S_sq.filter (fun p => cell 251 t p.1 p.2 = false)) := by
      rw [Finset.disjoint_filter]
      intro p _ h1 h2; rw [h1] at h2; cases h2
    rw [← Finset.card_union_of_disjoint hdisj]
    congr 1
    ext p
    simp only [Finset.mem_union, Finset.mem_filter]
    cases cell 251 t p.1 p.2 <;> simp
  set D : Finset (ℤ × ℤ) :=
    (Finset.Ico (-(M : ℤ)) (M : ℤ) ×ˢ Finset.Ico (-(M : ℤ)) (M : ℤ)).image
      (fun q => (q.1 + q.2 + 1, q.1 - q.2))
  set T : Finset (ℤ × ℤ) :=
    {((t : ℤ), (0 : ℤ)), (-(t : ℤ), 0), (0, (t : ℤ)), (0, -(t : ℤ))}
  have hcell_false : ∀ p : ℤ × ℤ,
      p ∈ S_sq ∧ cell 251 t p.1 p.2 = false ↔ p ∈ D ∪ T := by
    intro ⟨x, y⟩
    have hodd := (cell_even_odd M).2 x y
    rw [hS, blockActive_rect (by omega) (by omega)] at hodd
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_product, Finset.mem_Ico,
      Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton, S_sq, D, T, t]
    rw [hodd]
    by_cases hpar : (x + y) % 2 = 0
    · rw [if_pos hpar]
      simp only [Bool.true_eq_false, and_false, false_iff, not_or, not_exists, not_and]
      refine ⟨?_, ?_⟩
      · rintro ⟨a, b⟩ _ heq
        have h1 : a + b + 1 = x := congrArg Prod.fst heq
        have h2 : a - b = y := congrArg Prod.snd heq
        omega
      · simp only [Prod.mk.injEq]; omega
    · rw [if_neg hpar]
      simp only [Bool.not_eq_false', Bool.or_eq_true, decide_eq_true_eq]
      constructor
      · rintro ⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, h⟩
        rcases h with (((h | h) | h) | h) | h
        · left
          refine ⟨((x + y - 1) / 2, (x - y - 1) / 2), ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩, ?_⟩
          ext <;> dsimp <;> omega
        · right; left; ext <;> dsimp <;> omega
        · right; right; right; right; ext <;> dsimp <;> omega
        · right; right; right; left; ext <;> dsimp <;> omega
        · right; right; left; ext <;> dsimp <;> omega
      · intro h
        rcases h with ⟨⟨a, b⟩, ⟨⟨ha1, ha2⟩, ⟨hb1, hb2⟩⟩, heq⟩ | h
        · have h1 : a + b + 1 = x := congrArg Prod.fst heq
          have h2 : a - b = y := congrArg Prod.snd heq
          refine ⟨⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩, Or.inl (Or.inl (Or.inl (Or.inl ?_)))⟩
          omega
        · rcases h with h | h | h | h
          · have h1 : x = (2 * M + 1 : ℤ) := congrArg Prod.fst h
            have h2 : y = 0 := congrArg Prod.snd h
            refine ⟨⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩, Or.inl (Or.inl (Or.inl (Or.inr ?_)))⟩
            omega
          · have h1 : x = -(2 * M + 1 : ℤ) := congrArg Prod.fst h
            have h2 : y = 0 := congrArg Prod.snd h
            refine ⟨⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩, Or.inr ?_⟩
            omega
          · have h1 : x = 0 := congrArg Prod.fst h
            have h2 : y = (2 * M + 1 : ℤ) := congrArg Prod.snd h
            refine ⟨⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩, Or.inl (Or.inr ?_)⟩
            omega
          · have h1 : x = 0 := congrArg Prod.fst h
            have h2 : y = -(2 * M + 1 : ℤ) := congrArg Prod.snd h
            refine ⟨⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩, Or.inl (Or.inl (Or.inr ?_))⟩
            omega
  have hfilt : S_sq.filter (fun p => cell 251 t p.1 p.2 = false) = D ∪ T := by
    ext p
    rw [Finset.mem_filter]
    exact hcell_false p
  have hDcard : D.card = 4 * M ^ 2 := by
    rw [Finset.card_image_of_injective]
    · rw [Finset.card_product, Int.card_Ico]
      have : ((M : ℤ) - -(M : ℤ)).toNat = 2 * M := by omega
      rw [this]; ring
    · intro ⟨a1, b1⟩ ⟨a2, b2⟩ heq
      have h1 : a1 + b1 + 1 = a2 + b2 + 1 := congrArg Prod.fst heq
      have h2 : a1 - b1 = a2 - b2 := congrArg Prod.snd heq
      ext <;> dsimp <;> omega
  have hTcard : T.card = 4 := by
    simp only [T, t]
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_insert_of_notMem, Finset.card_singleton]
    all_goals simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    all_goals omega
  have hdisjDT : Disjoint D T := by
    rw [Finset.disjoint_left]
    intro ⟨x, y⟩ hx hy
    simp only [D, Finset.mem_image, Finset.mem_product, Finset.mem_Ico] at hx
    rcases hx with ⟨⟨a, b⟩, ⟨⟨ha1, ha2⟩, ⟨hb1, hb2⟩⟩, heq⟩
    have h1 : a + b + 1 = x := congrArg Prod.fst heq
    have h2 : a - b = y := congrArg Prod.snd heq
    simp only [T, t, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hy
    omega
  have hSsqcard : S_sq.card = (4 * M + 3) ^ 2 := by
    rw [Finset.card_product, Int.card_Icc]
    have : ((t : ℤ) + 1 - -(t : ℤ)).toNat = 4 * M + 3 := by omega
    rw [this]; ring
  rw [hon]
  rw [hfilt, Finset.card_union_of_disjoint hdisjDT, hDcard, hTcard, hSsqcard] at hpart
  have hcal : (4 * M + 3) ^ 2 = (12 * M ^ 2 + 24 * M + 5) + (4 * M ^ 2 + 4) := by ring
  omega

-- Closed form for a n (n ≥ 1).
private lemma a_zero : a 0 = 1 := by decide
private lemma a_one : a 1 = 5 := by decide

private lemma a_closed (n : ℕ) (hn : 1 ≤ n) : (a n : ℚ) = 3 * (4 : ℚ) ^ n - 7 := by
  by_cases hn1 : n = 1
  · subst hn1; rw [a_one]; norm_num
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have hk : 1 ≤ k := by omega
    set M : ℕ := 2 ^ k - 1
    have hM1 : 1 ≤ M := by
      have : 2 ^ 1 ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hk
      omega
    have h2n : 2 ^ (k + 1) - 1 = 2 * M + 1 := by
      have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
      rw [pow_succ']; omega
    have hSM : S_iter M = rect (-(M : ℤ)) (M : ℤ) (-(M : ℤ)) (M : ℤ) := by
      have h := S_iter_pow2 k hk
      have hcast : (M : ℤ) = (2 ^ k : ℤ) - 1 := by
        simp only [M]
        rw [Nat.cast_sub (Nat.one_le_two_pow)]
        push_cast; rfl
      rwa [← hcast] at h
    unfold a
    rw [h2n, onCount_odd_solid M hM1 hSM]
    have hMcast : (M : ℚ) + 1 = (2 : ℚ) ^ k := by
      have h1 : M + 1 = 2 ^ k := by
        have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
        omega
      exact_mod_cast h1
    push_cast
    calc
      (12 * (M : ℚ) ^ 2 + 24 * (M : ℚ) + 5)
          = 12 * ((M : ℚ) + 1) ^ 2 - 7 := by ring
      _ = 12 * ((2 : ℚ) ^ k) ^ 2 - 7 := by rw [hMcast]
      _ = 3 * (4 : ℚ) ^ (k + 1) - 7 := by
          have h4 : ((2 : ℚ) ^ k) ^ 2 = (4 : ℚ) ^ k := by
            rw [← pow_mul, mul_comm, pow_mul]; norm_num
          rw [h4, pow_succ']; ring

private lemma a_rec (n : ℕ) (hn : 3 ≤ n) : (a n : ℚ) = 5 * a (n - 1) - 4 * a (n - 2) := by
  rw [a_closed n (by omega), a_closed (n - 1) (by omega), a_closed (n - 2) (by omega)]
  have h1 : n = (n - 2) + 2 := by omega
  have h2 : n - 1 = (n - 2) + 1 := by omega
  conv_lhs => rw [h1]
  conv_rhs => rw [h2]
  ring

open PowerSeries in
private lemma a_gf :
    PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) * (1 - 4 * X) : PowerSeries ℚ) =
      1 + 20 * X ^ 2 := by
  have hfac : ((1 - X) * (1 - 4 * X) : PowerSeries ℚ) = 1 - C (5 : ℚ) * X + C (4 : ℚ) * X ^ 2 := by
    have h4 : (4 : PowerSeries ℚ) = C (4 : ℚ) := (map_ofNat C 4).symm
    have h5 : (5 : PowerSeries ℚ) = C (5 : ℚ) := (map_ofNat C 5).symm
    rw [← h4, ← h5]; ring
  rw [hfac]
  ext n
  set F : PowerSeries ℚ := PowerSeries.mk (fun k => (a k : ℚ))
  have hF : ∀ k, coeff k F = (a k : ℚ) := fun k => coeff_mk k _
  have hmul : F * (1 - C (5 : ℚ) * X + C (4 : ℚ) * X ^ 2) =
      F - C (5 : ℚ) * (X * F) + C (4 : ℚ) * (X ^ 2 * F) := by ring
  rw [hmul]
  have h20 : (20 : PowerSeries ℚ) * X ^ 2 = C (20 : ℚ) * X ^ 2 := by
    rw [← map_ofNat C 20]
  rw [h20]
  have hX2eq : (X : PowerSeries ℚ) ^ 2 * F = X * (X * F) := by ring
  match n with
  | 0 =>
    simp only [map_add, map_sub, coeff_C_mul, hF, coeff_one, coeff_X_pow,
      coeff_zero_X_mul, hX2eq, a_zero]
    norm_num
  | 1 =>
    simp only [map_add, map_sub, coeff_C_mul, hF, coeff_one, coeff_X_pow,
      hX2eq, coeff_succ_X_mul, coeff_zero_X_mul, a_zero, a_one]
    norm_num
  | 2 =>
    have ha2 : (a 2 : ℚ) = 41 := by rw [a_closed 2 (by omega)]; norm_num
    simp only [map_add, map_sub, coeff_C_mul, hF, coeff_one, coeff_X_pow,
      hX2eq, coeff_succ_X_mul, a_zero, a_one, ha2]
    norm_num
  | k + 3 =>
    have hrec := a_rec (k + 3) (by omega)
    have hsub1 : k + 3 - 1 = k + 2 := by omega
    have hsub2 : k + 3 - 2 = k + 1 := by omega
    rw [hsub1, hsub2] at hrec
    have h1 : coeff (k + 3) (1 : PowerSeries ℚ) = 0 := by
      rw [coeff_one]; simp
    have h2 : coeff (k + 3) (C (20 : ℚ) * X ^ 2) = 0 := by
      rw [coeff_C_mul, coeff_X_pow]; simp
    have hX : coeff (k + 3) (X * F) = (a (k + 2) : ℚ) := by
      rw [show k + 3 = (k + 2) + 1 by omega, coeff_succ_X_mul, hF]
    have hX2 : coeff (k + 3) (X ^ 2 * F) = (a (k + 1) : ℚ) := by
      rw [hX2eq, show k + 3 = (k + 2) + 1 by omega, coeff_succ_X_mul,
          show k + 2 = (k + 1) + 1 by omega, coeff_succ_X_mul, hF]
    simp only [map_add, map_sub, coeff_C_mul, hF, hX, hX2, h1, h2]
    linarith

private lemma solution_aux :
    (∀ n : ℕ, 1 ≤ n → (a n : ℚ) = 3 * (4 : ℚ) ^ n - 7) ∧
    (∀ n : ℕ, 3 ≤ n → (a n : ℚ) = 5 * a (n - 1) - 4 * a (n - 2)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - PowerSeries.X) * (1 - 4 * PowerSeries.X) : PowerSeries ℚ) =
      1 + 20 * PowerSeries.X ^ 2) :=
  ⟨a_closed, a_rec, a_gf⟩

end OMA.E271017

theorem OMA.solution : type_of% @OMA.S_oeis_a271017.main :=
  OMA.E271017.solution_aux
