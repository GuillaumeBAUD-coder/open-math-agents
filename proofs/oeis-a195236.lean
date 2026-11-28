import OMAStatements.S_oeis_a195236

-- Credit: @Dariusthedoggie
-- Proof: king-move graph diameter of the 6x6 lower triangle is 5, so arrays with minimum entry 0 stabilize for n >= 5 and first differences are constant for n > 5

namespace OMA.P195236

open OMA.S_oeis_a195236

private lemma good_diff_le (n : ℕ) (f : Cell → Fin (n + 1)) (hf : Good f) :
    ∀ d : ℕ, ∀ p q : Cell,
      ((p.1.1 : ℤ) - q.1.1).natAbs ≤ d →
      ((p.1.2 : ℤ) - q.1.2).natAbs ≤ d →
      |(f p : ℤ) - f q| ≤ d := by
  intro d
  induction d with
  | zero =>
    intro p q h1 h2
    have hpq : p = q := by
      ext
      · omega
      · omega
    subst hpq
    simp
  | succ d ih =>
    intro p q h1 h2
    by_cases hpq : p = q
    · subst hpq
      simp only [sub_self, abs_zero]
      positivity
    · let r1 : ℕ :=
        if (p.1.1 : ℕ) < q.1.1 then p.1.1 + 1
        else if q.1.1 < p.1.1 then p.1.1 - 1
        else p.1.1
      let r2 : ℕ :=
        if (p.1.2 : ℕ) < q.1.2 then p.1.2 + 1
        else if q.1.2 < p.1.2 then p.1.2 - 1
        else p.1.2
      have hr1_lt : r1 < 6 := by
        dsimp [r1]
        split_ifs <;> omega
      have hr2_lt : r2 < 6 := by
        dsimp [r2]
        split_ifs <;> omega
      have hr_le : r2 ≤ r1 := by
        dsimp [r1, r2]
        have hp := p.2
        have hq := q.2
        split_ifs <;> omega
      let r : Cell := ⟨(⟨r1, hr1_lt⟩, ⟨r2, hr2_lt⟩), hr_le⟩
      have hadj : Adj p.1 r.1 := by
        refine ⟨?_, ?_, ?_⟩
        · intro heq
          have h1' : (p.1.1 : ℕ) = r1 := congrArg (fun x => (x.1 : ℕ)) heq
          have h2' : (p.1.2 : ℕ) = r2 := congrArg (fun x => (x.2 : ℕ)) heq
          dsimp [r1, r2] at h1' h2'
          apply hpq
          ext <;> split_ifs at h1' h2' <;> omega
        · dsimp [r, r1]
          rw [abs_le]
          split_ifs <;> omega
        · dsimp [r, r2]
          rw [abs_le]
          split_ifs <;> omega
      have hstep : |(f p : ℤ) - f r| ≤ 1 := hf p r hadj
      have hrq1 : ((r.1.1 : ℤ) - q.1.1).natAbs ≤ d := by
        dsimp [r, r1]
        split_ifs <;> omega
      have hrq2 : ((r.1.2 : ℤ) - q.1.2).natAbs ≤ d := by
        dsimp [r, r2]
        split_ifs <;> omega
      have hrest : |(f r : ℤ) - f q| ≤ d := ih r q hrq1 hrq2
      have htri : |(f p : ℤ) - f q| ≤ |(f p : ℤ) - f r| + |(f r : ℤ) - f q| := by
        have := abs_add_le ((f p : ℤ) - f r) ((f r : ℤ) - f q)
        simpa using this
      push_cast
      linarith

private lemma good_le_five (n : ℕ) (f : Cell → Fin (n + 1)) (hf : Good f)
    (p0 : Cell) (hp0 : (f p0 : ℕ) = 0) (q : Cell) : (f q : ℕ) ≤ 5 := by
  have h := good_diff_le n f hf 5 q p0 (by omega) (by omega)
  rw [hp0, abs_le] at h
  omega

private noncomputable def B : ℕ := by
  classical
  exact Fintype.card {f : Cell → Fin 6 // Good f ∧ ∃ p : Cell, (f p : ℕ) = 0}

private lemma a_step (m : ℕ) (hm : 4 ≤ m) :
    a (m + 1) = a m + B := by
  classical
  unfold a B
  let S := {f : Cell → Fin (m + 2) // Good f}
  let P : S → Prop := fun f => ∃ p : Cell, (f.1 p : ℕ) = 0
  have hsplit : Fintype.card S = Fintype.card {f : S // ¬ P f} + Fintype.card {f : S // P f} := by
    have := Fintype.card_subtype_compl P; have := Fintype.card_subtype_le P
    omega
  have h1 : Fintype.card {f : S // ¬ P f} = Fintype.card {f : Cell → Fin (m + 1) // Good f} := by
    refine Fintype.card_congr ?_
    refine
      { toFun := fun f =>
          ⟨fun p => ⟨(f.1.1 p : ℕ) - 1, by
            have hne : (f.1.1 p : ℕ) ≠ 0 := fun hz => f.2 ⟨p, hz⟩
            omega⟩, by
            intro p q hadj
            have hnp : (f.1.1 p : ℕ) ≠ 0 := fun hz => f.2 ⟨p, hz⟩
            have hnq : (f.1.1 q : ℕ) ≠ 0 := fun hz => f.2 ⟨q, hz⟩
            have hg := f.1.2 p q hadj
            rw [abs_le] at hg ⊢
            dsimp
            omega⟩
        invFun := fun g =>
          ⟨⟨fun p => ⟨(g.1 p : ℕ) + 1, by omega⟩, by
            intro p q hadj
            have hg := g.2 p q hadj
            rw [abs_le] at hg ⊢
            dsimp
            omega⟩, by
            rintro ⟨p, hp⟩
            dsimp at hp
            omega⟩
        left_inv := fun f => by
          ext p
          have hne : (f.1.1 p : ℕ) ≠ 0 := fun hz => f.2 ⟨p, hz⟩
          dsimp
          omega
        right_inv := fun g => by
          ext p
          dsimp }
  have h2 : Fintype.card {f : S // P f} =
      Fintype.card {f : Cell → Fin 6 // Good f ∧ ∃ p : Cell, (f p : ℕ) = 0} := by
    refine Fintype.card_congr ?_
    refine
      { toFun := fun f =>
          ⟨fun p => ⟨(f.1.1 p : ℕ), by
            obtain ⟨p0, hp0⟩ := f.2
            have := good_le_five (m + 1) f.1.1 f.1.2 p0 hp0 p
            omega⟩, by
            refine ⟨?_, ?_⟩
            · intro p q hadj
              exact f.1.2 p q hadj
            · obtain ⟨p0, hp0⟩ := f.2
              exact ⟨p0, hp0⟩⟩
        invFun := fun g =>
          ⟨⟨fun p => ⟨(g.1 p : ℕ), by omega⟩, by
            intro p q hadj
            exact g.2.1 p q hadj⟩, g.2.2⟩
        left_inv := fun f => by
          ext p
          rfl
        right_inv := fun g => by
          ext p
          rfl }
  have hcardS : Fintype.card {f : Cell → Fin (m + 1 + 1) // Good f} = Fintype.card S :=
    Fintype.card_congr (Equiv.refl _)
  calc
    Fintype.card {f : Cell → Fin (m + 1 + 1) // Good f}
        = Fintype.card S := hcardS
    _ = Fintype.card {f : S // ¬ P f} + Fintype.card {f : S // P f} := hsplit
    _ = _ := by
      rw [h1, h2]

theorem main_proof : ∀ n : ℕ, 5 < n → (a n : ℤ) = 2 * a (n - 1) - a (n - 2) := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k + 6 := ⟨n - 6, by omega⟩
  have h1 := a_step (k + 5) (by omega)
  have h2 := a_step (k + 4) (by omega)
  have h34 : k + 5 + 1 = k + 6 := by omega
  have h23 : k + 4 + 1 = k + 5 := by omega
  rw [h34] at h1
  rw [h23] at h2
  have hsub1 : k + 6 - 1 = k + 5 := by omega
  have hsub2 : k + 6 - 2 = k + 4 := by omega
  rw [hsub1, hsub2]
  have hnat : a (k + 6) + a (k + 4) = 2 * a (k + 5) := by omega
  omega

end OMA.P195236

theorem OMA.solution : type_of% @OMA.S_oeis_a195236.main := OMA.P195236.main_proof
