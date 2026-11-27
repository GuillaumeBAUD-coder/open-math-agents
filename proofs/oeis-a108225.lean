import OMAStatements.S_oeis_a108225

open OMA.S_oeis_a108225

lemma step (n : ℕ) (h0 : a n = b n + 1) (h1 : a (n + 1) = b (n + 1) + 1) :
    a (n + 2) = b (n + 2) + 1 := by
  have ha : a (n + 2) = (a (n + 1) + a n) * (a (n + 1) - a n + 1) / 2 := rfl
  have hb1 : b (n + 1) = b n * (b n + 1) / 2 + 1 := rfl
  have hb2 : b (n + 2) = b (n + 1) * (b (n + 1) + 1) / 2 + 1 := rfl
  set x := b n with hx
  obtain ⟨T, hT⟩ : ∃ T, x * (x + 1) = 2 * T :=
    (Nat.even_mul_succ_self x).exists_two_nsmul _ |>.imp fun _ h => by rw [h]; ring
  have hTd : x * (x + 1) / 2 = T := by rw [hT]; omega
  rw [hTd] at hb1
  rw [hb1] at hb2 h1
  obtain ⟨S, hS⟩ : ∃ S, (T + 1) * (T + 1 + 1) = 2 * S :=
    (Nat.even_mul_succ_self (T + 1)).exists_two_nsmul _ |>.imp fun _ h => by rw [h]; ring
  have hSd : (T + 1) * (T + 1 + 1) / 2 = S := by rw [hS]; omega
  rw [hSd] at hb2
  rw [ha, h0, h1, hb2]
  have hxT : x ≤ T + 1 := by nlinarith
  obtain ⟨d, hd⟩ : ∃ d, T + 1 = x + d := ⟨T + 1 - x, by omega⟩
  have e1 : T + 1 + 1 + (x + 1) = T + x + 3 := by ring
  have e2 : T + 1 + 1 - (x + 1) + 1 = d + 1 := by omega
  rw [e1, e2]
  have key : (T + x + 3) * (d + 1) = 2 * (S + 2) := by
    have : ((T + x + 3) * (d + 1) : ℤ) = 2 * (S + 2) := by
      have hT' : ((x : ℤ) * (x + 1)) = 2 * T := by exact_mod_cast hT
      have hS' : ((T : ℤ) + 1) * (T + 1 + 1) = 2 * S := by exact_mod_cast hS
      have hd' : (T : ℤ) + 1 = x + d := by exact_mod_cast hd
      linear_combination (-(T + x + 3 : ℤ)) * hd' - hT' + hS'
    exact_mod_cast this
  rw [key]
  omega

theorem OMA.solution : type_of% @OMA.S_oeis_a108225.main := by
  have h : ∀ n : ℕ, OMA.S_oeis_a108225.a (n + 1) = OMA.S_oeis_a108225.b (n + 1) + 1 ∧
      OMA.S_oeis_a108225.a (n + 2) = OMA.S_oeis_a108225.b (n + 2) + 1 := by
    intro n
    induction n with
    | zero => exact ⟨rfl, rfl⟩
    | succ k ih => exact ⟨ih.2, step (k + 1) ih.1 ih.2⟩
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact (h m).1
