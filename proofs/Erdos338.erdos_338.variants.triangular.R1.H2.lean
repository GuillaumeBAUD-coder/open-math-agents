import OMAReductions.R_Erdos338_erdos_338_variants_triangular_R1

/-! Triangular numbers have residues 0, 1, 3, and 6 modulo nine. -/

open Filter Erdos338

lemma triangular_residue (k : ℕ) :
    let r := k * (k+1) / 2 % 9
    r = 0 ∨ r = 1 ∨ r = 3 ∨ r = 6 := by
  have tab : ∀ j : Fin 18,
      let v := (j.val * ((j.val + 1) % 18) % 18) / 2
      v = 0 ∨ v = 1 ∨ v = 3 ∨ v = 6 := by decide
  have h := tab ⟨k%18, Nat.mod_lt _ (by decide)⟩
  have hm : k*(k+1)%18 = (k%18)*((k%18+1)%18)%18 := by
    rw [Nat.mul_mod k (k+1), Nat.add_mod k 1 18]
  dsimp only at *
  omega

theorem OMA.solution : OMA.R_Erdos338_erdos_338_variants_triangular_R1.H2 := by
  intro h
  obtain ⟨N,hN⟩ := eventually_atTop.mp h
  obtain ⟨S, hS, hc, hsum⟩ := hN (9*N+5) (by omega)
  have res (x : ℕ) (hx : x ∈ S) : x%9=0 ∨ x%9=1 ∨ x%9=3 ∨ x%9=6 := by
    obtain ⟨k,rfl⟩ := hS x hx
    exact triangular_residue k
  rcases Nat.lt_trichotomy S.card 1 with hz | ho | ht
  · have e : S = 0 := Multiset.card_eq_zero.mp (by omega)
    simp [e] at hsum
  · obtain ⟨x,rfl⟩ := Multiset.card_eq_one.mp ho
    have := res x (by simp)
    simp at hsum
    omega
  · obtain ⟨x,y,rfl⟩ := Multiset.card_eq_two.mp (by omega : S.card = 2)
    have hx := res x (by simp)
    have hy := res y (by simp)
    simp at hsum
    omega
