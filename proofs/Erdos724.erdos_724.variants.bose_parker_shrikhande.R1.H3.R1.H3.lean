import OMAReductions.R_Erdos724_erdos_724_variants_bose_parker_shrikhande_R1_H3_R1

-- Step Erdos724.erdos_724.variants.bose_parker_shrikhande.R1.H3.R1.H3: hypothesis H3 of reduction Erdos724.erdos_724.variants.bose_parker_shrikhande.R1.H3.R1

/-!
Direct product. For odd `b` the squares `(i, j) ↦ i + j` and `(i, j) ↦ i - j` over `Fin b` are
orthogonal, because `(i + j, i - j)` determines `2 i` and doubling is injective modulo an odd
number. Given orthogonal `L`, `M` of order `a`, identify `Fin (a * b)` with `Fin a × Fin b` and
take `(L x₁ y₁, x₂ + y₂)` and `(M x₁ y₁, x₂ - y₂)`. They differ already in the first coordinate,
at a cell where `L` and `M` differ.
-/

namespace OMA

theorem dbl (n : ℕ) (hodd : Odd n) (x y : Fin n) (h : x + x = y + y) : x = y := by
  have hv := congrArg Fin.val h
  rw [Fin.val_add, Fin.val_add] at hv
  have hc : Nat.gcd n 2 = 1 := Nat.coprime_two_right.mpr hodd
  have h2 : 2 * x.val ≡ 2 * y.val [MOD n] := by
    unfold Nat.ModEq
    rw [two_mul, two_mul]
    exact hv
  have h3 := Nat.ModEq.cancel_left_of_coprime hc h2
  unfold Nat.ModEq at h3
  rw [Nat.mod_eq_of_lt x.isLt, Nat.mod_eq_of_lt y.isLt] at h3
  exact Fin.ext h3

end OMA

theorem OMA.solution :
    OMA.R_Erdos724_erdos_724_variants_bose_parker_shrikhande_R1_H3_R1.H3 := by
  unfold OMA.R_Erdos724_erdos_724_variants_bose_parker_shrikhande_R1_H3_R1.H3
  intro a b hodd hb hex
  obtain ⟨L, M, hne, horth⟩ := hex
  have : NeZero b := ⟨by omega⟩
  have hmat : L.mat ≠ M.mat := by
    intro h
    apply hne
    cases L
    cases M
    simp only [LatinSquare.mk.injEq]
    exact h
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hmat
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hi
  obtain ⟨e, -⟩ : ∃ e : Fin a × Fin b ≃ Fin (a * b), True := ⟨finProdFinEquiv, trivial⟩
  refine ⟨⟨fun x y => e (L.mat (e.symm x).1 (e.symm y).1, (e.symm x).2 + (e.symm y).2), ?_, ?_⟩,
    ⟨fun x y => e (M.mat (e.symm x).1 (e.symm y).1, (e.symm x).2 - (e.symm y).2), ?_, ?_⟩,
    ?_, ?_⟩
  · intro x y y' h
    have h0 : e (L.mat (e.symm x).1 (e.symm y).1, (e.symm x).2 + (e.symm y).2) =
        e (L.mat (e.symm x).1 (e.symm y').1, (e.symm x).2 + (e.symm y').2) := h
    have h' := e.injective h0
    have h1 : L.mat (e.symm x).1 (e.symm y).1 = L.mat (e.symm x).1 (e.symm y').1 :=
      congrArg Prod.fst h'
    have h2 : (e.symm x).2 + (e.symm y).2 = (e.symm x).2 + (e.symm y').2 :=
      congrArg Prod.snd h'
    exact e.symm.injective (Prod.ext (L.row_injective _ h1) (add_left_cancel h2))
  · intro y x x' h
    have h0 : e (L.mat (e.symm x).1 (e.symm y).1, (e.symm x).2 + (e.symm y).2) =
        e (L.mat (e.symm x').1 (e.symm y).1, (e.symm x').2 + (e.symm y).2) := h
    have h' := e.injective h0
    have h1 : L.mat (e.symm x).1 (e.symm y).1 = L.mat (e.symm x').1 (e.symm y).1 :=
      congrArg Prod.fst h'
    have h2 : (e.symm x).2 + (e.symm y).2 = (e.symm x').2 + (e.symm y).2 :=
      congrArg Prod.snd h'
    exact e.symm.injective (Prod.ext (L.col_injective _ h1) (add_right_cancel h2))
  · intro x y y' h
    have h0 : e (M.mat (e.symm x).1 (e.symm y).1, (e.symm x).2 - (e.symm y).2) =
        e (M.mat (e.symm x).1 (e.symm y').1, (e.symm x).2 - (e.symm y').2) := h
    have h' := e.injective h0
    have h1 : M.mat (e.symm x).1 (e.symm y).1 = M.mat (e.symm x).1 (e.symm y').1 :=
      congrArg Prod.fst h'
    have h2 : (e.symm x).2 - (e.symm y).2 = (e.symm x).2 - (e.symm y').2 :=
      congrArg Prod.snd h'
    exact e.symm.injective (Prod.ext (M.row_injective _ h1) (sub_right_injective h2))
  · intro y x x' h
    have h0 : e (M.mat (e.symm x).1 (e.symm y).1, (e.symm x).2 - (e.symm y).2) =
        e (M.mat (e.symm x').1 (e.symm y).1, (e.symm x').2 - (e.symm y).2) := h
    have h' := e.injective h0
    have h1 : M.mat (e.symm x).1 (e.symm y).1 = M.mat (e.symm x').1 (e.symm y).1 :=
      congrArg Prod.fst h'
    have h2 : (e.symm x).2 - (e.symm y).2 = (e.symm x').2 - (e.symm y).2 :=
      congrArg Prod.snd h'
    exact e.symm.injective (Prod.ext (M.col_injective _ h1) (sub_left_injective h2))
  · intro h
    have h0 : e (L.mat (e.symm (e (i, 0))).1 (e.symm (e (j, 0))).1,
          (e.symm (e (i, 0))).2 + (e.symm (e (j, 0))).2) =
        e (M.mat (e.symm (e (i, 0))).1 (e.symm (e (j, 0))).1,
          (e.symm (e (i, 0))).2 - (e.symm (e (j, 0))).2) :=
      congrArg (fun S : LatinSquare (a * b) => S.mat (e (i, 0)) (e (j, 0))) h
    have h1 := congrArg Prod.fst (e.injective h0)
    simp only [Equiv.symm_apply_apply] at h1
    exact hj h1
  · unfold Erdos724.IsOrthogonal at horth ⊢
    intro p q h
    obtain ⟨x, y⟩ := p
    obtain ⟨x', y'⟩ := q
    have hL : e (L.mat (e.symm x).1 (e.symm y).1, (e.symm x).2 + (e.symm y).2) =
        e (L.mat (e.symm x').1 (e.symm y').1, (e.symm x').2 + (e.symm y').2) :=
      congrArg Prod.fst h
    have hM : e (M.mat (e.symm x).1 (e.symm y).1, (e.symm x).2 - (e.symm y).2) =
        e (M.mat (e.symm x').1 (e.symm y').1, (e.symm x').2 - (e.symm y').2) :=
      congrArg Prod.snd h
    have hL' := e.injective hL
    have hM' := e.injective hM
    have l1 : L.mat (e.symm x).1 (e.symm y).1 = L.mat (e.symm x').1 (e.symm y').1 :=
      congrArg Prod.fst hL'
    have l2 : (e.symm x).2 + (e.symm y).2 = (e.symm x').2 + (e.symm y').2 :=
      congrArg Prod.snd hL'
    have m1 : M.mat (e.symm x).1 (e.symm y).1 = M.mat (e.symm x').1 (e.symm y').1 :=
      congrArg Prod.fst hM'
    have m2 : (e.symm x).2 - (e.symm y).2 = (e.symm x').2 - (e.symm y').2 :=
      congrArg Prod.snd hM'
    have hp : ((e.symm x).1, (e.symm y).1) = ((e.symm x').1, (e.symm y').1) :=
      @horth ((e.symm x).1, (e.symm y).1) ((e.symm x').1, (e.symm y').1) (Prod.ext l1 m1)
    have hx1 : (e.symm x).1 = (e.symm x').1 := (Prod.mk.inj hp).1
    have hy1 : (e.symm y).1 = (e.symm y').1 := (Prod.mk.inj hp).2
    have h3 : (e.symm x).2 + (e.symm x).2 = (e.symm x').2 + (e.symm x').2 := by
      calc (e.symm x).2 + (e.symm x).2
          = ((e.symm x).2 + (e.symm y).2) + ((e.symm x).2 - (e.symm y).2) :=
            (add_add_sub_cancel _ _ _).symm
        _ = ((e.symm x').2 + (e.symm y').2) + ((e.symm x').2 - (e.symm y').2) := by
            rw [l2, m2]
        _ = (e.symm x').2 + (e.symm x').2 := add_add_sub_cancel _ _ _
    have hx2 : (e.symm x).2 = (e.symm x').2 := OMA.dbl b hodd _ _ h3
    have hy2 : (e.symm y).2 = (e.symm y').2 := by
      rw [hx2] at l2
      exact add_left_cancel l2
    have hx : x = x' := e.symm.injective (Prod.ext hx1 hx2)
    have hy : y = y' := e.symm.injective (Prod.ext hy1 hy2)
    rw [hx, hy]
