import OMAReductions.R_LatinSquare_oddOrderLeq9LatinSquareTransversal_R1

/-! Orders 1, 3, 5 by reflection: a Boolean backtracking search over normalized latin squares
(rows as lists of naturals), checked by `decide +kernel`, plus one soundness lemma. -/

namespace OMA.LatinSmall

/-- Candidate rows: all permutations of `0, …, n-1`. -/
def P (n : ℕ) : List (List ℕ) := (List.range n).permutations'

/-- Two rows never agree in a column. -/
def compat (n : ℕ) (p q : List ℕ) : Bool :=
  (List.range n).all fun j => p.getD j 0 != q.getD j 0

/-- The column selector `s` picks pairwise distinct symbols. -/
def trans (n : ℕ) (rows : List (List ℕ)) (s : List ℕ) : Bool :=
  decide (((List.range n).map fun i => (rows.getD i []).getD (s.getD i 0) 0).Nodup)

/-- Extend the partial square by `f` more rows (row `k` must start with `k`), then
look for a transversal. -/
def search (n : ℕ) : ℕ → List (List ℕ) → Bool
  | 0, rows => (P n).any (trans n rows)
  | f + 1, rows => (P n).all fun p =>
      !(p.head? == some rows.length && rows.all (compat n p)) || search n f (rows ++ [p])

def row {n : ℕ} (L : LatinSquare n) (i : Fin n) : List ℕ := List.ofFn fun j => (L.mat i j : ℕ)

def rowsOf {n : ℕ} (L : LatinSquare n) : List (List ℕ) := List.ofFn (row L)

theorem getD_rowsOf {n : ℕ} (L : LatinSquare n) (i j : ℕ) (hi : i < n) (hj : j < n) :
    ((rowsOf L).getD i []).getD j 0 = (L.mat ⟨i, hi⟩ ⟨j, hj⟩ : ℕ) := by
  simp [rowsOf, row, List.getD_eq_getElem?_getD, hi, hj]

theorem row_mem_P {n : ℕ} (L : LatinSquare n) (i : Fin n) : row L i ∈ P n := by
  rw [P, List.mem_permutations']
  have hnd : (row L i).Nodup :=
    List.nodup_ofFn.mpr (Fin.val_injective.comp (L.row_injective i))
  have hsub : row L i ⊆ List.range n := by
    intro x hx
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
    exact List.mem_range.mpr (L.mat i j).isLt
  exact (List.subperm_of_subset hnd hsub).perm_of_length_le (by simp [row])

theorem length_rowsOf {n : ℕ} (L : LatinSquare n) : (rowsOf L).length = n := by
  simp [rowsOf]

theorem getElem?_rowsOf {n : ℕ} (L : LatinSquare n) (k : ℕ) (hk : k < n) :
    (rowsOf L)[k]? = some (row L ⟨k, hk⟩) := by
  simp [rowsOf, hk]

theorem search_sound {n : ℕ} (L : LatinSquare n) (hc : ∀ i, L.mat i ⟨0, i.pos⟩ = i) :
    ∀ f k, k + f = n → search n f ((rowsOf L).take k) = true →
      (P n).any (trans n (rowsOf L)) = true := by
  intro f
  induction f with
  | zero =>
    intro k hk h
    simp only [Nat.add_zero] at hk
    subst hk
    simpa [search, ← length_rowsOf L, List.take_length] using h
  | succ f ih =>
    intro k hk h
    have hkn : k < n := by omega
    apply ih (k + 1) (by omega)
    have hlen : ((rowsOf L).take k).length = k := by simp [length_rowsOf]; omega
    rw [List.take_add_one,getElem?_rowsOf L k hkn, Option.toList_some]
    simp only [search, List.all_eq_true] at h
    have := h (row L ⟨k, hkn⟩) (row_mem_P L _)
    simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff] at this
    rcases this with (h1 | h1) | h1
    · exfalso
      revert h1
      simp only [hlen]
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      simp [row, List.ofFn_succ]
      exact congrArg Fin.val (hc ⟨k, hkn⟩)
    · exfalso
      rw [Bool.eq_false_iff] at h1
      apply h1
      rw [List.all_eq_true]
      intro q hq
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hq
      have hik : i < k := by simpa [hlen] using hi
      simp only [compat, List.all_eq_true, List.mem_range, bne_iff_ne, ne_eq]
      intro j hj
      rw [List.getElem_take]
      have e1 : (row L ⟨k, hkn⟩).getD j 0 = ((rowsOf L).getD k []).getD j 0 := by
        simp [List.getD_eq_getElem?_getD, getElem?_rowsOf L k hkn]
      have e2 : ((rowsOf L)[i]'(by simp [length_rowsOf]; omega)).getD j 0 =
          ((rowsOf L).getD i []).getD j 0 := by
        have hil : i < (rowsOf L).length := by simp [length_rowsOf]; omega
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hil]
      rw [e1, e2, getD_rowsOf L k j hkn hj, getD_rowsOf L i j (by omega) hj]
      intro heq
      have := L.col_injective ⟨j, hj⟩ (Fin.val_injective heq)
      simp at this
      omega
    · exact h1

theorem of_search {n : ℕ} [NeZero n] (h : search n (n - 1) [List.range n] = true)
    (L : LatinSquare n) (hr : ∀ i, L.mat 0 i = i) (hc : ∀ i, L.mat i 0 = i) :
    ∃ σ, IsTransversal L σ := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have h0 : (rowsOf L).take 1 = [List.range n] := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp only [rowsOf, List.ofFn_succ, List.take_succ_cons, List.take_zero]
    congr 1
    apply List.ext_getElem (by simp [row])
    intro j h1 h2
    simp only [row, List.getElem_ofFn, List.getElem_range]
    have := hr ⟨j, by simpa [row] using h1⟩
    exact congrArg Fin.val this
  have hc' : ∀ i, L.mat i ⟨0, i.pos⟩ = i := fun i => hc i
  have hany := search_sound L hc' (n - 1) 1 (by omega) (by rw [h0]; exact h)
  obtain ⟨s, hsP, hs⟩ := List.any_eq_true.mp hany
  rw [P, List.mem_permutations'] at hsP
  have hslen : s.length = n := by simpa using hsP.length_eq
  have hsnd : s.Nodup := hsP.nodup_iff.mpr List.nodup_range
  have hslt : ∀ i (hi : i < s.length), s[i] < n := fun i hi =>
    List.mem_range.mp (hsP.subset (List.getElem_mem hi))
  let σ : Fin n → Fin n := fun i => ⟨s[i.val]'(by omega), hslt _ _⟩
  have hσ : ∀ i : Fin n, s.getD i.val 0 = (σ i : ℕ) := fun i => by
    simp [σ, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i.val < s.length by omega)]
  refine ⟨σ, ?_, ?_⟩
  · intro a b hab
    have := (hsnd.getElem_inj_iff (hi := by omega) (hj := by omega)).mp (congrArg Fin.val hab)
    exact Fin.ext this
  · intro a b hab
    have hnd := of_decide_eq_true hs
    have := List.inj_on_of_nodup_map hnd (List.mem_range.mpr a.isLt) (List.mem_range.mpr b.isLt)
    apply Fin.ext
    apply this
    rw [hσ a, hσ b, getD_rowsOf L _ _ a.isLt (σ a).isLt, getD_rowsOf L _ _ b.isLt (σ b).isLt]
    exact congrArg Fin.val hab

theorem check1 : search 1 0 [List.range 1] = true := by decide +kernel
theorem check3 : search 3 2 [List.range 3] = true := by decide +kernel
theorem check5 : search 5 4 [List.range 5] = true := by decide +kernel

end OMA.LatinSmall

open OMA.LatinSmall in
theorem OMA.solution : OMA.R_LatinSquare_oddOrderLeq9LatinSquareTransversal_R1.H2 := by
  intro n _ hn L hr hc
  simp only [Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl | rfl
  · exact of_search check1 L hr hc
  · exact of_search check3 L hr hc
  · exact of_search check5 L hr hc
