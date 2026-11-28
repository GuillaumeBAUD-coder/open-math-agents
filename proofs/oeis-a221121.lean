import OMAStatements.S_oeis_a221121

open OMA.S_oeis_a221121 PowerSeries

private abbrev Rw := Fin 3 → Move
private abbrev V := ℕ × ℕ × ℕ
private abbrev Q := V × V

private def tr (f : Fin 3 → ℕ) : V := (f 0, f 1, f 2)

-- What a row of moves sends to the row at offset k, column j.
private def Cf (k : ℤ) (r : Rw) (j : Fin 3) : ℕ :=
  ∑ j' : Fin 3, if (r j').dr = k ∧ (j' : ℤ) + (r j').dc = j then 1 else 0

private def H (r : Rw) : V := tr (Cf 0 r)
private def U (r : Rw) : V := tr (Cf (-1) r)
private def D (r : Rw) : V := tr (Cf 1 r)

private def rowValid (t b : Bool) (r : Rw) : Prop :=
  ∀ j : Fin 3, (t = true → (r j).dr ≠ -1) ∧ (b = true → (r j).dr ≠ 1) ∧
    0 ≤ (j : ℤ) + (r j).dc ∧ (j : ℤ) + (r j).dc < 3

private instance (t b : Bool) : DecidablePred (rowValid t b) := fun r => by
  unfold rowValid; infer_instance

private def ok (r : Rw) : Prop := rowValid false false r

private instance : DecidablePred ok := fun r => by unfold ok; infer_instance

private theorem rowValid_iff : ∀ t b r, rowValid t b r ↔ ok r ∧ (t = true → U r = 0) ∧
    (b = true → D r = 0) := by
  decide +kernel

private theorem valid_iff (n : ℕ) (mv : Fin n → Rw) : valid n mv ↔
    ∀ i : Fin n, rowValid (decide ((i : ℕ) = 0)) (decide ((i : ℕ) + 1 = n)) (mv i) := by
  unfold valid rowValid
  refine forall_congr' fun i => forall_congr' fun j => ?_
  have := i.isLt
  cases mv i j <;> simp [Move.dr] <;> omega

private def VL : Bool → List Rw → Prop
  | _, [] => True
  | t, r :: rs => rowValid t rs.isEmpty r ∧ VL false rs

private theorem VL_ofFn : ∀ (n : ℕ) (t : Bool) (mv : Fin n → Rw), VL t (List.ofFn mv) ↔
    ∀ i : Fin n, rowValid (t && decide ((i : ℕ) = 0)) (decide ((i : ℕ) + 1 = n)) (mv i) := by
  intro n
  induction n with
  | zero => intro t mv; simp [VL]
  | succ n ih =>
    intro t mv
    rw [List.ofFn_succ, VL, ih, Fin.forall_fin_succ]
    have h1 : (List.ofFn fun i : Fin n => mv i.succ).isEmpty = decide (0 + 1 = n + 1) := by
      cases n <;> simp
    simp [h1, Fin.val_succ]

private def headU : List Rw → V
  | [] => 0
  | r :: _ => U r

private def occRows : V → List Rw → List V
  | _, [] => []
  | ab, r :: rs => (ab + H r + headU rs) :: occRows (D r) rs

private theorem occRows_length : ∀ (L : List Rw) (ab : V), (occRows ab L).length = L.length
  | [], _ => rfl
  | r :: rs, _ => by simp [occRows, occRows_length rs]

private theorem occ_eq (n : ℕ) (mv : Fin n → Rw) (i : Fin n) (j : Fin 3) :
    occ n mv i j = ∑ i' : Fin n, Cf ((i : ℤ) - i') (mv i') j := by
  unfold occ Cf
  refine Finset.sum_congr rfl fun i' _ => Finset.sum_congr rfl fun j' _ => ?_
  have : ((i' : ℤ) + (mv i' j').dr = i ∧ (j' : ℤ) + (mv i' j').dc = j) ↔
      ((mv i' j').dr = (i : ℤ) - i' ∧ (j' : ℤ) + (mv i' j').dc = j) := by
    constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by omega, h2⟩
  simp only [this]

private theorem C_far (k : ℤ) (hk : 2 ≤ k ∨ k ≤ -2) (r : Rw) (j : Fin 3) : Cf k r j = 0 := by
  unfold Cf
  refine Finset.sum_eq_zero fun j' _ => ?_
  have : (r j').dr ≠ k := by cases r j' <;> simp [Move.dr] <;> omega
  simp [this]

private theorem occ_cons_succ (n : ℕ) (r : Rw) (mv : Fin n → Rw) (i : Fin n) :
    tr (occ (n + 1) (Fin.cons r mv : Fin (n + 1) → Rw) i.succ) =
      (if (i : ℕ) = 0 then D r else 0) + tr (occ n mv i) := by
  have h : ∀ j, occ (n + 1) (Fin.cons r mv : Fin (n + 1) → Rw) i.succ j =
      Cf ((i : ℤ) + 1) r j + occ n mv i j := by
    intro j
    rw [occ_eq, occ_eq, Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, Fin.val_succ, Fin.val_zero]
    congr 1
    push_cast; ring_nf
  by_cases hi : (i : ℕ) = 0
  · simp only [tr, h, hi, if_true, D, Nat.cast_zero, zero_add]
    rfl
  · have h0 : ∀ j, Cf ((i : ℤ) + 1) r j = 0 := fun j => C_far _ (by omega) r j
    simp only [tr, h, h0, hi, if_false, zero_add]

private theorem occ_cons_zero (n : ℕ) (r : Rw) (mv : Fin n → Rw) :
    tr (occ (n + 1) (Fin.cons r mv : Fin (n + 1) → Rw) 0) = H r + headU (List.ofFn mv) := by
  have h : ∀ j, occ (n + 1) (Fin.cons r mv : Fin (n + 1) → Rw) 0 j =
      Cf 0 r j + ∑ i' : Fin n, Cf (-(i' : ℤ) - 1) (mv i') j := by
    intro j
    rw [occ_eq, Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, Fin.val_succ, Fin.val_zero]
    congr 1
    refine Finset.sum_congr rfl fun i' _ => ?_
    push_cast; ring_nf
  cases n with
  | zero =>
    simp only [tr, h, Finset.univ_eq_empty, Finset.sum_empty, add_zero, List.ofFn_zero, headU, H]
  | succ m =>
    have h2 : ∀ j, ∑ i' : Fin (m + 1), Cf (-(i' : ℤ) - 1) (mv i') j = Cf (-1) (mv 0) j := by
      intro j
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, Fin.val_succ]
      rw [Finset.sum_eq_zero fun i' _ => C_far _ (by omega) _ j]
      simp
    simp only [tr, h, h2, List.ofFn_succ, headU, H, U]
    rfl

private theorem occ_rows : ∀ (n : ℕ) (ab : V) (mv : Fin n → Rw),
    List.ofFn (fun i : Fin n => (if (i : ℕ) = 0 then ab else 0) + tr (occ n mv i)) =
      occRows ab (List.ofFn mv) := by
  intro n
  induction n with
  | zero => intro ab mv; rfl
  | succ n ih =>
    intro ab mv
    rw [← Fin.cons_self_tail mv]
    generalize mv 0 = r
    generalize Fin.tail mv = mv'
    rw [List.ofFn_succ, List.ofFn_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, occRows]
    rw [← ih (D r) mv', occ_cons_zero]
    simp only [Fin.val_zero, if_true, Fin.val_succ, Nat.add_one_ne_zero, if_false, zero_add,
      add_assoc]
    congr 1
    exact List.ofFn_inj.2 (funext fun i => occ_cons_succ n r mv' i)

private def RunFrom : Q → List V → Prop
  | _, [] => False
  | q, a :: ws => (ws = [] ∧ q.2 = 0 ∧ a = q.1) ∨
      ∃ r, ok r ∧ a = q.1 + U r ∧ RunFrom (q.2 + H r, D r) ws

private theorem fits : ∀ (ws : List V) (ab : V) (r0 : Rw),
    (∃ rs, VL false (r0 :: rs) ∧ occRows ab (r0 :: rs) = ws) ↔
      ok r0 ∧ RunFrom (ab + H r0, D r0) ws := by
  intro ws
  induction ws with
  | nil => intro ab r0; simp [occRows, RunFrom]
  | cons a ws ih =>
    intro ab r0
    constructor
    · rintro ⟨rs, ⟨hv, hvl⟩, he⟩
      rw [rowValid_iff] at hv
      simp only [occRows, List.cons.injEq] at he
      obtain ⟨ha, hws⟩ := he
      cases rs with
      | nil =>
        refine ⟨hv.1, Or.inl ⟨?_, hv.2.2 rfl, ?_⟩⟩
        · rw [← hws]; rfl
        · rw [← ha]; simp [headU]
      | cons r1 rs' =>
        have := (ih (D r0) r1).1 ⟨rs', hvl, hws⟩
        refine ⟨hv.1, Or.inr ⟨r1, this.1, ?_, this.2⟩⟩
        rw [← ha]; rfl
    · rintro ⟨hok, ⟨h1, h2, h3⟩ | ⟨r1, hr1, ha, hrun⟩⟩
      · refine ⟨[], ⟨(rowValid_iff _ _ _).2 ⟨hok, by simp, fun _ => h2⟩, trivial⟩, ?_⟩
        simp [occRows, headU, h1, h3]
      · obtain ⟨rs', hv', he'⟩ := (ih (D r0) r1).2 ⟨hr1, hrun⟩
        refine ⟨r1 :: rs', ⟨(rowValid_iff _ _ _).2 ⟨hok, by simp, by simp⟩, hv'⟩, ?_⟩
        simp only [occRows] at he' ⊢
        rw [he', ha]
        rfl

private theorem sem (m : ℕ) (ws : List V) (hl : ws.length = m + 1) :
    (∃ mv, valid (m + 1) mv ∧ List.ofFn (fun i => tr (occ (m + 1) mv i)) = ws) ↔
      ∃ r0, ok r0 ∧ U r0 = 0 ∧ RunFrom (H r0, D r0) ws := by
  have hrows : ∀ mv : Fin (m + 1) → Rw,
      List.ofFn (fun i => tr (occ (m + 1) mv i)) = occRows 0 (List.ofFn mv) := by
    intro mv
    rw [← occ_rows]
    simp
  have hval : ∀ mv : Fin (m + 1) → Rw, valid (m + 1) mv ↔ VL true (List.ofFn mv) := by
    intro mv
    rw [valid_iff, VL_ofFn]
    simp
  have hVL : ∀ r0 rs, VL true (r0 :: rs) ↔ U r0 = 0 ∧ VL false (r0 :: rs) := by
    intro r0 rs
    rw [VL, VL, rowValid_iff, rowValid_iff]
    constructor
    · rintro ⟨⟨h1, h2, h3⟩, h4⟩; exact ⟨h2 rfl, ⟨h1, by simp, h3⟩, h4⟩
    · rintro ⟨h0, ⟨h1, -, h3⟩, h4⟩; exact ⟨⟨h1, fun _ => h0, h3⟩, h4⟩
  constructor
  · rintro ⟨mv, hv, he⟩
    rw [hval, List.ofFn_succ] at hv
    rw [hrows, List.ofFn_succ] at he
    obtain ⟨hu, hv'⟩ := (hVL _ _).1 hv
    obtain ⟨hok, hrun⟩ := (fits ws 0 (mv 0)).1 ⟨_, hv', he⟩
    exact ⟨mv 0, hok, hu, by simpa using hrun⟩
  · rintro ⟨r0, hok, hu, hrun⟩
    obtain ⟨rs, hv, he⟩ := (fits ws 0 r0).2 ⟨hok, by simpa using hrun⟩
    have hlen : (r0 :: rs).length = m + 1 := by rw [← occRows_length _ 0, he, hl]
    refine ⟨fun i => (r0 :: rs)[(i : ℕ)]'(by omega), ?_, ?_⟩
    · have hL : List.ofFn (fun i : Fin (m + 1) => (r0 :: rs)[(i : ℕ)]'(by omega)) = r0 :: rs := by
        apply List.ext_getElem (by simp [hlen]); intro k h1 h2; cases k <;> simp
      rw [hval, hL, hVL]
      exact ⟨hu, hv⟩
    · have hL : List.ofFn (fun i : Fin (m + 1) => (r0 :: rs)[(i : ℕ)]'(by omega)) = r0 :: rs := by
        apply List.ext_getElem (by simp [hlen]); intro k h1 h2; cases k <;> simp
      rw [hrows, hL, he]

private def rd : List (V × V × V) :=
  [((0, 0, 0), (0, 1, 0), (1, 1, 0)), ((0, 0, 0), (0, 1, 1), (0, 1, 0)), ((0, 0, 1), (0, 1, 0), (0, 1, 0)), ((0, 0, 1), (0, 1, 0), (1, 0, 0)), ((0, 0, 1), (0, 1, 1), (0, 0, 0)), ((0, 0, 2), (0, 1, 0), (0, 0, 0)), ((0, 1, 0), (0, 0, 0), (1, 1, 0)), ((0, 1, 0), (0, 0, 1), (0, 1, 0)), ((0, 1, 0), (0, 1, 0), (0, 1, 0)), ((0, 1, 0), (0, 1, 0), (1, 0, 0)), ((0, 1, 0), (0, 1, 1), (0, 0, 0)), ((0, 1, 1), (0, 0, 0), (0, 1, 0)), ((0, 1, 1), (0, 0, 0), (1, 0, 0)), ((0, 1, 1), (0, 0, 1), (0, 0, 0)), ((0, 1, 1), (0, 1, 0), (0, 0, 0)), ((0, 1, 2), (0, 0, 0), (0, 0, 0)), ((0, 2, 0), (0, 0, 0), (0, 1, 0)), ((0, 2, 0), (0, 0, 0), (1, 0, 0)), ((0, 2, 0), (0, 0, 1), (0, 0, 0)), ((0, 2, 0), (0, 1, 0), (0, 0, 0)), ((0, 2, 1), (0, 0, 0), (0, 0, 0)), ((0, 3, 0), (0, 0, 0), (0, 0, 0)), ((1, 0, 0), (0, 0, 0), (1, 1, 0)), ((1, 0, 0), (0, 0, 1), (0, 1, 0)), ((1, 0, 0), (0, 1, 0), (0, 1, 0)), ((1, 0, 1), (0, 0, 0), (0, 1, 0)), ((1, 0, 1), (0, 0, 0), (1, 0, 0)), ((1, 0, 1), (0, 0, 1), (0, 0, 0)), ((1, 0, 1), (0, 1, 0), (0, 0, 0)), ((1, 0, 2), (0, 0, 0), (0, 0, 0)), ((1, 1, 0), (0, 0, 0), (0, 1, 0)), ((1, 1, 0), (0, 0, 0), (1, 0, 0)), ((1, 1, 0), (0, 0, 1), (0, 0, 0)), ((1, 1, 0), (0, 1, 0), (0, 0, 0)), ((1, 1, 1), (0, 0, 0), (0, 0, 0)), ((1, 2, 0), (0, 0, 0), (0, 0, 0)), ((2, 0, 0), (0, 0, 0), (0, 1, 0)), ((2, 0, 1), (0, 0, 0), (0, 0, 0)), ((2, 1, 0), (0, 0, 0), (0, 0, 0))]

private def SS : Fin 8 → List Q := ![
  [((0, 1, 0), (1, 1, 0)), ((0, 1, 1), (0, 1, 0)), ((0, 1, 1), (1, 0, 0)), ((0, 1, 2), (0, 0, 0)), ((0, 2, 0), (0, 1, 0)), ((0, 2, 0), (1, 0, 0)), ((0, 2, 1), (0, 0, 0)), ((0, 3, 0), (0, 0, 0)), ((1, 0, 0), (1, 1, 0)), ((1, 0, 1), (0, 1, 0)), ((1, 0, 1), (1, 0, 0)), ((1, 0, 2), (0, 0, 0)), ((1, 1, 0), (0, 1, 0)), ((1, 1, 0), (1, 0, 0)), ((1, 1, 1), (0, 0, 0)), ((1, 2, 0), (0, 0, 0)), ((2, 0, 0), (0, 1, 0)), ((2, 0, 1), (0, 0, 0)), ((2, 1, 0), (0, 0, 0))],
  [((1, 2, 0), (1, 1, 0)), ((1, 2, 1), (0, 1, 0)), ((1, 2, 1), (1, 0, 0)), ((1, 2, 2), (0, 0, 0)), ((1, 3, 0), (0, 1, 0)), ((1, 3, 0), (1, 0, 0)), ((1, 3, 1), (0, 0, 0)), ((1, 4, 0), (0, 0, 0)), ((2, 1, 0), (1, 1, 0)), ((2, 1, 1), (0, 1, 0)), ((2, 1, 1), (1, 0, 0)), ((2, 1, 2), (0, 0, 0)), ((2, 2, 0), (0, 1, 0)), ((2, 2, 0), (1, 0, 0)), ((2, 2, 1), (0, 0, 0)), ((2, 3, 0), (0, 0, 0)), ((3, 1, 0), (0, 1, 0)), ((3, 1, 1), (0, 0, 0)), ((3, 2, 0), (0, 0, 0))],
  [((0, 2, 0), (1, 1, 0)), ((0, 2, 1), (0, 1, 0)), ((0, 2, 1), (1, 0, 0)), ((0, 2, 2), (0, 0, 0)), ((0, 3, 0), (0, 1, 0)), ((0, 3, 0), (1, 0, 0)), ((0, 3, 1), (0, 0, 0)), ((0, 4, 0), (0, 0, 0)), ((1, 1, 0), (1, 1, 0)), ((1, 1, 1), (0, 1, 0)), ((1, 1, 1), (1, 0, 0)), ((1, 1, 2), (0, 0, 0)), ((1, 2, 0), (0, 1, 0)), ((1, 2, 0), (1, 0, 0)), ((1, 2, 1), (0, 0, 0)), ((1, 3, 0), (0, 0, 0)), ((2, 0, 0), (1, 1, 0)), ((2, 0, 1), (0, 1, 0)), ((2, 0, 1), (1, 0, 0)), ((2, 0, 2), (0, 0, 0)), ((2, 1, 0), (0, 1, 0)), ((2, 1, 0), (1, 0, 0)), ((2, 1, 1), (0, 0, 0)), ((2, 2, 0), (0, 0, 0)), ((3, 0, 0), (0, 1, 0)), ((3, 0, 1), (0, 0, 0)), ((3, 1, 0), (0, 0, 0))],
  [((0, 1, 0), (0, 1, 0)), ((0, 1, 1), (0, 0, 0)), ((0, 2, 0), (0, 0, 0)), ((1, 0, 0), (0, 1, 0)), ((1, 0, 1), (0, 0, 0)), ((1, 1, 0), (0, 0, 0))],
  [((0, 0, 0), (1, 1, 0)), ((0, 0, 1), (0, 1, 0)), ((0, 0, 1), (1, 0, 0)), ((0, 0, 2), (0, 0, 0)), ((0, 1, 0), (0, 1, 0)), ((0, 1, 0), (1, 0, 0)), ((0, 1, 1), (0, 0, 0)), ((0, 2, 0), (0, 0, 0)), ((1, 0, 0), (0, 1, 0)), ((1, 0, 1), (0, 0, 0)), ((1, 1, 0), (0, 0, 0))],
  [((0, 0, 0), (0, 1, 0)), ((0, 0, 1), (0, 0, 0)), ((0, 1, 0), (0, 0, 0))],
  [((0, 2, 0), (1, 1, 0)), ((0, 2, 1), (0, 1, 0)), ((0, 2, 1), (1, 0, 0)), ((0, 2, 2), (0, 0, 0)), ((0, 3, 0), (0, 1, 0)), ((0, 3, 0), (1, 0, 0)), ((0, 3, 1), (0, 0, 0)), ((0, 4, 0), (0, 0, 0)), ((1, 1, 0), (1, 1, 0)), ((1, 1, 1), (0, 1, 0)), ((1, 1, 1), (1, 0, 0)), ((1, 1, 2), (0, 0, 0)), ((1, 2, 0), (0, 1, 0)), ((1, 2, 0), (1, 0, 0)), ((1, 2, 1), (0, 0, 0)), ((1, 3, 0), (0, 0, 0)), ((2, 1, 0), (0, 1, 0)), ((2, 1, 1), (0, 0, 0)), ((2, 2, 0), (0, 0, 0))],
  []]

private def tblN : Fin 8 → ℕ := ![
  777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777754777540777306777777777777777754777540775402773021777777777754777540775402773021777777,
  777777777777777777777777777777777777777777777777777777777777777777777777777777777777777754777540777306777777777777777754777540775402773021777777777754777540775402773021777777777777777777777777777777777777777777777777,
  777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777754777540777306777777777777777754777540775402773021777777777754777540775402773021777777777754777540775402773021777777777777,
  777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777754777540777306777777777777777754777540777306777777,
  777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777754777540777306777777777777777754777540775402773021,
  777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777754777540777306,
  777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777754777540777306777777777777777754777540775402773021777777777754777540775402773021777777777777,
  777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777]


-- The subset automaton.
private def AccS (S : List Q) (ws : List V) : Prop := ∃ q ∈ S, RunFrom q ws

private def stepL (S : List Q) (a : V) : List Q :=
  S.flatMap fun q => (rd.filter fun x => decide (a = q.1 + x.2.1)).map fun x => (q.2 + x.1, x.2.2)

private def finB (S : List Q) (a : V) : Bool := S.any fun q => decide (q.2 = 0 ∧ a = q.1)

private def seteq (S S' : List Q) : Bool :=
  S.all (fun q => decide (q ∈ S')) && S'.all (fun q => decide (q ∈ S))

private theorem rd_sound : ∀ x ∈ rd, ∃ r, ok r ∧ (H r, U r, D r) = x := by decide +kernel

private theorem rd_complete : ∀ r, ok r → (H r, U r, D r) ∈ rd := by decide +kernel

private theorem mem_stepL (S : List Q) (a : V) (q' : Q) : q' ∈ stepL S a ↔
    ∃ q ∈ S, ∃ r, ok r ∧ a = q.1 + U r ∧ q' = (q.2 + H r, D r) := by
  simp only [stepL, List.mem_flatMap, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨q, hq, x, ⟨hx, ha⟩, rfl⟩
    obtain ⟨r, hr, rfl⟩ := rd_sound x hx
    exact ⟨q, hq, r, hr, ha, rfl⟩
  · rintro ⟨q, hq, r, hr, ha, rfl⟩
    exact ⟨q, hq, _, ⟨rd_complete r hr, ha⟩, rfl⟩

private theorem Acc_cons (S : List Q) (a : V) (ws : List V) :
    AccS S (a :: ws) ↔ (ws = [] ∧ finB S a = true) ∨ AccS (stepL S a) ws := by
  simp only [AccS, RunFrom, finB, List.any_eq_true, decide_eq_true_eq, mem_stepL]
  constructor
  · rintro ⟨q, hq, ⟨h1, h2, h3⟩ | ⟨r, hr, ha, hrun⟩⟩
    · exact Or.inl ⟨h1, q, hq, h2, h3⟩
    · exact Or.inr ⟨_, ⟨q, hq, r, hr, ha, rfl⟩, hrun⟩
  · rintro (⟨h1, q, hq, h2, h3⟩ | ⟨q', ⟨q, hq, r, hr, ha, rfl⟩, hrun⟩)
    · exact ⟨q, hq, Or.inl ⟨h1, h2, h3⟩⟩
    · exact ⟨q, hq, Or.inr ⟨r, hr, ha, hrun⟩⟩

private theorem Acc_congr (S S' : List Q) (h : seteq S S' = true) (ws : List V) :
    AccS S ws ↔ AccS S' ws := by
  simp only [seteq, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  constructor
  · rintro ⟨q, hq, hr⟩; exact ⟨q, h.1 q hq, hr⟩
  · rintro ⟨q, hq, hr⟩; exact ⟨q, h.2 q hq, hr⟩

private abbrev L := Fin 6 × Fin 6 × Fin 6

private def val (a : L) : V := ((a.1 : ℕ), (a.2.1 : ℕ), (a.2.2 : ℕ))

private def tblV (i : Fin 8) (v : V) : Fin 8 :=
  if v.1 < 6 ∧ v.2.1 < 6 ∧ v.2.2 < 6 then
    ⟨tblN i / 10 ^ (36 * v.1 + 6 * v.2.1 + v.2.2) % 10 % 8, Nat.mod_lt _ (by norm_num)⟩
  else 7

private def tbl (i : Fin 8) (a : L) : Fin 8 := tblV i (val a)

private theorem hfwd : ∀ i : Fin 8, ∀ q ∈ SS i, ∀ x ∈ rd,
    (SS (tblV i (q.1 + x.2.1))).elem (q.2 + x.1, x.2.2) = true := by
  decide +kernel

private theorem hbwd : ∀ i : Fin 8, ∀ a : L, tbl i a = 7 ∨
    (SS (tbl i a)).all (fun q' => decide (q' ∈ stepL (SS i) (val a))) = true := by
  decide +kernel

private theorem hstep_iff (i : Fin 8) (a : L) (q' : Q) :
    q' ∈ stepL (SS i) (val a) ↔ q' ∈ SS (tbl i a) := by
  constructor
  · intro h
    simp only [stepL, List.mem_flatMap, List.mem_map, List.mem_filter, decide_eq_true_eq] at h
    obtain ⟨q, hq, x, ⟨hx, ha⟩, rfl⟩ := h
    have := List.elem_iff.1 (hfwd i q hq x hx)
    rw [tbl, ha]
    exact this
  · intro h
    rcases hbwd i a with h7 | h2
    · have hS : SS 7 = [] := rfl
      rw [h7, hS] at h
      simp at h
    · simp only [List.all_eq_true, decide_eq_true_eq] at h2
      exact h2 q' h

private theorem Acc_congr' (S S' : List Q) (h : ∀ q, q ∈ S ↔ q ∈ S') (ws : List V) :
    AccS S ws ↔ AccS S' ws := by
  constructor
  · rintro ⟨q, hq, hr⟩; exact ⟨q, (h q).1 hq, hr⟩
  · rintro ⟨q, hq, hr⟩; exact ⟨q, (h q).2 hq, hr⟩

private theorem hstart1 : ∀ q ∈ SS 0, ∃ r, ok r ∧ U r = 0 ∧ (H r, D r) = q := by decide +kernel

private theorem hstart2' : ∀ r : Rw, ok r → U r = 0 → (SS 0).elem (H r, D r) = true := by
  decide +kernel

private theorem hstart2 (r : Rw) (h1 : ok r) (h2 : U r = 0) : (H r, D r) ∈ SS 0 :=
  List.elem_iff.1 (hstart2' r h1 h2)

open Classical in
private noncomputable def cnt (S : List Q) (n : ℕ) : ℕ :=
  (Finset.univ.filter fun w : Fin n → L => AccS S (List.ofFn fun i => val (w i))).card

private theorem card_cons {α : Type} [Fintype α] [DecidableEq α] (n : ℕ)
    (P : (Fin (n + 1) → α) → Prop) [DecidablePred P] :
    (Finset.univ.filter P).card =
      ∑ c : α, (Finset.univ.filter fun y : Fin n → α => P (Fin.cons c y)).card := by
  simp only [Finset.card_filter]
  rw [← (Fin.consEquiv fun _ => α).sum_comp, Fintype.sum_prod_type]
  simp [Fin.consEquiv]
  simp only [Finset.card_filter]
  congr! 3

private theorem cnt_one (S : List Q) :
    cnt S 1 = (Finset.univ.filter fun a : L => finB S (val a) = true).card := by
  classical
  rw [cnt, card_cons, Finset.card_filter]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hA : AccS S [val a] ↔ finB S (val a) = true := by
    rw [Acc_cons]; simp [AccS, RunFrom]
  by_cases h : finB S (val a) = true
  · rw [if_pos h, Finset.filter_true_of_mem]
    · rfl
    · intro y _; simpa [List.ofFn_succ, hA] using h
  · rw [if_neg h, Finset.filter_false_of_mem]
    · rfl
    · intro y _; simpa [List.ofFn_succ, hA] using h

private theorem cnt_succ (S : List Q) (n : ℕ) :
    cnt S (n + 2) = ∑ a : L, cnt (stepL S (val a)) (n + 1) := by
  classical
  rw [cnt, card_cons]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [cnt]
  congr 1
  refine Finset.filter_congr fun y _ => ?_
  rw [List.ofFn_succ, Fin.cons_zero, Acc_cons]
  simp only [Fin.cons_succ, List.ofFn_succ, reduceCtorEq, false_and, false_or]

private def T (i j : Fin 8) : ℕ := (Finset.univ.filter fun a : L => tbl i a = j).card

private def fc (i : Fin 8) : ℕ := (Finset.univ.filter fun a : L => finB (SS i) (val a) = true).card

private def cv : ℕ → Fin 8 → ℕ
  | 0 => fc
  | n + 1 => fun i => ∑ j, T i j * cv n j

private theorem cnt_cv (n : ℕ) : ∀ i, cnt (SS i) (n + 1) = cv n i := by
  classical
  induction n with
  | zero => intro i; rw [cnt_one]; rfl
  | succ n ih =>
    intro i
    rw [cnt_succ]
    have h1 : ∀ a : L, cnt (stepL (SS i) (val a)) (n + 1) = cv n (tbl i a) := by
      intro a
      rw [← ih]
      unfold cnt
      congr 1
      exact Finset.filter_congr fun w _ => Acc_congr' _ _ (hstep_iff i a) _
    rw [Finset.sum_congr rfl fun a _ => h1 a]
    rw [← Finset.sum_fiberwise Finset.univ (tbl i) (fun a => cv n (tbl i a))]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_congr rfl (g := fun _ => cv n j) (fun a ha => by rw [(Finset.mem_filter.1 ha).2])]
    rw [Finset.sum_const, smul_eq_mul]
    rfl

private theorem cv_base : ∀ i, cv 2 i + 41 * cv 0 i = 26 * cv 1 i := by decide +kernel

private theorem cv_rec (n : ℕ) : ∀ i, cv (n + 2) i + 41 * cv n i = 26 * cv (n + 1) i := by
  induction n with
  | zero => exact cv_base
  | succ n ih =>
    intro i
    show ∑ j, T i j * cv (n + 2) j + 41 * ∑ j, T i j * cv n j = 26 * ∑ j, T i j * cv (n + 1) j
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show T i j * cv (n + 2) j + 41 * (T i j * cv n j) =
      T i j * (cv (n + 2) j + 41 * cv n j) by ring, ih j]
    ring

private theorem occ_le (n : ℕ) (mv : Fin n → Rw) (i : Fin n) (j : Fin 3) : occ n mv i j ≤ 5 := by
  classical
  have h : occ n mv i j = ((Finset.univ ×ˢ Finset.univ).filter fun p : Fin n × Fin 3 =>
      (p.1 : ℤ) + (mv p.1 p.2).dr = i ∧ (p.2 : ℤ) + (mv p.1 p.2).dc = j).card := by
    rw [Finset.card_filter, Finset.sum_product]; rfl
  rw [h]
  calc _ ≤ (Finset.univ : Finset Move).card := by
        apply Finset.card_le_card_of_injOn (fun p => mv p.1 p.2)
        · intro p _; simp
        · intro p hp q hq he
          simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_univ, true_and,
            Set.mem_ofPred_eq] at hp hq
          simp only at he
          rw [he] at hp
          exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))
    _ = 5 := rfl

private def f5 (x : ℕ) : Fin 6 := ⟨x % 6, Nat.mod_lt _ (by norm_num)⟩

private theorem card_img (m : ℕ) : a (m + 1) = (Finset.univ.filter fun w : Fin (m + 1) → L =>
    ∃ mv, valid (m + 1) mv ∧ ∀ i, tr (occ (m + 1) mv i) = val (w i)).card := by
  have hb : ∀ mv i j, occ (m + 1) mv i j < 6 := fun mv i j => by
    have := occ_le (m + 1) mv i j; omega
  unfold a
  apply Finset.card_nbij'
    (fun (z : Fin (m + 1) → Fin 3 → ℕ) i =>
      (f5 (z i 0), f5 (z i 1), f5 (z i 2)))
    (fun (w : Fin (m + 1) → L) i j => ![((w i).1 : ℕ), ((w i).2.1 : ℕ), ((w i).2.2 : ℕ)] j)
  · intro z hz
    obtain ⟨mv, hmv, rfl⟩ := Finset.mem_image.1 hz
    rw [Finset.mem_coe, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, mv, (Finset.mem_filter.1 hmv).2, fun i => ?_⟩
    simp only [tr, val, f5, Nat.mod_eq_of_lt (hb _ _ _)]
  · intro w hw
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hw
    obtain ⟨mv, hmv, h⟩ := hw
    refine Finset.mem_image.2 ⟨mv, by simpa using hmv, funext fun i => funext fun j => ?_⟩
    have := h i
    simp only [tr, val, Prod.mk.injEq] at this
    fin_cases j <;> simp [this.1, this.2.1, this.2.2]
  · intro z hz
    obtain ⟨mv, hmv, rfl⟩ := Finset.mem_image.1 hz
    funext i j
    fin_cases j <;> simp [f5, Nat.mod_eq_of_lt (hb _ _ _)]
  · intro w _
    funext i
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
    ext <;> simp [f5, Nat.mod_eq_of_lt (Fin.isLt _)]

private theorem start_iff (ws : List V) :
    (∃ r0, ok r0 ∧ U r0 = 0 ∧ RunFrom (H r0, D r0) ws) ↔ AccS (SS 0) ws := by
  constructor
  · rintro ⟨r0, h1, h2, h3⟩; exact ⟨_, hstart2 r0 h1 h2, h3⟩
  · rintro ⟨q, hq, h⟩
    obtain ⟨r0, h1, h2, rfl⟩ := hstart1 q hq
    exact ⟨r0, h1, h2, h⟩

private theorem a_eq (m : ℕ) : a (m + 1) = cv m 0 := by
  classical
  rw [← cnt_cv, card_img, cnt]
  congr 1
  refine Finset.filter_congr fun w _ => ?_
  rw [← start_iff, ← sem m _ (by simp)]
  simp only [List.ofFn_inj, funext_iff]

private theorem a1 : a 1 = 8 := by rw [a_eq]; decide +kernel
private theorem a2 : a 2 = 200 := by rw [a_eq]; decide +kernel

private theorem a_rec (m : ℕ) : a (m + 3) + 41 * a (m + 1) = 26 * a (m + 2) := by
  rw [a_eq, a_eq, a_eq]
  exact cv_rec m 0

private theorem gf :
    (1 - 26 * X + 41 * X ^ 2) * mk (fun n => if n = 0 then 0 else (a n : ℤ)) =
      (8 * X * (1 - X) : PowerSeries ℤ) := by
  set s : PowerSeries ℤ := mk (fun n => if n = 0 then 0 else (a n : ℤ)) with hs
  have hd : (1 - 26 * X + 41 * X ^ 2) * s =
      s - (s * C (26 : ℤ)) * X ^ 1 + (s * C (41 : ℤ)) * X ^ 2 := by
    simp only [pow_one, map_ofNat]
    ring
  have hn : (8 * X * (1 - X) : PowerSeries ℤ) = C (8 : ℤ) * X ^ 1 - C (8 : ℤ) * X ^ 2 := by
    simp only [pow_one, map_ofNat]
    ring
  rw [hd, hn]
  ext n
  simp only [map_add, map_sub, coeff_mul_X_pow', coeff_mul_C, coeff_C, hs, coeff_mk]
  rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2 ∨ 3 ≤ n) with h | h | h | h
  · subst h; simp
  · subst h; simp [a1]
  · subst h; simp [a1, a2]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    have := a_rec m
    simp only [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega]
    simp
    omega

private noncomputable def R (n : ℕ) : ℝ :=
  ((13 - 8 * Real.sqrt 2) ^ n * (4 - 7 * Real.sqrt 2) +
    (4 + 7 * Real.sqrt 2) * (13 + 8 * Real.sqrt 2) ^ n) / 41

private theorem root_step (x : ℝ) (h : x ^ 2 = 26 * x - 41) (j : ℕ) :
    x ^ (j + 2) = 26 * x ^ (j + 1) - 41 * x ^ j := by
  linear_combination x ^ j * h

private theorem R_rec (j : ℕ) : R (j + 2) = 26 * R (j + 1) - 41 * R j := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h1 := root_step (13 - 8 * Real.sqrt 2) (by linear_combination 64 * hs) j
  have h2 := root_step (13 + 8 * Real.sqrt 2) (by linear_combination 64 * hs) j
  unfold R
  rw [h1, h2]
  ring

private theorem closed (m : ℕ) : (a (m + 1) : ℝ) = R (m + 1) ∧ (a (m + 2) : ℝ) = R (m + 2) := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  induction m with
  | zero =>
    refine ⟨?_, ?_⟩
    · rw [a1, R, eq_div_iff (by norm_num)]; push_cast; linear_combination (-112) * hs
    · rw [a2, R, eq_div_iff (by norm_num)]; push_cast; linear_combination (-3424) * hs
  | succ m ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨h2, ?_⟩
    have hr : (a (m + 3) : ℝ) + 41 * (a (m + 1) : ℝ) = 26 * (a (m + 2) : ℝ) := by
      exact_mod_cast a_rec m
    rw [show m + 1 + 2 = m + 1 + 2 from rfl, R_rec (m + 1)]
    rw [show m + 1 + 1 = m + 2 by ring] at h2 ⊢
    rw [show m + 1 + 2 = m + 3 by ring]
    linarith

theorem OMA.solution : type_of% @OMA.S_oeis_a221121.main := by
  refine ⟨gf, fun n hn => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [(closed m).1, R]
