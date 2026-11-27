import OMAReductions.R_OeisA109074_conjecture_R1

-- Step OeisA109074.conjecture.R1.H1: hypothesis H1 of reduction OeisA109074.conjecture.R1
-- Credit: @senamakel
-- H1 := ∀ n : ℕ,   let I := Fin (2*n+1)   let lineOK (v : I → Fin 3) :=     let partialSum (k : ℕ) := ∑ j : I, if j.val < k then ((v j).val : ℤ) - 1 else 0     partialSum (2*n+1) = 1 ∧ ∀ k : Fin (2*n+2), partialSum k.val = 0 ∨ partialSum k.val = 1   let matrices : Set (I → I → Fin 3) := {M | (∀ i, lineOK (M i)) ∧     (∀ j, lineOK fun i => M i j) ∧ ∀ i j, M i j = M i (Fin.rev j)}   b n = matrices.ncard


open OeisA109074

namespace OMAA109074H1

theorem take_ofFn_sum : ∀ (m : ℕ) (g : Fin m → ℤ) (k : ℕ),
    ((List.ofFn g).take k).sum = ∑ j : Fin m, if j.val < k then g j else 0
  | 0, g, k => by simp
  | m+1, g, 0 => by simp
  | m+1, g, k+1 => by
    rw [List.ofFn_succ, List.take_succ_cons, List.sum_cons, take_ofFn_sum m _ k, Fin.sum_univ_succ]
    simp [Fin.val_succ]

theorem aux_iff : ∀ (xs : List ℤ) (acc : ℤ), isAsmLineAux acc xs = true ↔
    (∀ i, i < xs.length → (acc + (xs.take (i+1)).sum = 0 ∨ acc + (xs.take (i+1)).sum = 1)) ∧
      acc + xs.sum = 1
  | [], acc => by simp [isAsmLineAux]
  | x :: xs, acc => by
    simp only [isAsmLineAux, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, aux_iff xs (acc + x)]
    constructor
    · rintro ⟨h0, h1, h2⟩
      refine ⟨fun i hi => ?_, by simp; linarith⟩
      cases i with
      | zero => simpa using h0
      | succ i =>
        have := h1 i (by simpa using hi)
        simp only [List.take_succ_cons, List.sum_cons]
        rw [← add_assoc]; exact this
    · rintro ⟨h1, h2⟩
      refine ⟨by simpa using h1 0 (by simp), fun i hi => ?_, by simp at h2; linarith⟩
      have := h1 (i+1) (by simp; omega)
      simp only [List.take_succ_cons, List.sum_cons] at this
      rw [add_assoc]; exact this

def rowList {m : ℕ} (v : Fin m → Fin 3) : List ℤ := List.ofFn fun j => ((v j).val : ℤ) - 1

def LineOK (m : ℕ) (v : Fin m → Fin 3) : Prop :=
  let partialSum (k : ℕ) := ∑ j : Fin m, if j.val < k then ((v j).val : ℤ) - 1 else 0
  partialSum m = 1 ∧ ∀ k : Fin (m+1), partialSum k.val = 0 ∨ partialSum k.val = 1

theorem isAsmLine_rowList (m : ℕ) (v : Fin m → Fin 3) :
    isAsmLine (rowList v) = true ↔ LineOK m v := by
  unfold isAsmLine LineOK
  rw [aux_iff]
  simp only [zero_add, ← take_ofFn_sum]
  have hl : (rowList v).length = m := by simp [rowList]
  have hs : ((rowList v).take m).sum = (rowList v).sum := by
    rw [List.take_of_length_le (by omega)]
  rw [hl]
  unfold rowList at hs ⊢
  rw [hs]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h2, fun k => ?_⟩
    rcases k with ⟨k, hk⟩
    cases k with
    | zero => simp
    | succ k => exact h1 k (by omega)
  · rintro ⟨h1, h2⟩
    exact ⟨fun i hi => h2 ⟨i+1, by omega⟩, h1⟩


def Tri (x : ℤ) : Prop := x = -1 ∨ x = 0 ∨ x = 1

theorem mem_trinaryLists : ∀ (k : ℕ) (xs : List ℤ),
    xs ∈ trinaryLists k ↔ xs.length = k ∧ ∀ x ∈ xs, Tri x
  | 0, xs => by
    simp only [trinaryLists, List.mem_singleton]
    constructor
    · rintro rfl; simp
    · rintro ⟨h, -⟩; exact List.length_eq_zero_iff.mp h
  | k+1, xs => by
    simp only [trinaryLists, List.mem_flatMap, mem_trinaryLists k, List.mem_cons,
      List.not_mem_nil, or_false]
    constructor
    · rintro ⟨ys, ⟨hl, hy⟩, h | h | h⟩ <;> subst h <;>
        refine ⟨by simp [hl], fun x hx => ?_⟩ <;>
        simp only [List.mem_cons] at hx <;> rcases hx with rfl | hx <;>
        first | exact hy x hx | (unfold Tri; norm_num)
    · rintro ⟨hl, hx⟩
      cases xs with
      | nil => simp at hl
      | cons x ys =>
        refine ⟨ys, ⟨by simpa using hl, fun y hy => hx y (by simp [hy])⟩, ?_⟩
        rcases hx x (by simp) with rfl | rfl | rfl <;> simp

theorem nodup_trinaryLists : ∀ k, (trinaryLists k).Nodup
  | 0 => by simp [trinaryLists]
  | k+1 => by
    rw [trinaryLists, List.nodup_flatMap]
    refine ⟨fun xs _ => by simp, ?_⟩
    refine (nodup_trinaryLists k).imp ?_
    intro a b hab
    simp only [Function.onFun, List.disjoint_left, List.mem_cons, List.not_mem_nil, or_false]
    rintro l (rfl | rfl | rfl) (h | h | h) <;> simp at h <;> exact hab h

theorem row_decomp (n : ℕ) (r : List ℤ) (hl : r.length = 2*n+1) (hr : r.reverse = r) :
    r = r.take n ++ [r[n]'(by omega)] ++ (r.take n).reverse := by
  have h1 : (r.take n).reverse = r.drop (n+1) := by
    rw [List.reverse_take, hr, hl]; congr 1; omega
  rw [h1, List.append_assoc, List.singleton_append, ← List.drop_eq_getElem_cons,
    List.take_append_drop]

theorem mem_symAsmRows (n : ℕ) (r : List ℤ) :
    r ∈ symAsmRows n ↔ r.length = 2*n+1 ∧ (∀ x ∈ r, Tri x) ∧ r.reverse = r ∧
      isAsmLine r = true := by
  unfold symAsmRows
  simp only [List.mem_flatMap, List.mem_filterMap, mem_trinaryLists]
  constructor
  · rintro ⟨half, ⟨hl, hh⟩, mid, hmid, h⟩
    split_ifs at h with ha
    simp only [Option.some.injEq] at h
    subst h
    refine ⟨by simp [hl]; omega, fun x hx => ?_, by simp, ha⟩
    simp only [List.mem_append, List.mem_reverse, List.mem_singleton] at hx
    rcases hx with (hx | rfl) | hx
    · exact hh x hx
    · simp at hmid; unfold Tri; omega
    · exact hh x hx
  · rintro ⟨hl, hx, hr, ha⟩
    have hd := row_decomp n r hl hr
    refine ⟨r.take n, ⟨by simp; omega, fun x h => hx x (List.mem_of_mem_take h)⟩,
      r[n]'(by omega), ?_, ?_⟩
    · have := hx (r[n]'(by omega)) (List.getElem_mem _)
      unfold Tri at this; simp; omega
    · rw [← hd, if_pos ha]

theorem nodup_symAsmRows (n : ℕ) : (symAsmRows n).Nodup := by
  unfold symAsmRows
  rw [List.nodup_flatMap]
  constructor
  · intro half _
    apply List.Nodup.filterMap _ (by simp)
    intro a a' b ha ha'
    simp only [Option.mem_def] at ha ha'
    split_ifs at ha ha' <;> simp at ha ha'
    subst ha
    simp at ha'
    exact ha'.symm
  · refine (nodup_trinaryLists n).imp_of_mem ?_
    intro a b ha hb hab
    simp only [Function.onFun, List.disjoint_left, List.mem_filterMap]
    rintro l ⟨x, -, hx⟩ ⟨y, -, hy⟩
    split_ifs at hx hy <;> simp at hx hy
    rw [mem_trinaryLists] at ha hb
    have := congrArg (List.take n) (hx.trans hy.symm)
    simp [ha.1, hb.1] at this
    exact hab this


theorem rowList_injective {m : ℕ} : Function.Injective (@rowList m) := by
  intro v w h
  have := List.ofFn_injective h
  funext j
  have hj := congrFun this j
  apply Fin.ext
  omega

theorem rowList_reverse {m : ℕ} (v : Fin m → Fin 3) :
    (rowList v).reverse = rowList (fun j => v j.rev) := by
  apply List.ext_getElem (by simp [rowList])
  intro i h1 h2
  simp only [rowList, List.getElem_reverse, List.getElem_ofFn, List.length_ofFn]
  have hi : i < m := by simpa [rowList] using h2
  have : (Fin.rev ⟨i, hi⟩ : Fin m) = ⟨m - 1 - i, by omega⟩ := Fin.ext (by simp [Fin.val_rev]; omega)
  rw [this]

theorem rowList_mem (n : ℕ) (v : Fin (2*n+1) → Fin 3) :
    rowList v ∈ symAsmRows n ↔ LineOK (2*n+1) v ∧ ∀ j, v j = v j.rev := by
  rw [mem_symAsmRows, isAsmLine_rowList, rowList_reverse]
  have htri : ∀ x ∈ rowList v, Tri x := by
    intro x hx
    simp only [rowList, List.mem_ofFn] at hx
    obtain ⟨j, rfl⟩ := hx
    have := (v j).isLt
    unfold Tri; omega
  have hsym : rowList (fun j => v j.rev) = rowList v ↔ ∀ j, v j = v j.rev := by
    constructor
    · intro h j; exact (congrFun (rowList_injective h) j).symm
    · intro h; congr 1; funext j; exact (h j).symm
  rw [hsym]
  simp [rowList, htri]
  tauto

def toF3 (x : ℤ) : Fin 3 := if x = -1 then 0 else if x = 0 then 1 else 2

theorem exists_rowList {m : ℕ} (r : List ℤ) (hl : r.length = m) (ht : ∀ x ∈ r, Tri x) :
    ∃ v : Fin m → Fin 3, rowList v = r := by
  refine ⟨fun j => toF3 (r[j.val]'(by omega)), ?_⟩
  apply List.ext_getElem (by simp [rowList, hl])
  intro i h1 h2
  simp only [rowList, List.getElem_ofFn]
  have := ht _ (List.getElem_mem h2)
  unfold Tri at this
  unfold toF3
  rcases this with h | h | h <;> simp [h]

theorem foldl_eq_sum (rows : List (List ℤ)) (p : List ℤ → Bool) (g : List ℤ → ℕ) :
    ∀ a : ℕ, rows.foldl (fun acc r => if p r then acc + g r else acc) a =
      a + (rows.map fun r => if p r then g r else 0).sum := by
  induction rows with
  | nil => intro a; simp
  | cons r rs ih =>
    intro a
    simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih]
    split_ifs <;> omega

def lists (rows : List (List ℤ)) : ℕ → List (List (List ℤ))
  | 0 => [[]]
  | k+1 => rows.flatMap fun r => (lists rows k).map (r :: ·)

def good : List ℤ → List (List ℤ) → Bool
  | c, [] => c.all (· == 1)
  | c, r :: L => (List.zipWith (· + ·) c r).all (fun s => s == 0 || s == 1) &&
      good (List.zipWith (· + ·) c r) L

theorem count_eq (rows : List (List ℤ)) : ∀ (k : ℕ) (c : List ℤ),
    countVsasmRows rows k c = ((lists rows k).filter (good c)).length
  | 0, c => by
    simp only [countVsasmRows, lists]
    by_cases h : (c.all fun x => x == 1) = true
    · rw [if_pos h, List.filter_cons_of_pos (by simpa [good] using h)]; rfl
    · rw [if_neg h, List.filter_cons_of_neg (by simpa [good] using h)]; rfl
  | k+1, c => by
    simp only [countVsasmRows]
    rw [foldl_eq_sum rows (fun r => (List.zipWith (· + ·) c r).all (fun s => s == 0 || s == 1))
      (fun r => countVsasmRows rows k (List.zipWith (· + ·) c r)) 0]
    simp only [lists, List.filter_flatMap, List.length_flatMap, zero_add]
    congr 1
    apply List.map_congr_left
    intro r _
    rw [List.filter_map, List.length_map, count_eq rows k]
    split_ifs with h
    · congr 2
      funext L
      simp [good, h]
    · have : (good c ∘ (r :: ·)) = fun _ => false := by
        funext L; simp [good, h]
      rw [this]; simp

theorem mem_lists (rows : List (List ℤ)) : ∀ (k : ℕ) (L : List (List ℤ)),
    L ∈ lists rows k ↔ L.length = k ∧ ∀ r ∈ L, r ∈ rows
  | 0, L => by
    simp only [lists, List.mem_singleton]
    constructor
    · rintro rfl; simp
    · rintro ⟨h, -⟩; exact List.length_eq_zero_iff.mp h
  | k+1, L => by
    simp only [lists, List.mem_flatMap, List.mem_map, mem_lists rows k]
    constructor
    · rintro ⟨r, hr, L', ⟨hl, hL⟩, rfl⟩
      refine ⟨by simp [hl], fun x hx => ?_⟩
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hr
      · exact hL x hx
    · rintro ⟨hl, hL⟩
      cases L with
      | nil => simp at hl
      | cons r L' =>
        exact ⟨r, hL r (by simp), L', ⟨by simpa using hl, fun x hx => hL x (by simp [hx])⟩, rfl⟩

theorem nodup_lists (rows : List (List ℤ)) (hr : rows.Nodup) : ∀ k, (lists rows k).Nodup
  | 0 => by simp [lists]
  | k+1 => by
    rw [lists, List.nodup_flatMap]
    refine ⟨fun r _ => (nodup_lists rows hr k).map (fun a b h => by simpa using h), ?_⟩
    refine hr.imp ?_
    intro a b hab
    simp only [Function.onFun, List.disjoint_left, List.mem_map]
    rintro l ⟨x, -, rfl⟩ ⟨y, -, hy⟩
    simp at hy
    exact hab hy.1.symm


theorem zipWith_ofFn {m : ℕ} (f g : Fin m → ℤ) :
    List.zipWith (· + ·) (List.ofFn f) (List.ofFn g) = List.ofFn (fun j => f j + g j) := by
  apply List.ext_getElem (by simp)
  intro i h1 h2; simp

theorem all_ofFn_iff {m : ℕ} (f : Fin m → ℤ) (p : ℤ → Bool) :
    (List.ofFn f).all p = true ↔ ∀ j, p (f j) = true := by
  simp [List.all_eq_true, List.mem_ofFn]

def ColGood (k m : ℕ) (cf : Fin m → ℤ) (A : Fin k → Fin m → ℤ) : Prop :=
  (∀ t, 1 ≤ t → t ≤ k → ∀ j, cf j + (∑ i : Fin k, if i.val < t then A i j else 0) = 0 ∨
      cf j + (∑ i : Fin k, if i.val < t then A i j else 0) = 1) ∧
  ∀ j, cf j + ∑ i, A i j = 1

theorem good_iff {m : ℕ} : ∀ (k : ℕ) (cf : Fin m → ℤ) (A : Fin k → Fin m → ℤ),
    good (List.ofFn cf) (List.ofFn fun i => List.ofFn (A i)) = true ↔ ColGood k m cf A
  | 0, cf, A => by
    rw [List.ofFn_zero, good, all_ofFn_iff]
    unfold ColGood
    simp only [beq_iff_eq, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
    constructor
    · intro h; exact ⟨fun t h1 h2 => by omega, h⟩
    · intro h; exact h.2
  | k+1, cf, A => by
    rw [List.ofFn_succ, good, zipWith_ofFn, Bool.and_eq_true, good_iff k, all_ofFn_iff]
    unfold ColGood
    simp only [Bool.or_eq_true, beq_iff_eq, Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ]
    constructor
    · rintro ⟨h0, h1, h2⟩
      refine ⟨fun t ht1 htk j => ?_, fun j => by rw [← h2 j]; ring⟩
      rcases (show t = 1 ∨ 2 ≤ t by omega) with rfl | ht
      · have : ∀ i : Fin k, ¬ (i.val + 1 < 1) := fun i => by omega
        simp only [this, if_false, Finset.sum_const_zero, add_zero, zero_lt_one, if_true]
        exact h0 j
      · obtain ⟨t', rfl⟩ : ∃ t', t = t'+1 := ⟨t-1, by omega⟩
        have := h1 t' (by omega) (by omega) j
        have e : ∀ i : Fin k, (i.val + 1 < t' + 1) ↔ i.val < t' := fun i => by omega
        simp only [e, Nat.zero_lt_succ, if_true]
        rw [← add_assoc]; exact this
    · rintro ⟨h1, h2⟩
      refine ⟨fun j => ?_, fun t ht1 htk j => ?_, fun j => by rw [← h2 j]; ring⟩
      · have := h1 1 le_rfl (by omega) j
        have : ∀ i : Fin k, ¬ (i.val + 1 < 1) := fun i => by omega
        simpa [this] using h1 1 le_rfl (by omega) j
      · have := h1 (t+1) (by omega) (by omega) j
        have e : ∀ i : Fin k, (i.val + 1 < t + 1) ↔ i.val < t := fun i => by omega
        simp only [e, Nat.zero_lt_succ, if_true] at this
        rw [add_assoc]; exact this

theorem colGood_iff (m : ℕ) (A : Fin m → Fin m → Fin 3) :
    ColGood m m (fun _ => 0) (fun i j => ((A i j).val : ℤ) - 1) ↔
      ∀ j, LineOK m (fun i => A i j) := by
  unfold ColGood LineOK
  simp only [zero_add]
  have htot : ∀ j, (∑ i : Fin m, if i.val < m then ((A i j).val : ℤ) - 1 else 0) =
      ∑ i : Fin m, (((A i j).val : ℤ) - 1) :=
    fun j => Finset.sum_congr rfl fun i _ => if_pos i.isLt
  constructor
  · rintro ⟨h1, h2⟩ j
    refine ⟨by rw [htot]; exact h2 j, fun k => ?_⟩
    rcases k with ⟨k, hk⟩
    cases k with
    | zero => simp
    | succ k => exact h1 (k+1) (by omega) (by omega) j
  · intro h
    exact ⟨fun t h1 h2 j => (h j).2 ⟨t, by omega⟩, fun j => by rw [← htot]; exact (h j).1⟩

def Mat (n : ℕ) : Set (Fin (2*n+1) → Fin (2*n+1) → Fin 3) :=
  {M | (∀ i, LineOK (2*n+1) (M i)) ∧ (∀ j, LineOK (2*n+1) fun i => M i j) ∧
    ∀ i j, M i j = M i (Fin.rev j)}

def fM {m : ℕ} (M : Fin m → Fin m → Fin 3) : List (List ℤ) := List.ofFn fun i => rowList (M i)

theorem fM_injective {m : ℕ} : Function.Injective (@fM m) := by
  intro M M' h
  have := List.ofFn_injective h
  funext i
  exact rowList_injective (congrFun this i)

theorem fM_mem (n : ℕ) (M : Fin (2*n+1) → Fin (2*n+1) → Fin 3) :
    (fM M ∈ lists (symAsmRows n) (2*n+1) ∧
      good (List.replicate (2*n+1) 0) (fM M) = true) ↔ M ∈ Mat n := by
  have hc : List.replicate (2*n+1) (0:ℤ) = List.ofFn (fun _ : Fin (2*n+1) => (0:ℤ)) := by
    rw [List.ofFn_const]
  rw [mem_lists, hc, show fM M = List.ofFn fun i => List.ofFn fun j => ((M i j).val : ℤ) - 1
    from rfl, good_iff, colGood_iff]
  have hrows : (∀ r ∈ List.ofFn (fun i => List.ofFn fun j => ((M i j).val : ℤ) - 1),
      r ∈ symAsmRows n) ↔ ∀ i, LineOK (2*n+1) (M i) ∧ ∀ j, M i j = M i j.rev := by
    simp only [List.mem_ofFn, forall_exists_index, forall_apply_eq_imp_iff]
    exact forall_congr' fun i => rowList_mem n (M i)
  rw [hrows]
  simp only [List.length_ofFn, true_and, Mat, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨fun i => (h1 i).1, h2, fun i => (h1 i).2⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨fun i => ⟨h1 i, h3 i⟩, h2⟩

theorem surj (n : ℕ) (L : List (List ℤ)) (hL : L ∈ lists (symAsmRows n) (2*n+1)) :
    ∃ M : Fin (2*n+1) → Fin (2*n+1) → Fin 3, fM M = L := by
  rw [mem_lists] at hL
  obtain ⟨hl, hr⟩ := hL
  have : ∀ i : Fin (2*n+1), ∃ v : Fin (2*n+1) → Fin 3, rowList v = L[i.val]'(by omega) := by
    intro i
    have h := (mem_symAsmRows n (L[i.val]'(by omega))).1 (hr _ (List.getElem_mem _))
    exact exists_rowList _ h.1 h.2.1
  choose M hM using this
  refine ⟨M, List.ext_getElem (by simp [fM, hl]) fun i h1 h2 => ?_⟩
  simp only [fM, List.getElem_ofFn]
  exact hM ⟨i, by simpa [fM] using h1⟩

theorem main_eq (n : ℕ) : b n = (Mat n).ncard := by
  have hb : b n = ((lists (symAsmRows n) (2*n+1)).filter
      (good (List.replicate (2*n+1) 0))).length := count_eq _ _ _
  have hnd := ((nodup_lists _ (nodup_symAsmRows n) (2*n+1)).filter
    (good (List.replicate (2*n+1) 0)))
  have himg : fM '' Mat n = ↑((lists (symAsmRows n) (2*n+1)).filter
      (good (List.replicate (2*n+1) 0))).toFinset := by
    ext L
    simp only [Set.mem_image, Finset.mem_coe, List.mem_toFinset, List.mem_filter]
    constructor
    · rintro ⟨M, hM, rfl⟩; exact (fM_mem n M).2 hM
    · rintro hL
      obtain ⟨M, rfl⟩ := surj n L hL.1
      exact ⟨M, (fM_mem n M).1 hL, rfl⟩
  rw [hb, ← List.toFinset_card_of_nodup hnd, ← Set.ncard_coe_finset, ← himg,
    Set.ncard_image_of_injective _ fM_injective]

end OMAA109074H1

theorem OMA.solution : OMA.R_OeisA109074_conjecture_R1.H1 := by
  intro n
  exact OMAA109074H1.main_eq n
