import OMAStatements.S_oeis_a097399

/-!
A097399: the maximum determinant for all n >= 0.
Credit: @arcstone09
Source: https://oeis.org/A097399
Related positive-entry result: Brother U. Alfred, Note on Third Order
Determinants, Fibonacci Quarterly 3(1) (1965), 59-60.
https://www.fq.math.ca/Scanned/3-1/alfred2.pdf
The finite bounds below are checked by the kernel after cyclic normalization.
-/

-- Numeric
namespace A097399Numeric

def det (n : ℤ) (l : List ℤ) : ℤ :=
  let a := n + l.getD 0 0
  let b := n + l.getD 1 0
  let c := n + l.getD 2 0
  let d := n + l.getD 3 0
  let e := n + l.getD 4 0
  let f := n + l.getD 5 0
  let g := n + l.getD 6 0
  let h := n + l.getD 7 0
  let i := n + l.getD 8 0
  a * (e*i-f*h) - b * (d*i-f*g) + c * (d*h-e*g)

def slope (l : List ℤ) : ℤ := det 1 l - det 0 l

def fastSlope (l : List ℤ) : ℤ :=
  let da := l.getD 3 0 - l.getD 0 0
  let eb := l.getD 4 0 - l.getD 1 0
  let fc := l.getD 5 0 - l.getD 2 0
  let ga := l.getD 6 0 - l.getD 0 0
  let hb := l.getD 7 0 - l.getD 1 0
  let ic := l.getD 8 0 - l.getD 2 0
  (eb-da)*(ic-ga)-(fc-da)*(hb-ga)

def bounds (l : List ℤ) : Bool :=
  let b := det 0 l
  let s := fastSlope l
  decide (b ≤ 86 ∧ s+b ≤ 104 ∧ 2*s+b ≤ 172 ∧ 12*s+b ≤ 972 ∧ s ≤ 81)


def checkTree : ℕ → List ℤ → List ℤ → Bool
  | 0, acc, _ => bounds acc
  | k+1, acc, rest => rest.all (fun x => checkTree k (acc ++ [x]) (rest.erase x))

end A097399Numeric

-- Core
namespace A097399Research

def offsets : List ℤ := [-4, -3, -2, -1, 0, 1, 2, 3, 4]

def matrix (n : ℤ) (l : List ℤ) : Matrix (Fin 3) (Fin 3) ℤ :=
  fun i j => n + l.getD (3 * i.val + j.val) 0

def det (n : ℤ) (l : List ℤ) : ℤ :=
  let a := n + l.getD 0 0
  let b := n + l.getD 1 0
  let c := n + l.getD 2 0
  let d := n + l.getD 3 0
  let e := n + l.getD 4 0
  let f := n + l.getD 5 0
  let g := n + l.getD 6 0
  let h := n + l.getD 7 0
  let i := n + l.getD 8 0
  a * (e*i-f*h) - b * (d*i-f*g) + c * (d*h-e*g)

theorem det_eq_matrix (n : ℤ) (l : List ℤ) : det n l = (matrix n l).det := by
  simp [det, matrix, Matrix.det_fin_three]
  ring

def slope (l : List ℤ) : ℤ := det 1 l - det 0 l

theorem affine (n : ℤ) (l : List ℤ) : det n l = n * slope l + det 0 l := by
  simp only [slope, det]
  ring

def bounds (l : List ℤ) : Bool :=
  let b := det 0 l
  let s := slope l
  decide (b ≤ 86 ∧ s+b ≤ 104 ∧ 2*s+b ≤ 172 ∧ 12*s+b ≤ 972 ∧ s ≤ 81)


def Certificate : Prop := offsets.permutations.all bounds = true

def answer (n : ℕ) : ℤ :=
  if n = 0 then 86 else if n = 1 then 104 else if n ≤ 12 then 80*n+12 else 81*n

theorem upper_from_certificate (hc : Certificate) (n : ℕ) (l : List ℤ)
    (hl : l.Perm offsets) : det n l ≤ answer n := by
  have hb : bounds l = true := List.all_eq_true.mp hc l (List.mem_permutations.mpr hl)
  have h : det 0 l ≤ 86 ∧ slope l + det 0 l ≤ 104 ∧
      2*slope l + det 0 l ≤ 172 ∧ 12*slope l + det 0 l ≤ 972 ∧ slope l ≤ 81 := by
    simpa only [bounds, decide_eq_true_eq] using hb
  rw [affine]
  unfold answer
  split_ifs with h0 h1 h12
  · subst n; norm_num; exact h.1
  · subst n; norm_num; exact h.2.1
  · have hn2 : (2 : ℤ) ≤ n := by omega
    have hn12 : (n : ℤ) ≤ 12 := by omega
    have hleft := mul_nonneg (sub_nonneg.mpr hn2) (sub_nonneg.mpr h.2.2.2.1)
    have hright := mul_nonneg (sub_nonneg.mpr hn12) (sub_nonneg.mpr h.2.2.1)
    nlinarith
  · have hn12 : (12 : ℤ) ≤ n := by omega
    have hm := mul_nonneg (sub_nonneg.mpr hn12) (sub_nonneg.mpr h.2.2.2.2)
    nlinarith [h.2.2.2.1]

def w0 : List ℤ := [-4,-3,0,1,-1,4,-2,3,2]
def w1 : List ℤ := [-4,-3,1,2,-1,3,-2,4,0]
def w2 : List ℤ := [-4,-1,3,2,-3,1,0,4,-2]
def w3 : List ℤ := [-4,-1,2,3,-3,0,1,4,-2]

theorem w0_perm : w0.Perm offsets := by decide
theorem w1_perm : w1.Perm offsets := by decide
theorem w2_perm : w2.Perm offsets := by decide
theorem w3_perm : w3.Perm offsets := by decide

theorem w0_det (n : ℤ) : det n w0 = 4*n+86 := by
  simp [det, w0]; ring
theorem w1_det (n : ℤ) : det n w1 = 32*n+72 := by
  simp [det, w1]; ring
theorem w2_det (n : ℤ) : det n w2 = 80*n+12 := by
  simp [det, w2]; ring
theorem w3_det (n : ℤ) : det n w3 = 81*n := by
  simp [det, w3]; ring

theorem attained (n : ℕ) : ∃ l, l.Perm offsets ∧ det n l = answer n := by
  unfold answer
  split_ifs with h0 h1 h12
  · subst n; exact ⟨w0, w0_perm, by simpa using w0_det 0⟩
  · subst n; exact ⟨w1, w1_perm, by simpa using w1_det 1⟩
  · exact ⟨w2, w2_perm, w2_det n⟩
  · exact ⟨w3, w3_perm, w3_det n⟩

def arrangements : Finset (List ℤ) := offsets.permutations.toFinset

theorem arrangements_nonempty : arrangements.Nonempty := by
  refine ⟨offsets, ?_⟩
  simp only [arrangements, List.mem_toFinset, List.mem_permutations]
  exact List.Perm.refl _

def a (n : ℕ) : ℤ :=
  arrangements.sup' arrangements_nonempty (fun l => (matrix n l).det)

theorem formula_from_certificate (hc : Certificate) (n : ℕ) : a n = answer n := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro l hl
    rw [← det_eq_matrix]
    exact upper_from_certificate hc n l (List.mem_permutations.mp (List.mem_toFinset.mp hl))
  · obtain ⟨l, hl, hd⟩ := attained n
    have hm : l ∈ arrangements := List.mem_toFinset.mpr (List.mem_permutations.mpr hl)
    have hh := Finset.le_sup' (fun l => (matrix (n : ℤ) l).det) hm
    change (matrix (n : ℤ) l).det ≤ a n at hh
    rw [← det_eq_matrix, hd] at hh
    exact hh

-- Coefficient of (86-68X+50X²+12X³+X¹³)/(1-X)².
def gfCoefficient (n : ℕ) : ℤ :=
  86*((n : ℤ)+1) - (if 1 ≤ n then 68*(n : ℤ) else 0) +
  (if 2 ≤ n then 50*((n : ℤ)-1) else 0) +
  (if 3 ≤ n then 12*((n : ℤ)-2) else 0) +
  (if 13 ≤ n then (n : ℤ)-12 else 0)

theorem generating_coefficients (n : ℕ) : gfCoefficient n = answer n := by
  unfold gfCoefficient answer
  split_ifs <;> omega


end A097399Research

-- Symmetry
namespace A097399Research

theorem fastSlope_eq (l : List ℤ) : A097399Numeric.fastSlope l = slope l := by
  simp only [A097399Numeric.fastSlope, slope, det]
  ring

theorem numeric_bounds_eq (l : List ℤ) : A097399Numeric.bounds l = bounds l := by
  simp only [A097399Numeric.bounds, bounds, fastSlope_eq]
  rfl

abbrev checkTree := A097399Numeric.checkTree

theorem checkTree_sound (k : ℕ) (acc rest suffix : List ℤ)
    (hp : suffix.Perm rest) (hl : suffix.length = k)
    (hc : checkTree k acc rest = true) : A097399Numeric.bounds (acc ++ suffix) = true := by
  induction k generalizing acc rest suffix with
  | zero =>
    have hs : suffix = [] := List.length_eq_zero_iff.mp hl
    subst suffix
    simpa only [checkTree, A097399Numeric.checkTree, List.append_nil] using hc
  | succ k ih =>
    cases suffix with
    | nil => simp at hl
    | cons x xs =>
      have hx : x ∈ rest := hp.mem_iff.mp (by simp)
      have hperm : xs.Perm (rest.erase x) := by
        simpa only [List.erase_cons_head] using hp.erase x
      have hlen : xs.length = k := by simpa using hl
      have hchild := List.all_eq_true.mp hc x hx
      have result := ih (acc ++ [x]) (rest.erase x) xs hperm hlen hchild
      simpa only [List.append_assoc, List.singleton_append] using result



theorem det_rotation (n a b c d e f g h i : ℤ) :
    det n [a,b,c,d,e,f,g,h,i] = det n [d,e,f,g,h,i,a,b,c] := by
  simp [det]
  ring

theorem rotate_perm_01 (a b c d e f g h i : ℤ) :
    [b,c,a,e,f,d,h,i,g].Perm [a,b,c,d,e,f,g,h,i] := by
  have hperm : ([1, 2, 0, 4, 5, 3, 7, 8, 6] : List ℕ).Perm [0,1,2,3,4,5,6,7,8] := by decide
  simpa using hperm.map (fun k => ([a,b,c,d,e,f,g,h,i] : List ℤ).getD k 0)

theorem rotate_det_01 (n a b c d e f g h i : ℤ) :
    det n [a,b,c,d,e,f,g,h,i] = det n [b,c,a,e,f,d,h,i,g] := by
  simp [det]
  ring

theorem rotate_perm_02 (a b c d e f g h i : ℤ) :
    [c,a,b,f,d,e,i,g,h].Perm [a,b,c,d,e,f,g,h,i] := by
  have hperm : ([2, 0, 1, 5, 3, 4, 8, 6, 7] : List ℕ).Perm [0,1,2,3,4,5,6,7,8] := by decide
  simpa using hperm.map (fun k => ([a,b,c,d,e,f,g,h,i] : List ℤ).getD k 0)

theorem rotate_det_02 (n a b c d e f g h i : ℤ) :
    det n [a,b,c,d,e,f,g,h,i] = det n [c,a,b,f,d,e,i,g,h] := by
  simp [det]
  ring

theorem rotate_perm_10 (a b c d e f g h i : ℤ) :
    [d,e,f,g,h,i,a,b,c].Perm [a,b,c,d,e,f,g,h,i] := by
  have hperm : ([3, 4, 5, 6, 7, 8, 0, 1, 2] : List ℕ).Perm [0,1,2,3,4,5,6,7,8] := by decide
  simpa using hperm.map (fun k => ([a,b,c,d,e,f,g,h,i] : List ℤ).getD k 0)

theorem rotate_det_10 (n a b c d e f g h i : ℤ) :
    det n [a,b,c,d,e,f,g,h,i] = det n [d,e,f,g,h,i,a,b,c] := by
  simp [det]
  ring

theorem rotate_perm_11 (a b c d e f g h i : ℤ) :
    [e,f,d,h,i,g,b,c,a].Perm [a,b,c,d,e,f,g,h,i] := by
  have hperm : ([4, 5, 3, 7, 8, 6, 1, 2, 0] : List ℕ).Perm [0,1,2,3,4,5,6,7,8] := by decide
  simpa using hperm.map (fun k => ([a,b,c,d,e,f,g,h,i] : List ℤ).getD k 0)

theorem rotate_det_11 (n a b c d e f g h i : ℤ) :
    det n [a,b,c,d,e,f,g,h,i] = det n [e,f,d,h,i,g,b,c,a] := by
  simp [det]
  ring

theorem rotate_perm_12 (a b c d e f g h i : ℤ) :
    [f,d,e,i,g,h,c,a,b].Perm [a,b,c,d,e,f,g,h,i] := by
  have hperm : ([5, 3, 4, 8, 6, 7, 2, 0, 1] : List ℕ).Perm [0,1,2,3,4,5,6,7,8] := by decide
  simpa using hperm.map (fun k => ([a,b,c,d,e,f,g,h,i] : List ℤ).getD k 0)

theorem rotate_det_12 (n a b c d e f g h i : ℤ) :
    det n [a,b,c,d,e,f,g,h,i] = det n [f,d,e,i,g,h,c,a,b] := by
  simp [det]
  ring

theorem rotate_perm_20 (a b c d e f g h i : ℤ) :
    [g,h,i,a,b,c,d,e,f].Perm [a,b,c,d,e,f,g,h,i] := by
  have hperm : ([6, 7, 8, 0, 1, 2, 3, 4, 5] : List ℕ).Perm [0,1,2,3,4,5,6,7,8] := by decide
  simpa using hperm.map (fun k => ([a,b,c,d,e,f,g,h,i] : List ℤ).getD k 0)

theorem rotate_det_20 (n a b c d e f g h i : ℤ) :
    det n [a,b,c,d,e,f,g,h,i] = det n [g,h,i,a,b,c,d,e,f] := by
  simp [det]
  ring

theorem rotate_perm_21 (a b c d e f g h i : ℤ) :
    [h,i,g,b,c,a,e,f,d].Perm [a,b,c,d,e,f,g,h,i] := by
  have hperm : ([7, 8, 6, 1, 2, 0, 4, 5, 3] : List ℕ).Perm [0,1,2,3,4,5,6,7,8] := by decide
  simpa using hperm.map (fun k => ([a,b,c,d,e,f,g,h,i] : List ℤ).getD k 0)

theorem rotate_det_21 (n a b c d e f g h i : ℤ) :
    det n [a,b,c,d,e,f,g,h,i] = det n [h,i,g,b,c,a,e,f,d] := by
  simp [det]
  ring

theorem rotate_perm_22 (a b c d e f g h i : ℤ) :
    [i,g,h,c,a,b,f,d,e].Perm [a,b,c,d,e,f,g,h,i] := by
  have hperm : ([8, 6, 7, 2, 0, 1, 5, 3, 4] : List ℕ).Perm [0,1,2,3,4,5,6,7,8] := by decide
  simpa using hperm.map (fun k => ([a,b,c,d,e,f,g,h,i] : List ℤ).getD k 0)

theorem rotate_det_22 (n a b c d e f g h i : ℤ) :
    det n [a,b,c,d,e,f,g,h,i] = det n [i,g,h,c,a,b,f,d,e] := by
  simp [det]
  ring

theorem bounds_of_det_eq (l k : List ℤ)
    (h0 : det 0 l = det 0 k) (h1 : det 1 l = det 1 k) : bounds l = bounds k := by
  apply Bool.eq_iff_iff.mpr
  simp [bounds, slope, h0, h1]

-- Cyclic row and column permutations preserve the determinant and put -4 first.
theorem normalize_nine (a b c d e f g h i : ℤ)
    (hp : [a,b,c,d,e,f,g,h,i].Perm offsets) :
    ∃ tail, tail.Perm [-3,-2,-1,0,1,2,3,4] ∧
      bounds [a,b,c,d,e,f,g,h,i] = bounds (-4 :: tail) := by
  have hm : (-4 : ℤ) ∈ [a,b,c,d,e,f,g,h,i] := hp.mem_iff.mpr (by simp [offsets])
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with ha | hb | hc | hd | he | hf | hg | hh | hi
  · subst a
    refine ⟨[b,c,d,e,f,g,h,i], ?_, ?_⟩
    · simpa only [offsets, List.erase_cons_head] using hp.erase (-4)
    · rfl
  · subst b
    refine ⟨[c,a,e,f,d,h,i,g], ?_, ?_⟩
    · have hrot := (rotate_perm_01 a (-4) c d e f g h i).trans hp
      simpa only [offsets, List.erase_cons_head] using hrot.erase (-4)
    · exact bounds_of_det_eq _ _ (rotate_det_01 0 a (-4) c d e f g h i) (rotate_det_01 1 a (-4) c d e f g h i)
  · subst c
    refine ⟨[a,b,f,d,e,i,g,h], ?_, ?_⟩
    · have hrot := (rotate_perm_02 a b (-4) d e f g h i).trans hp
      simpa only [offsets, List.erase_cons_head] using hrot.erase (-4)
    · exact bounds_of_det_eq _ _ (rotate_det_02 0 a b (-4) d e f g h i) (rotate_det_02 1 a b (-4) d e f g h i)
  · subst d
    refine ⟨[e,f,g,h,i,a,b,c], ?_, ?_⟩
    · have hrot := (rotate_perm_10 a b c (-4) e f g h i).trans hp
      simpa only [offsets, List.erase_cons_head] using hrot.erase (-4)
    · exact bounds_of_det_eq _ _ (rotate_det_10 0 a b c (-4) e f g h i) (rotate_det_10 1 a b c (-4) e f g h i)
  · subst e
    refine ⟨[f,d,h,i,g,b,c,a], ?_, ?_⟩
    · have hrot := (rotate_perm_11 a b c d (-4) f g h i).trans hp
      simpa only [offsets, List.erase_cons_head] using hrot.erase (-4)
    · exact bounds_of_det_eq _ _ (rotate_det_11 0 a b c d (-4) f g h i) (rotate_det_11 1 a b c d (-4) f g h i)
  · subst f
    refine ⟨[d,e,i,g,h,c,a,b], ?_, ?_⟩
    · have hrot := (rotate_perm_12 a b c d e (-4) g h i).trans hp
      simpa only [offsets, List.erase_cons_head] using hrot.erase (-4)
    · exact bounds_of_det_eq _ _ (rotate_det_12 0 a b c d e (-4) g h i) (rotate_det_12 1 a b c d e (-4) g h i)
  · subst g
    refine ⟨[h,i,a,b,c,d,e,f], ?_, ?_⟩
    · have hrot := (rotate_perm_20 a b c d e f (-4) h i).trans hp
      simpa only [offsets, List.erase_cons_head] using hrot.erase (-4)
    · exact bounds_of_det_eq _ _ (rotate_det_20 0 a b c d e f (-4) h i) (rotate_det_20 1 a b c d e f (-4) h i)
  · subst h
    refine ⟨[i,g,b,c,a,e,f,d], ?_, ?_⟩
    · have hrot := (rotate_perm_21 a b c d e f g (-4) i).trans hp
      simpa only [offsets, List.erase_cons_head] using hrot.erase (-4)
    · exact bounds_of_det_eq _ _ (rotate_det_21 0 a b c d e f g (-4) i) (rotate_det_21 1 a b c d e f g (-4) i)
  · subst i
    refine ⟨[g,h,c,a,b,f,d,e], ?_, ?_⟩
    · have hrot := (rotate_perm_22 a b c d e f g h (-4)).trans hp
      simpa only [offsets, List.erase_cons_head] using hrot.erase (-4)
    · exact bounds_of_det_eq _ _ (rotate_det_22 0 a b c d e f g h (-4)) (rotate_det_22 1 a b c d e f g h (-4))

theorem normalize (l : List ℤ) (hp : l.Perm offsets) :
    ∃ tail, tail.Perm [-3,-2,-1,0,1,2,3,4] ∧ bounds l = bounds (-4 :: tail) := by
  have hlen : l.length = 9 := by simpa [offsets] using hp.length_eq
  cases l with
  | nil => simp at hlen
  | cons a l =>
    cases l with
    | nil => simp at hlen
    | cons b l =>
      cases l with
      | nil => simp at hlen
      | cons c l =>
        cases l with
        | nil => simp at hlen
        | cons d l =>
          cases l with
          | nil => simp at hlen
          | cons e l =>
            cases l with
            | nil => simp at hlen
            | cons f l =>
              cases l with
              | nil => simp at hlen
              | cons g l =>
                cases l with
                | nil => simp at hlen
                | cons h l =>
                  cases l with
                  | nil => simp at hlen
                  | cons i l =>
                    have hl : l = [] := by
                      apply List.length_eq_zero_iff.mp
                      simpa using hlen
                    subst l
                    exact normalize_nine a b c d e f g h i hp

end A097399Research

-- SubChunk00
namespace A097399Numeric
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem subchunk_0_0 : checkTree 7 [-4, -3] [-2, -1, 0, 1, 2, 3, 4] = true := by
  decide +kernel
end A097399Numeric

-- SubChunk01
namespace A097399Numeric
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem subchunk_0_1 : checkTree 7 [-4, -2] [-3, -1, 0, 1, 2, 3, 4] = true := by
  decide +kernel
end A097399Numeric

-- SubChunk02
namespace A097399Numeric
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem subchunk_0_2 : checkTree 7 [-4, -1] [-3, -2, 0, 1, 2, 3, 4] = true := by
  decide +kernel
end A097399Numeric

-- SubChunk03
namespace A097399Numeric
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem subchunk_0_3 : checkTree 7 [-4, 0] [-3, -2, -1, 1, 2, 3, 4] = true := by
  decide +kernel
end A097399Numeric

-- SubChunk04
namespace A097399Numeric
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem subchunk_0_4 : checkTree 7 [-4, 1] [-3, -2, -1, 0, 2, 3, 4] = true := by
  decide +kernel
end A097399Numeric

-- SubChunk05
namespace A097399Numeric
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem subchunk_0_5 : checkTree 7 [-4, 2] [-3, -2, -1, 0, 1, 3, 4] = true := by
  decide +kernel
end A097399Numeric

-- SubChunk06
namespace A097399Numeric
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem subchunk_0_6 : checkTree 7 [-4, 3] [-3, -2, -1, 0, 1, 2, 4] = true := by
  decide +kernel
end A097399Numeric

-- SubChunk07
namespace A097399Numeric
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem subchunk_0_7 : checkTree 7 [-4, 4] [-3, -2, -1, 0, 1, 2, 3] = true := by
  decide +kernel
end A097399Numeric

-- Chunk0
namespace A097399Numeric
theorem chunk_0 : checkTree 8 [-4] [-3, -2, -1, 0, 1, 2, 3, 4] = true := by
  change (checkTree 7 [-4, -3] [-2, -1, 0, 1, 2, 3, 4] && (checkTree 7 [-4, -2] [-3, -1, 0, 1, 2, 3, 4] && (checkTree 7 [-4, -1] [-3, -2, 0, 1, 2, 3, 4] && (checkTree 7 [-4, 0] [-3, -2, -1, 1, 2, 3, 4] && (checkTree 7 [-4, 1] [-3, -2, -1, 0, 2, 3, 4] && (checkTree 7 [-4, 2] [-3, -2, -1, 0, 1, 3, 4] && (checkTree 7 [-4, 3] [-3, -2, -1, 0, 1, 2, 4] && (checkTree 7 [-4, 4] [-3, -2, -1, 0, 1, 2, 3] && true)))))))) = true
  rw [subchunk_0_0, subchunk_0_1, subchunk_0_2, subchunk_0_3, subchunk_0_4, subchunk_0_5, subchunk_0_6, subchunk_0_7]
  rfl
end A097399Numeric

-- Certified
namespace A097399Research

theorem normalized_bounds (tail : List ℤ)
    (ht : tail.Perm [-3,-2,-1,0,1,2,3,4]) : bounds (-4 :: tail) = true := by
  have hl : tail.length = 8 := by simpa using ht.length_eq
  have hc := checkTree_sound 8 [-4] [-3,-2,-1,0,1,2,3,4] tail ht hl A097399Numeric.chunk_0
  rw [numeric_bounds_eq] at hc
  exact hc

theorem finite_certificate : Certificate := by
  apply List.all_eq_true.mpr
  intro l hl
  obtain ⟨tail, ht, heq⟩ := normalize l (List.mem_permutations.mp hl)
  rw [heq]
  exact normalized_bounds tail ht

theorem formula (n : ℕ) : a n = answer n :=
  formula_from_certificate finite_certificate n

end A097399Research

-- Series
namespace A097399Series

def answer (n : ℕ) : ℤ :=
  if n = 0 then 86 else if n = 1 then 104 else if n ≤ 12 then 80*n+12 else 81*n

set_option maxHeartbeats 2000000 in
theorem answer_series :
    PowerSeries.mk answer * (1 - PowerSeries.X)^2 =
      PowerSeries.X^13 + 12*PowerSeries.X^3 + 50*PowerSeries.X^2 -
        68*PowerSeries.X + (86 : PowerSeries ℤ) := by
  have expand (f : PowerSeries ℤ) :
      f * (1 - PowerSeries.X)^2 =
        f - (f*PowerSeries.X + f*PowerSeries.X) + (f*PowerSeries.X)*PowerSeries.X := by ring
  rw [expand]
  have c12 : (12 : PowerSeries ℤ) = PowerSeries.C 12 := by simp
  have c50 : (50 : PowerSeries ℤ) = PowerSeries.C 50 := by simp
  have c68 : (68 : PowerSeries ℤ) = PowerSeries.C 68 := by simp
  have c86 : (86 : PowerSeries ℤ) = PowerSeries.C 86 := by simp
  rw [c12, c50, c68, c86]
  apply PowerSeries.ext
  intro n
  cases n with
  | zero =>
    simp only [map_add, map_sub, PowerSeries.coeff_mk, PowerSeries.coeff_C_mul,
      PowerSeries.coeff_X_pow, PowerSeries.coeff_X, PowerSeries.coeff_C,
      PowerSeries.coeff_zero_mul_X]
    norm_num [answer]
  | succ n =>
    cases n with
    | zero =>
      simp only [map_add, map_sub, PowerSeries.coeff_mk, PowerSeries.coeff_C_mul,
        PowerSeries.coeff_X_pow, PowerSeries.coeff_C,
        PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_zero_mul_X]
      norm_num [answer]
    | succ n =>
      simp only [map_add, map_sub,
        PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_mk,
        PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, PowerSeries.coeff_C]
      unfold answer
      split_ifs <;> norm_num only [Nat.cast_add, Nat.cast_one] <;> first | contradiction | omega


theorem series_iff (f : ℕ → ℤ) :
    (PowerSeries.mk f * (1 - PowerSeries.X)^2 =
      PowerSeries.X^13 + 12*PowerSeries.X^3 + 50*PowerSeries.X^2 -
        68*PowerSeries.X + (86 : PowerSeries ℤ)) ↔ ∀ n, f n = answer n := by
  have hn : (1 - (PowerSeries.X : PowerSeries ℤ))^2 ≠ 0 := by
    intro h
    have hh := congrArg PowerSeries.constantCoeff h
    simp only [map_pow, map_sub, map_one, PowerSeries.constantCoeff_X, map_zero,
      sub_zero, one_pow, one_ne_zero] at hh
  constructor
  · intro h n
    have hh := mul_right_cancel₀ hn (h.trans answer_series.symm)
    have hc := congrArg (PowerSeries.coeff n) hh
    simpa only [PowerSeries.coeff_mk] using hc
  · intro h
    have hf : f = answer := funext h
    rw [hf]
    exact answer_series

end A097399Series

-- Bridge
namespace A097399Research

theorem generating_function :
    PowerSeries.mk a * (1 - PowerSeries.X)^2 =
      PowerSeries.X^13 + 12*PowerSeries.X^3 + 50*PowerSeries.X^2 -
        68*PowerSeries.X + (86 : PowerSeries ℤ) := by
  have h : a = A097399Series.answer := by
    funext n
    exact formula n
  rw [h]
  exact A097399Series.answer_series

end A097399Research

-- RegistrationProof
namespace OMA.S_oeis_a097399

theorem model_eq (n : ℕ) : a n = A097399Research.a n := rfl

theorem verified_main :
    PowerSeries.mk a * (1 - PowerSeries.X) ^ 2 =
      PowerSeries.X ^ 13 + 12 * PowerSeries.X ^ 3 +
        50 * PowerSeries.X ^ 2 - 68 * PowerSeries.X + (86 : PowerSeries ℤ) := by
  have h : a = A097399Research.a := funext model_eq
  rw [h]
  exact A097399Research.generating_function

end OMA.S_oeis_a097399

theorem OMA.solution : type_of% @OMA.S_oeis_a097399.main :=
  OMA.S_oeis_a097399.verified_main
