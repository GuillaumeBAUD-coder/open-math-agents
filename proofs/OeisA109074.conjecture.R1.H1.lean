import OMAReductions.R_OeisA109074_conjecture_R1

/-! # Correctness of the vertically symmetric alternating-sign matrix counter -/
-- Credit: @steveDOTdigital
namespace OMA.MatrixRows
open Finset OeisA109074
open scoped Classical

private def digit (a : Fin 3) : ℤ := a.val-1

-- Enumerate one more digit by splitting a tuple into a head and tail.
private lemma sum_cons {α β : Type*} [Fintype α] [AddCommMonoid β] (n : ℕ)
    (F : (Fin (n+1) → α) → β) :
    ∑ f, F f = ∑ t : Fin n → α, ∑ a : α, F (Fin.cons a t) := by
  rw [← (Fin.consEquiv (fun _ : Fin (n+1) => α)).sum_comp]
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  rfl

private lemma flat_sum {α β : Type*} (xs : List α) (g : α → List β) (F : β → ℕ) :
    ((xs.flatMap g).map F).sum = (xs.map (fun x => ((g x).map F).sum)).sum := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [ih]

private lemma tri_enum (n : ℕ) (F : List ℤ → ℕ) :
    ((trinaryLists n).map F).sum =
      ∑ f : Fin n → Fin 3, F (List.ofFn (fun j => digit (f j))) := by
  induction n generalizing F with
  | zero => simp [trinaryLists]
  | succ n ih =>
    rw [sum_cons n]
    have fe (f : Fin n → Fin 3) :
        (∑ a : Fin 3, F (List.ofFn (fun j => digit ((Fin.cons a f : Fin (n+1) → Fin 3) j)))) =
          F (-1 :: (List.ofFn fun j => digit (f j))) +
          F (0 :: (List.ofFn fun j => digit (f j))) +
          F (1 :: (List.ofFn fun j => digit (f j))) := by
      simp [Fin.sum_univ_succ,List.ofFn_succ,digit,add_assoc]
    simp_rw [fe]
    rw [← ih (fun l => F (-1 :: l) + F (0 :: l) + F (1 :: l))]
    rw [trinaryLists,flat_sum]
    simp [add_assoc]

-- Prefix sums along a tuple can also be read recursively, one row at a time.
private def pref {n : ℕ} (f : Fin n → ℤ) (k : ℕ) : ℤ :=
  ∑ i : Fin n, if i.val < k then f i else 0

private lemma pref_succ {n : ℕ} (f : Fin (n+1) → ℤ) (k : ℕ) :
    pref f (k+1) = f 0 + pref (fun i => f i.succ) k := by
  simp [pref,Fin.sum_univ_succ]

private lemma path_iff (n : ℕ) (f : Fin n → ℤ) (c : ℤ) :
    isAsmLineAux c (List.ofFn f) = true ↔ c + pref f n = 1 ∧
    ∀ k : Fin n, c + pref f (k.val+1) = 0 ∨ c + pref f (k.val+1) = 1 := by
  induction n generalizing c with
  | zero => simp [isAsmLineAux,pref]
  | succ n ih =>
    rw [List.ofFn_succ]
    simp only [isAsmLineAux,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq,ih,pref_succ]
    constructor
    · rintro ⟨first,last,steps⟩
      refine ⟨by omega,?_⟩
      intro k
      refine Fin.cases ?_ (fun i => ?_) k
      · simpa [pref] using first
      · have h := steps i
        simp only [Fin.val_succ]
        omega
    · rintro ⟨last,steps⟩
      have first := steps 0
      refine ⟨by simpa [pref] using first,by omega,?_⟩
      intro i
      have h := steps i.succ
      simp only [Fin.val_succ] at h
      omega

private abbrev Sym (n : ℕ) := {r : Fin (2*n+1) → Fin 3 // ∀ j, r j=r j.rev}

private def mirror {n : ℕ} (a : Fin n → Fin 3) (mid : Fin 3) (j : Fin (2*n+1)) : Fin 3 :=
  if l : j.val<n then a ⟨j.val,l⟩ else if centre : j.val=n then mid else a ⟨2*n-j.val,by have := j.isLt; omega⟩

private lemma mirror_rev {n : ℕ} (a : Fin n → Fin 3) (m : Fin 3) (j : Fin (2*n+1)) :
    mirror a m j = mirror a m j.rev := by
  have he : j.rev.val=2*n-j.val := by simp [Fin.rev]
  unfold mirror
  split_ifs <;> first | rfl | (congr 2; omega)

private def symEquiv (n : ℕ) : ((Fin n → Fin 3) × Fin 3) ≃ Sym n where
  toFun t := ⟨mirror t.1 t.2,mirror_rev t.1 t.2⟩
  invFun r := (fun j => r.val ⟨j.val,by omega⟩,r.val ⟨n,by omega⟩)
  left_inv t := by
    ext j <;> simp [mirror]
  right_inv r := by
    apply Subtype.ext
    funext j
    dsimp only
    unfold mirror
    split_ifs with lo mid
    · rfl
    · exact congrArg r.val (Fin.ext mid.symm)
    · rw [r.property j]
      exact congrArg r.val (Fin.ext (by simp [Fin.rev]))

private lemma mirror_list {n : ℕ} (a : Fin n → Fin 3) (m : Fin 3) :
    (List.ofFn fun j => digit (mirror a m j)) =
      (List.ofFn fun j => digit (a j)) ++ [digit m] ++ (List.ofFn fun j => digit (a j)).reverse := by
  apply List.ext_getElem
  · simp; omega
  · intro i hi hj
    have bound : i<2*n+1 := by simpa using hi
    rw [List.getElem_ofFn]
    by_cases lo : i<n
    · simp [mirror,lo]
    · by_cases mid : i=n
      · subst i; simp [mirror]
      · obtain ⟨t,ht⟩ : ∃ t, i-n=t+1 := ⟨i-n-1,by omega⟩
        simp [List.getElem_append,mirror,lo,mid]
        simp only [ht,List.getElem_cons_succ,List.getElem_reverse,List.getElem_ofFn,List.length_ofFn]
        apply congrArg digit
        apply congrArg a
        apply Fin.ext
        dsimp
        omega

private def word {n : ℕ} (r : Fin n → Fin 3) : List ℤ := List.ofFn (fun j => digit (r j))

private lemma row_enum (n : ℕ) (F : List ℤ → ℕ) :
    ((symAsmRows n).map F).sum =
      ∑ r : Sym n, if isAsmLine (word r.val) then F (word r.val) else 0 := by
  classical
  rw [← (symEquiv n).sum_comp,Fintype.sum_prod_type,symAsmRows,flat_sum,tri_enum]
  apply sum_congr rfl
  intro a _
  let half := word a
  let score (m : ℤ) :=
    if isAsmLine (half ++ [m] ++ half.reverse) then F (half ++ [m] ++ half.reverse) else 0
  have simplify_mid (m : Fin 3) :
      word ((symEquiv n (a,m)).val) = half ++ [digit m] ++ half.reverse :=
    mirror_list a m
  dsimp only
  simp_rw [simplify_mid]
  change (_ : ℕ) = ∑ m : Fin 3, score (digit m)
  rw [Fin.sum_univ_three]
  change ((([-1,0,1] : List ℤ).filterMap (fun m =>
    if isAsmLine (half ++ [m] ++ half.reverse) then some (half ++ [m] ++ half.reverse) else none)).map F).sum =
    score (-1) + score 0 + score 1
  simp only [List.filterMap_cons]
  split_ifs <;> simp_all [score,add_assoc]

private lemma fold_add {α : Type*} (xs : List α) (F : α → ℕ) (b : ℕ) :
    xs.foldl (fun acc x => acc + F x) b = b + (xs.map F).sum := by
  induction xs generalizing b with
  | nil => simp
  | cons a xs ih => simp [ih,add_assoc]

private lemma zip_add (n : ℕ) (a b : Fin n → ℤ) :
    List.zipWith (·+·) (List.ofFn a) (List.ofFn b) = List.ofFn (fun i => a i+b i) := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.ofFn_succ,ih]

private lemma all_ok (n : ℕ) (c : Fin n → ℤ) :
    (List.ofFn c).all (fun x => x==0 || x==1) = true ↔ ∀ j, c j=0 ∨ c j=1 := by
  simp [List.all_eq_true]

private lemma all_one (n : ℕ) (c : Fin n → ℤ) :
    (List.ofFn c).all (· == 1) = true ↔ ∀ j, c j=1 := by
  simp [List.all_eq_true]

private def accepted {n k : ℕ} (c : Fin (2*n+1) → ℤ) (s : Fin k → Sym n) : Prop :=
  (∀ i, isAsmLine (word (s i).val) = true) ∧
  ∀ j, isAsmLineAux (c j) (List.ofFn (fun i => digit ((s i).val j))) = true

private lemma accepted_cons {n k : ℕ} (c : Fin (2*n+1) → ℤ) (r : Sym n) (s : Fin k → Sym n) :
    accepted c (Fin.cons r s) ↔ isAsmLine (word r.val) = true ∧
      (∀ j, c j+digit (r.val j)=0 ∨ c j+digit (r.val j)=1) ∧
      accepted (fun j => c j + digit (r.val j)) s := by
  unfold accepted
  simp only [Fin.forall_fin_succ,Fin.cons_zero,Fin.cons_succ,List.ofFn_succ,isAsmLineAux,
    Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq]
  simp only [forall_and]
  tauto

-- A sequence of k rows has a unique first row and a unique remaining sequence.
private theorem count_sequences (n k : ℕ) (c : Fin (2*n+1) → ℤ) :
    countVsasmRows (symAsmRows n) k (List.ofFn c) =
      ∑ s : Fin k → Sym n, if accepted c s then 1 else 0 := by
  classical
  induction k generalizing c with
  | zero =>
    simp [countVsasmRows,accepted,isAsmLineAux,Fin.forall_fin_succ]
  | succ k ih =>
    let F (r : List ℤ) : ℕ :=
      let next := List.zipWith (·+·) (List.ofFn c) r
      if next.all (fun x => x==0 || x==1) then countVsasmRows (symAsmRows n) k next else 0
    have step (acc : ℕ) (r : List ℤ) :
        (let next := List.zipWith (·+·) (List.ofFn c) r
         if next.all (fun x => x==0 || x==1) then acc+countVsasmRows (symAsmRows n) k next else acc)
        = acc+F r := by dsimp [F]; split <;> simp
    calc
      _ = ((symAsmRows n).map F).sum := by
        rw [countVsasmRows]
        simp_rw [step]
        simpa using fold_add (symAsmRows n) F 0
      _ = _ := row_enum n F
      _ = ∑ r : Sym n, ∑ s : Fin k → Sym n, if accepted c (Fin.cons r s) then 1 else 0 := by
        apply sum_congr rfl
        intro r _
        simp only [F,word,zip_add,all_ok,accepted_cons]
        by_cases row : isAsmLine (List.ofFn (fun j => digit (r.val j))) = true
        · by_cases cols : ∀ j, c j+digit (r.val j)=0 ∨ c j+digit (r.val j)=1
          · simp only [row,cols,if_true,true_and]
            simpa using ih (fun j => c j+digit (r.val j))
          · simp only [row,cols,if_true,if_false,true_and,false_and,Finset.sum_const_zero]
        · simp only [row]
          simp
      _ = _ := by
        symm
        rw [sum_cons,Finset.sum_comm]

private def lineOK {w : ℕ} (r : Fin w → Fin 3) : Prop :=
  pref (fun j => digit (r j)) w = 1 ∧ ∀ k : Fin (w+1),
    pref (fun j => digit (r j)) k.val = 0 ∨ pref (fun j => digit (r j)) k.val = 1

private lemma line_iff {w : ℕ} (r : Fin w → Fin 3) :
    isAsmLine (word r) = true ↔ lineOK r := by
  rw [isAsmLine,word,path_iff]
  unfold lineOK
  simp only [zero_add,Fin.forall_fin_succ,Fin.val_zero,pref,Fin.val_succ]
  simp

private def matrixSet (n : ℕ) : Set (Fin (2*n+1) → Fin (2*n+1) → Fin 3) :=
  {M | (∀ i, lineOK (M i)) ∧ (∀ j, lineOK fun i => M i j) ∧ ∀ i j, M i j=M i j.rev}

private def toMatrix (n : ℕ) :
    {s : Fin (2*n+1) → Sym n // accepted (fun _ => 0) s} ≃ matrixSet n where
  toFun s := ⟨fun i => (s.val i).val,
    fun i => (line_iff _).mp (s.property.1 i),
    fun j => (line_iff _).mp (s.property.2 j),
    fun i j => (s.val i).property j⟩
  invFun M := ⟨fun i => ⟨M.val i,M.property.2.2 i⟩,
    fun i => (line_iff _).mpr (M.property.1 i),
    fun j => (line_iff _).mpr (M.property.2.1 j)⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem count_matrices (n : ℕ) : b n = (matrixSet n).ncard := by
  classical
  let c : Fin (2*n+1) → ℤ := fun _ => 0
  have start : List.replicate (2*n+1) (0 : ℤ) = List.ofFn c := by simp [c,List.replicate_succ]
  rw [b,start,count_sequences]
  calc
    _ = Fintype.card {s : Fin (2*n+1) → Sym n // accepted c s} := by
      rw [Fintype.card_subtype]; simp
    _ = Nat.card (matrixSet n) := by
      rw [←Nat.card_eq_fintype_card]
      exact Nat.card_congr (toMatrix n)
    _ = _ := rfl

end OMA.MatrixRows

theorem OMA.solution : OMA.R_OeisA109074_conjecture_R1.H1 := OMA.MatrixRows.count_matrices
