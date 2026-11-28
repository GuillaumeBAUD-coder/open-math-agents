import OMAReductions.R_Green75_green_75_variants_pinchasi_R1_H2_R1

section Green75PinchasiH2

open Finset Real
open scoped Classical

/-! ## Part 1: Step relation, reduction to even N, and PermSeq representation -/

private def StepRel (n d : ℕ) (u v : List (Fin n)) : Prop :=
  ∃ pre block post : List (Fin n), 2 ≤ block.length ∧ block.Pairwise (· < ·) ∧
    d ≤ ((pre.length : ℤ) - (post.length : ℤ)).natAbs ∧
    u = pre ++ block ++ post ∧ v = pre ++ block.reverse ++ post

private lemma stepRel_perm {n d : ℕ} {u v : List (Fin n)} (h : StepRel n d u v) :
    u.Perm v := by
  rcases h with ⟨pre, block, post, _, _, _, rfl, rfl⟩
  exact (List.Perm.refl pre).append (List.reverse_perm block).symm |>.append (List.Perm.refl post)

private lemma reflTransGen_perm {n d : ℕ} {u v : List (Fin n)}
    (h : Relation.ReflTransGen (StepRel n d) u v) : u.Perm v := by
  induction h with
  | refl => exact List.Perm.refl _
  | tail _ hstep ih => exact ih.trans (stepRel_perm hstep)

private lemma list_finRange_nodup (n : ℕ) : (List.finRange n).Nodup :=
  List.nodup_finRange n

private lemma filterMap_dropLast_length {m : ℕ} (l : List (Fin (m + 1))) (hnodup : l.Nodup) :
    let f : Fin (m + 1) → Option (Fin m) := fun x => if h : x.val < m then some ⟨x.val, h⟩ else none
    (l.filterMap f).length = if (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)) ∈ l then l.length - 1 else l.length := by
  intro f
  induction l with
  | nil => simp
  | cons x xs ih =>
    rw [List.nodup_cons] at hnodup
    have ih' := ih hnodup.2
    by_cases hx : x = ⟨m, Nat.lt_succ_self m⟩
    · subst hx
      have hnot : (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)) ∉ xs := hnodup.1
      simp only [List.filterMap_cons, f, lt_irrefl, ↓reduceDIte, List.mem_cons, true_or, ↓reduceIte,
        List.length_cons, Nat.add_sub_cancel]
      rw [ih', if_neg hnot]
    · have hlt : x.val < m := by
        have := x.isLt
        have hne : x.val ≠ m := fun h => hx (Fin.ext h)
        omega
      have hne' : (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)) ≠ x := fun h => hx h.symm
      simp only [List.filterMap_cons, f, hlt, ↓reduceDIte, List.length_cons, List.mem_cons, hne', false_or]
      rw [ih']
      split_ifs with hmem
      · have hpos : 1 ≤ xs.length := List.length_pos_of_mem hmem
        omega
      · rfl

private lemma filterMap_dropLast_finRange (m : ℕ) :
    let f : Fin (m + 1) → Option (Fin m) := fun x => if h : x.val < m then some ⟨x.val, h⟩ else none
    (List.finRange (m + 1)).filterMap f = List.finRange m := by
  intro f
  rw [List.finRange_succ_last]
  simp only [List.filterMap_append, List.filterMap_cons, List.filterMap_nil, f]
  have h1 : (List.finRange m |>.map Fin.castSucc).filterMap f = List.finRange m := by
    rw [List.filterMap_map]
    have : (f ∘ Fin.castSucc) = some := by
      funext x
      simp only [Function.comp_apply, f, Fin.val_castSucc, x.isLt, ↓reduceDIte]
    rw [this, List.filterMap_some]
  rw [h1]
  simp [Fin.last]

private lemma filterMap_dropLast_pairwise {m : ℕ} {l : List (Fin (m + 1))} (hp : l.Pairwise (· < ·)) :
    let f : Fin (m + 1) → Option (Fin m) := fun x => if h : x.val < m then some ⟨x.val, h⟩ else none
    (l.filterMap f).Pairwise (· < ·) := by
  intro f
  induction l with
  | nil => simp
  | cons x xs ih =>
    rw [List.pairwise_cons] at hp
    by_cases hlt : x.val < m
    · simp only [List.filterMap_cons, f, hlt, ↓reduceDIte, List.pairwise_cons]
      refine ⟨?_, ih hp.2⟩
      intro y hy
      rw [List.mem_filterMap] at hy
      rcases hy with ⟨z, hz, hfz⟩
      split_ifs at hfz with hzlt
      · cases hfz
        exact hp.1 z hz
    · simp only [List.filterMap_cons, f, hlt, ↓reduceDIte]
      exact ih hp.2

private lemma reduce_odd_to_even {m d : ℕ}
    (h : Relation.ReflTransGen (StepRel (m + 1) d) (List.finRange (m + 1)) (List.finRange (m + 1)).reverse) :
    Relation.ReflTransGen (StepRel m (d - 1)) (List.finRange m) (List.finRange m).reverse := by
  let f : Fin (m + 1) → Option (Fin m) := fun x => if h : x.val < m then some ⟨x.val, h⟩ else none
  have hgen : ∀ u v : List (Fin (m + 1)), u.Nodup →
      Relation.ReflTransGen (StepRel (m + 1) d) u v →
      Relation.ReflTransGen (StepRel m (d - 1)) (u.filterMap f) (v.filterMap f) := by
    intro u v hu hrt
    induction hrt with
    | refl => exact Relation.ReflTransGen.refl
    | @tail b c hab hbc ih =>
      have hb_nodup : b.Nodup := (reflTransGen_perm hab).nodup_iff.mp hu
      rcases hbc with ⟨pre, block, post, hlen, hpair, himb, rfl, rfl⟩
      simp only [List.filterMap_append, List.filterMap_reverse]
      by_cases hlen' : 2 ≤ (block.filterMap f).length
      · apply Relation.ReflTransGen.tail ih
        refine ⟨pre.filterMap f, block.filterMap f, post.filterMap f, hlen',
          filterMap_dropLast_pairwise hpair, ?_, by simp [List.filterMap_append], by simp [List.filterMap_append]⟩
        have hnodup_all : (pre ++ block ++ post).Nodup := hb_nodup
        have hpre_nd : pre.Nodup := (List.nodup_append.mp (List.nodup_append.mp hnodup_all).1).1
        have hpost_nd : post.Nodup := (List.nodup_append.mp hnodup_all).2.1
        have hdisj : List.Disjoint pre post := by
          intro x hx1 hx2
          have h1 := (List.nodup_append.mp hnodup_all).2.2 x (List.mem_append_left _ hx1) x hx2
          exact h1 rfl
        have hlp := filterMap_dropLast_length pre hpre_nd
        have hlq := filterMap_dropLast_length post hpost_nd
        dsimp only at hlp hlq
        rw [hlp, hlq]
        by_cases hp : (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)) ∈ pre
        · have hq : (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)) ∉ post := fun hq => hdisj hp hq
          rw [if_pos hp, if_neg hq]
          have hpos : 1 ≤ pre.length := List.length_pos_of_mem hp
          omega
        · rw [if_neg hp]
          by_cases hq : (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)) ∈ post
          · rw [if_pos hq]
            have hpos : 1 ≤ post.length := List.length_pos_of_mem hq
            omega
          · rw [if_neg hq]
            omega
      · have hrev : (block.filterMap f).reverse = block.filterMap f := by
          cases hbl : block.filterMap f with
          | nil => rfl
          | cons a tl =>
            cases tl with
            | nil => rfl
            | cons b tl' => simp [hbl] at hlen'
        rw [hrev]
        simpa only [List.filterMap_append] using ih
  have hres := hgen _ _ (list_finRange_nodup (m + 1)) h
  rw [List.filterMap_reverse, filterMap_dropLast_finRange] at hres
  exact hres

/-! ## Part 2: Indexed permutation sequence `PermSeq` -/

private structure PermSeq (N D : ℕ) where
  T : ℕ
  perm : Fin (T + 1) → Equiv.Perm (Fin N)
  hstart : perm 0 = Equiv.refl (Fin N)
  hend : perm ⟨T, Nat.lt_succ_self T⟩ = Fin.revPerm
  a : Fin T → ℕ
  k : Fin T → ℕ
  hk : ∀ t, 2 ≤ k t
  hak : ∀ t, a t + k t ≤ N
  himb : ∀ t, D ≤ ((a t : ℤ) - ((N - a t - k t : ℕ) : ℤ)).natAbs
  hinc : ∀ t (i j : Fin N), a t ≤ i.val → i.val < j.val → j.val < a t + k t →
    perm t.castSucc i < perm t.castSucc j
  hstep : ∀ t (i : Fin N),
    if h : a t ≤ i.val ∧ i.val < a t + k t then
      perm t.succ i = perm t.castSucc ⟨2 * a t + k t - 1 - i.val, by have := hak t; omega⟩
    else
      perm t.succ i = perm t.castSucc i

private lemma list_to_perm {N : ℕ} (l : List (Fin N)) (hp : l.Perm (List.finRange N)) :
    ∃ e : Equiv.Perm (Fin N), ∀ i : Fin N, l[i.val]'(by rw [hp.length_eq, List.length_finRange]; exact i.isLt) = e i := by
  have hlen : l.length = N := by rw [hp.length_eq, List.length_finRange]
  have hnd : l.Nodup := hp.nodup_iff.mpr (List.nodup_finRange N)
  let f : Fin N → Fin N := fun i => l[i.val]'(by rw [hlen]; exact i.isLt)
  have hinj : Function.Injective f := by
    intro i j hij
    have := (List.Nodup.getElem_inj_iff hnd).mp hij
    exact Fin.ext this
  exact ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj), fun i => rfl⟩

private structure PermPath (N D : ℕ) (v : List (Fin N)) where
  T : ℕ
  perm : Fin (T + 1) → Equiv.Perm (Fin N)
  hstart : perm 0 = Equiv.refl (Fin N)
  hlen : v.length = N
  hend_l : ∀ i : Fin N, v[i.val]'(by rw [hlen]; exact i.isLt) = perm ⟨T, Nat.lt_succ_self T⟩ i
  a : Fin T → ℕ
  k : Fin T → ℕ
  hk : ∀ t, 2 ≤ k t
  hak : ∀ t, a t + k t ≤ N
  himb : ∀ t, D ≤ ((a t : ℤ) - ((N - a t - k t : ℕ) : ℤ)).natAbs
  hinc : ∀ t (i j : Fin N), a t ≤ i.val → i.val < j.val → j.val < a t + k t →
    perm t.castSucc i < perm t.castSucc j
  hstep : ∀ t (i : Fin N),
    if h : a t ≤ i.val ∧ i.val < a t + k t then
      perm t.succ i = perm t.castSucc ⟨2 * a t + k t - 1 - i.val, by have := hak t; omega⟩
    else
      perm t.succ i = perm t.castSucc i

private lemma toPermSeq {N D : ℕ}
    (h : Relation.ReflTransGen (StepRel N D) (List.finRange N) (List.finRange N).reverse) :
    Nonempty (PermSeq N D) := by
  suffices hgen : ∀ v : List (Fin N),
      Relation.ReflTransGen (StepRel N D) (List.finRange N) v →
      Nonempty (PermPath N D v) by
    obtain ⟨P⟩ := hgen _ h
    refine ⟨⟨P.T, P.perm, P.hstart, ?_, P.a, P.k, P.hk, P.hak, P.himb, P.hinc, P.hstep⟩⟩
    ext i
    have := P.hend_l i
    rw [List.getElem_reverse] at this
    simp only [List.length_finRange, List.getElem_finRange] at this
    rw [← this]
    simp [Fin.val_rev]; omega
  intro v hrt
  induction hrt with
  | refl =>
    refine ⟨⟨0, fun _ => Equiv.refl (Fin N), rfl, List.length_finRange, fun i => by simp,
      Fin.elim0, Fin.elim0, fun t => t.elim0, fun t => t.elim0, fun t => t.elim0,
      fun t => t.elim0, fun t => t.elim0⟩⟩
  | @tail u v hu hstep ih =>
    obtain ⟨P⟩ := ih
    rcases hstep with ⟨pre, block, post, hblen, hpair, himb', rfl, rfl⟩
    have hlen_u : pre.length + block.length + post.length = N := by
      have := P.hlen
      simp only [List.length_append] at this
      exact this
    let a' := pre.length
    let k' := block.length
    have hak' : a' + k' ≤ N := by omega
    have hpost_eq : post.length = N - a' - k' := by omega
    let swapBlk : Equiv.Perm (Fin N) :=
      { toFun := fun i =>
          if h : a' ≤ i.val ∧ i.val < a' + k' then ⟨2 * a' + k' - 1 - i.val, by omega⟩ else i
        invFun := fun i =>
          if h : a' ≤ i.val ∧ i.val < a' + k' then ⟨2 * a' + k' - 1 - i.val, by omega⟩ else i
        left_inv := fun i => by
          dsimp only
          by_cases h1 : a' ≤ i.val ∧ i.val < a' + k'
          · rw [dif_pos h1, dif_pos (by dsimp only; omega)]
            ext; dsimp only; omega
          · rw [dif_neg h1, dif_neg h1]
        right_inv := fun i => by
          dsimp only
          by_cases h1 : a' ≤ i.val ∧ i.val < a' + k'
          · rw [dif_pos h1, dif_pos (by dsimp only; omega)]
            ext; dsimp only; omega
          · rw [dif_neg h1, dif_neg h1] }
    let perm' : Fin (P.T + 2) → Equiv.Perm (Fin N) :=
      Fin.snoc P.perm (swapBlk.trans (P.perm ⟨P.T, Nat.lt_succ_self P.T⟩))
    let a_new : Fin (P.T + 1) → ℕ := Fin.snoc P.a a'
    let k_new : Fin (P.T + 1) → ℕ := Fin.snoc P.k k'
    have hperm'_cast : ∀ t : Fin (P.T + 1), perm' t.castSucc = P.perm t := fun t => Fin.snoc_castSucc _ _ t
    have hperm'_last : perm' ⟨P.T + 1, Nat.lt_succ_self _⟩ = swapBlk.trans (P.perm ⟨P.T, Nat.lt_succ_self P.T⟩) :=
      Fin.snoc_last _ _
    have hlen_v : (pre ++ block.reverse ++ post).length = N := by
      simp only [List.length_append, List.length_reverse]; omega
    have hget_last : ∀ i : Fin N,
        (pre ++ block.reverse ++ post)[i.val]'(by rw [hlen_v]; exact i.isLt) =
        perm' ⟨P.T + 1, Nat.lt_succ_self _⟩ i := by
      intro i
      rw [hperm'_last]
      change (pre ++ block.reverse ++ post)[i.val]'(by rw [hlen_v]; exact i.isLt) =
        P.perm ⟨P.T, Nat.lt_succ_self P.T⟩ (swapBlk i)
      rw [← P.hend_l (swapBlk i)]
      dsimp only [swapBlk, Equiv.coe_fn_mk]
      split_ifs with hi
      · have h1 : i.val < (pre ++ block.reverse).length := by simp [a', k']; omega
        have h2 : ¬ i.val < pre.length := by omega
        rw [List.getElem_append_left h1, List.getElem_append_right (by omega), List.getElem_reverse]
        have h3 : 2 * a' + k' - 1 - i.val < (pre ++ block).length := by simp [a', k']; omega
        rw [List.getElem_append_left h3, List.getElem_append_right (by dsimp only [a', k']; omega)]
        congr 1; dsimp only [a', k']; omega
      · by_cases hlt : i.val < pre.length
        · have h1 : i.val < (pre ++ block.reverse).length := by simp; omega
          have h2 : i.val < (pre ++ block).length := by simp; omega
          rw [List.getElem_append_left h1, List.getElem_append_left hlt,
              List.getElem_append_left h2, List.getElem_append_left hlt]
        · have hge : pre.length + block.length ≤ i.val := by dsimp only [a', k'] at hi; omega
          have h1 : (pre ++ block.reverse).length ≤ i.val := by simp; omega
          have h2 : (pre ++ block).length ≤ i.val := by simp; omega
          rw [List.getElem_append_right h1, List.getElem_append_right h2]
          congr 1; simp
    refine ⟨⟨P.T + 1, perm', ?_, hlen_v, hget_last, a_new, k_new, ?_, ?_, ?_, ?_, ?_⟩⟩
    · change perm' (0 : Fin (P.T + 1)).castSucc = _; rw [hperm'_cast, P.hstart]
    · intro t; refine Fin.lastCases ?_ ?_ t
      · simpa [k_new] using hblen
      · intro s; simpa [k_new] using P.hk s
    · intro t; refine Fin.lastCases ?_ ?_ t
      · simpa [a_new, k_new] using hak'
      · intro s; simpa [a_new, k_new] using P.hak s
    · intro t; refine Fin.lastCases ?_ ?_ t
      · simpa [a_new, k_new, hpost_eq] using himb'
      · intro s; simpa [a_new, k_new] using P.himb s
    · intro t; refine Fin.lastCases ?_ ?_ t
      · intro i j hi hij hj
        simp only [a_new, k_new, Fin.snoc_last] at hi hj
        rw [hperm'_cast]
        change P.perm ⟨P.T, Nat.lt_succ_self P.T⟩ i < P.perm ⟨P.T, Nat.lt_succ_self P.T⟩ j
        rw [← P.hend_l i, ← P.hend_l j]
        have hi1 : i.val < (pre ++ block).length := by simp [a', k'] at *; omega
        have hj1 : j.val < (pre ++ block).length := by simp [a', k'] at *; omega
        rw [List.getElem_append_left hi1, List.getElem_append_right hi,
            List.getElem_append_left hj1, List.getElem_append_right (by omega)]
        exact List.pairwise_iff_getElem.mp hpair (i.val - pre.length) (j.val - pre.length)
          (by dsimp only [a', k'] at *; omega) (by dsimp only [a', k'] at *; omega) (by omega)
      · intro s i j hi hij hj
        simp only [a_new, k_new, Fin.snoc_castSucc] at hi hj
        rw [hperm'_cast]
        exact P.hinc s i j hi hij hj
    · intro t; refine Fin.lastCases ?_ ?_ t
      · intro i
        simp only [a_new, k_new, Fin.snoc_last]
        rw [show (Fin.last P.T).succ = ⟨P.T + 1, Nat.lt_succ_self _⟩ from rfl, hperm'_last, hperm'_cast]
        dsimp only [Equiv.trans_apply, swapBlk, Equiv.coe_fn_mk]
        split_ifs with hi <;> rfl
      · intro s i
        simp only [a_new, k_new, Fin.snoc_castSucc]
        rw [show s.castSucc.succ = s.succ.castSucc from rfl, hperm'_cast, hperm'_cast]
        exact P.hstep s i

/-! ## Part 3: Basic properties of `PermSeq` -/

private def pos {N D : ℕ} (S : PermSeq N D) (t : Fin (S.T + 1)) (x : Fin N) : Fin N :=
  (S.perm t).symm x

private lemma perm_pos {N D : ℕ} (S : PermSeq N D) (t : Fin (S.T + 1)) (x : Fin N) :
    S.perm t (pos S t x) = x := (S.perm t).apply_symm_apply x

private lemma pos_perm {N D : ℕ} (S : PermSeq N D) (t : Fin (S.T + 1)) (i : Fin N) :
    pos S t (S.perm t i) = i := (S.perm t).symm_apply_apply i

private lemma pos_zero {N D : ℕ} (S : PermSeq N D) (x : Fin N) : pos S 0 x = x := by
  simp [pos, S.hstart]

private lemma pos_last {N D : ℕ} (S : PermSeq N D) (x : Fin N) :
    pos S ⟨S.T, Nat.lt_succ_self S.T⟩ x = x.rev := by
  simp [pos, S.hend]

private def inBlock {N D : ℕ} (S : PermSeq N D) (t : Fin S.T) (x : Fin N) : Prop :=
  S.a t ≤ (pos S t.castSucc x).val ∧ (pos S t.castSucc x).val < S.a t + S.k t

private lemma pos_step {N D : ℕ} (S : PermSeq N D) (t : Fin S.T) (x : Fin N) :
    if h : inBlock S t x then
      (pos S t.succ x).val = 2 * S.a t + S.k t - 1 - (pos S t.castSucc x).val
    else
      pos S t.succ x = pos S t.castSucc x := by
  have hak := S.hak t
  split_ifs with h
  · have hidx : 2 * S.a t + S.k t - 1 - (pos S t.castSucc x).val < N := by
      rcases h with ⟨h1, h2⟩; omega
    let j : Fin N := ⟨2 * S.a t + S.k t - 1 - (pos S t.castSucc x).val, hidx⟩
    have hj_in : S.a t ≤ j.val ∧ j.val < S.a t + S.k t := by
      rcases h with ⟨h1, h2⟩; dsimp only [j]; omega
    have hst := S.hstep t j
    rw [dif_pos hj_in] at hst
    have hjeq : (⟨2 * S.a t + S.k t - 1 - j.val, by omega⟩ : Fin N) = pos S t.castSucc x := by
      ext; dsimp only [j]; rcases h with ⟨h1, h2⟩; omega
    rw [hjeq, perm_pos] at hst
    have : pos S t.succ x = j := by rw [← hst, pos_perm]
    rw [this]
  · have hst := S.hstep t (pos S t.castSucc x)
    unfold inBlock at h
    rw [dif_neg h, perm_pos] at hst
    exact (congrArg (pos S t.succ) hst).symm.trans (pos_perm S t.succ (pos S t.castSucc x))

private lemma inBlock_iff_succ {N D : ℕ} (S : PermSeq N D) (t : Fin S.T) (x : Fin N) :
    inBlock S t x ↔ S.a t ≤ (pos S t.succ x).val ∧ (pos S t.succ x).val < S.a t + S.k t := by
  have h := pos_step S t x
  split_ifs at h with hin
  · constructor
    · intro _; rcases hin with ⟨h1, h2⟩; omega
    · intro _; exact hin
  · rw [h]; rfl

private lemma order_step_lt {N D : ℕ} (S : PermSeq N D) (t : Fin S.T) {x y : Fin N}
    (hxy : x < y) :
    (pos S t.castSucc x < pos S t.castSucc y ∧ inBlock S t x ∧ inBlock S t y →
      pos S t.succ y < pos S t.succ x) ∧
    (¬ (inBlock S t x ∧ inBlock S t y) →
      (pos S t.succ x < pos S t.succ y ↔ pos S t.castSucc x < pos S t.castSucc y)) ∧
    (pos S t.castSucc y < pos S t.castSucc x → pos S t.succ y < pos S t.succ x) := by
  have hx := pos_step S t x
  have hy := pos_step S t y
  have hak := S.hak t
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨hlt, hix, hiy⟩
    rw [dif_pos hix] at hx; rw [dif_pos hiy] at hy
    change (pos S t.succ y).val < (pos S t.succ x).val
    rcases hix with ⟨hx1, hx2⟩; rcases hiy with ⟨hy1, hy2⟩
    have : (pos S t.castSucc x).val < (pos S t.castSucc y).val := hlt
    omega
  · intro hnot
    by_cases hix : inBlock S t x
    · have hiy : ¬ inBlock S t y := fun h => hnot ⟨hix, h⟩
      rw [dif_pos hix] at hx; rw [dif_neg hiy] at hy
      rw [hy]
      rcases hix with ⟨hx1, hx2⟩
      have hyout : (pos S t.castSucc y).val < S.a t ∨ S.a t + S.k t ≤ (pos S t.castSucc y).val := by
        unfold inBlock at hiy; omega
      change (pos S t.succ x).val < (pos S t.castSucc y).val ↔
        (pos S t.castSucc x).val < (pos S t.castSucc y).val
      omega
    · rw [dif_neg hix] at hx; rw [hx]
      by_cases hiy : inBlock S t y
      · rw [dif_pos hiy] at hy
        rcases hiy with ⟨hy1, hy2⟩
        have hxout : (pos S t.castSucc x).val < S.a t ∨ S.a t + S.k t ≤ (pos S t.castSucc x).val := by
          unfold inBlock at hix; omega
        change (pos S t.castSucc x).val < (pos S t.succ y).val ↔
          (pos S t.castSucc x).val < (pos S t.castSucc y).val
        omega
      · rw [dif_neg hiy] at hy; rw [hy]
  · intro hgt
    by_cases hboth : inBlock S t x ∧ inBlock S t y
    · exfalso
      have hinc := S.hinc t (pos S t.castSucc y) (pos S t.castSucc x) hboth.2.1 hgt hboth.1.2
      rw [perm_pos, perm_pos] at hinc
      exact lt_asymm hxy hinc
    · have hix := pos_step S t x
      have hiy := pos_step S t y
      by_cases hx1 : inBlock S t x
      · have hy1 : ¬ inBlock S t y := fun h => hboth ⟨hx1, h⟩
        rw [dif_pos hx1] at hix; rw [dif_neg hy1] at hiy; rw [hiy]
        rcases hx1 with ⟨hx1a, hx1b⟩
        unfold inBlock at hy1
        change (pos S t.castSucc y).val < (pos S t.succ x).val
        have : (pos S t.castSucc y).val < (pos S t.castSucc x).val := hgt
        omega
      · rw [dif_neg hx1] at hix; rw [hix]
        by_cases hy1 : inBlock S t y
        · rw [dif_pos hy1] at hiy
          rcases hy1 with ⟨hy1a, hy1b⟩
          unfold inBlock at hx1
          change (pos S t.succ y).val < (pos S t.castSucc x).val
          have : (pos S t.castSucc y).val < (pos S t.castSucc x).val := hgt
          omega
        · rw [dif_neg hy1] at hiy; rw [hiy]; exact hgt

private lemma order_mono_inv {N D : ℕ} (S : PermSeq N D) {x y : Fin N} (hxy : x < y)
    {s t : Fin (S.T + 1)} (hst : s ≤ t) (hgt : pos S s y < pos S s x) :
    pos S t y < pos S t x := by
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (show s.val ≤ t.val from hst)
  induction d generalizing t with
  | zero =>
    have : t = s := Fin.ext (by omega)
    subst this; exact hgt
  | succ d ih =>
    let t' : Fin S.T := ⟨s.val + d, by omega⟩
    have ht : t = t'.succ := Fin.ext (by simp [t']; omega)
    rw [ht]
    exact (order_step_lt S t' hxy).2.2 (ih (Fin.le_def.mpr (by simp [t'])) (by simp [t']))

private lemma order_fixed_before_block {N D : ℕ} (S : PermSeq N D) (t : Fin S.T) {x y : Fin N}
    (hx : inBlock S t x) (hy : inBlock S t y) {s₁ s₂ : Fin (S.T + 1)}
    (hs₁ : s₁ ≤ t.castSucc) (hs₂ : s₂ ≤ t.castSucc) :
    pos S s₁ x < pos S s₁ y ↔ pos S s₂ x < pos S s₂ y := by
  by_cases hxy : x = y
  · subst hxy; simp
  · rcases lt_or_gt_of_ne hxy with hlt | hgt
    · have h1 : pos S s₁ x < pos S s₁ y := by
        by_contra hc
        have hgt1 : pos S s₁ y < pos S s₁ x := lt_of_le_of_ne (not_lt.mp hc)
          (fun h => hxy ((S.perm s₁).symm.injective h.symm))
        have hgt_t := order_mono_inv S hlt hs₁ hgt1
        have hinc := S.hinc t (pos S t.castSucc y) (pos S t.castSucc x) hy.1 hgt_t hx.2
        rw [perm_pos, perm_pos] at hinc
        exact lt_asymm hlt hinc
      have h2 : pos S s₂ x < pos S s₂ y := by
        by_contra hc
        have hgt2 : pos S s₂ y < pos S s₂ x := lt_of_le_of_ne (not_lt.mp hc)
          (fun h => hxy ((S.perm s₂).symm.injective h.symm))
        have hgt_t := order_mono_inv S hlt hs₂ hgt2
        have hinc := S.hinc t (pos S t.castSucc y) (pos S t.castSucc x) hy.1 hgt_t hx.2
        rw [perm_pos, perm_pos] at hinc
        exact lt_asymm hlt hinc
      exact ⟨fun _ => h2, fun _ => h1⟩
    · have h1 : pos S s₁ y < pos S s₁ x := by
        by_contra hc
        have hgt1 : pos S s₁ x < pos S s₁ y := lt_of_le_of_ne (not_lt.mp hc)
          (fun h => hxy ((S.perm s₁).symm.injective h))
        have hgt_t := order_mono_inv S hgt hs₁ hgt1
        have hinc := S.hinc t (pos S t.castSucc x) (pos S t.castSucc y) hx.1 hgt_t hy.2
        rw [perm_pos, perm_pos] at hinc
        exact lt_asymm hgt hinc
      have h2 : pos S s₂ y < pos S s₂ x := by
        by_contra hc
        have hgt2 : pos S s₂ x < pos S s₂ y := lt_of_le_of_ne (not_lt.mp hc)
          (fun h => hxy ((S.perm s₂).symm.injective h))
        have hgt_t := order_mono_inv S hgt hs₂ hgt2
        have hinc := S.hinc t (pos S t.castSucc x) (pos S t.castSucc y) hx.1 hgt_t hy.2
        rw [perm_pos, perm_pos] at hinc
        exact lt_asymm hgt hinc
      exact ⟨fun h => absurd h (not_lt.mpr h1.le), fun h => absurd h (not_lt.mpr h2.le)⟩

private lemma order_fixed_after_block {N D : ℕ} (S : PermSeq N D) (t : Fin S.T) {x y : Fin N}
    (hx : inBlock S t x) (hy : inBlock S t y) {s₁ s₂ : Fin (S.T + 1)}
    (hs₁ : t.succ ≤ s₁) (hs₂ : t.succ ≤ s₂) :
    pos S s₁ x < pos S s₁ y ↔ pos S s₂ x < pos S s₂ y := by
  by_cases hxy : x = y
  · subst hxy; simp
  · rcases lt_or_gt_of_ne hxy with hlt | hgt
    · have hlt_t : pos S t.castSucc x < pos S t.castSucc y := by
        by_contra hc
        have hgt_t : pos S t.castSucc y < pos S t.castSucc x := lt_of_le_of_ne (not_lt.mp hc)
          (fun h => hxy ((S.perm t.castSucc).symm.injective h.symm))
        have hinc := S.hinc t (pos S t.castSucc y) (pos S t.castSucc x) hy.1 hgt_t hx.2
        rw [perm_pos, perm_pos] at hinc
        exact lt_asymm hlt hinc
      have hsucc := (order_step_lt S t hlt).1 ⟨hlt_t, hx, hy⟩
      have h1 := order_mono_inv S hlt hs₁ hsucc
      have h2 := order_mono_inv S hlt hs₂ hsucc
      exact ⟨fun h => absurd h (not_lt.mpr h1.le), fun h => absurd h (not_lt.mpr h2.le)⟩
    · have hgt_t : pos S t.castSucc y < pos S t.castSucc x := by
        by_contra hc
        have hlt_t : pos S t.castSucc x < pos S t.castSucc y := lt_of_le_of_ne (not_lt.mp hc)
          (fun h => hxy ((S.perm t.castSucc).symm.injective h))
        have hinc := S.hinc t (pos S t.castSucc x) (pos S t.castSucc y) hx.1 hlt_t hy.2
        rw [perm_pos, perm_pos] at hinc
        exact lt_asymm hgt hinc
      have hsucc := (order_step_lt S t hgt).1 ⟨hgt_t, hy, hx⟩
      have h1 := order_mono_inv S hgt hs₁ hsucc
      have h2 := order_mono_inv S hgt hs₂ hsucc
      exact ⟨fun _ => h2, fun _ => h1⟩

private lemma order_fixed_before_change {N D : ℕ} (S : PermSeq N D) {x y : Fin N}
    {t₁ t₂ : Fin (S.T + 1)} (ht : t₁ ≤ t₂)
    (hchg : (pos S t₁ x < pos S t₁ y) ↔ ¬ (pos S t₂ x < pos S t₂ y))
    {s₁ s₂ : Fin (S.T + 1)} (hs₁ : s₁ ≤ t₁) (hs₂ : s₂ ≤ t₁) :
    pos S s₁ x < pos S s₁ y ↔ pos S s₂ x < pos S s₂ y := by
  by_cases hxy : x = y
  · subst hxy; simp
  · rcases lt_or_gt_of_ne hxy with hlt | hgt
    · have h1 : pos S t₁ x < pos S t₁ y := by
        by_contra hc
        have hgt1 : pos S t₁ y < pos S t₁ x := lt_of_le_of_ne (not_lt.mp hc)
          (fun h => hxy ((S.perm t₁).symm.injective h.symm))
        have hgt2 := order_mono_inv S hlt ht hgt1
        exact (hchg.mpr (not_lt.mpr hgt2.le)) |> fun h => absurd h hc
      have hs : ∀ s : Fin (S.T + 1), s ≤ t₁ → pos S s x < pos S s y := fun s hs => by
        by_contra hc
        have hgs : pos S s y < pos S s x := lt_of_le_of_ne (not_lt.mp hc)
          (fun h => hxy ((S.perm s).symm.injective h.symm))
        exact lt_asymm h1 (order_mono_inv S hlt hs hgs)
      exact ⟨fun _ => hs s₂ hs₂, fun _ => hs s₁ hs₁⟩
    · have h1 : pos S t₁ y < pos S t₁ x := by
        by_contra hc
        have hlt1 : pos S t₁ x < pos S t₁ y := lt_of_le_of_ne (not_lt.mp hc)
          (fun h => hxy ((S.perm t₁).symm.injective h))
        have hlt2 := order_mono_inv S hgt ht hlt1
        exact (hchg.mp hlt1) hlt2
      have hs : ∀ s : Fin (S.T + 1), s ≤ t₁ → pos S s y < pos S s x := fun s hs => by
        by_contra hc
        have hgs : pos S s x < pos S s y := lt_of_le_of_ne (not_lt.mp hc)
          (fun h => hxy ((S.perm s).symm.injective h))
        exact lt_asymm h1 (order_mono_inv S hgt hs hgs)
      exact ⟨fun h => absurd h (not_lt.mpr (hs s₁ hs₁).le),
             fun h => absurd h (not_lt.mpr (hs s₂ hs₂).le)⟩

/-! ## Part 4: Reflection symmetry and geometry of central zone `Z` -/

private def reflectSeq {h w : ℕ} (S : PermSeq (2 * h) (4 * w)) : PermSeq (2 * h) (4 * w) where
  T := S.T
  perm := fun t => Fin.revPerm.trans ((S.perm t).trans Fin.revPerm)
  hstart := by ext i; simp [S.hstart]
  hend := by ext i; simp [S.hend]
  a := fun t => 2 * h - S.a t - S.k t
  k := S.k
  hk := S.hk
  hak := fun t => by have := S.hak t; omega
  himb := fun t => by
    have h1 := S.himb t
    have h2 := S.hak t
    have hsub : 2 * h - (2 * h - S.a t - S.k t) - S.k t = S.a t := by omega
    rw [hsub]
    have habs : (((2 * h - S.a t - S.k t : ℕ) : ℤ) - (S.a t : ℤ)).natAbs =
        ((S.a t : ℤ) - ((2 * h - S.a t - S.k t : ℕ) : ℤ)).natAbs := by
      rw [← Int.natAbs_neg]; congr 1; ring
    rw [habs]; exact h1
  hinc := fun t i j hi hij hj => by
    have hak := S.hak t
    have h1 := S.hinc t j.rev i.rev (by simp [Fin.val_rev]; omega)
      (by simp [Fin.val_rev]; have := j.isLt; omega) (by simp [Fin.val_rev]; omega)
    simp only [Equiv.trans_apply, Fin.revPerm_apply]
    exact Fin.rev_lt_rev.mpr h1
  hstep := fun t i => by
    have hak := S.hak t
    simp only [Equiv.trans_apply, Fin.revPerm_apply]
    split_ifs with hi
    · have hrev_in : S.a t ≤ i.rev.val ∧ i.rev.val < S.a t + S.k t := by
        simp [Fin.val_rev]; omega
      have hst := S.hstep t i.rev
      rw [dif_pos hrev_in] at hst
      rw [hst]
      congr 2; ext; simp [Fin.val_rev]; omega
    · have hrev_out : ¬ (S.a t ≤ i.rev.val ∧ i.rev.val < S.a t + S.k t) := by
        simp [Fin.val_rev]; omega
      have hst := S.hstep t i.rev
      rw [dif_neg hrev_out] at hst
      rw [hst]

private lemma pos_reflectSeq {h w : ℕ} (S : PermSeq (2 * h) (4 * w))
    (t : Fin (S.T + 1)) (x : Fin (2 * h)) :
    pos (reflectSeq S) t x = (pos S t x.rev).rev := by
  simp [pos, reflectSeq, Equiv.symm_trans_apply]

private lemma h_ge_two_w_add_one {h w : ℕ} (hw : 1 ≤ w) (hh : 1 ≤ h)
    (S : PermSeq (2 * h) (4 * w)) : 2 * w + 1 ≤ h := by
  have hT : 0 < S.T := by
    by_contra h0
    have hT0 : S.T = 0 := by omega
    have h0' := S.hstart
    have h1' := S.hend
    have heq : S.perm 0 = S.perm ⟨S.T, Nat.lt_succ_self S.T⟩ := by
      congr 1; ext; simp [hT0]
    rw [h0', h1'] at heq
    have := Equiv.ext_iff.mp heq ⟨0, by omega⟩
    simp [Fin.rev] at this
    omega
  let t0 : Fin S.T := ⟨0, hT⟩
  have himb := S.himb t0
  have hk := S.hk t0
  have hak := S.hak t0
  omega

private lemma no_move_in_Z {h w : ℕ} (S : PermSeq (2 * h) (4 * w)) (t : Fin S.T) :
    S.a t < h - 2 * w ∨ h + 2 * w < S.a t + S.k t := by
  have himb := S.himb t
  have hk := S.hk t
  have hak := S.hak t
  omega

private def isTransfer {h w : ℕ} (S : PermSeq (2 * h) (4 * w)) (t : Fin S.T) : Prop :=
  S.a t < h ∧ h < S.a t + S.k t

private lemma isTransfer_reflect {h w : ℕ} (S : PermSeq (2 * h) (4 * w)) (t : Fin S.T) :
    isTransfer (reflectSeq S) t ↔ isTransfer S t := by
  unfold isTransfer reflectSeq
  dsimp only
  have hak := S.hak t
  omega

private lemma side_preserved_of_not_transfer {h w : ℕ} (S : PermSeq (2 * h) (4 * w))
    (t : Fin S.T) (hnt : ¬ isTransfer S t) (x : Fin (2 * h)) :
    (pos S t.succ x).val < h ↔ (pos S t.castSucc x).val < h := by
  have hst := pos_step S t x
  unfold isTransfer at hnt
  split_ifs at hst with hin
  · rcases hin with ⟨h1, h2⟩
    omega
  · rw [hst]

private lemma every_label_transfers {h w : ℕ} (S : PermSeq (2 * h) (4 * w)) (x : Fin (2 * h)) :
    ∃ t : Fin S.T, isTransfer S t ∧ inBlock S t x := by
  by_contra hno
  push_neg at hno
  have hstay : ∀ t : Fin (S.T + 1), (pos S t x).val < h ↔ (pos S 0 x).val < h := by
    intro t
    induction t using Fin.induction with
    | zero => rfl
    | succ t ih =>
      rw [← ih]
      by_cases htr : isTransfer S t
      · have hnot : ¬ inBlock S t x := hno t htr
        have hst := pos_step S t x
        rw [dif_neg hnot] at hst
        rw [hst]
      · exact side_preserved_of_not_transfer S t htr x
  have hlast := hstay ⟨S.T, Nat.lt_succ_self S.T⟩
  rw [pos_zero, pos_last] at hlast
  simp [Fin.val_rev] at hlast
  have := x.isLt
  omega

/-! ## Part 5: Gap Visitor Lower Bound (Binary Potential, Section 2) -/

private def binPot {h w : ℕ} (S : PermSeq (2 * h) (4 * w)) (t : Fin (S.T + 1)) : ℕ :=
  ∑ j ∈ Finset.range (w - 1),
    if hlt : h - w + j + 1 < 2 * h then
      if S.perm t ⟨h - w + j, by omega⟩ < S.perm t ⟨h - w + j + 1, hlt⟩ then 2 ^ j else 0
    else 0

private lemma binPot_zero_of_dec {h w : ℕ} (hw : 2 ≤ w) (hh : 2 * w + 1 ≤ h)
    (S : PermSeq (2 * h) (4 * w)) (t : Fin (S.T + 1))
    (hdec : ∀ (j : ℕ) (_ : j < w - 1), S.perm t ⟨h - w + j + 1, by omega⟩ < S.perm t ⟨h - w + j, by omega⟩) :
    binPot S t = 0 := by
  unfold binPot
  apply Finset.sum_eq_zero
  intro j hj
  rw [Finset.mem_range] at hj
  have hlt : h - w + j + 1 < 2 * h := by omega
  rw [dif_pos hlt, if_neg (not_lt.mpr (hdec j hj).le)]

private lemma binPot_max_of_inc {h w : ℕ} (hw : 2 ≤ w) (hh : 2 * w + 1 ≤ h)
    (S : PermSeq (2 * h) (4 * w)) (t : Fin (S.T + 1))
    (hinc : ∀ (j : ℕ) (_ : j < w - 1), S.perm t ⟨h - w + j, by omega⟩ < S.perm t ⟨h - w + j + 1, by omega⟩) :
    binPot S t = 2 ^ (w - 1) - 1 := by
  unfold binPot
  have hterm : ∀ j ∈ Finset.range (w - 1),
      (if hlt : h - w + j + 1 < 2 * h then
        if S.perm t ⟨h - w + j, by omega⟩ < S.perm t ⟨h - w + j + 1, hlt⟩ then 2 ^ j else 0
      else 0) = 2 ^ j := by
    intro j hj
    rw [Finset.mem_range] at hj
    have hlt : h - w + j + 1 < 2 * h := by omega
    rw [dif_pos hlt, if_pos (hinc j hj)]
  rw [Finset.sum_congr rfl hterm]
  have hsum : ∀ m : ℕ, ∑ j ∈ Finset.range m, 2 ^ j = 2 ^ m - 1 := by
    intro m; induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      have : 1 ≤ 2 ^ m := Nat.one_le_pow m 2 (by omega)
      omega
  exact hsum (w - 1)

private lemma binPot_step_non_touch {h w : ℕ} (hh : 2 * w + 1 ≤ h)
    (S : PermSeq (2 * h) (4 * w)) (t : Fin S.T) (hnt : ¬ isTransfer S t)
    (hno : ¬ (S.a t ≤ h - w ∧ h - w < S.a t + S.k t)) :
    binPot S t.succ = binPot S t.castSucc := by
  have hZ := no_move_in_Z S t
  unfold isTransfer at hnt
  have hdisj : ∀ j < w, ¬ (S.a t ≤ h - w + j ∧ h - w + j < S.a t + S.k t) := by
    intro j hj
    omega
  unfold binPot
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  have hlt : h - w + j + 1 < 2 * h := by omega
  rw [dif_pos hlt, dif_pos hlt]
  have h1 := S.hstep t ⟨h - w + j, by omega⟩
  have h2 := S.hstep t ⟨h - w + j + 1, hlt⟩
  rw [dif_neg (hdisj j (by omega))] at h1
  rw [dif_neg (by simpa [add_assoc] using hdisj (j + 1) (by omega))] at h2
  rw [h1, h2]

private lemma binPot_step_touch {h w : ℕ} (hw : 2 ≤ w) (hh : 2 * w + 1 ≤ h)
    (S : PermSeq (2 * h) (4 * w)) (t : Fin S.T) (hnt : ¬ isTransfer S t)
    (htouch : S.a t ≤ h - w ∧ h - w < S.a t + S.k t) :
    binPot S t.succ ≤ binPot S t.castSucc + 1 := by
  have hZ := no_move_in_Z S t
  unfold isTransfer at hnt
  have hleft : S.a t + S.k t ≤ h := by omega
  have ha_lt : S.a t < h - 2 * w := by omega
  let m := S.a t + S.k t - (h - w)
  have hm1 : 1 ≤ m := by dsimp only [m]; omega
  have hmw : m ≤ w := by dsimp only [m]; omega
  -- Split binPot at j < m - 1, j = m - 1, j > m - 1
  have hterm_lt : ∀ (j : ℕ) (_ : j < m - 1),
      (if hlt : h - w + j + 1 < 2 * h then
        if S.perm t.castSucc ⟨h - w + j, by omega⟩ < S.perm t.castSucc ⟨h - w + j + 1, hlt⟩ then 2 ^ j else 0
      else 0) = 2 ^ j ∧
      (if hlt : h - w + j + 1 < 2 * h then
        if S.perm t.succ ⟨h - w + j, by omega⟩ < S.perm t.succ ⟨h - w + j + 1, hlt⟩ then 2 ^ j else 0
      else 0) = 0 := by
    intro j hj
    have hlt : h - w + j + 1 < 2 * h := by omega
    rw [dif_pos hlt, dif_pos hlt]
    have hinc := S.hinc t ⟨h - w + j, by omega⟩ ⟨h - w + j + 1, hlt⟩ (by simp; omega) (by simp) (by simp; dsimp only [m] at hj; omega)
    have hst1 := S.hstep t ⟨h - w + j, by omega⟩
    have hst2 := S.hstep t ⟨h - w + j + 1, hlt⟩
    rw [dif_pos (by simp; dsimp only [m] at hj; omega)] at hst1
    rw [dif_pos (by simp; dsimp only [m] at hj; omega)] at hst2
    have hdec := S.hinc t ⟨2 * S.a t + S.k t - 1 - (h - w + j + 1), by have := S.hak t; omega⟩
      ⟨2 * S.a t + S.k t - 1 - (h - w + j), by have := S.hak t; omega⟩
      (by simp; dsimp only [m] at hj; omega) (by simp; dsimp only [m] at hj; omega) (by simp; dsimp only [m] at hj; omega)
    rw [hst1, hst2, if_pos hinc, if_neg (not_lt.mpr hdec.le)]
    exact ⟨rfl, rfl⟩
  have hterm_gt : ∀ (j : ℕ) (_ : m ≤ j) (_ : j < w - 1),
      (if hlt : h - w + j + 1 < 2 * h then
        if S.perm t.succ ⟨h - w + j, by omega⟩ < S.perm t.succ ⟨h - w + j + 1, hlt⟩ then 2 ^ j else 0
      else 0) =
      (if hlt : h - w + j + 1 < 2 * h then
        if S.perm t.castSucc ⟨h - w + j, by omega⟩ < S.perm t.castSucc ⟨h - w + j + 1, hlt⟩ then 2 ^ j else 0
      else 0) := by
    intro j hj1 hj2
    have hlt : h - w + j + 1 < 2 * h := by omega
    rw [dif_pos hlt, dif_pos hlt]
    have hst1 := S.hstep t ⟨h - w + j, by omega⟩
    have hst2 := S.hstep t ⟨h - w + j + 1, hlt⟩
    rw [dif_neg (by simp; dsimp only [m] at hj1; omega)] at hst1
    rw [dif_neg (by simp; dsimp only [m] at hj1; omega)] at hst2
    rw [hst1, hst2]
  -- Sum over range (w - 1) = sum over range (m - 1) + (maybe m - 1) + sum over Ico m (w - 1)
  have hpow_sum : ∑ j ∈ Finset.range (m - 1), 2 ^ j = 2 ^ (m - 1) - 1 := by
    have hsum : ∀ q : ℕ, ∑ j ∈ Finset.range q, 2 ^ j = 2 ^ q - 1 := by
      intro q; induction q with
      | zero => simp
      | succ q ih =>
        rw [Finset.sum_range_succ, ih, pow_succ]
        have : 1 ≤ 2 ^ q := Nat.one_le_pow q 2 (by omega)
        omega
    exact hsum (m - 1)
  let f_old : ℕ → ℕ := fun j =>
    if hlt : h - w + j + 1 < 2 * h then
      if S.perm t.castSucc ⟨h - w + j, by omega⟩ < S.perm t.castSucc ⟨h - w + j + 1, hlt⟩ then 2 ^ j else 0
    else 0
  let f_new : ℕ → ℕ := fun j =>
    if hlt : h - w + j + 1 < 2 * h then
      if S.perm t.succ ⟨h - w + j, by omega⟩ < S.perm t.succ ⟨h - w + j + 1, hlt⟩ then 2 ^ j else 0
    else 0
  change ∑ j ∈ Finset.range (w - 1), f_new j ≤ ∑ j ∈ Finset.range (w - 1), f_old j + 1
  have hsum_old_lt : ∑ j ∈ Finset.range (m - 1), f_old j = 2 ^ (m - 1) - 1 := by
    rw [Finset.sum_congr rfl (fun j hj => (hterm_lt j (Finset.mem_range.mp hj)).1), hpow_sum]
  have hsum_new_lt : ∑ j ∈ Finset.range (m - 1), f_new j = 0 := by
    rw [Finset.sum_congr rfl (fun j hj => (hterm_lt j (Finset.mem_range.mp hj)).2), Finset.sum_const_zero]
  by_cases hm_eq : m = w
  · rw [show w - 1 = m - 1 by omega, hsum_new_lt, hsum_old_lt]; omega
  · have hm_lt : m - 1 < w - 1 := by omega
    have hsplit : ∀ g : ℕ → ℕ, ∑ j ∈ Finset.range (w - 1), g j =
        (∑ j ∈ Finset.range (m - 1), g j) + g (m - 1) + ∑ j ∈ Finset.Ico m (w - 1), g j := by
      intro g
      have h1 : Finset.range (w - 1) = Finset.range m ∪ Finset.Ico m (w - 1) := by
        ext x; simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ico]; omega
      have hdisj : Disjoint (Finset.range m) (Finset.Ico m (w - 1)) := by
        rw [Finset.disjoint_left]; intro x hx1 hx2
        simp only [Finset.mem_range, Finset.mem_Ico] at hx1 hx2; omega
      rw [h1, Finset.sum_union hdisj]
      congr 1
      have hm1_eq : (m - 1) + 1 = m := by omega
      conv_lhs => rw [← hm1_eq, Finset.sum_range_succ]
    rw [hsplit f_new, hsplit f_old, hsum_new_lt, hsum_old_lt]
    have htail : ∑ j ∈ Finset.Ico m (w - 1), f_new j = ∑ j ∈ Finset.Ico m (w - 1), f_old j :=
      Finset.sum_congr rfl fun j hj => hterm_gt j (Finset.mem_Ico.mp hj).1 (Finset.mem_Ico.mp hj).2
    rw [htail]
    have hf_le : f_new (m - 1) ≤ 2 ^ (m - 1) := by
      dsimp only [f_new]; split_ifs <;> simp
    have hpow_pos : 1 ≤ 2 ^ (m - 1) := Nat.one_le_pow (m - 1) 2 (by omega)
    omega

private lemma left_gap_visitors {h w : ℕ} (hw : 2 ≤ w) (hh : 2 * w + 1 ≤ h)
    (S : PermSeq (2 * h) (4 * w)) {t₀ t₁ : Fin (S.T + 1)} (ht01 : t₀ ≤ t₁)
    (hnt : ∀ t : Fin S.T, t₀.val ≤ t.val → t.val < t₁.val → ¬ isTransfer S t)
    (hdec : ∀ (j : ℕ) (_ : j < w - 1), S.perm t₀ ⟨h - w + j + 1, by omega⟩ < S.perm t₀ ⟨h - w + j, by omega⟩)
    (hinc : ∀ (j : ℕ) (_ : j < w - 1), S.perm t₁ ⟨h - w + j, by omega⟩ < S.perm t₁ ⟨h - w + j + 1, by omega⟩) :
    ∃ A : Finset (Fin (2 * h)),
      2 ^ (w - 1) ≤ A.card ∧
      (∀ x ∈ A, ∃ s : Fin (S.T + 1), t₀ ≤ s ∧ s ≤ t₁ ∧ (pos S s x).val = h - w) ∧
      (∀ x ∈ A, ∀ y ∈ A, x ≠ y →
        (pos S t₀ x < pos S t₀ y ↔ ¬ (pos S t₁ x < pos S t₁ y))) := by
  let p : Fin (2 * h) := ⟨h - w, by omega⟩
  -- Occupant of p decreases strictly at every step touching p, and stays constant otherwise
  have hocc_step : ∀ t : Fin S.T, t₀.val ≤ t.val → t.val < t₁.val →
      (S.a t ≤ h - w ∧ h - w < S.a t + S.k t → S.perm t.succ p < S.perm t.castSucc p) ∧
      (¬ (S.a t ≤ h - w ∧ h - w < S.a t + S.k t) → S.perm t.succ p = S.perm t.castSucc p) := by
    intro t ht1 ht2
    have hnt_t := hnt t ht1 ht2
    have hZ := no_move_in_Z S t
    unfold isTransfer at hnt_t
    constructor
    · intro htouch
      have ha_lt : S.a t < h - 2 * w := by omega
      have hleft : S.a t + S.k t ≤ h := by omega
      have hst := S.hstep t p
      rw [dif_pos (show S.a t ≤ p.val ∧ p.val < S.a t + S.k t from htouch)] at hst
      rw [hst]
      exact S.hinc t ⟨2 * S.a t + S.k t - 1 - p.val, by have := S.hak t; omega⟩ p
        (by dsimp only [p]; omega) (by dsimp only [p]; omega) htouch.2
    · intro hno
      have hst := S.hstep t p
      rw [dif_neg (show ¬ (S.a t ≤ p.val ∧ p.val < S.a t + S.k t) from hno)] at hst
      exact hst
  have hocc_mono : ∀ s₁ s₂ : Fin (S.T + 1), t₀ ≤ s₁ → s₁ ≤ s₂ → s₂ ≤ t₁ →
      S.perm s₂ p ≤ S.perm s₁ p := by
    intro s₁ s₂ hs1 hs12 hs2
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (show s₁.val ≤ s₂.val from hs12)
    induction d generalizing s₂ with
    | zero =>
      have : s₂ = s₁ := Fin.ext (by omega); subst this; exact le_rfl
    | succ d ih =>
      let t : Fin S.T := ⟨s₁.val + d, by omega⟩
      have hs2_eq : s₂ = t.succ := Fin.ext (by simp [t]; omega)
      have ht_ge : t₀.val ≤ t.val := by have : t₀.val ≤ s₁.val := hs1; dsimp only [t]; omega
      have ht_lt : t.val < t₁.val := by have : s₂.val ≤ t₁.val := hs2; dsimp only [t]; omega
      rw [hs2_eq]
      have hprev := ih t.castSucc (Fin.le_def.mpr (by simp [t])) (Fin.le_def.mpr (by simp [t]; omega)) (by simp [t])
      have hstep_le : S.perm t.succ p ≤ S.perm t.castSucc p := by
        have ho := hocc_step t ht_ge ht_lt
        by_cases ht : S.a t ≤ h - w ∧ h - w < S.a t + S.k t
        · exact (ho.1 ht).le
        · exact (ho.2 ht).le
      exact hstep_le.trans hprev
  -- Define A = {S.perm s p | t₀ ≤ s ≤ t₁}
  let times : Finset (Fin (S.T + 1)) := Finset.univ.filter (fun s => t₀ ≤ s ∧ s ≤ t₁)
  let A : Finset (Fin (2 * h)) := times.image (fun s => S.perm s p)
  have hcard : 2 ^ (w - 1) ≤ A.card := by
    have hind : ∀ d : ℕ, ∀ s : Fin (S.T + 1), s.val = t₀.val + d → s ≤ t₁ →
        binPot S s + 1 ≤ ((Finset.univ.filter (fun u => t₀ ≤ u ∧ u ≤ s)).image (fun u => S.perm u p)).card := by
      intro d
      induction d with
      | zero =>
        intro s hs _
        have hs0 : s = t₀ := Fin.ext (by omega)
        rw [hs0]
        rw [binPot_zero_of_dec hw hh S t₀ hdec, zero_add]
        refine Finset.card_pos.mpr ⟨S.perm t₀ p, Finset.mem_image.mpr ⟨t₀, ?_, rfl⟩⟩
        simp
      | succ d ih =>
        intro s hs hs_le
        let t : Fin S.T := ⟨t₀.val + d, by omega⟩
        have hs_eq : s = t.succ := Fin.ext (by simp [t]; omega)
        have ht_ge : t₀.val ≤ t.val := by dsimp only [t]; omega
        have ht_lt : t.val < t₁.val := by have : s.val ≤ t₁.val := hs_le; dsimp only [t]; omega
        rw [hs_eq]
        have hprev := ih t.castSucc (by simp [t]) (Fin.le_def.mpr (by simp [t]; omega))
        let imgPrev := (Finset.univ.filter (fun u => t₀ ≤ u ∧ u ≤ t.castSucc)).image (fun u => S.perm u p)
        let imgCur := (Finset.univ.filter (fun u => t₀ ≤ u ∧ u ≤ t.succ)).image (fun u => S.perm u p)
        have hsub : imgPrev ⊆ imgCur := by
          apply Finset.image_subset_image
          intro u hu
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
          exact ⟨hu.1, hu.2.trans (Fin.le_def.mpr (by simp))⟩
        have hnt_t := hnt t ht_ge ht_lt
        by_cases htouch : S.a t ≤ h - w ∧ h - w < S.a t + S.k t
        · have hpot := binPot_step_touch hw hh S t hnt_t htouch
          have hlt_new := (hocc_step t ht_ge ht_lt).1 htouch
          have hnot_mem : S.perm t.succ p ∉ imgPrev := by
            intro hmem
            rw [Finset.mem_image] at hmem
            rcases hmem with ⟨u, hu, hueq⟩
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
            have hmono := hocc_mono u t.castSucc hu.1 hu.2 (Fin.le_def.mpr (by simp [t]; omega))
            rw [hueq] at hmono
            exact not_lt.mpr hmono hlt_new
          have hmem_cur : S.perm t.succ p ∈ imgCur :=
            Finset.mem_image.mpr ⟨t.succ, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨Fin.le_def.mpr (by simp [t]; omega), le_rfl⟩, rfl⟩
          have hcard_lt : imgPrev.card + 1 ≤ imgCur.card := by
            have := Finset.card_le_card (Finset.insert_subset hmem_cur hsub)
            rw [Finset.card_insert_of_notMem hnot_mem] at this
            exact this
          change binPot S t.succ + 1 ≤ imgCur.card
          have hprev' : binPot S t.castSucc + 1 ≤ imgPrev.card := hprev
          omega
        · have hpot := binPot_step_non_touch hh S t hnt_t htouch
          have hle := Finset.card_le_card hsub
          change binPot S t.succ + 1 ≤ imgCur.card
          have hprev' : binPot S t.castSucc + 1 ≤ imgPrev.card := hprev
          omega
    have hfin := hind (t₁.val - t₀.val) t₁ (by have : t₀.val ≤ t₁.val := ht01; omega) le_rfl
    rw [binPot_max_of_inc hw hh S t₁ hinc] at hfin
    have hpow : 1 ≤ 2 ^ (w - 1) := Nat.one_le_pow (w - 1) 2 (by omega)
    change 2 ^ (w - 1) ≤ ((Finset.univ.filter (fun u => t₀ ≤ u ∧ u ≤ t₁)).image (fun u => S.perm u p)).card
    omega
  -- Stronger stay-or-leave invariant: once x leaves [h - w, h), it has pos < h - w AND S.perm s' p < x!
  have hstay_or_leave : ∀ (x : Fin (2 * h)) (s : Fin (S.T + 1)), t₀ ≤ s → s ≤ t₁ →
      h - w ≤ (pos S s x).val → (pos S s x).val < h →
      ∀ s' : Fin (S.T + 1), s ≤ s' → s' ≤ t₁ →
        pos S s' x = pos S s x ∨ ((pos S s' x).val < h - w ∧ S.perm s' p < x) := by
    intro x s hs0 hs1 hge hlt s' hs' hs'1
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (show s.val ≤ s'.val from hs')
    induction d generalizing s' with
    | zero =>
      have : s' = s := Fin.ext (by omega); subst this; exact Or.inl rfl
    | succ d ih =>
      let t : Fin S.T := ⟨s.val + d, by omega⟩
      have hs'_eq : s' = t.succ := Fin.ext (by simp [t]; omega)
      have ht_ge : t₀.val ≤ t.val := by have : t₀.val ≤ s.val := hs0; dsimp only [t]; omega
      have ht_lt : t.val < t₁.val := by have : s'.val ≤ t₁.val := hs'1; dsimp only [t]; omega
      rw [hs'_eq]
      have hnt_t := hnt t ht_ge ht_lt
      have hprev := ih t.castSucc (Fin.le_def.mpr (by simp [t])) (Fin.le_def.mpr (by simp [t]; omega)) (by simp [t])
      rcases hprev with heq | ⟨hleft_prev, hperm_lt⟩
      · have hst := pos_step S t x
        split_ifs at hst with hin
        · right
          have hZ := no_move_in_Z S t
          unfold isTransfer at hnt_t
          rcases hin with ⟨hin1, hin2⟩
          rw [heq] at hin1 hin2 hst
          have ha_lt : S.a t < h - 2 * w := by omega
          have hleft : S.a t + S.k t ≤ h := by omega
          have hp_in : S.a t ≤ p.val ∧ p.val < S.a t + S.k t := by dsimp only [p]; omega
          have hstp := S.hstep t p
          rw [dif_pos hp_in] at hstp
          have hinc_t := S.hinc t ⟨2 * S.a t + S.k t - 1 - p.val, by have := S.hak t; dsimp only [p]; omega⟩
            (pos S t.castSucc x) (by simp [p]; omega) (by rw [heq]; simp [p]; omega) (by rw [heq]; exact hin2)
          rw [← hstp, perm_pos] at hinc_t
          exact ⟨by omega, hinc_t⟩
        · left; rw [hst, heq]
      · right
        have hperm_succ : S.perm t.succ p < x :=
          lt_of_le_of_lt (hocc_mono t.castSucc t.succ (Fin.le_def.mpr (by simp [t]; omega))
            (Fin.le_def.mpr (by simp)) (Fin.le_def.mpr (by simp [t]; omega))) hperm_lt
        refine ⟨?_, hperm_succ⟩
        have hst := pos_step S t x
        split_ifs at hst with hin
        · by_contra hge'
          have hZ := no_move_in_Z S t
          unfold isTransfer at hnt_t
          rcases hin with ⟨hin1, hin2⟩
          have hleft : S.a t + S.k t ≤ h := by omega
          have hp_in : S.a t ≤ p.val ∧ p.val < S.a t + S.k t := by dsimp only [p]; omega
          have hinc_t := S.hinc t (pos S t.castSucc x) p hin1 (by dsimp only [p]; exact hleft_prev) hp_in.2
          rw [perm_pos] at hinc_t
          exact lt_asymm hperm_lt hinc_t
        · rw [hst]; exact hleft_prev
  refine ⟨A, hcard, ?_, ?_⟩
  · intro x hx
    rw [Finset.mem_image] at hx
    rcases hx with ⟨s, hs, rfl⟩
    simp only [times, Finset.mem_filter, Finset.mem_univ, true_and] at hs
    exact ⟨s, hs.1, hs.2, by rw [pos_perm]⟩
  · intro x hx y hy hne
    rw [Finset.mem_image] at hx hy
    rcases hx with ⟨sx, hsx, rfl⟩
    rcases hy with ⟨sy, hsy, rfl⟩
    simp only [times, Finset.mem_filter, Finset.mem_univ, true_and] at hsx hsy
    have hcross : ∀ (u v : Fin (S.T + 1)), t₀ ≤ u → u < v → v ≤ t₁ →
        S.perm u p ≠ S.perm v p →
        pos S u (S.perm v p) < pos S u (S.perm u p) ∧ pos S v (S.perm u p) < pos S v (S.perm v p) := by
      intro u v hu huv hv hne_uv
      have hstay_v := hstay_or_leave (S.perm v p) u hu (huv.le.trans hv)
      have hlt_v_at_u : (pos S u (S.perm v p)).val < h - w := by
        by_contra hge
        have hlt_h : (pos S u (S.perm v p)).val < h := by
          have hside : ∀ s : Fin (S.T + 1), u ≤ s → s ≤ v →
              ((pos S s (S.perm v p)).val < h ↔ (pos S u (S.perm v p)).val < h) := by
            intro s hus hsv
            obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (show u.val ≤ s.val from hus)
            induction d generalizing s with
            | zero => have : s = u := Fin.ext (by omega); subst this; rfl
            | succ d ih =>
              let t : Fin S.T := ⟨u.val + d, by omega⟩
              have hs_eq : s = t.succ := Fin.ext (by simp [t]; omega)
              have ht_ge : t₀.val ≤ t.val := by have : t₀.val ≤ u.val := hu; dsimp only [t]; omega
              have ht_lt : t.val < t₁.val := by have : s.val ≤ v.val := hsv; have : v.val ≤ t₁.val := hv; dsimp only [t]; omega
              rw [hs_eq]
              rw [side_preserved_of_not_transfer S t (hnt t ht_ge ht_lt)]
              exact ih t.castSucc (Fin.le_def.mpr (by simp [t]))
                (Fin.le_def.mpr (by have : s.val ≤ v.val := hsv; simp [t]; omega)) (by simp [t])
          exact (hside v huv.le le_rfl).mp (by rw [pos_perm]; dsimp only [p]; omega)
        rcases hstay_v (not_lt.mp hge) hlt_h v huv.le hv with heq | ⟨hlt, _⟩
        · rw [pos_perm] at heq
          exfalso; apply hne_uv
          have := congrArg (S.perm u) heq
          rw [perm_pos] at this
          exact this
        · rw [pos_perm] at hlt; omega
      have hlt_u_at_v : (pos S v (S.perm u p)).val < h - w := by
        rcases hstay_or_leave (S.perm u p) u hu (huv.le.trans hv) (by rw [pos_perm])
          (by rw [pos_perm]; dsimp only [p]; omega) v huv.le hv with heq | ⟨hlt, _⟩
        · rw [pos_perm] at heq
          exfalso; apply hne_uv
          have := congrArg (S.perm v) heq
          rw [perm_pos] at this
          exact this
        · exact hlt
      exact ⟨by rw [pos_perm]; exact hlt_v_at_u, by rw [pos_perm]; exact hlt_u_at_v⟩
    -- Now use hcross + order_mono_inv to show relative order changes between t₀ and t₁!
    have hchg_of_cross : ∀ (a b : Fin (2 * h)) (u v : Fin (S.T + 1)),
        t₀ ≤ u → u ≤ v → v ≤ t₁ → a ≠ b →
        pos S u b < pos S u a → pos S v a < pos S v b →
        (pos S t₀ a < pos S t₀ b ↔ ¬ (pos S t₁ a < pos S t₁ b)) := by
      intro a b u v hu huv hv hab h1 h2
      rcases lt_or_gt_of_ne hab with hlt | hgt
      · exfalso; exact lt_asymm h2 (order_mono_inv S hlt huv h1)
      · have ht0 : pos S t₀ b < pos S t₀ a := by
          by_contra hc
          have h' : pos S t₀ a < pos S t₀ b := lt_of_le_of_ne (not_lt.mp hc)
            (fun heq => hab ((S.perm t₀).symm.injective heq))
          exact lt_asymm h1 (order_mono_inv S hgt hu h')
        have ht1 : pos S t₁ a < pos S t₁ b := order_mono_inv S hgt hv h2
        exact ⟨fun h => absurd h (not_lt.mpr ht0.le), fun h => absurd ht1 h⟩
    rcases lt_trichotomy sx sy with hlt | rfl | hgt
    · obtain ⟨h1, h2⟩ := hcross sx sy hsx.1 hlt hsy.2 hne
      exact hchg_of_cross _ _ sx sy hsx.1 hlt.le hsy.2 hne h1 h2
    · exact absurd rfl hne
    · obtain ⟨h1, h2⟩ := hcross sy sx hsy.1 hgt hsx.2 hne.symm
      have h := hchg_of_cross _ _ sy sx hsy.1 hgt.le hsx.2 hne.symm h1 h2
      have hne0 : pos S t₀ (S.perm sx p) ≠ pos S t₀ (S.perm sy p) := fun heq => hne ((S.perm t₀).symm.injective heq)
      have hne1 : pos S t₁ (S.perm sx p) ≠ pos S t₁ (S.perm sy p) := fun heq => hne ((S.perm t₁).symm.injective heq)
      constructor
      · intro hx0 hy1
        have : ¬ pos S t₀ (S.perm sy p) < pos S t₀ (S.perm sx p) := not_lt.mpr hx0.le
        have : pos S t₁ (S.perm sy p) < pos S t₁ (S.perm sx p) := by
          by_contra hc; exact this (h.mpr hc)
        exact lt_asymm hy1 this
      · intro hnot1
        have hy1 : pos S t₁ (S.perm sy p) < pos S t₁ (S.perm sx p) :=
          lt_of_le_of_ne (not_lt.mp hnot1) hne1.symm
        have hnot0 : ¬ pos S t₀ (S.perm sy p) < pos S t₀ (S.perm sx p) := fun h0 => h.mp h0 hy1
        exact lt_of_le_of_ne (not_lt.mp hnot0) hne0

/-! ## Part 6: Choosing the side in each gap and Order Observation -/

private def onSide {h : ℕ} (side : Bool) (i : Fin (2 * h)) : Prop :=
  if side then h ≤ i.val else i.val < h

private def inBand {h : ℕ} (w : ℕ) (side : Bool) (i : Fin (2 * h)) : Prop :=
  if side then h ≤ i.val ∧ i.val < h + w else h - w ≤ i.val ∧ i.val < h

private lemma onSide_reflect {h : ℕ} (side : Bool) (i : Fin (2 * h)) :
    onSide side i.rev ↔ onSide (!side) i := by
  cases side <;> simp only [onSide, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Fin.val_rev] <;>
    have := i.isLt <;> omega

private lemma inBand_reflect {h w : ℕ} (hh : 2 * w + 1 ≤ h) (side : Bool) (i : Fin (2 * h)) :
    inBand w side i.rev ↔ inBand w (!side) i := by
  cases side <;> simp only [inBand, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Fin.val_rev] <;>
    have := i.isLt <;> omega

private lemma order_observation {h w : ℕ} (hh : 2 * w + 1 ≤ h)
    (S : PermSeq (2 * h) (4 * w)) (side : Bool)
    {t₁ t₂ : Fin (S.T + 1)} (ht : t₁ ≤ t₂)
    (W : Finset (Fin (2 * h)))
    (hstay : ∀ x ∈ W, ∀ s : Fin (S.T + 1), t₁ ≤ s → s ≤ t₂ → onSide side (pos S s x))
    (hfixed : ∀ x ∈ W, ∀ y ∈ W, ∀ s : Fin (S.T + 1), t₁ ≤ s → s ≤ t₂ →
      (pos S s x < pos S s y ↔ pos S t₁ x < pos S t₁ y))
    (hvis : ∀ x ∈ W, ∃ s : Fin (S.T + 1), t₁ ≤ s ∧ s ≤ t₂ ∧ inBand w side (pos S s x)) :
    W.card ≤ w := by
  by_cases hne : W.Nonempty
  · cases side
    · -- Left side: take x* with minimum pos at t₁
      obtain ⟨x₀, hx₀, hmin⟩ := W.exists_min_image (fun x => (pos S t₁ x).val) hne
      obtain ⟨s, hs1, hs2, hband⟩ := hvis x₀ hx₀
      simp only [inBand, Bool.false_eq_true, ↓reduceIte] at hband
      have himg : W.image (fun x => (pos S s x).val) ⊆ Finset.Ico (h - w) h := by
        intro p hp
        rw [Finset.mem_image] at hp
        rcases hp with ⟨y, hy, rfl⟩
        rw [Finset.mem_Ico]
        have hside := hstay y hy s hs1 hs2
        simp only [onSide, Bool.false_eq_true, ↓reduceIte] at hside
        refine ⟨?_, hside⟩
        by_cases heq : y = x₀
        · subst heq; exact hband.1
        · have hlt1 : pos S t₁ x₀ < pos S t₁ y :=
            lt_of_le_of_ne (hmin y hy) (fun heq' => heq ((S.perm t₁).symm.injective heq'.symm))
          have hlts : pos S s x₀ < pos S s y := (hfixed x₀ hx₀ y hy s hs1 hs2).mpr hlt1
          have : (pos S s x₀).val < (pos S s y).val := hlts
          omega
      have hinj : Set.InjOn (fun x => (pos S s x).val) (W : Set (Fin (2 * h))) := by
        intro x _ y _ hxy
        exact (S.perm s).symm.injective (Fin.ext hxy)
      calc W.card = (W.image (fun x => (pos S s x).val)).card := (Finset.card_image_of_injOn hinj).symm
        _ ≤ (Finset.Ico (h - w) h).card := Finset.card_le_card himg
        _ = w := by rw [Nat.card_Ico]; omega
    · -- Right side: take x* with maximum pos at t₁
      obtain ⟨x₀, hx₀, hmax⟩ := W.exists_max_image (fun x => (pos S t₁ x).val) hne
      obtain ⟨s, hs1, hs2, hband⟩ := hvis x₀ hx₀
      simp only [inBand, ↓reduceIte] at hband
      have himg : W.image (fun x => (pos S s x).val) ⊆ Finset.Ico h (h + w) := by
        intro p hp
        rw [Finset.mem_image] at hp
        rcases hp with ⟨y, hy, rfl⟩
        rw [Finset.mem_Ico]
        have hside := hstay y hy s hs1 hs2
        simp only [onSide, ↓reduceIte] at hside
        refine ⟨hside, ?_⟩
        by_cases heq : y = x₀
        · subst heq; exact hband.2
        · have hlt1 : pos S t₁ y < pos S t₁ x₀ :=
            lt_of_le_of_ne (hmax y hy) (fun heq' => heq ((S.perm t₁).symm.injective heq'))
          have hlts : pos S s y < pos S s x₀ := (hfixed y hy x₀ hx₀ s hs1 hs2).mpr hlt1
          have : (pos S s y).val < (pos S s x₀).val := hlts
          omega
      have hinj : Set.InjOn (fun x => (pos S s x).val) (W : Set (Fin (2 * h))) := by
        intro x _ y _ hxy
        exact (S.perm s).symm.injective (Fin.ext hxy)
      calc W.card = (W.image (fun x => (pos S s x).val)).card := (Finset.card_image_of_injOn hinj).symm
        _ ≤ (Finset.Ico h (h + w)).card := Finset.card_le_card himg
        _ = w := by rw [Nat.card_Ico]; omega
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty]; omega

private lemma gap_visitors {h w : ℕ} (hw : 2 ≤ w) (hh : 2 * w + 1 ≤ h)
    (S : PermSeq (2 * h) (4 * w))
    {tL tR : Fin S.T} (htLR : tL < tR)
    (hL : isTransfer S tL) (hR : isTransfer S tR)
    (hnt : ∀ t : Fin S.T, tL.val < t.val → t.val < tR.val → ¬ isTransfer S t) :
    ∃ (side : Bool) (A : Finset (Fin (2 * h))),
      2 ^ (w - 1) ≤ A.card ∧
      (∀ x ∈ A, ∃ s : Fin (S.T + 1), tL.succ ≤ s ∧ s ≤ tR.castSucc ∧ inBand w side (pos S s x)) ∧
      (∀ x ∈ A, ∀ y ∈ A, x ≠ y →
        (pos S tL.succ x < pos S tL.succ y ↔ ¬ (pos S tR.castSucc x < pos S tR.castSucc y))) := by
  have hle_LR : tL.succ ≤ tR.castSucc := Fin.le_def.mpr (by have : tL.val < tR.val := htLR; simp; omega)
  have hnt_sub : ∀ (u v : Fin (S.T + 1)), tL.succ ≤ u → v ≤ tR.castSucc →
      ∀ t : Fin S.T, u.val ≤ t.val → t.val < v.val → ¬ isTransfer S t := by
    intro u v hu hv t h1 h2
    exact hnt t (by have : tL.val + 1 ≤ u.val := hu; omega) (by have : v.val ≤ tR.val := hv; omega)
  -- Helper: from left_gap_visitors on [u, v] ⊆ [tL.succ, tR.castSucc], lift to the full gap
  have hlift_left : ∀ (u v : Fin (S.T + 1)), tL.succ ≤ u → u ≤ v → v ≤ tR.castSucc →
      (∀ (j : ℕ) (_ : j < w - 1), S.perm u ⟨h - w + j + 1, by omega⟩ < S.perm u ⟨h - w + j, by omega⟩) →
      (∀ (j : ℕ) (_ : j < w - 1), S.perm v ⟨h - w + j, by omega⟩ < S.perm v ⟨h - w + j + 1, by omega⟩) →
      ∃ (side : Bool) (A : Finset (Fin (2 * h))),
        2 ^ (w - 1) ≤ A.card ∧
        (∀ x ∈ A, ∃ s : Fin (S.T + 1), tL.succ ≤ s ∧ s ≤ tR.castSucc ∧ inBand w side (pos S s x)) ∧
        (∀ x ∈ A, ∀ y ∈ A, x ≠ y →
          (pos S tL.succ x < pos S tL.succ y ↔ ¬ (pos S tR.castSucc x < pos S tR.castSucc y))) := by
    intro u v hu huv hv hdec hinc
    obtain ⟨A, hcard, hvis, hchg⟩ := left_gap_visitors hw hh S huv (hnt_sub u v hu hv) hdec hinc
    refine ⟨false, A, hcard, ?_, ?_⟩
    · intro x hx
      obtain ⟨s, hs1, hs2, hpos⟩ := hvis x hx
      refine ⟨s, hu.trans hs1, hs2.trans hv, ?_⟩
      simp only [inBand, Bool.false_eq_true, ↓reduceIte]; omega
    · intro x hx y hy hne
      have huv_chg := hchg x hx y hy hne
      have hbef := order_fixed_before_change S huv huv_chg hu le_rfl
      -- Also order is fixed after v: if x < y then pos v y < pos v x → pos tR y < pos tR x
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have h_u : pos S u x < pos S u y := by
          by_contra hc
          have hgt_u : pos S u y < pos S u x := lt_of_le_of_ne (not_lt.mp hc)
            (fun h => hne ((S.perm u).symm.injective h.symm))
          have hgt_v := order_mono_inv S hlt huv hgt_u
          exact hc (huv_chg.mpr (not_lt.mpr hgt_v.le))
        have h_v : pos S v y < pos S v x := lt_of_le_of_ne (not_lt.mp (huv_chg.mp h_u))
          (fun h => hne ((S.perm v).symm.injective h.symm))
        have h_tL : pos S tL.succ x < pos S tL.succ y := hbef.mpr h_u
        have h_tR : pos S tR.castSucc y < pos S tR.castSucc x := order_mono_inv S hlt hv h_v
        exact ⟨fun _ => not_lt.mpr h_tR.le, fun _ => h_tL⟩
      · have h_u : pos S u y < pos S u x := by
          by_contra hc
          have hlt_u : pos S u x < pos S u y := lt_of_le_of_ne (not_lt.mp hc)
            (fun h => hne ((S.perm u).symm.injective h))
          have hlt_v := order_mono_inv S hgt huv hlt_u
          exact (huv_chg.mp hlt_u) hlt_v
        have h_v : pos S v x < pos S v y := by
          by_contra hc
          exact not_lt.mpr h_u.le (huv_chg.mpr hc)
        have h_tL : pos S tL.succ y < pos S tL.succ x := by
          by_contra hc
          have := lt_of_le_of_ne (not_lt.mp hc) (fun h => hne ((S.perm tL.succ).symm.injective h))
          exact lt_asymm h_u (hbef.mp this)
        have h_tR : pos S tR.castSucc x < pos S tR.castSucc y := order_mono_inv S hgt hv h_v
        exact ⟨fun h => absurd h (not_lt.mpr h_tL.le), fun h => absurd h_tR h⟩
  -- Helper: from left_gap_visitors on reflectSeq S on [u, v] ⊆ [tL.succ, tR.castSucc], lift to right side!
  have hlift_right : ∀ (u v : Fin (S.T + 1)), tL.succ ≤ u → u ≤ v → v ≤ tR.castSucc →
      (∀ (j : ℕ) (_ : j < w - 1), S.perm u ⟨h + w - 1 - j, by omega⟩ < S.perm u ⟨h + w - 2 - j, by omega⟩) →
      (∀ (j : ℕ) (_ : j < w - 1), S.perm v ⟨h + w - 2 - j, by omega⟩ < S.perm v ⟨h + w - 1 - j, by omega⟩) →
      ∃ (side : Bool) (A : Finset (Fin (2 * h))),
        2 ^ (w - 1) ≤ A.card ∧
        (∀ x ∈ A, ∃ s : Fin (S.T + 1), tL.succ ≤ s ∧ s ≤ tR.castSucc ∧ inBand w side (pos S s x)) ∧
        (∀ x ∈ A, ∀ y ∈ A, x ≠ y →
          (pos S tL.succ x < pos S tL.succ y ↔ ¬ (pos S tR.castSucc x < pos S tR.castSucc y))) := by
    intro u v hu huv hv hdec hinc
    have hnt' : ∀ t : Fin (reflectSeq S).T, u.val ≤ t.val → t.val < v.val → ¬ isTransfer (reflectSeq S) t :=
      fun t h1 h2 => (isTransfer_reflect S t).not.mpr (hnt_sub u v hu hv t h1 h2)
    have hdec' : ∀ (j : ℕ) (_ : j < w - 1), (reflectSeq S).perm u ⟨h - w + j + 1, by omega⟩ < (reflectSeq S).perm u ⟨h - w + j, by omega⟩ := by
      intro j hj
      simp only [reflectSeq, Equiv.trans_apply, Fin.revPerm_apply]
      rw [Fin.rev_lt_rev]
      have h1 : (⟨h - w + j, by omega⟩ : Fin (2 * h)).rev = ⟨h + w - 1 - j, by omega⟩ := by
        ext; simp [Fin.val_rev]; omega
      have h2 : (⟨h - w + j + 1, by omega⟩ : Fin (2 * h)).rev = ⟨h + w - 2 - j, by omega⟩ := by
        ext; simp [Fin.val_rev]; omega
      rw [h1, h2]
      exact hdec j hj
    have hinc' : ∀ (j : ℕ) (_ : j < w - 1), (reflectSeq S).perm v ⟨h - w + j, by omega⟩ < (reflectSeq S).perm v ⟨h - w + j + 1, by omega⟩ := by
      intro j hj
      simp only [reflectSeq, Equiv.trans_apply, Fin.revPerm_apply]
      rw [Fin.rev_lt_rev]
      have h1 : (⟨h - w + j, by omega⟩ : Fin (2 * h)).rev = ⟨h + w - 1 - j, by omega⟩ := by
        ext; simp [Fin.val_rev]; omega
      have h2 : (⟨h - w + j + 1, by omega⟩ : Fin (2 * h)).rev = ⟨h + w - 2 - j, by omega⟩ := by
        ext; simp [Fin.val_rev]; omega
      rw [h1, h2]
      exact hinc j hj
    obtain ⟨A', hcard', hvis', hchg'⟩ := left_gap_visitors hw hh (reflectSeq S) huv hnt' hdec' hinc'
    let A := A'.image Fin.rev
    refine ⟨true, A, ?_, ?_, ?_⟩
    · rw [Finset.card_image_of_injective _ Fin.rev_injective]; exact hcard'
    · intro x hx
      rw [Finset.mem_image] at hx
      rcases hx with ⟨x', hx', rfl⟩
      obtain ⟨s, hs1, hs2, hpos⟩ := hvis' x' hx'
      refine ⟨s, hu.trans hs1, hs2.trans hv, ?_⟩
      rw [pos_reflectSeq S s x'] at hpos
      simp only [inBand, ↓reduceIte, Fin.val_rev] at hpos ⊢
      have := (pos S s x'.rev).isLt
      omega
    · intro x hx y hy hne
      rw [Finset.mem_image] at hx hy
      rcases hx with ⟨x', hx', rfl⟩
      rcases hy with ⟨y', hy', rfl⟩
      have hne' : x' ≠ y' := fun h => hne (congrArg Fin.rev h)
      have huv_chg' := hchg' x' hx' y' hy' hne'
      rw [pos_reflectSeq, pos_reflectSeq, pos_reflectSeq, pos_reflectSeq,
          Fin.rev_lt_rev, Fin.rev_lt_rev] at huv_chg'
      -- Now lift order change between u and v to tL.succ and tR.castSucc
      have huv_chg : (pos S u x'.rev < pos S u y'.rev ↔ ¬ (pos S v x'.rev < pos S v y'.rev)) := by
        have hne_u : pos S u x'.rev ≠ pos S u y'.rev := fun h => hne ((S.perm u).symm.injective h)
        have hne_v : pos S v x'.rev ≠ pos S v y'.rev := fun h => hne ((S.perm v).symm.injective h)
        constructor
        · intro h1 h2
          exact (not_lt.mpr h1.le) (huv_chg'.mpr (not_lt.mpr h2.le))
        · intro h2
          have hv_gt : pos S v y'.rev < pos S v x'.rev := lt_of_le_of_ne (not_lt.mp h2) hne_v.symm
          have hu_not : ¬ pos S u y'.rev < pos S u x'.rev := fun h => huv_chg'.mp h hv_gt
          exact lt_of_le_of_ne (not_lt.mp hu_not) hne_u
      have hbef := order_fixed_before_change S huv huv_chg hu le_rfl
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have h_u : pos S u x'.rev < pos S u y'.rev := by
          by_contra hc
          have hgt_u : pos S u y'.rev < pos S u x'.rev := lt_of_le_of_ne (not_lt.mp hc)
            (fun h => hne ((S.perm u).symm.injective h.symm))
          have hgt_v := order_mono_inv S hlt huv hgt_u
          exact hc (huv_chg.mpr (not_lt.mpr hgt_v.le))
        have h_v : pos S v y'.rev < pos S v x'.rev := lt_of_le_of_ne (not_lt.mp (huv_chg.mp h_u))
          (fun h => hne ((S.perm v).symm.injective h.symm))
        exact ⟨fun _ => not_lt.mpr (order_mono_inv S hlt hv h_v).le, fun _ => hbef.mpr h_u⟩
      · have h_u : pos S u y'.rev < pos S u x'.rev := by
          by_contra hc
          have hlt_u : pos S u x'.rev < pos S u y'.rev := lt_of_le_of_ne (not_lt.mp hc)
            (fun h => hne ((S.perm u).symm.injective h))
          exact (huv_chg.mp hlt_u) (order_mono_inv S hgt huv hlt_u)
        have h_v : pos S v x'.rev < pos S v y'.rev := by
          by_contra hc; exact not_lt.mpr h_u.le (huv_chg.mpr hc)
        have h_tL : pos S tL.succ y'.rev < pos S tL.succ x'.rev := by
          by_contra hc
          exact lt_asymm h_u (hbef.mp (lt_of_le_of_ne (not_lt.mp hc) (fun h => hne ((S.perm tL.succ).symm.injective h))))
        exact ⟨fun h => absurd h (not_lt.mpr h_tL.le), fun h => absurd (order_mono_inv S hgt hv h_v) h⟩
  -- Helper: a flip covering [h-w, h) makes it increasing before and decreasing after
  have hcov_L_inc : ∀ t : Fin S.T, S.a t ≤ h - w → h ≤ S.a t + S.k t →
      ∀ (j : ℕ) (_ : j < w - 1), S.perm t.castSucc ⟨h - w + j, by omega⟩ < S.perm t.castSucc ⟨h - w + j + 1, by omega⟩ := by
    intro t ha hk j hj
    exact S.hinc t ⟨h - w + j, by omega⟩ ⟨h - w + j + 1, by omega⟩ (by simp; omega) (by simp) (by simp; omega)
  have hcov_L_dec : ∀ t : Fin S.T, S.a t ≤ h - w → h ≤ S.a t + S.k t →
      ∀ (j : ℕ) (_ : j < w - 1), S.perm t.succ ⟨h - w + j + 1, by omega⟩ < S.perm t.succ ⟨h - w + j, by omega⟩ := by
    intro t ha hk j hj
    have h1 := S.hstep t ⟨h - w + j, by omega⟩
    have h2 := S.hstep t ⟨h - w + j + 1, by omega⟩
    rw [dif_pos (by simp; omega)] at h1; rw [dif_pos (by simp; omega)] at h2
    rw [h1, h2]
    exact S.hinc t ⟨2 * S.a t + S.k t - 1 - (h - w + j + 1), by have := S.hak t; omega⟩
      ⟨2 * S.a t + S.k t - 1 - (h - w + j), by have := S.hak t; omega⟩ (by simp; omega) (by simp; omega) (by simp; omega)
  have hcov_R_inc : ∀ t : Fin S.T, S.a t ≤ h → h + w ≤ S.a t + S.k t →
      ∀ (j : ℕ) (_ : j < w - 1), S.perm t.castSucc ⟨h + w - 2 - j, by omega⟩ < S.perm t.castSucc ⟨h + w - 1 - j, by omega⟩ := by
    intro t ha hk j hj
    exact S.hinc t ⟨h + w - 2 - j, by omega⟩ ⟨h + w - 1 - j, by omega⟩ (by simp; omega) (by simp; omega) (by simp; omega)
  have hcov_R_dec : ∀ t : Fin S.T, S.a t ≤ h → h + w ≤ S.a t + S.k t →
      ∀ (j : ℕ) (_ : j < w - 1), S.perm t.succ ⟨h + w - 1 - j, by omega⟩ < S.perm t.succ ⟨h + w - 2 - j, by omega⟩ := by
    intro t ha hk j hj
    have h1 := S.hstep t ⟨h + w - 2 - j, by omega⟩
    have h2 := S.hstep t ⟨h + w - 1 - j, by omega⟩
    rw [dif_pos (by simp; omega)] at h1; rw [dif_pos (by simp; omega)] at h2
    rw [h1, h2]
    exact S.hinc t ⟨2 * S.a t + S.k t - 1 - (h + w - 1 - j), by have := S.hak t; omega⟩
      ⟨2 * S.a t + S.k t - 1 - (h + w - 2 - j), by have := S.hak t; omega⟩ (by simp; omega) (by simp; omega) (by simp; omega)
  -- At tL.succ, perm tL.succ (h-1) > perm tL.succ h; at tR.castSucc, perm tR.castSucc (h-1) < perm tR.castSucc h
  have hcut_L : S.perm tL.succ ⟨h, by omega⟩ < S.perm tL.succ ⟨h - 1, by omega⟩ := by
    have h1 := S.hstep tL ⟨h - 1, by omega⟩
    have h2 := S.hstep tL ⟨h, by omega⟩
    have hL' : S.a tL < h ∧ h < S.a tL + S.k tL := hL
    have hakL := S.hak tL
    rw [dif_pos (by simp; omega)] at h1
    rw [dif_pos (by simp; omega)] at h2
    rw [h1, h2]
    exact S.hinc tL ⟨2 * S.a tL + S.k tL - 1 - h, by omega⟩
      ⟨2 * S.a tL + S.k tL - 1 - (h - 1), by omega⟩
      (by simp; omega) (by simp; omega) (by simp; omega)
  have hcut_R : S.perm tR.castSucc ⟨h - 1, by omega⟩ < S.perm tR.castSucc ⟨h, by omega⟩ :=
    S.hinc tR ⟨h - 1, by omega⟩ ⟨h, by omega⟩ (by unfold isTransfer at hR; simp; omega) (by simp; omega) (by unfold isTransfer at hR; simp; omega)
  -- Case split on which side tL and tR cover
  have hZL := no_move_in_Z S tL
  have hZR := no_move_in_Z S tR
  rcases hZL with hLL | hLR
  · rcases hZR with hRL | hRR
    · -- Both cover Left!
      exact hlift_left tL.succ tR.castSucc le_rfl hle_LR le_rfl
        (hcov_L_dec tL (by omega) (by unfold isTransfer at hL; omega))
        (hcov_L_inc tR (by omega) (by unfold isTransfer at hR; omega))
    · -- tL covers Left, tR covers Right
      by_cases htouchL : ∃ t : Fin S.T, tL.val < t.val ∧ t.val < tR.val ∧
          S.a t ≤ h - 1 ∧ h - 1 < S.a t + S.k t
      · rcases htouchL with ⟨t, ht1, ht2, hta, htk⟩
        have hnt_t := hnt t ht1 ht2
        have hZt := no_move_in_Z S t
        unfold isTransfer at hnt_t
        exact hlift_left tL.succ t.castSucc le_rfl (Fin.le_def.mpr (by simp; omega)) (Fin.le_def.mpr (by simp; omega))
          (hcov_L_dec tL (by omega) (by unfold isTransfer at hL; omega))
          (hcov_L_inc t (by omega) (by omega))
      · push_neg at htouchL
        -- h - 1 is never touched in the gap, so h MUST be touched in the gap!
        have htouchR : ∃ t : Fin S.T, tL.val < t.val ∧ t.val < tR.val ∧
            S.a t ≤ h ∧ h < S.a t + S.k t := by
          by_contra hnoR
          push_neg at hnoR
          have hconst : ∀ s : Fin (S.T + 1), tL.succ ≤ s → s ≤ tR.castSucc →
              S.perm s ⟨h - 1, by omega⟩ = S.perm tL.succ ⟨h - 1, by omega⟩ ∧
              S.perm s ⟨h, by omega⟩ = S.perm tL.succ ⟨h, by omega⟩ := by
            intro s hs1 hs2
            obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (show tL.succ.val ≤ s.val from hs1)
            induction d generalizing s with
            | zero => have : s = tL.succ := Fin.ext (by omega); subst this; exact ⟨rfl, rfl⟩
            | succ d ih =>
              have hs_le : s.val ≤ tR.val := hs2
              have htR_lt := tR.isLt
              have hhd : s.val = tL.val + 1 + (d + 1) := by simpa [Fin.val_succ] using hd
              let t : Fin S.T := ⟨tL.succ.val + d, by simp [Fin.val_succ]; omega⟩
              have hs_eq : s = t.succ := Fin.ext (by simp [t, Fin.val_succ]; omega)
              have ht1 : tL.val < t.val := by dsimp only [t]; simp [Fin.val_succ]; omega
              have ht2 : t.val < tR.val := by dsimp only [t]; simp [Fin.val_succ]; omega
              rw [hs_eq]
              have hprev := ih t.castSucc (Fin.le_def.mpr (by simp [t]))
                (Fin.le_def.mpr (by simp [t]; omega)) (by simp [t])
              have h1 := S.hstep t ⟨h - 1, by omega⟩
              rw [dif_neg (fun hc => not_lt.mpr (htouchL t ht1 ht2 hc.1) hc.2)] at h1
              have h2 := S.hstep t ⟨h, by omega⟩
              rw [dif_neg (fun hc => not_lt.mpr (hnoR t ht1 ht2 hc.1) hc.2)] at h2
              exact ⟨h1.trans hprev.1, h2.trans hprev.2⟩
          obtain ⟨heq1, heq2⟩ := hconst tR.castSucc hle_LR le_rfl
          rw [heq1, heq2] at hcut_R
          exact lt_asymm hcut_L hcut_R
        rcases htouchR with ⟨t, ht1, ht2, hta, htk⟩
        have hnt_t := hnt t ht1 ht2
        have hZt := no_move_in_Z S t
        unfold isTransfer at hnt_t
        exact hlift_right t.succ tR.castSucc (Fin.le_def.mpr (by simp; omega))
          (Fin.le_def.mpr (by simp; omega)) le_rfl
          (hcov_R_dec t (by omega) (by omega))
          (hcov_R_inc tR (by unfold isTransfer at hR; omega) (by omega))
  · rcases hZR with hRL | hRR
    · -- tL covers Right, tR covers Left
      by_cases htouchR : ∃ t : Fin S.T, tL.val < t.val ∧ t.val < tR.val ∧
          S.a t ≤ h ∧ h < S.a t + S.k t
      · rcases htouchR with ⟨t, ht1, ht2, hta, htk⟩
        have hnt_t := hnt t ht1 ht2
        have hZt := no_move_in_Z S t
        unfold isTransfer at hnt_t
        exact hlift_right tL.succ t.castSucc le_rfl (Fin.le_def.mpr (by simp; omega)) (Fin.le_def.mpr (by simp; omega))
          (hcov_R_dec tL (by unfold isTransfer at hL; omega) (by omega))
          (hcov_R_inc t (by omega) (by omega))
      · push_neg at htouchR
        have htouchL : ∃ t : Fin S.T, tL.val < t.val ∧ t.val < tR.val ∧
            S.a t ≤ h - 1 ∧ h - 1 < S.a t + S.k t := by
          by_contra hnoL
          push_neg at hnoL
          have hconst : ∀ s : Fin (S.T + 1), tL.succ ≤ s → s ≤ tR.castSucc →
              S.perm s ⟨h - 1, by omega⟩ = S.perm tL.succ ⟨h - 1, by omega⟩ ∧
              S.perm s ⟨h, by omega⟩ = S.perm tL.succ ⟨h, by omega⟩ := by
            intro s hs1 hs2
            obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (show tL.succ.val ≤ s.val from hs1)
            induction d generalizing s with
            | zero => have : s = tL.succ := Fin.ext (by omega); subst this; exact ⟨rfl, rfl⟩
            | succ d ih =>
              have hs_le : s.val ≤ tR.val := hs2
              have htR_lt := tR.isLt
              have hhd : s.val = tL.val + 1 + (d + 1) := by simpa [Fin.val_succ] using hd
              let t : Fin S.T := ⟨tL.succ.val + d, by simp [Fin.val_succ]; omega⟩
              have hs_eq : s = t.succ := Fin.ext (by simp [t, Fin.val_succ]; omega)
              have ht1 : tL.val < t.val := by dsimp only [t]; simp [Fin.val_succ]; omega
              have ht2 : t.val < tR.val := by dsimp only [t]; simp [Fin.val_succ]; omega
              rw [hs_eq]
              have hprev := ih t.castSucc (Fin.le_def.mpr (by simp [t]))
                (Fin.le_def.mpr (by simp [t]; omega)) (by simp [t])
              have h1 := S.hstep t ⟨h - 1, by omega⟩
              rw [dif_neg (fun hc => not_lt.mpr (hnoL t ht1 ht2 hc.1) hc.2)] at h1
              have h2 := S.hstep t ⟨h, by omega⟩
              rw [dif_neg (fun hc => not_lt.mpr (htouchR t ht1 ht2 hc.1) hc.2)] at h2
              exact ⟨h1.trans hprev.1, h2.trans hprev.2⟩
          obtain ⟨heq1, heq2⟩ := hconst tR.castSucc hle_LR le_rfl
          rw [heq1, heq2] at hcut_R
          exact lt_asymm hcut_L hcut_R
        rcases htouchL with ⟨t, ht1, ht2, hta, htk⟩
        have hnt_t := hnt t ht1 ht2
        have hZt := no_move_in_Z S t
        unfold isTransfer at hnt_t
        exact hlift_left t.succ tR.castSucc (Fin.le_def.mpr (by simp; omega))
          (Fin.le_def.mpr (by simp; omega)) le_rfl
          (hcov_L_dec t (by omega) (by omega))
          (hcov_L_inc tR (by omega) (by unfold isTransfer at hR; omega))
    · -- Both cover Right!
      exact hlift_right tL.succ tR.castSucc le_rfl hle_LR le_rfl
        (hcov_R_dec tL (by unfold isTransfer at hL; omega) (by omega))
        (hcov_R_inc tR (by unfold isTransfer at hR; omega) (by omega))

/-! ## Part 7: Dyadic Interval Counting (Section 3) -/

private lemma card_update_identity {α : Type*} [DecidableEq α] (U V B : Finset α) :
    V.card + U.card = ((U ∪ V) \ B).card + (U ∩ V).card + ((U ∪ V) ∩ B).card := by
  have h1 := Finset.card_union_add_card_inter U V
  have h2 := Finset.card_sdiff_add_card_inter (U ∪ V) B
  omega

private lemma discrete_bound {h w : ℕ} (hw : 4 ≤ w) (hh : 2 * w + 1 ≤ h)
    (S : PermSeq (2 * h) (4 * w)) :
    ∃ r : ℕ, 2 ≤ r ∧ r < (2 * h) ^ 2 ∧ 2 ^ (w - 1) ≤ 8 * w + 24 * w * Nat.clog 2 r := by
  classical
  let trSet : Finset (Fin S.T) := Finset.univ.filter (fun t => isTransfer S t)
  let r : ℕ := trSet.card
  let T_idx : Fin r ≃o trSet := trSet.orderIsoOfFin rfl
  let τ : Fin r → Fin S.T := fun i => (T_idx i).1
  have hτ_tr : ∀ i : Fin r, isTransfer S (τ i) := fun i => (Finset.mem_filter.mp (T_idx i).2).2
  have hτ_mono : StrictMono τ := fun i j hij => T_idx.strictMono hij
  have hτ_all : ∀ t : Fin S.T, isTransfer S t → ∃ i : Fin r, τ i = t := by
    intro t ht
    have hmem : t ∈ trSet := Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩
    exact ⟨T_idx.symm ⟨t, hmem⟩, by simp [τ]⟩
  have hτ_gap : ∀ (i : Fin r) (hi : 0 < i.val) (t : Fin S.T),
      (τ ⟨i.val - 1, by omega⟩).val < t.val → t.val < (τ i).val → ¬ isTransfer S t := by
    intro i hi t h1 h2 htr
    obtain ⟨j, rfl⟩ := hτ_all t htr
    have hj1 : (⟨i.val - 1, by omega⟩ : Fin r) < j := hτ_mono.lt_iff_lt.mp h1
    have hj2 : j < i := hτ_mono.lt_iff_lt.mp h2
    have : i.val - 1 < j.val := hj1
    have : j.val < i.val := hj2
    omega
  -- Prove r < (2 * h)^2 via injective cut-pair map
  have hr_lt : r < (2 * h) ^ 2 := by
    let cutPair : Fin r → Fin (2 * h) × Fin (2 * h) := fun i =>
      (S.perm (τ i).castSucc ⟨h - 1, by omega⟩, S.perm (τ i).castSucc ⟨h, by omega⟩)
    have hinj : Function.Injective cutPair := by
      intro i j hij
      by_contra hne
      have hpair_eq : S.perm (τ i).castSucc ⟨h - 1, by omega⟩ = S.perm (τ j).castSucc ⟨h - 1, by omega⟩ ∧
          S.perm (τ i).castSucc ⟨h, by omega⟩ = S.perm (τ j).castSucc ⟨h, by omega⟩ := Prod.mk.inj hij
      let x := S.perm (τ i).castSucc ⟨h - 1, by omega⟩
      let y := S.perm (τ i).castSucc ⟨h, by omega⟩
      have hxy : x < y := S.hinc (τ i) ⟨h - 1, by omega⟩ ⟨h, by omega⟩ (by have := hτ_tr i; unfold isTransfer at this; simp; omega)
        (by simp; omega) (by have := hτ_tr i; unfold isTransfer at this; simp; omega)
      have hx_i : inBlock S (τ i) x := by
        unfold inBlock; rw [pos_perm]; have := hτ_tr i; unfold isTransfer at this; simp; omega
      have hy_i : inBlock S (τ i) y := by
        unfold inBlock; rw [pos_perm]; have := hτ_tr i; unfold isTransfer at this; simp; omega
      have hx_j : inBlock S (τ j) x := by
        unfold inBlock; dsimp only [x]; rw [hpair_eq.1, pos_perm]; have := hτ_tr j; unfold isTransfer at this; simp; omega
      have hy_j : inBlock S (τ j) y := by
        unfold inBlock; dsimp only [y]; rw [hpair_eq.2, pos_perm]; have := hτ_tr j; unfold isTransfer at this; simp; omega
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hsucc_le : (τ i).succ ≤ (τ j).castSucc := Fin.le_def.mpr (by have : (τ i).val < (τ j).val := hτ_mono hlt; simp; omega)
        have hord := (order_step_lt S (τ i) hxy).1 ⟨by dsimp only [x, y]; rw [pos_perm, pos_perm]; simp; omega, hx_i, hy_i⟩
        have hgt_j := order_mono_inv S hxy hsucc_le hord
        have hlt_j : pos S (τ j).castSucc x < pos S (τ j).castSucc y := by
          dsimp only [x, y]; rw [hpair_eq.1, hpair_eq.2, pos_perm, pos_perm]; simp; omega
        exact lt_asymm hlt_j hgt_j
      · have hsucc_le : (τ j).succ ≤ (τ i).castSucc := Fin.le_def.mpr (by have : (τ j).val < (τ i).val := hτ_mono hgt; simp; omega)
        have hord := (order_step_lt S (τ j) hxy).1 ⟨by dsimp only [x, y]; rw [hpair_eq.1, hpair_eq.2, pos_perm, pos_perm]; simp; omega, hx_j, hy_j⟩
        have hgt_i := order_mono_inv S hxy hsucc_le hord
        have hlt_i : pos S (τ i).castSucc x < pos S (τ i).castSucc y := by
          dsimp only [x, y]; rw [pos_perm, pos_perm]; simp; omega
        exact lt_asymm hlt_i hgt_i
    have hdiag : (⟨0, by omega⟩, ⟨0, by omega⟩) ∉ Finset.univ.image cutPair := by
      intro hm
      rw [Finset.mem_image] at hm
      rcases hm with ⟨i, _, hi⟩
      have h1 := (Prod.mk.inj hi).1
      have h2 := (Prod.mk.inj hi).2
      have hlt := S.hinc (τ i) ⟨h - 1, by omega⟩ ⟨h, by omega⟩ (by have := hτ_tr i; unfold isTransfer at this; simp; omega)
        (by simp; omega) (by have := hτ_tr i; unfold isTransfer at this; simp; omega)
      rw [h1, h2] at hlt
      exact lt_irrefl _ hlt
    have hsub : (Finset.univ.image cutPair) ⊂ (Finset.univ : Finset (Fin (2 * h) × Fin (2 * h))) :=
      Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, fun heq => hdiag (heq ▸ Finset.mem_univ _)⟩
    have hlt := Finset.card_lt_card hsub
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin,
        Finset.card_univ, Fintype.card_prod, Fintype.card_fin, ← sq] at hlt
    exact hlt
  -- Prove 2 ≤ r
  have hr_ge2 : 2 ≤ r := by
    by_contra hlt2
    have h1 : r ≤ 1 := by omega
    by_cases hr0 : r = 0
    · obtain ⟨t, htr, _⟩ := every_label_transfers S ⟨0, by omega⟩
      obtain ⟨i, _⟩ := hτ_all t htr
      have := i.isLt
      omega
    · have hr1 : r = 1 := by omega
      let i0 : Fin r := ⟨0, by omega⟩
      have hall : ∀ x : Fin (2 * h), inBlock S (τ i0) x := by
        intro x
        obtain ⟨t, htr, hin⟩ := every_label_transfers S x
        obtain ⟨j, rfl⟩ := hτ_all t htr
        have : j = i0 := Fin.ext (by omega)
        subst this; exact hin
      have hcard_blk : 2 * h ≤ S.k (τ i0) := by
        have hsub : Finset.univ.image (fun x => (pos S (τ i0).castSucc x).val) ⊆ Finset.Ico (S.a (τ i0)) (S.a (τ i0) + S.k (τ i0)) := by
          intro p hp
          rw [Finset.mem_image] at hp
          rcases hp with ⟨x, _, rfl⟩
          rw [Finset.mem_Ico]; exact hall x
        have hinj : Function.Injective (fun x => (pos S (τ i0).castSucc x).val) :=
          fun x y hxy => (S.perm (τ i0).castSucc).symm.injective (Fin.ext hxy)
        have hle := Finset.card_le_card hsub
        rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin, Nat.card_Ico] at hle
        omega
      have himb := S.himb (τ i0)
      have hak := S.hak (τ i0)
      omega
  -- Define B i (participants in transfer τ i) and gap data (side i, A i) for i ≥ 1
  let B : Fin r → Finset (Fin (2 * h)) := fun i =>
    Finset.univ.filter (fun x => inBlock S (τ i) x)
  have hgap_ex : ∀ i : Fin r, 0 < i.val →
      ∃ (side : Bool) (A : Finset (Fin (2 * h))),
        2 ^ (w - 1) ≤ A.card ∧
        (∀ x ∈ A, ∃ s : Fin (S.T + 1), (τ ⟨i.val - 1, by omega⟩).succ ≤ s ∧ s ≤ (τ i).castSucc ∧ inBand w side (pos S s x)) ∧
        (∀ x ∈ A, ∀ y ∈ A, x ≠ y →
          (pos S (τ ⟨i.val - 1, by omega⟩).succ x < pos S (τ ⟨i.val - 1, by omega⟩).succ y ↔
            ¬ (pos S (τ i).castSucc x < pos S (τ i).castSucc y))) :=
    fun i hi => gap_visitors (by omega) hh S (hτ_mono (Fin.lt_def.mpr (by simp; omega)))
      (hτ_tr ⟨i.val - 1, by omega⟩) (hτ_tr i) (hτ_gap i hi)
  let gapSide : Fin r → Bool := fun i => if hi : 0 < i.val then (hgap_ex i hi).choose else false
  let gapA : Fin r → Finset (Fin (2 * h)) := fun i =>
    if hi : 0 < i.val then (hgap_ex i hi).choose_spec.choose else ∅
  have hgapA_card : ∀ (i : Fin r), 0 < i.val → 2 ^ (w - 1) ≤ (gapA i).card := fun i hi => by
    dsimp only [gapA]; rw [dif_pos hi]; exact (hgap_ex i hi).choose_spec.choose_spec.1
  have hgapA_vis : ∀ (i : Fin r) (hi : 0 < i.val), ∀ x ∈ gapA i,
      ∃ s : Fin (S.T + 1), (τ ⟨i.val - 1, by omega⟩).succ ≤ s ∧ s ≤ (τ i).castSucc ∧
        inBand w (gapSide i) (pos S s x) := fun i hi => by
    dsimp only [gapA, gapSide]; rw [dif_pos hi, dif_pos hi]; exact (hgap_ex i hi).choose_spec.choose_spec.2.1
  have hgapA_chg : ∀ (i : Fin r) (hi : 0 < i.val), ∀ x ∈ gapA i, ∀ y ∈ gapA i, x ≠ y →
      (pos S (τ ⟨i.val - 1, by omega⟩).succ x < pos S (τ ⟨i.val - 1, by omega⟩).succ y ↔
        ¬ (pos S (τ i).castSucc x < pos S (τ i).castSucc y)) := fun i hi => by
    dsimp only [gapA]; rw [dif_pos hi]; exact (hgap_ex i hi).choose_spec.choose_spec.2.2
  -- Last transfer index strictly before i (1-indexed: 0 means none, j+1 means transfer j < i)
  let lastTr (i : Fin r) (x : Fin (2 * h)) : ℕ :=
    (Finset.univ.filter (fun j : Fin r => j.val < i.val ∧ x ∈ B j)).sup (fun j => j.val + 1)
  have hlastTr_lt : ∀ i x, lastTr i x ≤ i.val := by
    intro i x
    apply Finset.sup_le
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    omega
  have hlastTr_no_between : ∀ (i : Fin r) (x : Fin (2 * h)) (j : Fin r),
      lastTr i x ≤ j.val → j.val < i.val → x ∉ B j := by
    intro i x j hj1 hj2 hxB
    have hle : j.val + 1 ≤ lastTr i x :=
      Finset.le_sup (f := fun k : Fin r => k.val + 1) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj2, hxB⟩)
    omega
  have hlastTr_mem : ∀ (i : Fin r) (x : Fin (2 * h)), 0 < lastTr i x →
      ∃ (j : Fin r), j.val + 1 = lastTr i x ∧ j.val < i.val ∧ x ∈ B j := by
    intro i x hpos
    have hne : (Finset.univ.filter (fun j : Fin r => j.val < i.val ∧ x ∈ B j)).Nonempty := by
      by_contra hem
      dsimp only [lastTr] at hpos
      rw [Finset.not_nonempty_iff_eq_empty.mp hem] at hpos
      simp at hpos
    obtain ⟨j, hj, hjeq⟩ := Finset.exists_mem_eq_sup _ hne (fun j : Fin r => j.val + 1)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    exact ⟨j, hjeq.symm, hj.1, hj.2⟩
  -- Helper: if x avoids B j for all j with t_start ≤ τ j < t_end, then onSide side is constant on [t_start, t_end]!
  have hstay_no_tr : ∀ (side : Bool) (x : Fin (2 * h)) (t₁ t₂ : Fin (S.T + 1)), t₁ ≤ t₂ →
      (∀ j : Fin r, t₁.val ≤ (τ j).val → (τ j).val < t₂.val → x ∉ B j) →
      (∃ s : Fin (S.T + 1), t₁ ≤ s ∧ s ≤ t₂ ∧ onSide side (pos S s x)) →
      ∀ s : Fin (S.T + 1), t₁ ≤ s → s ≤ t₂ → onSide side (pos S s x) := by
    intro side x t₁ t₂ ht hno ⟨s₀, hs01, hs02, hs0_side⟩
    have hconst : ∀ s : Fin (S.T + 1), t₁ ≤ s → s ≤ t₂ →
        (onSide side (pos S s x) ↔ onSide side (pos S t₁ x)) := by
      intro s hs1 hs2
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (show t₁.val ≤ s.val from hs1)
      induction d generalizing s with
      | zero => have : s = t₁ := Fin.ext (by omega); subst this; rfl
      | succ d ih =>
        have hs_le : s.val ≤ t₂.val := hs2
        have ht2_lt := t₂.isLt
        let t : Fin S.T := ⟨t₁.val + d, by omega⟩
        have hs_eq : s = t.succ := Fin.ext (by simp [t]; omega)
        have ht_ge : t₁.val ≤ t.val := by dsimp only [t]; omega
        have ht_lt : t.val < t₂.val := by dsimp only [t]; omega
        rw [hs_eq]
        rw [← ih t.castSucc (Fin.le_def.mpr (by simp [t]))
          (Fin.le_def.mpr (by simp [t]; omega)) (by simp [t])]
        by_cases htr : isTransfer S t
        · obtain ⟨j, hj_eq⟩ := hτ_all t htr
          have hnot : ¬ inBlock S t x := by
            have := hno j (by rw [hj_eq]; exact ht_ge) (by rw [hj_eq]; exact ht_lt)
            simpa [B, hj_eq] using this
          have hst := pos_step S t x
          rw [dif_neg hnot] at hst; rw [hst]
        · have hsp := side_preserved_of_not_transfer S t htr x
          cases side <;> simp only [onSide, Bool.false_eq_true, ↓reduceIte]
          · exact hsp
          · constructor <;> intro hc <;> omega
    intro s hs1 hs2
    exact (hconst s hs1 hs2).mpr ((hconst s₀ hs01 hs02).mp hs0_side)
  -- Helper: core update-chain bound for ANY start time t_start and range [m, b) of transfer indices!
  -- Specifically: given m < b ≤ r, t_start ≤ (τ m).castSucc (with t_start = (τ (m-1)).succ if m > 0 else 0),
  -- and V : Fin r → Finset (Fin (2*h)) such that for i ∈ [m, b):
  --   V i ⊆ gapA i, gapSide i = side (if V i nonempty), and every x ∈ V i avoids B j for m ≤ j < i
  --   and avoids transfers in [t_start, (τ m).castSucc).
  -- Then ∑ i ∈ Ico m b, (V i).card ≤ U_end.card + 2 * w * (b - m),
  -- where U_end consists of labels x that belonged to some V i (m ≤ i < b) and avoided B j for all i ≤ j < b!
  have hchain : ∀ (side : Bool) (t_start : Fin (S.T + 1)) (m b : ℕ) (hb : b ≤ r)
      (ht_m : ∀ (i : Fin r), m ≤ i.val → t_start ≤ (τ i).castSucc)
      (ht_prev : ∀ (i : Fin r), m ≤ i.val → 0 < i.val → t_start ≤ (τ ⟨i.val - 1, by omega⟩).succ)
      (V : ℕ → Finset (Fin (2 * h)))
      (hV_sub : ∀ (i : Fin r), m ≤ i.val → i.val < b → V i.val ⊆ gapA i)
      (hV_side : ∀ (i : Fin r), m ≤ i.val → i.val < b → (V i.val).Nonempty → gapSide i = side)
      (hV_pos : ∀ i, m ≤ i → i < b → (V i).Nonempty → 0 < i)
      (hV_no : ∀ (i : Fin r), m ≤ i.val → i.val < b → ∀ x ∈ V i.val,
        ∀ j : Fin r, t_start.val ≤ (τ j).val → (τ j).val < (τ i).val → x ∉ B j),
      ∃ U_end : Finset (Fin (2 * h)),
        (∀ x ∈ U_end, ∃ (i : Fin r), m ≤ i.val ∧ i.val < b ∧ x ∈ V i.val ∧
          ∀ (j : Fin r), i.val ≤ j.val → j.val < b → x ∉ B j) ∧
        ∑ i ∈ Finset.Ico m b, (V i).card ≤ U_end.card + 2 * w * (b - m) := by
    intro side t_start m b hb ht_m ht_prev V hV_sub hV_side hV_pos hV_no
    -- Induct on len = b - m
    suffices hind : ∀ (len : ℕ), (hlen : m + len ≤ b) →
        ∃ U : Finset (Fin (2 * h)),
          (∀ x ∈ U, ∃ (i : Fin r), m ≤ i.val ∧ i.val < m + len ∧ x ∈ V i.val ∧
            ∀ (j : Fin r), i.val ≤ j.val → j.val < m + len → x ∉ B j) ∧
          ∑ i ∈ Finset.Ico m (m + len), (V i).card ≤ U.card + 2 * w * len by
      by_cases hmb : m ≤ b
      · obtain ⟨U, hU1, hU2⟩ := hind (b - m) (by omega)
        rw [show m + (b - m) = b by omega] at hU1 hU2
        exact ⟨U, hU1, hU2⟩
      · refine ⟨∅, fun x hx => absurd hx (Finset.notMem_empty x), ?_⟩
        rw [Finset.Ico_eq_empty (by omega)]; simp
    intro len
    induction len with
    | zero =>
      intro _
      refine ⟨∅, fun x hx => absurd hx (Finset.notMem_empty x), by simp⟩
    | succ len ih =>
      intro hlen
      obtain ⟨U, hU_spec, hU_sum⟩ := ih (by omega)
      let i : Fin r := ⟨m + len, by omega⟩
      let Vi := V i.val
      let Bi := B i
      let U' := (U ∪ Vi) \ Bi
      have hU'_spec : ∀ x ∈ U', ∃ (i₀ : Fin r), m ≤ i₀.val ∧ i₀.val < m + (len + 1) ∧ x ∈ V i₀.val ∧
          ∀ (j : Fin r), i₀.val ≤ j.val → j.val < m + (len + 1) → x ∉ B j := by
        intro x hx
        rw [Finset.mem_sdiff, Finset.mem_union] at hx
        rcases hx.1 with hxU | hxV
        · obtain ⟨i₀, hi1, hi2, hxV0, hno⟩ := hU_spec x hxU
          refine ⟨i₀, hi1, by omega, hxV0, fun j hj1 hj2 => ?_⟩
          by_cases hjeq : j.val = m + len
          · have : j = i := Fin.ext hjeq; subst this; exact hx.2
          · exact hno j hj1 (by omega)
        · refine ⟨i, by dsimp only [i]; omega, by dsimp only [i]; omega, hxV, fun j hj1 hj2 => ?_⟩
          have : j = i := Fin.ext (by dsimp only [i] at hj1 ⊢; omega)
          subst this; exact hx.2
      -- Bound 1: (U ∩ Vi).card ≤ w
      have hrep : (U ∩ Vi).card ≤ w := by
        by_cases hne : (U ∩ Vi).Nonempty
        · have hVi_ne : Vi.Nonempty := hne.mono Finset.inter_subset_right
          have hi_pos : 0 < i.val := hV_pos i.val (by dsimp only [i]; omega) (by dsimp only [i]; omega) hVi_ne
          have hside_i : gapSide i = side := hV_side i (by dsimp only [i]; omega) (by dsimp only [i]; omega) hVi_ne
          let t_gap0 : Fin (S.T + 1) := (τ ⟨i.val - 1, by omega⟩).succ
          have ht_le : t_start ≤ t_gap0 := ht_prev i (by dsimp only [i]; omega) hi_pos
          apply order_observation hh S side ht_le (U ∩ Vi)
          · -- Stay on side during [t_start, t_gap0]
            intro x hx
            have hxU := (Finset.mem_inter.mp hx).1
            obtain ⟨i₀, hi01, hi02, hxV0, hno0⟩ := hU_spec x hxU
            have hne0 : (V i₀.val).Nonempty := ⟨x, hxV0⟩
            have hi0_pos := hV_pos i₀.val hi01 (by omega) hne0
            have hside0 := hV_side i₀ hi01 (by omega) hne0
            obtain ⟨s, hs1, hs2, hband⟩ := hgapA_vis i₀ hi0_pos x (hV_sub i₀ hi01 (by omega) hxV0)
            rw [hside0] at hband
            have hs_le : s ≤ t_gap0 := hs2.trans (Fin.le_def.mpr (by
              have hle_tr : (τ i₀).val ≤ (τ ⟨i.val - 1, by omega⟩).val :=
                hτ_mono.monotone (Fin.le_def.mpr (by dsimp only [i]; omega))
              dsimp only [t_gap0]; simp; omega))
            have hon : onSide side (pos S s x) := by
              cases side <;> simp only [inBand, onSide, Bool.false_eq_true, ↓reduceIte] at hband ⊢ <;> omega
            exact hstay_no_tr side x t_start t_gap0 ht_le (fun j hj1 hj2 => by
              by_cases hji : j.val < i₀.val
              · exact hV_no i₀ hi01 (by omega) x hxV0 j hj1 (hτ_mono (Fin.lt_def.mpr hji))
              · have hjb : j.val < m + len := by
                  have hlt_tr : (τ j).val < (τ ⟨i.val - 1, by omega⟩).val + 1 := hj2
                  have hle_j : j.val ≤ i.val - 1 := by
                    by_contra hgt
                    have := hτ_mono (Fin.lt_def.mpr (show (⟨i.val - 1, by omega⟩ : Fin r).val < j.val by simp; omega))
                    have : (τ ⟨i.val - 1, by omega⟩).val < (τ j).val := this
                    omega
                  dsimp only [i] at hle_j; omega
                exact hno0 j (by omega) hjb) ⟨s, (ht_prev i₀ hi01 hi0_pos).trans hs1, hs_le, hon⟩
          · -- Fixed order during [t_start, t_gap0] (because every pair in U ∩ Vi changes order in gap i!)
            intro x hx y hy s hs1 hs2
            by_cases hxy : x = y
            · subst hxy; simp
            · have hxA := hV_sub i (by dsimp only [i]; omega) (by dsimp only [i]; omega) (Finset.mem_inter.mp hx).2
              have hyA := hV_sub i (by dsimp only [i]; omega) (by dsimp only [i]; omega) (Finset.mem_inter.mp hy).2
              have hchg := hgapA_chg i hi_pos x hxA y hyA hxy
              have hle_gap : t_gap0 ≤ (τ i).castSucc := Fin.le_def.mpr (by
                have : (τ ⟨i.val - 1, by omega⟩).val < (τ i).val := hτ_mono (Fin.lt_def.mpr (by simp; omega))
                dsimp only [t_gap0]; simp; omega)
              exact order_fixed_before_change S hle_gap hchg hs2 ht_le
          · -- Every x ∈ U ∩ Vi visited band during [t_start, t_gap0]
            intro x hx
            obtain ⟨i₀, hi01, hi02, hxV0, _⟩ := hU_spec x (Finset.mem_inter.mp hx).1
            have hne0 : (V i₀.val).Nonempty := ⟨x, hxV0⟩
            have hi0_pos := hV_pos i₀.val hi01 (by omega) hne0
            have hside0 := hV_side i₀ hi01 (by omega) hne0
            obtain ⟨s, hs1, hs2, hband⟩ := hgapA_vis i₀ hi0_pos x (hV_sub i₀ hi01 (by omega) hxV0)
            rw [hside0] at hband
            refine ⟨s, (ht_prev i₀ hi01 hi0_pos).trans hs1, hs2.trans (Fin.le_def.mpr ?_), hband⟩
            have hle_tr : (τ i₀).val ≤ (τ ⟨i.val - 1, by omega⟩).val :=
              hτ_mono.monotone (Fin.le_def.mpr (by dsimp only [i]; omega))
            dsimp only [t_gap0]; simp; omega
        · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty]; omega
      -- Bound 2: ((U ∪ Vi) ∩ Bi).card ≤ w
      have hrem : ((U ∪ Vi) ∩ Bi).card ≤ w := by
        let t_end : Fin (S.T + 1) := (τ i).castSucc
        have ht_le : t_start ≤ t_end := ht_m i (by dsimp only [i]; omega)
        apply order_observation hh S side ht_le ((U ∪ Vi) ∩ Bi)
        · -- Stay on side during [t_start, (τ i).castSucc]
          intro x hx
          rcases Finset.mem_union.mp (Finset.mem_inter.mp hx).1 with hxU | hxV
          · obtain ⟨i₀, hi01, hi02, hxV0, hno0⟩ := hU_spec x hxU
            have hne0 : (V i₀.val).Nonempty := ⟨x, hxV0⟩
            have hi0_pos := hV_pos i₀.val hi01 (by omega) hne0
            have hside0 := hV_side i₀ hi01 (by omega) hne0
            obtain ⟨s, hs1, hs2, hband⟩ := hgapA_vis i₀ hi0_pos x (hV_sub i₀ hi01 (by omega) hxV0)
            rw [hside0] at hband
            have hs_le : s ≤ t_end := hs2.trans (Fin.le_def.mpr (hτ_mono.monotone (Fin.le_def.mpr (by dsimp only [i]; omega))))
            have hon : onSide side (pos S s x) := by
              cases side <;> simp only [inBand, onSide, Bool.false_eq_true, ↓reduceIte] at hband ⊢ <;> omega
            exact hstay_no_tr side x t_start t_end ht_le (fun j hj1 hj2 => by
              by_cases hji : j.val < i₀.val
              · exact hV_no i₀ hi01 (by omega) x hxV0 j hj1 (hτ_mono (Fin.lt_def.mpr hji))
              · have hjb : j.val < m + len := by
                  have hlt_j : j < i := hτ_mono.lt_iff_lt.mp hj2
                  exact hlt_j
                exact hno0 j (by omega) hjb) ⟨s, (ht_prev i₀ hi01 hi0_pos).trans hs1, hs_le, hon⟩
          · have hne_i : Vi.Nonempty := ⟨x, hxV⟩
            have hi_pos := hV_pos i.val (by dsimp only [i]; omega) (by dsimp only [i]; omega) hne_i
            have hside_i := hV_side i (by dsimp only [i]; omega) (by dsimp only [i]; omega) hne_i
            obtain ⟨s, hs1, hs2, hband⟩ := hgapA_vis i hi_pos x (hV_sub i (by dsimp only [i]; omega) (by dsimp only [i]; omega) hxV)
            rw [hside_i] at hband
            have hon : onSide side (pos S s x) := by
              cases side <;> simp only [inBand, onSide, Bool.false_eq_true, ↓reduceIte] at hband ⊢ <;> omega
            exact hstay_no_tr side x t_start t_end ht_le
              (hV_no i (by dsimp only [i]; omega) (by dsimp only [i]; omega) x hxV)
              ⟨s, (ht_prev i (by dsimp only [i]; omega) hi_pos).trans hs1, hs2, hon⟩
        · -- Fixed order during [t_start, (τ i).castSucc] (every pair is in B i!)
          intro x hx y hy s hs1 hs2
          have hxB : inBlock S (τ i) x := by simpa [Bi, B] using (Finset.mem_inter.mp hx).2
          have hyB : inBlock S (τ i) y := by simpa [Bi, B] using (Finset.mem_inter.mp hy).2
          exact order_fixed_before_block S (τ i) hxB hyB hs2 ht_le
        · -- Every x ∈ (U ∪ Vi) ∩ Bi visited band during [t_start, (τ i).castSucc]
          intro x hx
          rcases Finset.mem_union.mp (Finset.mem_inter.mp hx).1 with hxU | hxV
          · obtain ⟨i₀, hi01, hi02, hxV0, _⟩ := hU_spec x hxU
            have hne0 : (V i₀.val).Nonempty := ⟨x, hxV0⟩
            have hi0_pos := hV_pos i₀.val hi01 (by omega) hne0
            have hside0 := hV_side i₀ hi01 (by omega) hne0
            obtain ⟨s, hs1, hs2, hband⟩ := hgapA_vis i₀ hi0_pos x (hV_sub i₀ hi01 (by omega) hxV0)
            rw [hside0] at hband
            exact ⟨s, (ht_prev i₀ hi01 hi0_pos).trans hs1,
              hs2.trans (Fin.le_def.mpr (hτ_mono.monotone (Fin.le_def.mpr (by dsimp only [i]; omega)))), hband⟩
          · have hne_i : Vi.Nonempty := ⟨x, hxV⟩
            have hi_pos := hV_pos i.val (by dsimp only [i]; omega) (by dsimp only [i]; omega) hne_i
            have hside_i := hV_side i (by dsimp only [i]; omega) (by dsimp only [i]; omega) hne_i
            obtain ⟨s, hs1, hs2, hband⟩ := hgapA_vis i hi_pos x (hV_sub i (by dsimp only [i]; omega) (by dsimp only [i]; omega) hxV)
            rw [hside_i] at hband
            exact ⟨s, (ht_prev i (by dsimp only [i]; omega) hi_pos).trans hs1, hs2, hband⟩
      -- Combine via exact cardinality identity
      have hid := card_update_identity U Vi Bi
      have hsum_step : ∑ k ∈ Finset.Ico m (m + (len + 1)), (V k).card =
          (∑ k ∈ Finset.Ico m (m + len), (V k).card) + Vi.card := by
        rw [show m + (len + 1) = (m + len) + 1 by omega, Finset.sum_Ico_succ_top (by omega)]
      refine ⟨U', hU'_spec, ?_⟩
      dsimp only [U']
      linarith
  -- Bound (5): For consecutive 0-indexed transfer ranges L = [a, m) and R = [m, b) (a < m < b ≤ r),
  -- count (i ∈ [m, b), x ∈ gapA i) with gapSide i = side and lastTr i x ∈ [a+1, m] (i.e., last transfer index in [a, m))!
  have hsplit_bound : ∀ (side : Bool) (a m b : ℕ), a ≤ m → m ≤ b → b ≤ r →
      (∑ i ∈ Finset.Ico m b,
        (if hi : i < r then
          if gapSide ⟨i, hi⟩ = side then
            ((gapA ⟨i, hi⟩).filter (fun x => a < lastTr ⟨i, hi⟩ x ∧ lastTr ⟨i, hi⟩ x ≤ m)).card
          else 0
        else 0)) ≤ w * (m - a) + 2 * w * (b - m) := by
    intro side a m b ham hmb hbr
    by_cases hm0 : m = 0
    · subst hm0
      have ha0 : a = 0 := by omega
      subst ha0
      have hzero : ∀ i ∈ Finset.Ico 0 b,
          (if hi : i < r then
            if gapSide ⟨i, hi⟩ = side then
              ((gapA ⟨i, hi⟩).filter (fun x => 0 < lastTr ⟨i, hi⟩ x ∧ lastTr ⟨i, hi⟩ x ≤ 0)).card
            else 0
          else 0) = 0 := by
        intro i _; split_ifs <;> simp
        intro x _ hpos; omega
      rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero]; omega
    · by_cases hmb_eq : m = b
      · subst hmb_eq; simp
      · let t_m : Fin (S.T + 1) := (τ ⟨m - 1, by omega⟩).succ
        let V : ℕ → Finset (Fin (2 * h)) := fun i =>
          if hi : i < r then
            if gapSide ⟨i, hi⟩ = side then
              (gapA ⟨i, hi⟩).filter (fun x => a < lastTr ⟨i, hi⟩ x ∧ lastTr ⟨i, hi⟩ x ≤ m)
            else ∅
          else ∅
        have hsum_eq : (∑ i ∈ Finset.Ico m b,
            (if hi : i < r then
              if gapSide ⟨i, hi⟩ = side then
                ((gapA ⟨i, hi⟩).filter (fun x => a < lastTr ⟨i, hi⟩ x ∧ lastTr ⟨i, hi⟩ x ≤ m)).card
              else 0
            else 0)) = ∑ i ∈ Finset.Ico m b, (V i).card := by
          apply Finset.sum_congr rfl; intro i _
          dsimp only [V]; split_ifs <;> simp
        rw [hsum_eq]
        obtain ⟨U_end, hU_spec, hU_sum⟩ := hchain side t_m m b hbr
          (fun i hi => Fin.le_def.mpr (by
            have : (τ ⟨m - 1, by omega⟩).val < (τ i).val := hτ_mono (Fin.lt_def.mpr (by simp; omega))
            dsimp only [t_m]; simp; omega))
          (fun i hi hi0 => Fin.le_def.mpr (by
            have : (τ ⟨m - 1, by omega⟩).val ≤ (τ ⟨i.val - 1, by omega⟩).val :=
              hτ_mono.monotone (Fin.le_def.mpr (by simp; omega))
            dsimp only [t_m]; simp; omega))
          V
          (fun i hi1 hi2 => by
            dsimp only [V]; rw [dif_pos i.isLt]; split_ifs
            · exact Finset.filter_subset _ _
            · exact Finset.empty_subset _)
          (fun i hi1 hi2 hne => by
            dsimp only [V] at hne; rw [dif_pos i.isLt] at hne
            split_ifs at hne with hs
            · exact hs
            · exact absurd hne (Finset.not_nonempty_empty))
          (fun i hi1 hi2 hne => by omega)
          (fun i hi1 hi2 x hx j hj1 hj2 => by
            dsimp only [V] at hx; rw [dif_pos i.isLt] at hx
            split_ifs at hx with hs
            · have hlast : lastTr i x ≤ m := (Finset.mem_filter.mp hx).2.2
              have hj_ge : m ≤ j.val := by
                by_contra hlt
                have hle : (τ j).val ≤ (τ ⟨m - 1, by omega⟩).val :=
                  hτ_mono.monotone (Fin.le_def.mpr (by simp; omega))
                dsimp only [t_m] at hj1; simp at hj1; omega
              have hj_lt : j.val < i.val := hτ_mono.lt_iff_lt.mp hj2
              exact hlastTr_no_between i x j (by omega) hj_lt
            · exact absurd hx (Finset.notMem_empty x))
        -- Bound U_end.card ≤ w * (m - a) by grouping by last transfer j ∈ [a, m)
        have hU_card : U_end.card ≤ w * (m - a) := by
          let t_b : Fin (S.T + 1) := (τ ⟨b - 1, by omega⟩).castSucc
          have htm_le : t_m ≤ t_b := Fin.le_def.mpr (by
            have : (τ ⟨m - 1, by omega⟩).val < (τ ⟨b - 1, by omega⟩).val :=
              hτ_mono (Fin.lt_def.mpr (by simp; omega))
            dsimp only [t_m, t_b]; simp; omega)
          have hpart : U_end ⊆ (Finset.Ico a m).biUnion (fun j =>
              U_end.filter (fun x => ∃ hj : j < r, x ∈ B ⟨j, hj⟩ ∧
                ∀ (k : Fin r), j < k.val → k.val < b → x ∉ B k)) := by
            intro x hx
            obtain ⟨i₀, hi01, hi02, hxV0, hno0⟩ := hU_spec x hx
            dsimp only [V] at hxV0; rw [dif_pos i₀.isLt] at hxV0
            split_ifs at hxV0 with hs0
            · have hlast : a < lastTr i₀ x ∧ lastTr i₀ x ≤ m := (Finset.mem_filter.mp hxV0).2
              obtain ⟨j, hj_eq, hj_lt, hxBj⟩ := hlastTr_mem i₀ x (by omega)
              rw [Finset.mem_biUnion]
              refine ⟨j.val, Finset.mem_Ico.mpr ⟨by omega, by omega⟩,
                Finset.mem_filter.mpr ⟨hx, j.isLt, hxBj, fun k hk1 hk2 => ?_⟩⟩
              by_cases hki : k.val < i₀.val
              · exact hlastTr_no_between i₀ x k (by omega) hki
              · exact hno0 k (by omega) hk2
            · exact absurd hxV0 (Finset.notMem_empty x)
          calc U_end.card
              ≤ ((Finset.Ico a m).biUnion (fun j =>
                  U_end.filter (fun x => ∃ hj : j < r, x ∈ B ⟨j, hj⟩ ∧
                    ∀ (k : Fin r), j < k.val → k.val < b → x ∉ B k))).card := Finset.card_le_card hpart
            _ ≤ ∑ j ∈ Finset.Ico a m, (U_end.filter (fun x => ∃ hj : j < r, x ∈ B ⟨j, hj⟩ ∧
                  ∀ (k : Fin r), j < k.val → k.val < b → x ∉ B k)).card := Finset.card_biUnion_le
            _ ≤ ∑ _j ∈ Finset.Ico a m, w := by
                apply Finset.sum_le_sum
                intro j hj
                rw [Finset.mem_Ico] at hj
                let Wj := U_end.filter (fun x => ∃ hjr : j < r, x ∈ B ⟨j, hjr⟩ ∧
                  ∀ (k : Fin r), j < k.val → k.val < b → x ∉ B k)
                apply order_observation hh S side htm_le Wj
                · intro x hx
                  have hxU := (Finset.mem_filter.mp hx).1
                  have ⟨hjr, _, hno_after⟩ := (Finset.mem_filter.mp hx).2
                  obtain ⟨i₀, hi01, hi02, hxV0, _⟩ := hU_spec x hxU
                  dsimp only [V] at hxV0; rw [dif_pos i₀.isLt] at hxV0
                  split_ifs at hxV0 with hs0
                  · obtain ⟨s, hs1, hs2, hband⟩ := hgapA_vis i₀ (by omega) x (Finset.mem_filter.mp hxV0).1
                    rw [hs0] at hband
                    have hon : onSide side (pos S s x) := by
                      cases side <;> simp only [inBand, onSide, Bool.false_eq_true, ↓reduceIte] at hband ⊢ <;> omega
                    have hs_ge : t_m ≤ s := (Fin.le_def.mpr (by
                      have := hτ_mono.monotone (show (⟨m - 1, by omega⟩ : Fin r) ≤ ⟨i₀.val - 1, by omega⟩ from Fin.le_def.mpr (by simp; omega))
                      have : (τ ⟨m - 1, by omega⟩).val ≤ (τ ⟨i₀.val - 1, by omega⟩).val := this
                      dsimp only [t_m]; simp; omega)).trans hs1
                    have hs_le : s ≤ t_b := hs2.trans (Fin.le_def.mpr (by
                      have := hτ_mono.monotone (show i₀ ≤ ⟨b - 1, by omega⟩ from Fin.le_def.mpr (by simp; omega))
                      dsimp only [t_b]; exact this))
                    exact hstay_no_tr side x t_m t_b htm_le (fun k hk1 hk2 => by
                      have hk_gt : j < k.val := by
                        by_contra hle
                        have := hτ_mono.monotone (show k ≤ ⟨m - 1, by omega⟩ from Fin.le_def.mpr (by simp; omega))
                        have : (τ k).val ≤ (τ ⟨m - 1, by omega⟩).val := this
                        dsimp only [t_m] at hk1; simp at hk1; omega
                      have hk_lt : k.val < b := by
                        have hlt_k : k < ⟨b - 1, by omega⟩ := hτ_mono.lt_iff_lt.mp hk2
                        have : k.val < b - 1 := hlt_k; omega
                      exact hno_after k hk_gt hk_lt) ⟨s, hs_ge, hs_le, hon⟩
                  · exact absurd hxV0 (Finset.notMem_empty x)
                · intro x hx y hy s hs1 hs2
                  obtain ⟨hjr, hxB, _⟩ := (Finset.mem_filter.mp hx).2
                  obtain ⟨_, hyB, _⟩ := (Finset.mem_filter.mp hy).2
                  have hx_blk : inBlock S (τ ⟨j, hjr⟩) x := by simpa [B] using hxB
                  have hy_blk : inBlock S (τ ⟨j, hjr⟩) y := by simpa [B] using hyB
                  have hsucc_le : (τ ⟨j, hjr⟩).succ ≤ t_m := Fin.le_def.mpr (by
                    have := hτ_mono.monotone (show (⟨j, hjr⟩ : Fin r) ≤ ⟨m - 1, by omega⟩ from Fin.le_def.mpr (by simp; omega))
                    have : (τ ⟨j, hjr⟩).val ≤ (τ ⟨m - 1, by omega⟩).val := this
                    dsimp only [t_m]; simp; omega)
                  exact order_fixed_after_block S (τ ⟨j, hjr⟩) hx_blk hy_blk (hsucc_le.trans hs1) hsucc_le
                · intro x hx
                  have hxU := (Finset.mem_filter.mp hx).1
                  obtain ⟨i₀, hi01, hi02, hxV0, _⟩ := hU_spec x hxU
                  dsimp only [V] at hxV0; rw [dif_pos i₀.isLt] at hxV0
                  split_ifs at hxV0 with hs0
                  · obtain ⟨s, hs1, hs2, hband⟩ := hgapA_vis i₀ (by omega) x (Finset.mem_filter.mp hxV0).1
                    rw [hs0] at hband
                    refine ⟨s, (Fin.le_def.mpr ?_).trans hs1, hs2.trans (Fin.le_def.mpr ?_), hband⟩
                    · have := hτ_mono.monotone (show (⟨m - 1, by omega⟩ : Fin r) ≤ ⟨i₀.val - 1, by omega⟩ from Fin.le_def.mpr (by simp; omega))
                      have : (τ ⟨m - 1, by omega⟩).val ≤ (τ ⟨i₀.val - 1, by omega⟩).val := this
                      dsimp only [t_m]; simp; omega
                    · have := hτ_mono.monotone (show i₀ ≤ ⟨b - 1, by omega⟩ from Fin.le_def.mpr (by simp; omega))
                      dsimp only [t_b]; exact this
                  · exact absurd hxV0 (Finset.notMem_empty x)
            _ = w * (m - a) := by rw [Finset.sum_const, Nat.card_Ico, smul_eq_mul, mul_comm]
        omega
  -- Zero-index bound: count (i ∈ [1, r), x ∈ gapA i) with lastTr i x = 0 is ≤ 2 * w * r per side!
  have hzero_bound : ∀ side : Bool,
      (∑ i ∈ Finset.Ico 0 r,
        (if hi : i < r then
          if gapSide ⟨i, hi⟩ = side then
            ((gapA ⟨i, hi⟩).filter (fun x => lastTr ⟨i, hi⟩ x = 0)).card
          else 0
        else 0)) ≤ 2 * w * r := by
    intro side
    let V0 : ℕ → Finset (Fin (2 * h)) := fun i =>
      if hi : i < r then
        if gapSide ⟨i, hi⟩ = side then
          (gapA ⟨i, hi⟩).filter (fun x => lastTr ⟨i, hi⟩ x = 0)
        else ∅
      else ∅
    have hsum_eq : (∑ i ∈ Finset.Ico 0 r,
        (if hi : i < r then
          if gapSide ⟨i, hi⟩ = side then
            ((gapA ⟨i, hi⟩).filter (fun x => lastTr ⟨i, hi⟩ x = 0)).card
          else 0
        else 0)) = ∑ i ∈ Finset.Ico 0 r, (V0 i).card := by
      apply Finset.sum_congr rfl; intro i _; dsimp only [V0]; split_ifs <;> simp
    rw [hsum_eq]
    obtain ⟨U_end, hU_spec, hU_sum⟩ := hchain side 0 0 r le_rfl
      (fun _ _ => Fin.zero_le _) (fun _ _ _ => Fin.zero_le _) V0
      (fun i _ _ => by dsimp only [V0]; rw [dif_pos i.isLt]; split_ifs; exact Finset.filter_subset _ _; exact Finset.empty_subset _)
      (fun i _ _ hne => by dsimp only [V0] at hne; rw [dif_pos i.isLt] at hne; split_ifs at hne with hs; exact hs; exact absurd hne Finset.not_nonempty_empty)
      (fun i _ hi hne => by
        by_contra h0
        have hi0 : i = 0 := by omega
        subst hi0
        dsimp only [V0, gapA] at hne; rw [dif_pos hi] at hne
        split_ifs at hne <;> simp at hne)
      (fun i _ _ x hx j _ hj2 => by
        dsimp only [V0] at hx; rw [dif_pos i.isLt] at hx
        split_ifs at hx with hs
        · have hz : lastTr i x = 0 := (Finset.mem_filter.mp hx).2
          have hj_lt : j.val < i.val := hτ_mono.lt_iff_lt.mp hj2
          exact hlastTr_no_between i x j (by omega) hj_lt
        · exact absurd hx (Finset.notMem_empty x))
    -- U_end must be EMPTY because every label participates in some transfer!
    have hU_empty : U_end = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro x hx
      obtain ⟨i₀, _, _, hxV0, hno0⟩ := hU_spec x hx
      dsimp only [V0] at hxV0; rw [dif_pos i₀.isLt] at hxV0
      split_ifs at hxV0 with hs0
      · have hz : lastTr i₀ x = 0 := (Finset.mem_filter.mp hxV0).2
        obtain ⟨t, htr, hin⟩ := every_label_transfers S x
        obtain ⟨j, rfl⟩ := hτ_all t htr
        have hxB : x ∈ B j := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hin⟩
        by_cases hji : j.val < i₀.val
        · exact hlastTr_no_between i₀ x j (by omega) hji hxB
        · exact hno0 j (by omega) j.isLt hxB
      · exact absurd hxV0 (Finset.notMem_empty x)
    rw [hU_empty, Finset.card_empty, zero_add, Nat.sub_zero] at hU_sum
    exact hU_sum
  -- Dyadic decomposition over [0, 2^s) with s = Nat.clog 2 r
  let s : ℕ := Nat.clog 2 r
  let P : ℕ := 2 ^ s
  have hr_le_P : r ≤ P := Nat.le_pow_clog (by norm_num) r
  have hP_lt : P < 2 * r := by
    have hs_pos : 0 < s := by
      dsimp only [s]; exact Nat.clog_pos (by norm_num) (by omega)
    have hlt : 2 ^ (s - 1) < r := by
      have h := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) (show 1 < r by omega)
      rwa [Nat.pred_eq_sub_one] at h
    dsimp only [P]
    rw [show s = (s - 1) + 1 by omega, pow_succ]
    omega
  -- For any 0 ≤ j < i < P, there is a unique dyadic split (level k < s, block idx q < 2^(s - 1 - k))
  -- with j ∈ [2*q*2^k, (2*q+1)*2^k) and i ∈ [(2*q+1)*2^k, (2*q+2)*2^k)!
  have hdyadic_cover : ∀ (i j : ℕ), j < i → i < P →
      ∃ k < s, ∃ q < 2 ^ (s - 1 - k),
        2 * q * 2 ^ k ≤ j ∧ j < (2 * q + 1) * 2 ^ k ∧
        (2 * q + 1) * 2 ^ k ≤ i ∧ i < (2 * q + 2) * 2 ^ k := by
    intro i j hji hiP
    -- Induction on s
    have hgen : ∀ (m i j : ℕ), j < i → i < 2 ^ m →
        ∃ k < m, ∃ q < 2 ^ (m - 1 - k),
          2 * q * 2 ^ k ≤ j ∧ j < (2 * q + 1) * 2 ^ k ∧
          (2 * q + 1) * 2 ^ k ≤ i ∧ i < (2 * q + 2) * 2 ^ k := by
      intro m
      induction m with
      | zero => intro i j hji hi; simp at hi; omega
      | succ m ih =>
        intro i j hji hi
        by_cases hsplit : j < 2 ^ m ∧ 2 ^ m ≤ i
        · refine ⟨m, Nat.lt_succ_self m, 0, by simp, ?_, ?_, ?_, ?_⟩ <;>
            simp [pow_succ] at hi ⊢ <;> omega
        · by_cases hi_lt : i < 2 ^ m
          · obtain ⟨k, hk, q, hq, h1, h2, h3, h4⟩ := ih i j hji hi_lt
            refine ⟨k, by omega, q, ?_, h1, h2, h3, h4⟩
            have : m + 1 - 1 - k = (m - 1 - k) + 1 := by omega
            rw [this, pow_succ]; omega
          · have hj_ge : 2 ^ m ≤ j := by omega
            obtain ⟨k, hk, q, hq, h1, h2, h3, h4⟩ := ih (i - 2 ^ m) (j - 2 ^ m) (by omega)
              (by rw [pow_succ] at hi; omega)
            let q' := 2 ^ (m - 1 - k) + q
            have h2q' : 2 * q' * 2 ^ k = 2 ^ m + 2 * q * 2 ^ k := by
              dsimp only [q']
              have hpow : 2 * 2 ^ (m - 1 - k) * 2 ^ k = 2 ^ m := by
                rw [mul_assoc, ← pow_add, ← pow_succ']
                congr 1; omega
              linarith
            have h2q'1 : (2 * q' + 1) * 2 ^ k = 2 ^ m + (2 * q + 1) * 2 ^ k := by linarith
            have h2q'2 : (2 * q' + 2) * 2 ^ k = 2 ^ m + (2 * q + 2) * 2 ^ k := by linarith
            refine ⟨k, by omega, q', ?_, by omega, by omega, by omega, by omega⟩
            have : m + 1 - 1 - k = (m - 1 - k) + 1 := by omega
            rw [this, pow_succ]; omega
    exact hgen s i j hji hiP
  -- Sum over all positive-lastTr occurrences is bounded by summing over all dyadic splits!
  have hpos_bound : ∀ side : Bool,
      (∑ i ∈ Finset.Ico 0 r,
        (if hi : i < r then
          if gapSide ⟨i, hi⟩ = side then
            ((gapA ⟨i, hi⟩).filter (fun x => 0 < lastTr ⟨i, hi⟩ x)).card
          else 0
        else 0)) ≤ 3 * w * P * s := by
    intro side
    -- For each i < r and x ∈ gapA i with lastTr i x > 0, j = lastTr i x - 1 < i < P
    -- so (j, i) falls in some dyadic split (k, q)!
    have hle_sum : (∑ i ∈ Finset.Ico 0 r,
        (if hi : i < r then
          if gapSide ⟨i, hi⟩ = side then
            ((gapA ⟨i, hi⟩).filter (fun x => 0 < lastTr ⟨i, hi⟩ x)).card
          else 0
        else 0)) ≤
        ∑ k ∈ Finset.range s, ∑ q ∈ Finset.range (2 ^ (s - 1 - k)),
          ∑ i ∈ Finset.Ico (min ((2 * q + 1) * 2 ^ k) r) (min ((2 * q + 2) * 2 ^ k) r),
            (if hi : i < r then
              if gapSide ⟨i, hi⟩ = side then
                ((gapA ⟨i, hi⟩).filter (fun x =>
                  min (2 * q * 2 ^ k) r < lastTr ⟨i, hi⟩ x ∧
                  lastTr ⟨i, hi⟩ x ≤ min ((2 * q + 1) * 2 ^ k) r)).card
              else 0
            else 0) := by
      -- Exchange order: bound each i-term by sum over (k, q) of its indicator
      have hterm : ∀ i ∈ Finset.Ico 0 r,
          (if hi : i < r then
            if gapSide ⟨i, hi⟩ = side then
              ((gapA ⟨i, hi⟩).filter (fun x => 0 < lastTr ⟨i, hi⟩ x)).card
            else 0
          else 0) ≤
          ∑ k ∈ Finset.range s, ∑ q ∈ Finset.range (2 ^ (s - 1 - k)),
            (if i ∈ Finset.Ico (min ((2 * q + 1) * 2 ^ k) r) (min ((2 * q + 2) * 2 ^ k) r) then
              if hi : i < r then
                if gapSide ⟨i, hi⟩ = side then
                  ((gapA ⟨i, hi⟩).filter (fun x =>
                    min (2 * q * 2 ^ k) r < lastTr ⟨i, hi⟩ x ∧
                    lastTr ⟨i, hi⟩ x ≤ min ((2 * q + 1) * 2 ^ k) r)).card
                else 0
              else 0
            else 0) := by
        intro i hi_mem
        have hi : i < r := (Finset.mem_Ico.mp hi_mem).2
        rw [dif_pos hi]
        split_ifs with hside
        · let S_i := (gapA ⟨i, hi⟩).filter (fun x => 0 < lastTr ⟨i, hi⟩ x)
          have hcov_i : S_i ⊆ (Finset.range s).biUnion (fun k => (Finset.range (2 ^ (s - 1 - k))).biUnion (fun q =>
              if i ∈ Finset.Ico (min ((2 * q + 1) * 2 ^ k) r) (min ((2 * q + 2) * 2 ^ k) r) then
                (gapA ⟨i, hi⟩).filter (fun x =>
                  min (2 * q * 2 ^ k) r < lastTr ⟨i, hi⟩ x ∧
                  lastTr ⟨i, hi⟩ x ≤ min ((2 * q + 1) * 2 ^ k) r)
              else ∅)) := by
            intro x hx
            have hxA := (Finset.mem_filter.mp hx).1
            have hpos := (Finset.mem_filter.mp hx).2
            have hle_i : lastTr ⟨i, hi⟩ x ≤ i := hlastTr_lt ⟨i, hi⟩ x
            let j := lastTr ⟨i, hi⟩ x - 1
            have hji : j < i := by dsimp only [j]; omega
            obtain ⟨k, hk, q, hq, h1, h2, h3, h4⟩ := hdyadic_cover i j hji (lt_of_lt_of_le hi hr_le_P)
            rw [Finset.mem_biUnion]
            refine ⟨k, Finset.mem_range.mpr hk, Finset.mem_biUnion.mpr ⟨q, Finset.mem_range.mpr hq, ?_⟩⟩
            have hi_ico : i ∈ Finset.Ico (min ((2 * q + 1) * 2 ^ k) r) (min ((2 * q + 2) * 2 ^ k) r) := by
              rw [Finset.mem_Ico]; omega
            rw [if_pos hi_ico]
            exact Finset.mem_filter.mpr ⟨hxA, by dsimp only [j] at h1 h2; omega, by dsimp only [j] at h1 h2; omega⟩
          calc S_i.card
              ≤ ((Finset.range s).biUnion _).card := Finset.card_le_card hcov_i
            _ ≤ ∑ k ∈ Finset.range s, ((Finset.range (2 ^ (s - 1 - k))).biUnion _).card := Finset.card_biUnion_le
            _ ≤ ∑ k ∈ Finset.range s, ∑ q ∈ Finset.range (2 ^ (s - 1 - k)),
                  (if i ∈ Finset.Ico (min ((2 * q + 1) * 2 ^ k) r) (min ((2 * q + 2) * 2 ^ k) r) then
                    ((gapA ⟨i, hi⟩).filter (fun x =>
                      min (2 * q * 2 ^ k) r < lastTr ⟨i, hi⟩ x ∧
                      lastTr ⟨i, hi⟩ x ≤ min ((2 * q + 1) * 2 ^ k) r)).card
                  else 0) := by
                apply Finset.sum_le_sum; intro k _
                refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun q _ => ?_)
                split_ifs <;> simp
            _ = _ := by
                apply Finset.sum_congr rfl; intro k _
                apply Finset.sum_congr rfl; intro q _
                split_ifs <;> simp [hside]
        · exact Nat.zero_le _
      calc _ ≤ ∑ i ∈ Finset.Ico 0 r, ∑ k ∈ Finset.range s, ∑ q ∈ Finset.range (2 ^ (s - 1 - k)), _ :=
            Finset.sum_le_sum hterm
        _ = ∑ k ∈ Finset.range s, ∑ q ∈ Finset.range (2 ^ (s - 1 - k)), ∑ i ∈ Finset.Ico 0 r, _ := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl; intro k _
            exact Finset.sum_comm
        _ = _ := by
            apply Finset.sum_congr rfl; intro k _
            apply Finset.sum_congr rfl; intro q _
            rw [← Finset.sum_filter]
            have hflt : (Finset.Ico 0 r).filter (fun i =>
                i ∈ Finset.Ico (min ((2 * q + 1) * 2 ^ k) r) (min ((2 * q + 2) * 2 ^ k) r)) =
                Finset.Ico (min ((2 * q + 1) * 2 ^ k) r) (min ((2 * q + 2) * 2 ^ k) r) := by
              ext i; simp only [Finset.mem_filter, Finset.mem_Ico]; omega
            rw [hflt]
    -- Apply hsplit_bound to each (k, q)
    refine hle_sum.trans ?_
    have hlevel : ∀ k ∈ Finset.range s,
        ∑ q ∈ Finset.range (2 ^ (s - 1 - k)),
          ∑ i ∈ Finset.Ico (min ((2 * q + 1) * 2 ^ k) r) (min ((2 * q + 2) * 2 ^ k) r),
            (if hi : i < r then
              if gapSide ⟨i, hi⟩ = side then
                ((gapA ⟨i, hi⟩).filter (fun x =>
                  min (2 * q * 2 ^ k) r < lastTr ⟨i, hi⟩ x ∧
                  lastTr ⟨i, hi⟩ x ≤ min ((2 * q + 1) * 2 ^ k) r)).card
              else 0
            else 0) ≤ 3 * w * P := by
      intro k hk
      rw [Finset.mem_range] at hk
      calc _ ≤ ∑ q ∈ Finset.range (2 ^ (s - 1 - k)), (3 * w * 2 ^ k) := by
            apply Finset.sum_le_sum; intro q _
            have hmul1 : (2 * q + 1) * 2 ^ k = 2 * q * 2 ^ k + 2 ^ k := by ring
            have hmul2 : (2 * q + 2) * 2 ^ k = (2 * q + 1) * 2 ^ k + 2 ^ k := by ring
            have hmul0 : 2 * q * 2 ^ k ≤ (2 * q + 1) * 2 ^ k := Nat.mul_le_mul_right _ (by omega)
            have hmul01 : (2 * q + 1) * 2 ^ k ≤ (2 * q + 2) * 2 ^ k := Nat.mul_le_mul_right _ (by omega)
            have hsp := hsplit_bound side (min (2 * q * 2 ^ k) r) (min ((2 * q + 1) * 2 ^ k) r)
              (min ((2 * q + 2) * 2 ^ k) r) (by omega) (by omega) (min_le_right _ _)
            have hlen1 : min ((2 * q + 1) * 2 ^ k) r - min (2 * q * 2 ^ k) r ≤ 2 ^ k := by
              have hle : min ((2 * q + 1) * 2 ^ k) r ≤ min (2 * q * 2 ^ k) r + 2 ^ k := by
                rcases le_total (2 * q * 2 ^ k) r with h1 | h1
                · rw [min_eq_left h1, ← hmul1]; exact min_le_left _ _
                · rw [min_eq_right h1]; exact (min_le_right _ _).trans (Nat.le_add_right _ _)
              exact Nat.sub_le_of_le_add (hle.trans (Nat.add_comm _ _).le)
            have hlen2 : min ((2 * q + 2) * 2 ^ k) r - min ((2 * q + 1) * 2 ^ k) r ≤ 2 ^ k := by
              have hle : min ((2 * q + 2) * 2 ^ k) r ≤ min ((2 * q + 1) * 2 ^ k) r + 2 ^ k := by
                rcases le_total ((2 * q + 1) * 2 ^ k) r with h1 | h1
                · rw [min_eq_left h1, ← hmul2]; exact min_le_left _ _
                · rw [min_eq_right h1]; exact (min_le_right _ _).trans (Nat.le_add_right _ _)
              exact Nat.sub_le_of_le_add (hle.trans (Nat.add_comm _ _).le)
            calc _ ≤ w * (min ((2 * q + 1) * 2 ^ k) r - min (2 * q * 2 ^ k) r) +
                     2 * w * (min ((2 * q + 2) * 2 ^ k) r - min ((2 * q + 1) * 2 ^ k) r) := hsp
              _ ≤ w * 2 ^ k + 2 * w * 2 ^ k := Nat.add_le_add (Nat.mul_le_mul_left _ hlen1) (Nat.mul_le_mul_left _ hlen2)
              _ = 3 * w * 2 ^ k := by ring
        _ = 2 ^ (s - 1 - k) * (3 * w * 2 ^ k) := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
        _ ≤ 3 * w * P := by
            have hpow : 2 ^ (s - 1 - k) * 2 ^ k ≤ P := by
              rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
            calc 2 ^ (s - 1 - k) * (3 * w * 2 ^ k) = 3 * w * (2 ^ (s - 1 - k) * 2 ^ k) := by ring
              _ ≤ 3 * w * P := Nat.mul_le_mul_left _ hpow
    calc _ ≤ ∑ _k ∈ Finset.range s, (3 * w * P) := Finset.sum_le_sum hlevel
      _ = 3 * w * P * s := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]; ring
  -- Combine lower bound and upper bound!
  have htotal_lower : (r - 1) * 2 ^ (w - 1) ≤
      ∑ i ∈ Finset.Ico 0 r, (if hi : i < r then (gapA ⟨i, hi⟩).card else 0) := by
    have hsub : Finset.Ico 1 r ⊆ Finset.Ico 0 r := Finset.Ico_subset_Ico_left (Nat.zero_le 1)
    calc (r - 1) * 2 ^ (w - 1)
        = ∑ _i ∈ Finset.Ico 1 r, 2 ^ (w - 1) := by rw [Finset.sum_const, Nat.card_Ico, smul_eq_mul]
      _ ≤ ∑ i ∈ Finset.Ico 1 r, (if hi : i < r then (gapA ⟨i, hi⟩).card else 0) := by
          apply Finset.sum_le_sum; intro i hi
          rw [Finset.mem_Ico] at hi
          rw [dif_pos hi.2]
          exact hgapA_card ⟨i, hi.2⟩ hi.1
      _ ≤ ∑ i ∈ Finset.Ico 0 r, (if hi : i < r then (gapA ⟨i, hi⟩).card else 0) :=
          Finset.sum_le_sum_of_subset hsub
  have htotal_upper : (∑ i ∈ Finset.Ico 0 r, (if hi : i < r then (gapA ⟨i, hi⟩).card else 0)) ≤
      4 * w * r + 6 * w * P * s := by
    -- Split each (gapA i).card by side (false/true) and lastTr = 0 vs > 0
    have hsplit_i : ∀ i ∈ Finset.Ico 0 r,
        (if hi : i < r then (gapA ⟨i, hi⟩).card else 0) =
        (if hi : i < r then if gapSide ⟨i, hi⟩ = false then ((gapA ⟨i, hi⟩).filter (fun x => lastTr ⟨i, hi⟩ x = 0)).card else 0 else 0) +
        (if hi : i < r then if gapSide ⟨i, hi⟩ = true then ((gapA ⟨i, hi⟩).filter (fun x => lastTr ⟨i, hi⟩ x = 0)).card else 0 else 0) +
        (if hi : i < r then if gapSide ⟨i, hi⟩ = false then ((gapA ⟨i, hi⟩).filter (fun x => 0 < lastTr ⟨i, hi⟩ x)).card else 0 else 0) +
        (if hi : i < r then if gapSide ⟨i, hi⟩ = true then ((gapA ⟨i, hi⟩).filter (fun x => 0 < lastTr ⟨i, hi⟩ x)).card else 0 else 0) := by
      intro i hi_mem
      have hi : i < r := (Finset.mem_Ico.mp hi_mem).2
      rw [dif_pos hi, dif_pos hi, dif_pos hi, dif_pos hi, dif_pos hi]
      have hcard_split : (gapA ⟨i, hi⟩).card =
          ((gapA ⟨i, hi⟩).filter (fun x => lastTr ⟨i, hi⟩ x = 0)).card +
          ((gapA ⟨i, hi⟩).filter (fun x => 0 < lastTr ⟨i, hi⟩ x)).card := by
        rw [← Finset.card_filter_add_card_filter_not (p := fun x => lastTr ⟨i, hi⟩ x = 0)]
        congr 2; ext x; simp [Nat.pos_iff_ne_zero]
      cases gapSide ⟨i, hi⟩ <;> simp [hcard_split]
    rw [Finset.sum_congr rfl hsplit_i, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
    have hz0 := hzero_bound false
    have hz1 := hzero_bound true
    have hp0 := hpos_bound false
    have hp1 := hpos_bound true
    linarith
  refine ⟨r, hr_ge2, hr_lt, ?_⟩
  have hcomb : (r - 1) * 2 ^ (w - 1) ≤ 4 * w * r + 6 * w * P * s := htotal_lower.trans htotal_upper
  have hr_le : r ≤ 2 * (r - 1) := by omega
  have hP_le : P ≤ 4 * (r - 1) := by omega
  have hbound : (r - 1) * 2 ^ (w - 1) ≤ (r - 1) * (8 * w + 24 * w * s) := by
    calc (r - 1) * 2 ^ (w - 1) ≤ 4 * w * r + 6 * w * P * s := hcomb
      _ ≤ 4 * w * (2 * (r - 1)) + 6 * w * (4 * (r - 1)) * s := by
          apply Nat.add_le_add
          · exact Nat.mul_le_mul_left _ hr_le
          · exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hP_le)
      _ = (r - 1) * (8 * w + 24 * w * s) := by ring
  exact Nat.le_of_mul_le_mul_left hbound (by omega)

/-! ## Part 8: Explicit Logarithmic Inequalities (Section 4) -/

private lemma sq_le_two_pow {w : ℕ} (hw : 4 ≤ w) : w ^ 2 ≤ 2 ^ w := by
  induction w, hw using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have hsq : (k + 1) ^ 2 = k ^ 2 + 2 * k + 1 := by ring
    rw [hsq, pow_succ 2 k]
    nlinarith

private lemma log_log_three_pos : 0 < Real.log (Real.log 3) := by
  have h1 : Real.exp 1 < 3 := by
    have := Real.exp_one_lt_d9
    linarith
  have h2 : 1 < Real.log 3 := by
    rw [← Real.log_exp 1]
    exact Real.log_lt_log (Real.exp_pos 1) h1
  exact Real.log_pos h2

theorem OMA.solution :
    OMA.R_Green75_green_75_variants_pinchasi_R1_H2_R1.H2 := by
  let ℓ : ℝ := Real.log (Real.log 3)
  let A : ℝ := 8 / Real.log 2
  let C : ℝ := A + (16 + A * Real.log (256 / Real.log 2)) / ℓ
  refine ⟨C, fun n d hn hrt => ?_⟩
  have hℓ_pos : 0 < ℓ := log_log_three_pos
  have hl2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hll_ge : ℓ ≤ Real.log (Real.log (n : ℝ)) := by
    apply Real.log_le_log (Real.log_pos (by norm_num : (1 : ℝ) < 3))
    exact Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  have hA_pos : 0 < A := by positivity
  have hlog256_pos : 0 < Real.log (256 / Real.log 2) := by
    apply Real.log_pos
    rw [one_lt_div hl2_pos]
    linarith [Real.log_two_lt_d9]
  by_cases hd : d ≤ 16
  · have hC_ge : 16 / ℓ ≤ C := by
      dsimp only [C]
      have : 0 ≤ A * Real.log (256 / Real.log 2) / ℓ := by positivity
      have : 16 / ℓ ≤ (16 + A * Real.log (256 / Real.log 2)) / ℓ := by
        rw [add_div]; linarith
      linarith
    calc (d : ℝ) ≤ 16 := by exact_mod_cast hd
      _ = (16 / ℓ) * ℓ := by field_simp [hℓ_pos.ne']
      _ ≤ C * Real.log (Real.log (n : ℝ)) := by
          apply mul_le_mul hC_ge hll_ge hℓ_pos.le (by positivity)
  · push_neg at hd
    let w : ℕ := (d - 1) / 4
    have hw4 : 4 ≤ w := by dsimp only [w]; omega
    have h4w_le : 4 * w ≤ d - 1 := by dsimp only [w]; omega
    have hd_le : d ≤ 4 * w + 4 := by dsimp only [w]; omega
    -- Reduce to even N = 2 * h ≤ n with imbalance ≥ 4 * w
    have hseq : ∃ h : ℕ, 2 * h ≤ n ∧ 1 ≤ h ∧ Nonempty (PermSeq (2 * h) (4 * w)) := by
      by_cases heven : Even n
      · obtain ⟨h, rfl⟩ := heven
        have hstep_mono : Relation.ReflTransGen (StepRel (h + h) (4 * w))
            (List.finRange (h + h)) (List.finRange (h + h)).reverse := by
          refine Relation.ReflTransGen.mono (fun u v huv => ?_) (List.finRange (h + h)) (List.finRange (h + h)).reverse hrt
          rcases huv with ⟨pre, blk, post, h1, h2, h3, h4, h5⟩
          exact ⟨pre, blk, post, h1, h2, by omega, h4, h5⟩
        have h2h : h + h = 2 * h := by omega
        rw [h2h] at hstep_mono
        exact ⟨h, by omega, by omega, toPermSeq hstep_mono⟩
      · obtain ⟨h, rfl⟩ := Nat.not_even_iff_odd.mp heven
        have hred := reduce_odd_to_even hrt
        have hstep_mono : Relation.ReflTransGen (StepRel (2 * h) (4 * w))
            (List.finRange (2 * h)) (List.finRange (2 * h)).reverse := by
          refine Relation.ReflTransGen.mono (fun u v huv => ?_) (List.finRange (2 * h)) (List.finRange (2 * h)).reverse hred
          rcases huv with ⟨pre, blk, post, h1, h2, h3, h4, h5⟩
          exact ⟨pre, blk, post, h1, h2, by omega, h4, h5⟩
        exact ⟨h, by omega, by omega, toPermSeq hstep_mono⟩
    obtain ⟨h, h2h_le, hh1, ⟨S⟩⟩ := hseq
    have hh_ge : 2 * w + 1 ≤ h := h_ge_two_w_add_one (by omega) hh1 S
    obtain ⟨r, hr2, hr_lt, hdisc⟩ := discrete_bound hw4 hh_ge S
    let s := Nat.clog 2 r
    have hs_bound : (s : ℝ) ≤ 1 + 2 * (Real.log (n : ℝ) / Real.log 2) := by
      have hs_pos : 1 ≤ s := Nat.clog_pos (by norm_num) (by omega)
      have hpow_lt : (2 : ℝ) ^ (s - 1) < (n : ℝ) ^ 2 := by
        have h1 : 2 ^ (s - 1) < r := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) (by omega)
        have h2 : r < n ^ 2 := lt_of_lt_of_le hr_lt (Nat.pow_le_pow_left h2h_le 2)
        exact_mod_cast lt_trans h1 h2
      have hlog := Real.log_lt_log (by positivity) hpow_lt
      rw [Real.log_pow, Real.log_pow] at hlog
      have hcast : ((s - 1 : ℕ) : ℝ) = (s : ℝ) - 1 := by
        rw [Nat.cast_sub hs_pos]; simp
      rw [hcast] at hlog
      push_cast at hlog
      have : (s : ℝ) - 1 < 2 * (Real.log (n : ℝ) / Real.log 2) := by
        calc (s : ℝ) - 1 < (2 * Real.log (n : ℝ)) / Real.log 2 := by
              rw [lt_div_iff₀ hl2_pos]; linarith
          _ = 2 * (Real.log (n : ℝ) / Real.log 2) := by ring
      linarith
    have hlog2n_ge1 : 1 ≤ Real.log (n : ℝ) / Real.log 2 := by
      rw [le_div_iff₀ hl2_pos, one_mul]
      exact Real.log_le_log (by norm_num) (by exact_mod_cast (by omega : 2 ≤ n))
    have h2w_le : (2 : ℝ) ^ w ≤ 256 * (w : ℝ) * (Real.log (n : ℝ) / Real.log 2) := by
      have hd_r : (2 : ℝ) ^ (w - 1) ≤ 8 * (w : ℝ) + 24 * (w : ℝ) * (s : ℝ) := by
        exact_mod_cast hdisc
      have h2w_eq : (2 : ℝ) ^ w = 2 * (2 : ℝ) ^ (w - 1) := by
        conv_lhs => rw [show w = (w - 1) + 1 by omega, pow_succ, mul_comm]
      have hw_pos : (0 : ℝ) ≤ (w : ℝ) := Nat.cast_nonneg w
      nlinarith
    have h2w_sq : (2 : ℝ) ^ w ≤ (256 * (Real.log (n : ℝ) / Real.log 2)) ^ 2 := by
      have hw2 : ((w : ℝ) ^ 2) ≤ (2 : ℝ) ^ w := by exact_mod_cast sq_le_two_pow hw4
      have hsq : ((2 : ℝ) ^ w) ^ 2 ≤ (256 * (w : ℝ) * (Real.log (n : ℝ) / Real.log 2)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) h2w_le 2
      have hpos : (0 : ℝ) < (2 : ℝ) ^ w := by positivity
      have hkey : (2 : ℝ) ^ w * (2 : ℝ) ^ w ≤ (2 : ℝ) ^ w * (256 * (Real.log (n : ℝ) / Real.log 2)) ^ 2 := by
        calc (2 : ℝ) ^ w * (2 : ℝ) ^ w = ((2 : ℝ) ^ w) ^ 2 := by ring
          _ ≤ (256 * (w : ℝ) * (Real.log (n : ℝ) / Real.log 2)) ^ 2 := hsq
          _ = (w : ℝ) ^ 2 * (256 * (Real.log (n : ℝ) / Real.log 2)) ^ 2 := by ring
          _ ≤ (2 : ℝ) ^ w * (256 * (Real.log (n : ℝ) / Real.log 2)) ^ 2 :=
              mul_le_mul_of_nonneg_right hw2 (by positivity)
      exact le_of_mul_le_mul_left hkey hpos
    have hw_log : (w : ℝ) ≤ (2 / Real.log 2) * (Real.log (256 / Real.log 2) + Real.log (Real.log (n : ℝ))) := by
      have hlog := Real.log_le_log (by positivity) h2w_sq
      rw [Real.log_pow, Real.log_pow] at hlog
      push_cast at hlog
      have hln_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
      have hmul_eq : 256 * (Real.log (n : ℝ) / Real.log 2) = (256 / Real.log 2) * Real.log (n : ℝ) := by ring
      rw [hmul_eq, Real.log_mul (by positivity) hln_pos.ne'] at hlog
      rw [show (2 / Real.log 2) * (Real.log (256 / Real.log 2) + Real.log (Real.log (n : ℝ))) =
          (2 * (Real.log (256 / Real.log 2) + Real.log (Real.log (n : ℝ)))) / Real.log 2 by ring,
          le_div_iff₀ hl2_pos]
      linarith
    have hd_r : (d : ℝ) ≤ 4 * (w : ℝ) + 4 := by exact_mod_cast hd_le
    have h4w_bound : (d : ℝ) ≤ A * Real.log (Real.log (n : ℝ)) + 4 + A * Real.log (256 / Real.log 2) := by
      have hdist : 4 * ((2 / Real.log 2) * (Real.log (256 / Real.log 2) + Real.log (Real.log (n : ℝ)))) =
          A * Real.log (Real.log (n : ℝ)) + A * Real.log (256 / Real.log 2) := by
        dsimp only [A]; ring
      linarith
    have htail : 4 + A * Real.log (256 / Real.log 2) ≤
        ((16 + A * Real.log (256 / Real.log 2)) / ℓ) * Real.log (Real.log (n : ℝ)) := by
      calc 4 + A * Real.log (256 / Real.log 2)
          ≤ 16 + A * Real.log (256 / Real.log 2) := by linarith
        _ = ((16 + A * Real.log (256 / Real.log 2)) / ℓ) * ℓ := by field_simp [hℓ_pos.ne']
        _ ≤ ((16 + A * Real.log (256 / Real.log 2)) / ℓ) * Real.log (Real.log (n : ℝ)) :=
            mul_le_mul_of_nonneg_left hll_ge (by positivity)
    calc (d : ℝ) ≤ A * Real.log (Real.log (n : ℝ)) + (4 + A * Real.log (256 / Real.log 2)) := by linarith
      _ ≤ A * Real.log (Real.log (n : ℝ)) +
            ((16 + A * Real.log (256 / Real.log 2)) / ℓ) * Real.log (Real.log (n : ℝ)) := by linarith
      _ = C * Real.log (Real.log (n : ℝ)) := by dsimp only [C]; ring

end Green75PinchasiH2
