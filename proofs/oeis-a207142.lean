import OMAStatements.S_oeis_a207142

-- Problem: A207142: Barker's g.f. and closed forms for (n+1) X 2 0..2 arrays whose 2 X 2 subblocks are invertible and commute with their neighbors.
-- Upstream: statements/oeis-a207142.lean (declaration OMA.S_oeis_a207142.main)
-- Credit: @Raimo33 (the owner of the agent is credited as the solver)

namespace OMA.ProofA207142

open Finset PowerSeries OMA.S_oeis_a207142

private def detOk (r s : Fin 2 → Fin 3) : Prop :=
  ((r 0).val : ℤ) * ((s 1).val : ℤ) - ((r 1).val : ℤ) * ((s 0).val : ℤ) ≠ 0

private instance (r s : Fin 2 → Fin 3) : Decidable (detOk r s) := by
  unfold detOk; infer_instance

private def commOk (r s t : Fin 2 → Fin 3) : Prop :=
  !![((r 0).val : ℤ), ((r 1).val : ℤ); ((s 0).val : ℤ), ((s 1).val : ℤ)] *
    !![((s 0).val : ℤ), ((s 1).val : ℤ); ((t 0).val : ℤ), ((t 1).val : ℤ)] =
  !![((s 0).val : ℤ), ((s 1).val : ℤ); ((t 0).val : ℤ), ((t 1).val : ℤ)] *
    !![((r 0).val : ℤ), ((r 1).val : ℤ); ((s 0).val : ℤ), ((s 1).val : ℤ)]

private instance (r s t : Fin 2 → Fin 3) : Decidable (commOk r s t) := by
  unfold commOk; infer_instance

private def Valid {m : ℕ} (x : Fin m → Fin 2 → Fin 3) : Prop :=
  (∀ i i' : Fin m, i'.val = i.val + 1 →
    ∀ j j' : Fin 2, j'.val = j.val + 1 →
      ((x i j).val : ℤ) * ((x i' j').val : ℤ) - ((x i j').val : ℤ) * ((x i' j).val : ℤ) ≠ 0) ∧
  (∀ i i' i'' : Fin m, i'.val = i.val + 1 → i''.val = i'.val + 1 →
    ∀ j j' : Fin 2, j'.val = j.val + 1 →
      !![((x i j).val : ℤ), ((x i j').val : ℤ); ((x i' j).val : ℤ), ((x i' j').val : ℤ)] *
        !![((x i' j).val : ℤ), ((x i' j').val : ℤ); ((x i'' j).val : ℤ), ((x i'' j').val : ℤ)] =
      !![((x i' j).val : ℤ), ((x i' j').val : ℤ); ((x i'' j).val : ℤ), ((x i'' j').val : ℤ)] *
        !![((x i j).val : ℤ), ((x i j').val : ℤ); ((x i' j).val : ℤ), ((x i' j').val : ℤ)])

private instance {m : ℕ} (x : Fin m → Fin 2 → Fin 3) : Decidable (Valid x) := by
  unfold Valid; infer_instance

private lemma Valid_iff_succ {m : ℕ} (x : Fin (m + 2) → Fin 2 → Fin 3) :
    Valid x ↔
      (∀ i : Fin (m + 1), detOk (x i.castSucc) (x i.succ)) ∧
      (∀ i : Fin m, commOk (x i.castSucc.castSucc) (x i.castSucc.succ) (x i.succ.succ)) := by
  constructor
  · rintro ⟨hd, hc⟩
    refine ⟨fun i => hd i.castSucc i.succ (by simp) 0 1 (by decide),
      fun i => hc i.castSucc.castSucc i.castSucc.succ i.succ.succ (by simp) (by simp) 0 1 (by decide)⟩
  · rintro ⟨hd, hc⟩
    refine ⟨?_, ?_⟩
    · intro i i' hi j j' hj
      have hj0 : j = 0 := by fin_cases j <;> fin_cases j' <;> simp_all
      have hj1 : j' = 1 := by fin_cases j <;> fin_cases j' <;> simp_all
      subst hj0; subst hj1
      have hil : i.val < m + 1 := by omega
      let i0 : Fin (m + 1) := ⟨i.val, hil⟩
      have hi_eq : i = i0.castSucc := Fin.ext rfl
      have hi'_eq : i' = i0.succ := Fin.ext hi
      rw [hi_eq, hi'_eq]
      exact hd i0
    · intro i i' i'' hi hi' j j' hj
      have hj0 : j = 0 := by fin_cases j <;> fin_cases j' <;> simp_all
      have hj1 : j' = 1 := by fin_cases j <;> fin_cases j' <;> simp_all
      subst hj0; subst hj1
      have hil : i.val < m := by omega
      let i0 : Fin m := ⟨i.val, hil⟩
      have hi_eq : i = i0.castSucc.castSucc := Fin.ext rfl
      have hi'_eq : i' = i0.castSucc.succ := Fin.ext hi
      have hi''_eq : i'' = i0.succ.succ := Fin.ext (by simp [i0, hi, hi'])
      rw [hi_eq, hi'_eq, hi''_eq]
      exact hc i0

private def cnt (n : ℕ) (r s : Fin 2 → Fin 3) : ℕ :=
  ((Finset.univ : Finset (Fin (n + 2) → Fin 2 → Fin 3)).filter
    (fun x => Valid x ∧ x 0 = r ∧ x 1 = s)).card

private lemma a_succ_eq_sum_cnt (n : ℕ) :
    a (n + 1) = ∑ r : Fin 2 → Fin 3, ∑ s : Fin 2 → Fin 3, cnt n r s := by
  unfold a cnt
  have hpart : ((Finset.univ : Finset (Fin (n + 2) → Fin 2 → Fin 3)).filter Valid).card =
      ∑ rs : (Fin 2 → Fin 3) × (Fin 2 → Fin 3),
        ((Finset.univ : Finset (Fin (n + 2) → Fin 2 → Fin 3)).filter
          (fun x => Valid x ∧ x 0 = rs.1 ∧ x 1 = rs.2)).card := by
    rw [← Finset.card_biUnion]
    · congr 1
      ext x
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter, Prod.exists]
      exact ⟨fun h => ⟨x 0, x 1, h, rfl, rfl⟩, fun ⟨_, _, h, _, _⟩ => h⟩
    · intro p _ q _ hpq
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro x hxp hxq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hxp hxq
      exact hpq (Prod.ext (hxp.2.1.symm.trans hxq.2.1) (hxp.2.2.symm.trans hxq.2.2))
  change ((Finset.univ : Finset (Fin (n + 2) → Fin 2 → Fin 3)).filter Valid).card = _
  rw [hpart, Fintype.sum_prod_type]

private lemma cnt_zero (r s : Fin 2 → Fin 3) :
    cnt 0 r s = if detOk r s then 1 else 0 := by
  unfold cnt
  by_cases h : detOk r s
  · rw [if_pos h]
    let x0 : Fin 2 → Fin 2 → Fin 3 := fun i => if i = 0 then r else s
    have hfilt : (Finset.univ.filter (fun x : Fin 2 → Fin 2 → Fin 3 => Valid x ∧ x 0 = r ∧ x 1 = s)) = {x0} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · rintro ⟨_, h0, h1⟩
        funext i
        fin_cases i
        · exact h0
        · exact h1
      · rintro rfl
        refine ⟨?_, by simp [x0], by simp [x0]⟩
        rw [Valid_iff_succ]
        refine ⟨fun i => ?_, fun i => i.elim0⟩
        fin_cases i
        simpa [x0] using h
    rw [hfilt, Finset.card_singleton]
  · rw [if_neg h]
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro x _ ⟨hv, h0, h1⟩
    rw [Valid_iff_succ] at hv
    have hd := hv.1 0
    rw [Fin.castSucc_zero, Fin.succ_zero_eq_one, h0, h1] at hd
    exact h hd

private lemma cnt_succ (n : ℕ) (r s : Fin 2 → Fin 3) :
    cnt (n + 1) r s =
      if detOk r s then
        ∑ t : Fin 2 → Fin 3, if commOk r s t then cnt n s t else 0
      else 0 := by
  by_cases hd : detOk r s
  · rw [if_pos hd]
    unfold cnt
    have hsplit : (Finset.univ.filter (fun x : Fin (n + 3) → Fin 2 → Fin 3 => Valid x ∧ x 0 = r ∧ x 1 = s)).card =
        ∑ t : Fin 2 → Fin 3,
          (Finset.univ.filter (fun x : Fin (n + 3) → Fin 2 → Fin 3 =>
            Valid x ∧ x 0 = r ∧ x 1 = s ∧ x 2 = t)).card := by
      rw [← Finset.card_biUnion]
      · congr 1
        ext x
        simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter]
        exact ⟨fun ⟨hv, h0, h1⟩ => ⟨x 2, hv, h0, h1, rfl⟩, fun ⟨_, hv, h0, h1, _⟩ => ⟨hv, h0, h1⟩⟩
      · intro t1 _ t2 _ hne
        change Disjoint _ _
        rw [Finset.disjoint_left]
        intro x hx1 hx2
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx1 hx2
        exact hne (hx1.2.2.2.symm.trans hx2.2.2.2)
    rw [hsplit]
    refine Finset.sum_congr rfl fun t _ => ?_
    by_cases hc : commOk r s t
    · rw [if_pos hc]
      refine Finset.card_bij (fun x _ => fun i : Fin (n + 2) => x i.succ) ?_ ?_ ?_
      · intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        rcases hx with ⟨hv, h0, h1, h2⟩
        rw [Valid_iff_succ] at hv ⊢
        refine ⟨⟨fun i => hv.1 i.succ, fun i => hv.2 i.succ⟩, ?_, ?_⟩
        · simpa using h1
        · simpa using h2
      · intro x1 hx1 x2 hx2 heq
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx1 hx2
        funext i
        refine Fin.cases ?_ (fun j => congrFun heq j) i
        exact hx1.2.1.trans hx2.2.1.symm
      · intro y hy
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
        rcases hy with ⟨hv, h0, h1⟩
        let x : Fin (n + 3) → Fin 2 → Fin 3 := Fin.cons r y
        refine ⟨x, ?_, by funext j; simp [x]⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        have hx0 : x 0 = r := by simp [x]
        have hx1 : x 1 = s := by
          have h1' : (1 : Fin (n + 3)) = Fin.succ (0 : Fin (n + 2)) := rfl
          rw [h1']; dsimp only [x]; rw [Fin.cons_succ]; exact h0
        have hx2 : x 2 = t := by
          have h2' : (2 : Fin (n + 3)) = Fin.succ (1 : Fin (n + 2)) := rfl
          rw [h2']; dsimp only [x]; rw [Fin.cons_succ]; exact h1
        refine ⟨?_, hx0, hx1, hx2⟩
        rw [Valid_iff_succ] at hv ⊢
        refine ⟨fun i => ?_, fun i => ?_⟩
        · refine Fin.cases ?_ (fun j => hv.1 j) i
          rw [Fin.castSucc_zero, Fin.succ_zero_eq_one, hx0, hx1]
          exact hd
        · refine Fin.cases ?_ (fun j => hv.2 j) i
          have h00 : ((0 : Fin (n + 1)).castSucc.castSucc : Fin (n + 3)) = 0 := rfl
          have h01 : ((0 : Fin (n + 1)).castSucc.succ : Fin (n + 3)) = 1 := rfl
          have h02 : ((0 : Fin (n + 1)).succ.succ : Fin (n + 3)) = 2 := rfl
          rw [h00, h01, h02, hx0, hx1, hx2]
          exact hc
    · rw [if_neg hc]
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro x _ ⟨hv, h0, h1, h2⟩
      rw [Valid_iff_succ] at hv
      have hcomm := hv.2 0
      have h00 : ((0 : Fin (n + 1)).castSucc.castSucc : Fin (n + 3)) = 0 := rfl
      have h01 : ((0 : Fin (n + 1)).castSucc.succ : Fin (n + 3)) = 1 := rfl
      have h02 : ((0 : Fin (n + 1)).succ.succ : Fin (n + 3)) = 2 := rfl
      rw [h00, h01, h02, h0, h1, h2] at hcomm
      exact hc hcomm
  · rw [if_neg hd]
    unfold cnt
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro x _ ⟨hv, h0, h1⟩
    rw [Valid_iff_succ] at hv
    have hdet := hv.1 0
    rw [Fin.castSucc_zero, Fin.succ_zero_eq_one, h0, h1] at hdet
    exact hd hdet

private def decR (k : ℕ) : Fin 2 → Fin 3 :=
  fun j => if j = 0 then ⟨(k / 3) % 3, Nat.mod_lt _ (by decide)⟩
           else ⟨k % 3, Nat.mod_lt _ (by decide)⟩

private def encR (r : Fin 2 → Fin 3) : ℕ :=
  3 * (r 0).val + (r 1).val

private def eR : Fin 9 ≃ (Fin 2 → Fin 3) where
  toFun k := decR k.val
  invFun r := ⟨encR r, by have h0 := (r 0).isLt; have h1 := (r 1).isLt; dsimp [encR]; omega⟩
  left_inv k := by
    ext
    dsimp [encR, decR]
    have hk := k.isLt
    omega
  right_inv r := by
    ext j
    dsimp [encR, decR]
    have h0 := (r 0).isLt
    have h1 := (r 1).isLt
    fin_cases j <;> simp <;> omega

private def natDetOk (r s : ℕ) : Bool :=
  let a : ℤ := ((r / 3) % 3 : ℕ)
  let b : ℤ := (r % 3 : ℕ)
  let c : ℤ := ((s / 3) % 3 : ℕ)
  let d : ℤ := (s % 3 : ℕ)
  decide (a * d - b * c ≠ 0)

private def natCommOk (r s t : ℕ) : Bool :=
  let a : ℤ := ((r / 3) % 3 : ℕ)
  let b : ℤ := (r % 3 : ℕ)
  let c : ℤ := ((s / 3) % 3 : ℕ)
  let d : ℤ := (s % 3 : ℕ)
  let e : ℤ := ((t / 3) % 3 : ℕ)
  let f : ℤ := (t % 3 : ℕ)
  decide (a * c + b * e = c * a + d * c) &&
  decide (a * d + b * f = c * b + d * d) &&
  decide (c * c + d * e = e * a + f * c) &&
  decide (c * d + d * f = e * b + f * d)

private lemma natDetOk_iff (r s : ℕ) : natDetOk r s = true ↔ detOk (decR r) (decR s) := by
  simp [natDetOk, detOk, decR]

private lemma natCommOk_iff (r s t : ℕ) : natCommOk r s t = true ↔ commOk (decR r) (decR s) (decR t) := by
  simp only [natCommOk, commOk, decR, Bool.and_eq_true, decide_eq_true_eq, ↓reduceIte,
    Fin.one_eq_zero_iff, OfNat.ofNat_ne_zero]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> assumption
  · intro h
    have h00 := congrFun (congrFun h 0) 0
    have h01 := congrFun (congrFun h 0) 1
    have h10 := congrFun (congrFun h 1) 0
    have h11 := congrFun (congrFun h 1) 1
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at h00 h01 h10 h11
    exact ⟨⟨⟨h00, h01⟩, h10⟩, h11⟩

private def intListSum : List ℤ → ℤ
  | [] => 0
  | x :: xs => x + intListSum xs

private lemma intListSum_eq_sum : ∀ l : List ℤ, intListSum l = l.sum
  | [] => rfl
  | x :: xs => by simp [intListSum, intListSum_eq_sum xs]

private lemma finset_sum_range_eq_intListSum (n : ℕ) (f : ℕ → ℤ) :
    (∑ i ∈ Finset.range n, f i) = intListSum ((List.range n).map f) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Finset.sum_range_succ, List.range_succ, List.map_append, intListSum_eq_sum,
      List.sum_append, ← intListSum_eq_sum, ih]
    simp

private def v0 : List ℤ :=
  (List.range 81).map (fun st => if natDetOk (st / 9) (st % 9) then 1 else 0)

private def stepVec (v : List ℤ) : List ℤ :=
  (List.range 81).map (fun st =>
    let r := st / 9
    let s := st % 9
    if natDetOk r s then
      intListSum ((List.range 9).map (fun t =>
        if natCommOk r s t then v.getD (9 * s + t) 0 else 0))
    else 0)

private def vecAt : ℕ → List ℤ
  | 0 => v0
  | n + 1 => stepVec (vecAt n)

private lemma vecAt_len (n : ℕ) : (vecAt n).length = 81 := by
  cases n <;> simp [vecAt, v0, stepVec]

private lemma vecAt_getD_eq_cnt (n : ℕ) :
    ∀ r s : ℕ, r < 9 → s < 9 → (vecAt n).getD (9 * r + s) 0 = (cnt n (decR r) (decR s) : ℤ) := by
  induction n with
  | zero =>
    intro r s hr hs
    have hlt : 9 * r + s < 81 := by omega
    simp only [vecAt, v0, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range hlt, Option.map_some, Option.getD_some]
    rw [show (9 * r + s) / 9 = r by omega, show (9 * r + s) % 9 = s by omega, cnt_zero]
    by_cases h : natDetOk r s = true
    · rw [if_pos h, if_pos ((natDetOk_iff r s).mp h)]; rfl
    · have hf : natDetOk r s = false := Bool.eq_false_iff.mpr h
      rw [hf, if_neg (by simp), if_neg (fun hd => h ((natDetOk_iff r s).mpr hd))]; rfl
  | succ n ih =>
    intro r s hr hs
    have hlt : 9 * r + s < 81 := by omega
    simp only [vecAt, stepVec, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range hlt, Option.map_some, Option.getD_some]
    rw [show (9 * r + s) / 9 = r by omega, show (9 * r + s) % 9 = s by omega, cnt_succ]
    by_cases h : natDetOk r s = true
    · rw [if_pos h, if_pos ((natDetOk_iff r s).mp h)]
      rw [Nat.cast_sum]
      simp_rw [Nat.cast_ite, Nat.cast_zero]
      rw [← Fintype.sum_equiv eR
        (fun k => if commOk (decR r) (decR s) (decR k.val) then (cnt n (decR s) (decR k.val) : ℤ) else 0)
        (fun t => if commOk (decR r) (decR s) t then (cnt n (decR s) t : ℤ) else 0)
        (fun _ => rfl)]
      rw [Fin.sum_univ_eq_sum_range (fun t => if commOk (decR r) (decR s) (decR t) then (cnt n (decR s) (decR t) : ℤ) else 0) 9,
        finset_sum_range_eq_intListSum]
      congr 1
      apply List.map_congr_left
      intro t ht
      rw [List.mem_range] at ht
      by_cases hc : natCommOk r s t = true
      · rw [if_pos hc, if_pos ((natCommOk_iff r s t).mp hc)]
        exact ih s t hs ht
      · have hcf : natCommOk r s t = false := Bool.eq_false_iff.mpr hc
        rw [hcf, if_neg (by simp), if_neg (fun h' => hc ((natCommOk_iff r s t).mpr h'))]
    · have hf : natDetOk r s = false := Bool.eq_false_iff.mpr h
      rw [hf, if_neg (by simp), if_neg (fun hd => h ((natDetOk_iff r s).mpr hd))]; rfl

private lemma a_succ_eq_intListSum (n : ℕ) : (a (n + 1) : ℤ) = intListSum (vecAt n) := by
  rw [a_succ_eq_sum_cnt, Nat.cast_sum]
  simp_rw [Nat.cast_sum]
  have h1 : (∑ r : Fin 2 → Fin 3, ∑ s : Fin 2 → Fin 3, (cnt n r s : ℤ)) =
      ∑ r : Fin 9, ∑ s : Fin 9, (cnt n (eR r) (eR s) : ℤ) := by
    rw [← Fintype.sum_equiv eR _ _ (fun _ => rfl)]
    refine Finset.sum_congr rfl fun r _ => (Fintype.sum_equiv eR _ _ (fun _ => rfl)).symm
  rw [h1]
  have h2 : (∑ r : Fin 9, ∑ s : Fin 9, (cnt n (decR r.val) (decR s.val) : ℤ)) =
      ∑ st ∈ Finset.range 81, (vecAt n).getD st 0 := by
    rw [Fin.sum_univ_eq_sum_range (fun r => ∑ s : Fin 9, (cnt n (decR r) (decR s.val) : ℤ)) 9]
    have hsplit : (∑ st ∈ Finset.range 81, (vecAt n).getD st 0) =
        ∑ r ∈ Finset.range 9, ∑ s ∈ Finset.range 9, (vecAt n).getD (9 * r + s) 0 := by
      rw [← Finset.sum_product']
      refine Finset.sum_bij (fun st _ => (st / 9, st % 9)) ?_ ?_ ?_ ?_
      · intro st hst
        rw [Finset.mem_range] at hst
        simp only [Finset.mem_product, Finset.mem_range]
        omega
      · intro a _ b _ hab
        have h1 : a / 9 = b / 9 := congrArg Prod.fst hab
        have h2 : a % 9 = b % 9 := congrArg Prod.snd hab
        omega
      · intro ⟨r, s⟩ hrs
        simp only [Finset.mem_product, Finset.mem_range] at hrs
        refine ⟨9 * r + s, Finset.mem_range.mpr (by omega), ?_⟩
        ext <;> dsimp <;> omega
      · intro st _
        congr 1
        omega
    rw [hsplit]
    refine Finset.sum_congr rfl fun r hr => ?_
    rw [Fin.sum_univ_eq_sum_range (fun s => (cnt n (decR r) (decR s) : ℤ)) 9]
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [Finset.mem_range] at hr hs
    exact (vecAt_getD_eq_cnt n r s hr hs).symm
  change (∑ r : Fin 9, ∑ s : Fin 9, (cnt n (decR r.val) (decR s.val) : ℤ)) = _
  rw [h2, finset_sum_range_eq_intListSum]
  congr 1
  have hlen : (vecAt n).length = 81 := vecAt_len n
  apply List.ext_getElem
  · simp [hlen]
  · intro i hi1 hi2
    simp only [List.getElem_map, List.getElem_range, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hi2, Option.getD_some]

private lemma intListSum_map_linear (L : List ℕ) (f1 f2 f3 f4 : ℕ → ℤ) :
    intListSum (L.map (fun x => f1 x + 2 * f2 x - 2 * f3 x)) =
      intListSum (L.map f1) + 2 * intListSum (L.map f2) - 2 * intListSum (L.map f3) := by
  induction L with
  | nil => simp [intListSum]
  | cons x xs ih =>
    simp only [List.map_cons, intListSum, ih]
    ring

private def checkBaseRec : Bool :=
  (List.range 81).all (fun st =>
    decide ((vecAt 8).getD st 0 = (vecAt 7).getD st 0 + 2 * (vecAt 6).getD st 0 - 2 * (vecAt 5).getD st 0))

private theorem checkBaseRec_ok : checkBaseRec = true := by decide +kernel

private theorem base_vals :
    intListSum (vecAt 0) = 50 ∧ intListSum (vecAt 1) = 30 ∧ intListSum (vecAt 2) = 80 ∧
    intListSum (vecAt 3) = 62 ∧ intListSum (vecAt 4) = 159 ∧ intListSum (vecAt 5) = 122 ∧
    intListSum (vecAt 6) = 315 ∧ intListSum (vecAt 7) = 242 := by
  decide +kernel

private lemma vecAt_rec (k : ℕ) :
    ∀ st < 81, (vecAt (k + 8)).getD st 0 =
      (vecAt (k + 7)).getD st 0 + 2 * (vecAt (k + 6)).getD st 0 - 2 * (vecAt (k + 5)).getD st 0 := by
  induction k with
  | zero =>
    intro st hst
    have h := checkBaseRec_ok
    unfold checkBaseRec at h
    simp only [List.all_eq_true, decide_eq_true_eq] at h
    exact h st (List.mem_range.mpr hst)
  | succ k ih =>
    intro st hst
    have hstep : ∀ m : ℕ, (vecAt (m + 1)).getD st 0 =
        if natDetOk (st / 9) (st % 9) then
          intListSum ((List.range 9).map (fun t =>
            if natCommOk (st / 9) (st % 9) t then (vecAt m).getD (9 * (st % 9) + t) 0 else 0))
        else 0 := by
      intro m
      simp only [vecAt, stepVec, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_range hst, Option.map_some, Option.getD_some]
    rw [show k + 1 + 8 = (k + 8) + 1 by omega, show k + 1 + 7 = (k + 7) + 1 by omega,
      show k + 1 + 6 = (k + 6) + 1 by omega, show k + 1 + 5 = (k + 5) + 1 by omega]
    rw [hstep (k + 8), hstep (k + 7), hstep (k + 6), hstep (k + 5)]
    split_ifs with hdet
    · have hcongr : (List.range 9).map (fun t =>
          if natCommOk (st / 9) (st % 9) t then (vecAt (k + 8)).getD (9 * (st % 9) + t) 0 else 0) =
        (List.range 9).map (fun t =>
          (if natCommOk (st / 9) (st % 9) t then (vecAt (k + 7)).getD (9 * (st % 9) + t) 0 else 0) +
          2 * (if natCommOk (st / 9) (st % 9) t then (vecAt (k + 6)).getD (9 * (st % 9) + t) 0 else 0) -
          2 * (if natCommOk (st / 9) (st % 9) t then (vecAt (k + 5)).getD (9 * (st % 9) + t) 0 else 0)) := by
        apply List.map_congr_left
        intro t ht
        rw [List.mem_range] at ht
        split_ifs
        · exact ih (9 * (st % 9) + t) (by omega)
        · ring
      rw [hcongr, intListSum_map_linear (List.range 9) _ _ _ (fun _ => 0)]
    · ring

private lemma a_rec (k : ℕ) :
    (a (k + 9) : ℤ) = (a (k + 8) : ℤ) + 2 * (a (k + 7) : ℤ) - 2 * (a (k + 6) : ℤ) := by
  have hsum : ∀ m : ℕ, (a (m + 1) : ℤ) = intListSum ((List.range 81).map (fun st => (vecAt m).getD st 0)) := by
    intro m
    rw [a_succ_eq_intListSum m]
    congr 1
    have hlen : (vecAt m).length = 81 := vecAt_len m
    apply List.ext_getElem
    · simp [hlen]
    · intro i hi1 hi2
      simp only [List.getElem_map, List.getElem_range, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hi1, Option.getD_some]
  rw [hsum (k + 8), hsum (k + 7), hsum (k + 6), hsum (k + 5)]
  have hcongr : (List.range 81).map (fun st => (vecAt (k + 8)).getD st 0) =
      (List.range 81).map (fun st =>
        (vecAt (k + 7)).getD st 0 + 2 * (vecAt (k + 6)).getD st 0 - 2 * (vecAt (k + 5)).getD st 0) := by
    apply List.map_congr_left
    intro st hst
    exact vecAt_rec k st (List.mem_range.mp hst)
  rw [hcongr, intListSum_map_linear (List.range 81) _ _ _ (fun _ => 0)]

private lemma a_step2 (n : ℕ) (hn : 6 ≤ n) : (a (n + 2) : ℤ) = 2 * (a n : ℤ) - 2 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  clear hn
  induction k with
  | zero =>
    have h6 : (a 6 : ℤ) = 122 := by rw [a_succ_eq_intListSum 5]; exact base_vals.2.2.2.2.2.1
    have h8 : (a 8 : ℤ) = 242 := by rw [a_succ_eq_intListSum 7]; exact base_vals.2.2.2.2.2.2.2
    linarith
  | succ k ih =>
    have hrec := a_rec k
    rw [show 6 + (k + 1) + 2 = k + 9 by omega, show 6 + (k + 1) = k + 7 by omega]
    rw [show 6 + k + 2 = k + 8 by omega, show 6 + k = k + 6 by omega] at ih
    linarith

private lemma closed_even (n : ℕ) (hn : 5 < n) (he : n % 2 = 0) :
    (a n : ℝ) = 15 * (2 : ℝ) ^ ((n : ℝ) / 2) + 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m := ⟨n / 2, by omega⟩
  have hm : 3 ≤ m := by omega
  have hdiv : ((2 * m : ℕ) : ℝ) / 2 = (m : ℝ) := by push_cast; ring
  rw [hdiv, Real.rpow_natCast]
  suffices h : (a (2 * m) : ℤ) = 15 * 2 ^ m + 2 by exact_mod_cast h
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  clear hn he hm hdiv
  induction k with
  | zero =>
    have h6 : (a 6 : ℤ) = 122 := by rw [a_succ_eq_intListSum 5]; exact base_vals.2.2.2.2.2.1
    rw [show 2 * (3 + 0) = 6 by rfl, h6]; norm_num
  | succ k ih =>
    have hst := a_step2 (2 * (3 + k)) (by omega)
    rw [show 2 * (3 + (k + 1)) = 2 * (3 + k) + 2 by omega, hst, ih,
      show 3 + (k + 1) = (3 + k) + 1 by omega, pow_succ]
    ring

private lemma closed_odd (n : ℕ) (hn : 5 < n) (ho : n % 2 = 1) :
    (a n : ℝ) = 313 * (2 : ℝ) ^ (((n : ℝ) - 7) / 2) + 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m + 7 := ⟨(n - 7) / 2, by omega⟩
  have hdiv : (((2 * m + 7 : ℕ) : ℝ) - 7) / 2 = (m : ℝ) := by push_cast; ring
  rw [hdiv, Real.rpow_natCast]
  suffices h : (a (2 * m + 7) : ℤ) = 313 * 2 ^ m + 2 by exact_mod_cast h
  clear hn ho hdiv
  induction m with
  | zero =>
    have h7 : (a 7 : ℤ) = 315 := by rw [a_succ_eq_intListSum 6]; exact base_vals.2.2.2.2.2.2.1
    rw [show 2 * 0 + 7 = 7 by rfl, h7]; norm_num
  | succ m ih =>
    have hst := a_step2 (2 * m + 7) (by omega)
    rw [show 2 * (m + 1) + 7 = (2 * m + 7) + 2 by omega, hst, ih, pow_succ]
    ring

private lemma gf_eq :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      ((1 - X) * (1 - 2 * X ^ 2)) =
        X * (50 - 20 * X - 50 * X ^ 2 + 22 * X ^ 3 - 3 * X ^ 4 - X ^ 5 - X ^ 6 + X ^ 7) := by
  let A : PowerSeries ℚ := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ))
  have hL : A * ((1 - X) * (1 - 2 * X ^ 2)) =
      A - X ^ 1 * A - C 2 * (X ^ 2 * A) + C 2 * (X ^ 3 * A) := by
    simp only [map_ofNat]
    ring
  have hR : (X * (50 - 20 * X - 50 * X ^ 2 + 22 * X ^ 3 - 3 * X ^ 4 - X ^ 5 - X ^ 6 + X ^ 7) : PowerSeries ℚ) =
      C 50 * X ^ 1 - C 20 * X ^ 2 - C 50 * X ^ 3 + C 22 * X ^ 4 - C 3 * X ^ 5 - X ^ 6 - X ^ 7 + X ^ 8 := by
    simp only [map_ofNat]
    ring
  change A * ((1 - X) * (1 - 2 * X ^ 2)) = _
  rw [hL, hR]
  have ha1 : (a 1 : ℚ) = 50 := by exact_mod_cast (a_succ_eq_intListSum 0 ▸ base_vals.1)
  have ha2 : (a 2 : ℚ) = 30 := by exact_mod_cast (a_succ_eq_intListSum 1 ▸ base_vals.2.1)
  have ha3 : (a 3 : ℚ) = 80 := by exact_mod_cast (a_succ_eq_intListSum 2 ▸ base_vals.2.2.1)
  have ha4 : (a 4 : ℚ) = 62 := by exact_mod_cast (a_succ_eq_intListSum 3 ▸ base_vals.2.2.2.1)
  have ha5 : (a 5 : ℚ) = 159 := by exact_mod_cast (a_succ_eq_intListSum 4 ▸ base_vals.2.2.2.2.1)
  have ha6 : (a 6 : ℚ) = 122 := by exact_mod_cast (a_succ_eq_intListSum 5 ▸ base_vals.2.2.2.2.2.1)
  have ha7 : (a 7 : ℚ) = 315 := by exact_mod_cast (a_succ_eq_intListSum 6 ▸ base_vals.2.2.2.2.2.2.1)
  have ha8 : (a 8 : ℚ) = 242 := by exact_mod_cast (a_succ_eq_intListSum 7 ▸ base_vals.2.2.2.2.2.2.2)
  have hA0 : PowerSeries.coeff 0 A = 0 := by dsimp [A]; rw [PowerSeries.coeff_mk, if_pos rfl]
  have hA1 : PowerSeries.coeff 1 A = 50 := by dsimp [A]; rw [PowerSeries.coeff_mk, if_neg (by decide)]; exact ha1
  have hA2 : PowerSeries.coeff 2 A = 30 := by dsimp [A]; rw [PowerSeries.coeff_mk, if_neg (by decide)]; exact ha2
  have hA3 : PowerSeries.coeff 3 A = 80 := by dsimp [A]; rw [PowerSeries.coeff_mk, if_neg (by decide)]; exact ha3
  have hA4 : PowerSeries.coeff 4 A = 62 := by dsimp [A]; rw [PowerSeries.coeff_mk, if_neg (by decide)]; exact ha4
  have hA5 : PowerSeries.coeff 5 A = 159 := by dsimp [A]; rw [PowerSeries.coeff_mk, if_neg (by decide)]; exact ha5
  have hA6 : PowerSeries.coeff 6 A = 122 := by dsimp [A]; rw [PowerSeries.coeff_mk, if_neg (by decide)]; exact ha6
  have hA7 : PowerSeries.coeff 7 A = 315 := by dsimp [A]; rw [PowerSeries.coeff_mk, if_neg (by decide)]; exact ha7
  have hA8 : PowerSeries.coeff 8 A = 242 := by dsimp [A]; rw [PowerSeries.coeff_mk, if_neg (by decide)]; exact ha8
  ext k
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul',
    PowerSeries.coeff_X_pow]
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | k
  · simp only [show ¬ (1 ≤ 0) by decide, show ¬ (2 ≤ 0) by decide, show ¬ (3 ≤ 0) by decide, show ¬ (0 = 1) by decide, show ¬ (0 = 2) by decide, show ¬ (0 = 3) by decide, show ¬ (0 = 4) by decide, show ¬ (0 = 5) by decide, show ¬ (0 = 6) by decide, show ¬ (0 = 7) by decide, show ¬ (0 = 8) by decide, ↓reduceIte, hA0]; norm_num
  · simp only [show (1 ≤ 1) by decide, show 1 - 1 = 0 by decide, show ¬ (2 ≤ 1) by decide, show ¬ (3 ≤ 1) by decide, show (1 = 1) by decide, show ¬ (1 = 2) by decide, show ¬ (1 = 3) by decide, show ¬ (1 = 4) by decide, show ¬ (1 = 5) by decide, show ¬ (1 = 6) by decide, show ¬ (1 = 7) by decide, show ¬ (1 = 8) by decide, ↓reduceIte, hA0, hA1]; norm_num
  · simp only [show (1 ≤ 2) by decide, show 2 - 1 = 1 by decide, show (2 ≤ 2) by decide, show 2 - 2 = 0 by decide, show ¬ (3 ≤ 2) by decide, show ¬ (2 = 1) by decide, show (2 = 2) by decide, show ¬ (2 = 3) by decide, show ¬ (2 = 4) by decide, show ¬ (2 = 5) by decide, show ¬ (2 = 6) by decide, show ¬ (2 = 7) by decide, show ¬ (2 = 8) by decide, ↓reduceIte, hA0, hA1, hA2]; norm_num
  · simp only [show (1 ≤ 3) by decide, show 3 - 1 = 2 by decide, show (2 ≤ 3) by decide, show 3 - 2 = 1 by decide, show (3 ≤ 3) by decide, show 3 - 3 = 0 by decide, show ¬ (3 = 1) by decide, show ¬ (3 = 2) by decide, show (3 = 3) by decide, show ¬ (3 = 4) by decide, show ¬ (3 = 5) by decide, show ¬ (3 = 6) by decide, show ¬ (3 = 7) by decide, show ¬ (3 = 8) by decide, ↓reduceIte, hA0, hA1, hA2, hA3]; norm_num
  · simp only [show (1 ≤ 4) by decide, show 4 - 1 = 3 by decide, show (2 ≤ 4) by decide, show 4 - 2 = 2 by decide, show (3 ≤ 4) by decide, show 4 - 3 = 1 by decide, show ¬ (4 = 1) by decide, show ¬ (4 = 2) by decide, show ¬ (4 = 3) by decide, show (4 = 4) by decide, show ¬ (4 = 5) by decide, show ¬ (4 = 6) by decide, show ¬ (4 = 7) by decide, show ¬ (4 = 8) by decide, ↓reduceIte, hA0, hA1, hA2, hA3, hA4]; norm_num
  · simp only [show (1 ≤ 5) by decide, show 5 - 1 = 4 by decide, show (2 ≤ 5) by decide, show 5 - 2 = 3 by decide, show (3 ≤ 5) by decide, show 5 - 3 = 2 by decide, show ¬ (5 = 1) by decide, show ¬ (5 = 2) by decide, show ¬ (5 = 3) by decide, show ¬ (5 = 4) by decide, show (5 = 5) by decide, show ¬ (5 = 6) by decide, show ¬ (5 = 7) by decide, show ¬ (5 = 8) by decide, ↓reduceIte, hA0, hA1, hA2, hA3, hA4, hA5]; norm_num
  · simp only [show (1 ≤ 6) by decide, show 6 - 1 = 5 by decide, show (2 ≤ 6) by decide, show 6 - 2 = 4 by decide, show (3 ≤ 6) by decide, show 6 - 3 = 3 by decide, show ¬ (6 = 1) by decide, show ¬ (6 = 2) by decide, show ¬ (6 = 3) by decide, show ¬ (6 = 4) by decide, show ¬ (6 = 5) by decide, show (6 = 6) by decide, show ¬ (6 = 7) by decide, show ¬ (6 = 8) by decide, ↓reduceIte, hA0, hA1, hA2, hA3, hA4, hA5, hA6]; norm_num
  · simp only [show (1 ≤ 7) by decide, show 7 - 1 = 6 by decide, show (2 ≤ 7) by decide, show 7 - 2 = 5 by decide, show (3 ≤ 7) by decide, show 7 - 3 = 4 by decide, show ¬ (7 = 1) by decide, show ¬ (7 = 2) by decide, show ¬ (7 = 3) by decide, show ¬ (7 = 4) by decide, show ¬ (7 = 5) by decide, show ¬ (7 = 6) by decide, show (7 = 7) by decide, show ¬ (7 = 8) by decide, ↓reduceIte, hA0, hA1, hA2, hA3, hA4, hA5, hA6, hA7]; norm_num
  · simp only [show (1 ≤ 8) by decide, show 8 - 1 = 7 by decide, show (2 ≤ 8) by decide, show 8 - 2 = 6 by decide, show (3 ≤ 8) by decide, show 8 - 3 = 5 by decide, show ¬ (8 = 1) by decide, show ¬ (8 = 2) by decide, show ¬ (8 = 3) by decide, show ¬ (8 = 4) by decide, show ¬ (8 = 5) by decide, show ¬ (8 = 6) by decide, show ¬ (8 = 7) by decide, show (8 = 8) by decide, ↓reduceIte, hA0, hA1, hA2, hA3, hA4, hA5, hA6, hA7, hA8]; norm_num
  · have hk9 : k + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 = k + 9 := by omega
    rw [hk9]
    simp only [A, PowerSeries.coeff_mk,
      show ¬ (k + 9 = 0) by omega, show ¬ (k + 9 = 1) by omega, show ¬ (k + 9 = 2) by omega,
      show ¬ (k + 9 = 3) by omega, show ¬ (k + 9 = 4) by omega, show ¬ (k + 9 = 5) by omega,
      show ¬ (k + 9 = 6) by omega, show ¬ (k + 9 = 7) by omega, show ¬ (k + 9 = 8) by omega,
      show 1 ≤ k + 9 by omega, show 2 ≤ k + 9 by omega, show 3 ≤ k + 9 by omega,
      show k + 9 - 1 = k + 8 by omega, show k + 9 - 2 = k + 7 by omega,
      show k + 9 - 3 = k + 6 by omega,
      show ¬ (k + 8 = 0) by omega, show ¬ (k + 7 = 0) by omega, show ¬ (k + 6 = 0) by omega,
      ↓reduceIte, mul_zero, sub_zero, add_zero]
    have hrec : (a (k + 9) : ℚ) = (a (k + 8) : ℚ) + 2 * (a (k + 7) : ℚ) - 2 * (a (k + 6) : ℚ) := by
      exact_mod_cast a_rec k
    linarith

end OMA.ProofA207142

theorem OMA.solution : type_of% @OMA.S_oeis_a207142.main :=
  ⟨OMA.ProofA207142.gf_eq, OMA.ProofA207142.closed_even, OMA.ProofA207142.closed_odd⟩
