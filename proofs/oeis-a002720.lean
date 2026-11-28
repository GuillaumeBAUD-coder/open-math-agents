import OMAStatements.S_oeis_a002720

/-! Proof of A002720, following David Radcliffe's argument on the OEIS entry.
Credit: @cjchaffin with Codex. We work with the totals of largest parts
and of all parts. Their coupled recurrences eliminate the auxiliary total
and give the same recurrence as partial permutations. -/

namespace Mo2720Structure
open OMA.S_oeis_a002720

private theorem sorted_top (p : Multiset ℕ) (hc : 0 < p.card) :
    ∃ l : List ℕ, p.sort (· ≥ ·) = p.sup :: l := by
  have hs := Multiset.pairwise_sort p (· ≥ ·)
  have hl := Multiset.length_sort (s := p) (· ≥ ·)
  cases hh : p.sort (· ≥ ·) with
  | nil => rw [hh] at hl; simp at hl; omega
  | cons a l =>
    rw [hh] at hs
    have ha : a ∈ p := (Multiset.mem_sort (r := (· ≥ ·))).mp (by rw [hh]; simp)
    have hmax : p.sup ≤ a := Multiset.sup_le.mpr fun x hx => by
      have hx' := (Multiset.mem_sort (r := (· ≥ ·))).mpr hx
      rw [hh, List.mem_cons] at hx'
      rcases hx' with rfl | h
      · exact le_rfl
      · exact (List.pairwise_cons.mp hs).1 _ h
    exact ⟨l, by rw [le_antisymm hmax (Multiset.le_sup ha)]⟩

theorem step_iff {n k : ℕ} (hk : 1 ≤ k) (p : Multiset ℕ) :
    p ∈ admissible (n+1) k ↔ ∃ q ∈ admissible n k, ∃ x ∈ q, p = (q.sup+x) ::ₘ q := by
  constructor
  · rintro ⟨hpos,hcard,hkP,hle,hdiff⟩
    obtain ⟨l, htop⟩ := sorted_top p (by omega)
    have hmem : p.sup ∈ p := (Multiset.mem_sort (r := (· ≥ ·))).mp (by rw [htop]; simp)
    obtain ⟨q, heq⟩ := Multiset.exists_cons_of_mem hmem
    let a := p.sup
    have he : p = a ::ₘ q := heq
    have hc : q.card = n+1 := by rw [he, Multiset.card_cons] at hcard; omega
    have hsub (x : ℕ) (hx : x ∈ q) : x ∈ p := he ▸ Multiset.mem_cons_of_mem hx
    have hmax (x : ℕ) (hx : x ∈ q) : x ≤ a := Multiset.le_sup (hsub x hx)
    obtain ⟨lq, hqtop⟩ := sorted_top q (by omega)
    have hs : p.sort (· ≥ ·) = a :: q.sort (· ≥ ·) := by
      calc
        _ = (a ::ₘ q).sort (· ≥ ·) := congrArg (fun s : Multiset ℕ => s.sort (· ≥ ·)) he
        _ = _ := Multiset.sort_cons _ _ _ hmax
    have hsm : q.sup ∈ q := (Multiset.mem_sort (r := (· ≥ ·))).mp (by rw [hqtop]; simp)
    have hsmpos : 0 < q.sup := lt_of_lt_of_le hk (hle _ (hsub _ hsm))
    have hsmle := hmax _ hsm
    have hh : a-q.sup ∈ p := by
      have H := hdiff 0 (by rw [hs, hqtop]; simp)
      simpa [hs,hqtop] using H
    have hsmall (y : ℕ) (hy : y ∈ p) (hna : y < a) : y ∈ q := by
      rw [he, Multiset.mem_cons] at hy
      exact hy.resolve_left (Nat.ne_of_lt hna)
    have hx := hsmall _ hh (by omega)
    have hgap := hpos _ hh
    have hkq := hsmall _ hkP (by have := hle _ (hsub _ hsm); omega)
    refine ⟨q, ⟨fun x hx => hpos _ (hsub x hx), hc, hkq, fun x hx => hle _ (hsub x hx), ?_⟩,
      a-q.sup, hx, ?_⟩
    · intro i hi
      let s := q.sort (· ≥ ·)
      have hm (j : ℕ) (hj : j < s.length) : s[j] ∈ q :=
        (Multiset.mem_sort (r := (· ≥ ·))).mp (List.getElem_mem hj)
      have hi' : i < s.length := by dsimp [s]; omega
      have h₂ := hpos _ (hsub _ (hm (i+1) hi))
      have h₁ := hmax _ (hm i hi')
      have H := hdiff (i+1) (by rw [hs]; simp only [List.length_cons]; omega)
      have H' : s[i] - s[i+1] ∈ p := by simpa only [hs, List.getElem_cons_succ, s] using H
      apply hsmall _ H'
      omega
    · have ha : q.sup + (a-q.sup) = a := by omega
      rw [ha]
      exact he
  · rintro ⟨q, ⟨hpq,hcq,hkq,hleq,hdq⟩, x,hx,rfl⟩
    let a := q.sup+x
    have hax : q.sup < a := by have := hpq x hx; dsimp [a]; omega
    have hbound (y : ℕ) (hy : y ∈ q) : y ≤ a := (Multiset.le_sup hy).trans hax.le
    have hs : (a ::ₘ q).sort (· ≥ ·) = a :: q.sort (· ≥ ·) :=
      Multiset.sort_cons _ _ _ hbound
    obtain ⟨l, htop⟩ := sorted_top q (by omega)
    refine ⟨?_, by simp [hcq], Multiset.mem_cons_of_mem hkq, ?_, ?_⟩
    · intro y hy
      rcases Multiset.mem_cons.mp hy with rfl | hy
      · change 0 < a; omega
      · exact hpq _ hy
    · intro y hy
      rcases Multiset.mem_cons.mp hy with rfl | hy
      · exact hbound _ hkq
      · exact hleq _ hy
    · intro i hi
      change i+1 < ((a ::ₘ q).sort (· ≥ ·)).length at hi
      change ((a ::ₘ q).sort (· ≥ ·))[i] - ((a ::ₘ q).sort (· ≥ ·))[i+1] ∈ a ::ₘ q
      cases i with
      | zero =>
        simpa only [hs, htop, List.getElem_cons_zero, List.getElem_cons_succ, a,
          Nat.add_sub_cancel_left] using (Multiset.mem_cons_of_mem (b := a) hx)
      | succ i =>
        have hi' : i+1 < (q.sort (· ≥ ·)).length := by rw [hs] at hi; simpa only [List.length_cons, Nat.succ_lt_succ_iff] using hi
        simpa only [hs, List.getElem_cons_succ] using Multiset.mem_cons_of_mem (b := a) (hdq i hi')

theorem nodup_of_mem {n k : ℕ} {p : Multiset ℕ} (hp : p ∈ admissible n k) : p.Nodup := by
  induction n generalizing p with
  | zero =>
    have hc : p.card = 1 := hp.2.1
    obtain ⟨x, rfl⟩ := Multiset.card_eq_one.mp hc
    exact Multiset.nodup_singleton x
  | succ n ih =>
    have hk : 1 ≤ k := hp.1 k hp.2.2.1
    obtain ⟨q, hq, x, hx, rfl⟩ := (step_iff hk p).mp hp
    refine Multiset.nodup_cons.mpr ⟨?_, ih hq⟩
    intro h
    have he := Multiset.le_sup h
    have hpos := hq.1 x hx
    omega

end Mo2720Structure

namespace A002720Rook
open Finset OMA.S_oeis_a002720

private def w (r c i : ℕ) : ℕ := r.choose i * c.choose i * i.factorial
private def rect (r c : ℕ) : ℕ := ∑ i ∈ range (r + 1), w r c i

private theorem w_step (r c i : ℕ) :
    w (r+1) (c+1) (i+1) = w r (c+1) (i+1) + (c+1) * w r c i := by
  simp only [w, Nat.choose_succ_succ' r i, Nat.factorial_succ]
  linear_combination (r.choose i * i.factorial) * (Nat.add_one_mul_choose_eq c i).symm

private theorem rect_step (r c : ℕ) :
    rect (r+1) (c+1) = rect r (c+1) + (c+1) * rect r c := by
  have tail : (∑ i ∈ range (r+1), w r (c+1) (i+1)) + w r (c+1) 0 = rect r (c+1) := by
    rw [← sum_range_succ', sum_range_succ]
    simp [rect, w]
  unfold rect at ⊢
  rw [sum_range_succ']
  simp only [w_step, sum_add_distrib, ← mul_sum]
  change _ = rect r (c+1) + (c+1) * rect r c
  rw [← tail]
  simp only [rect, w, Nat.choose_zero_right, Nat.factorial_zero, one_mul]
  omega

private theorem near_symm (n : ℕ) : rect (n+1) n = rect n (n+1) := by
  unfold rect
  rw [sum_range_succ]
  simp only [w, Nat.choose_succ_self, mul_zero, zero_mul, add_zero]
  exact sum_congr rfl fun i _ => by ring

private theorem diagonal (n : ℕ) : rect n n = a n := by simp [rect, w, a, sq]

theorem a_zero : a 0 = 1 := by decide
theorem a_one : a 1 = 2 := by decide

theorem a_recurrence (n : ℕ) :
    a (n+2) + (n+1)^2 * a n = (2*n+4) * a (n+1) := by
  have h₁ := rect_step n n
  have h₂ := rect_step (n+1) n
  have h₃ := rect_step (n+1) (n+1)
  rw [diagonal] at h₁
  rw [diagonal] at h₂
  rw [diagonal, ← near_symm, h₂] at h₃
  rw [near_symm] at h₃
  rw [diagonal] at h₁ h₃
  linear_combination h₃ - (n+1) * h₁

end A002720Rook

/-! Each admissible partition grows by adjoining its largest part plus an
existing part. Tracking both the sum of the maxima and the sum of all parts
gives a second-order recurrence. -/

namespace A002720Totals
open Finset OMA.S_oeis_a002720

private def grow (q : Multiset ℕ) (x : ℕ) := (q.sup+x) ::ₘ q
private def family (k : ℕ) : ℕ → Finset (Multiset ℕ)
  | 0 => {{k}}
  | n+1 => (family k n).biUnion (fun q => q.toFinset.image (grow q))

private theorem grow_sup (q : Multiset ℕ) (x : ℕ) : (grow q x).sup = q.sup+x := by
  rw [grow, Multiset.sup_cons, sup_eq_left.mpr (by omega)]

private theorem grow_injective {q r : Multiset ℕ} {x y : ℕ} (h : grow q x = grow r y) :
    q=r ∧ x=y := by
  have hm := congrArg Multiset.sup h
  rw [grow_sup, grow_sup] at hm
  unfold grow at h
  rw [hm, Multiset.cons_inj_right] at h
  subst r
  exact ⟨rfl, by omega⟩

private theorem family_zero {k : ℕ} (hk : 1 ≤ k) (p : Multiset ℕ) :
    p ∈ family k 0 ↔ p ∈ admissible 0 k := by
  simp only [family, mem_singleton]
  constructor
  · rintro rfl
    refine ⟨?_, by simp, by simp, ?_, ?_⟩
    · simpa using (show 0 < k by omega)
    · simp
    · intro i hi
      simp at hi
  · rintro ⟨_, hcard, hmem, _, _⟩
    obtain ⟨m, rfl⟩ := Multiset.card_eq_one.mp hcard
    simpa using (Multiset.mem_singleton.mp hmem).symm

private theorem exact_family {k : ℕ} (hk : 1 ≤ k)
    (hstep : ∀ n p, p ∈ admissible (n+1) k ↔
      ∃ q ∈ admissible n k, ∃ x ∈ q, p = grow q x) (n : ℕ) (p : Multiset ℕ) :
    p ∈ family k n ↔ p ∈ admissible n k := by
  induction n generalizing p with
  | zero => exact family_zero hk p
  | succ n ih =>
    rw [hstep]
    simp only [family, mem_biUnion, mem_image, Multiset.mem_toFinset, ih]
    constructor <;> rintro ⟨q,hq,x,hx,he⟩ <;> exact ⟨q,hq,x,hx,he.symm⟩

private def S (k n : ℕ) := ∑ p ∈ family k n, p.sup
private def H (k n : ℕ) := ∑ p ∈ family k n, p.sum

private theorem grow_fold (k n : ℕ) (f : Multiset ℕ → ℕ) :
    (∑ p ∈ family k (n+1), f p) = ∑ q ∈ family k n, ∑ x ∈ q.toFinset, f (grow q x) := by
  rw [family, sum_biUnion]
  · apply sum_congr rfl
    intro q _
    exact sum_image (fun _ _ _ _ h => (grow_injective h).2)
  · intro q _ r _ hqr
    apply Finset.disjoint_left.mpr
    intro p hp hpr
    obtain ⟨x, _, hx⟩ := mem_image.mp hp
    obtain ⟨y, _, hy⟩ := mem_image.mp hpr
    exact hqr (grow_injective (hx.trans hy.symm)).1

private theorem recs (k n : ℕ)
    (data : ∀ p ∈ family k n, p.Nodup ∧ p.card = n+1) :
    S k (n+1) = (n+1)*S k n + H k n ∧ H k (n+1) = S k (n+1)+(n+1)*H k n := by
  have hc (p) (hp : p ∈ family k n) : p.toFinset.card = n+1 :=
    (Multiset.toFinset_card_of_nodup (data p hp).1).trans (data p hp).2
  have hs (p) (hp : p ∈ family k n) : (∑ x ∈ p.toFinset, x) = p.sum := by
    change p.toFinset.sum id = p.sum
    rw [← Finset.sum_val p.toFinset, Multiset.toFinset_val, Multiset.dedup_eq_self.mpr (data p hp).1]
  constructor
  · unfold S H
    rw [grow_fold, mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro p hp
    simp_rw [grow_sup]
    rw [sum_add_distrib, sum_const, hs p hp, hc p hp, nsmul_eq_mul]
    rfl
  · unfold S H
    rw [grow_fold, grow_fold, mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro p hp
    simp only [grow, Multiset.sum_cons, Multiset.sup_cons, sup_eq_left.mpr (Nat.le_add_right _ _),
      sum_add_distrib, sum_const, nsmul_eq_mul, hc p hp]
    rfl

theorem result_of_steps
    (hstep : ∀ {n k : ℕ}, 1 ≤ k → ∀ p : Multiset ℕ, p ∈ admissible (n+1) k ↔
      ∃ q ∈ admissible n k, ∃ x ∈ q, p = (q.sup+x) ::ₘ q)
    (hnodup : ∀ {n k : ℕ} {p : Multiset ℕ}, p ∈ admissible n k → p.Nodup)
    (ha0 : a 0 = 1) (ha1 : a 1 = 2)
    (ha : ∀ n, a (n+2)+(n+1)^2*a n=(2*n+4)*a (n+1)) :
    type_of% @OMA.S_oeis_a002720.main := by
  intro n k hk
  have hF (m : ℕ) (p : Multiset ℕ) := exact_family hk (fun n p => hstep hk p) m p
  have hset : admissible n k = (family k n : Set (Multiset ℕ)) := by
    ext p
    exact (hF n p).symm
  rw [hset, finsum_mem_coe_finset]
  refine ⟨(family k n).finite_toSet, ?_⟩
  change S k n = a n*k
  clear hset
  have hr (m : ℕ) := recs k m (fun p hp => ⟨hnodup ((hF m p).mp hp), ((hF m p).mp hp).2.1⟩)
  induction n using Nat.twoStepInduction with
  | zero => simp [S, family, ha0]
  | one => rw [(hr 0).1]; simp [S, H, family, ha1, two_mul]
  | more n ih0 ih1 =>
    have hS := (hr n).1
    have hH := (hr n).2
    have hSS := (hr (n+1)).1
    have hnum := congrArg (fun x : ℕ => x*k) (ha n)
    change (a (n+2)+(n+1)^2*a n)*k = ((2*n+4)*a (n+1))*k at hnum
    rw [ih0, ih1] at hS
    rw [ih1] at hH hSS
    nlinarith only [hSS, hH, hnum, congrArg (fun x : ℕ => (n+1)*x) hS]

end A002720Totals

theorem OMA.solution : type_of% @OMA.S_oeis_a002720.main :=
  A002720Totals.result_of_steps Mo2720Structure.step_iff Mo2720Structure.nodup_of_mem
    A002720Rook.a_zero A002720Rook.a_one A002720Rook.a_recurrence
