import FormalConjectures.ErdosProblems.«348»

/-!
# Erdős 348: finite deletion thresholds for complete sequences

A nondecreasing natural-number sequence can remain complete after *every*
deletion of `m` indexed terms, and become incomplete after *every* deletion
of `n > m` terms, exactly when `m ≤ 1`.

We formalize Jesse Geneson's central-interval theorem and deletion
classification (arXiv:2609.25107, Theorems 2 and 1). The two positive
examples are the binary and Fibonacci sequences of Erdős and Graham; the
interval criterion is Brown's. To extend a complete finite deletion, we
translate a represented prefix sum into its central interval and reuse
the tail. Zero terms are handled by enumerating the surviving positive
indices, without changing the meaning of a deletion.
-/

/- Locate gaps in the subset sums of a finite prefix of a complete nondecreasing sequence.
The cuts below are indexed by the number of included (zero-based) terms. -/

namespace OMA.Central348
open Finset Filter

def total (b : ℕ → ℕ) (k : ℕ) := ∑ i ∈ range k, b i

def Rep (b : ℕ → ℕ) (k x : ℕ) : Prop :=
  ∃ s ⊆ range k, x = ∑ i ∈ s, b i

theorem total_mono (b : ℕ → ℕ) : Monotone (total b) := by
  intro i j hij
  exact sum_le_sum_of_subset_of_nonneg (range_mono hij) (by simp)

theorem rep_mono {b : ℕ → ℕ} {k l x : ℕ} (h : k ≤ l) : Rep b k x → Rep b l x := by
  rintro ⟨s, hs, hx⟩
  exact ⟨s, hs.trans (range_mono h), hx⟩

theorem reflect_rep {b : ℕ → ℕ} {k x : ℕ} (h : Rep b k x) : Rep b k (total b k - x) := by
  obtain ⟨s, hs, rfl⟩ := h
  refine ⟨range k \ s, sdiff_subset, ?_⟩
  have he := sum_sdiff hs (f := b)
  dsimp [total]
  omega

theorem small_rep {b : ℕ → ℕ} (hb : Monotone b) {k x : ℕ}
    (hx : x < b k) (h : x ∈ subseqSums' b) : Rep b k x := by
  obtain ⟨s, hs⟩ := h
  refine ⟨s, ?_, hs⟩
  intro i hi
  apply mem_range.mpr
  by_contra! hki
  have hle : b i ≤ ∑ j ∈ s, b j := single_le_sum (fun _ _ => Nat.zero_le _) hi
  have hk := hb hki
  omega

/-- A missing central integer lies less than T below a strictly earlier prefix total. -/
theorem locate {b : ℕ → ℕ} (hb : Monotone b) {T N x : ℕ} (hT : 0 < T)
    (hglobal : ∀ y, T ≤ y → y ∈ subseqSums' b) (hx : T ≤ x)
    (hhi : x + T ≤ total b N) (miss : ¬ Rep b N x) :
    ∃ j < N, x ≤ total b j ∧ total b j < x + T := by
  let W : ∃ i, x + T ≤ total b i := ⟨N,hhi⟩
  have hh := Nat.find_spec W
  have hN := Nat.find_min' W hhi
  generalize heq : Nat.find W = i at hh hN
  obtain _ | j := i
  · simp [total] at hh
    omega
  have hprev : total b j < x+T := Nat.lt_of_not_ge fun h =>
    (by have := Nat.find_min' W h; omega : False)
  have htot : total b (j+1) = total b j + b j := sum_range_succ _ _
  refine ⟨j, by omega, ?_, hprev⟩
  by_contra! hlt
  let y := total b (j+1) - x
  have hy : T ≤ y := by dsimp [y]; omega
  have hyb : y < b j := by dsimp [y]; omega
  have hr := rep_mono (b := b) (Nat.le_succ j) (small_rep hb hyb (hglobal y hy))
  have hcompl := reflect_rep hr
  have hval : total b (j+1)-y = x := by dsimp [y]; omega
  exact miss (rep_mono hN (hval ▸ hcompl))

/-- All globally represented values below T already have witnesses in one common prefix. -/
theorem finite_capture (b : ℕ → ℕ) (T : ℕ) :
    ∃ J, ∀ e < T, e ∈ subseqSums' b → Rep b J e := by
  induction T with
  | zero => simp
  | succ T ih =>
    obtain ⟨J, hJ⟩ := ih
    by_cases ht : T ∈ subseqSums' b
    · obtain ⟨s, hsum⟩ := ht
      obtain ⟨j, hj⟩ := exists_nat_subset_range s
      refine ⟨max J j, ?_⟩
      intro e he hglob
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ he) with h | rfl
      · exact rep_mono (le_max_left _ _) (hJ _ h hglob)
      · exact rep_mono (le_max_right _ _) ⟨s,hj,hsum⟩
    · refine ⟨J, ?_⟩
      intro e he hglob
      have hn : e ≠ T := fun h => ht (h ▸ hglob)
      exact hJ e (by omega) hglob

theorem total_gap (b : ℕ → ℕ) {j l : ℕ} (h : j < l) :
    total b j + b j ≤ total b l := by
  calc _ = total b (j+1) := (sum_range_succ _ _).symm
       _ ≤ _ := total_mono b h

/-- Late missing values of bounded spread sit below one common cut. Their reflected
labels are not even represented globally, since every small represented label was captured. -/
theorem localize_cluster {b : ℕ → ℕ} (hb : Monotone b) {T J N : ℕ}
    (hT : 0 < T) (hg : ∀ y, T ≤ y → y ∈ subseqSums' b)
    (hcap : ∀ e < T, e ∈ subseqSums' b → Rep b J e) (hbJ : 3*T < b J)
    (R : Finset ℕ) (hR : R.Nonempty)
    (hlarge : ∀ x ∈ R, total b J < x ∧ T ≤ x ∧ x+T ≤ total b N)
    (hmiss : ∀ x ∈ R, ¬ Rep b N x) (hspread : ∀ x ∈ R, ∀ y ∈ R, x ≤ y+2*T) :
    ∃ j < N, J < j ∧ ∀ x ∈ R, x ≤ total b j ∧ total b j < x+T ∧
      total b j - x ∉ subseqSums' b := by
  have cut (x) (hx : x ∈ R) : ∃ j < N, J < j ∧ x ≤ total b j ∧ total b j < x+T := by
    obtain ⟨hxJ, hTx, hxN⟩ := hlarge x hx
    obtain ⟨j,hj,hxj,hjt⟩ := locate hb hT hg hTx hxN (hmiss x hx)
    exact ⟨j,hj,lt_of_not_ge (fun h => (not_le_of_gt hxJ) (hxj.trans (total_mono b h))),hxj,hjt⟩
  obtain ⟨x,hx⟩ := hR
  obtain ⟨j,hj,hJj,hxj,hjx⟩ := cut x hx
  refine ⟨j,hj,hJj,?_⟩
  intro y hy
  obtain ⟨l,hl,hJl,hyl,hly⟩ := cut y hy
  have heq : l = j := by
    rcases lt_trichotomy l j with hlt | he | hlt
    · have gap := total_gap b hlt
      have big := hb hJl.le
      have close := hspread x hx y hy
      omega
    · exact he
    · have gap := total_gap b hlt
      have big := hb hJj.le
      have close := hspread y hy x hx
      omega
  subst l
  refine ⟨hyl,hly,?_⟩
  intro hrep
  have hc := reflect_rep (rep_mono hJj.le (hcap _ (by omega) hrep))
  have he : total b j - (total b j - y) = y := by omega
  exact hmiss y hy (rep_mono hj.le (he ▸ hc))

end OMA.Central348

/- Normalize a missing-sum state by moving a constant available block to its first occurrence. -/

namespace OMA.Central348
open Finset

def Distinct (b : ℕ → ℕ) (j N : ℕ) : Prop := ∃ l, j ≤ l ∧ l < N ∧ b j < b l

theorem normalize_cut {b : ℕ → ℕ} (hb : Monotone b) {T M j N : ℕ}
    (hTM : T ≤ total b M) (hjN : j < N) (hg : b M < b j)
    (E : Finset ℕ) (hE : ∀ e ∈ E, e < T) (hmiss : ∀ e ∈ E, ¬ Rep b N (total b j-e)) :
    ∃ p N', M < p ∧ p ≤ j ∧ p < N' ∧ (∀ e ∈ E, ¬ Rep b N' (total b p-e)) ∧
      (Distinct b p N' ↔ Distinct b j N) ∧ (Distinct b p N' ∨ b (p-1) < b p) := by
  classical
  by_cases hd : Distinct b j N
  · exact ⟨j,N,lt_of_not_ge (fun h => (not_le_of_gt hg) (hb h)),le_rfl,hjN,hmiss,Iff.rfl,Or.inl hd⟩
  let existsValue : ∃ p, b p = b j := ⟨j, rfl⟩
  let p := Nat.find existsValue
  have bp : b p = b j := Nat.find_spec existsValue
  have hp : p ≤ j := Nat.find_min' existsValue rfl
  have hMp : M < p := lt_of_not_ge (fun h => (not_le_of_gt hg) (bp ▸ hb h))
  have hfirst : b (p-1) < b p := by
    apply lt_of_le_of_ne (hb (Nat.sub_le ..))
    intro he
    have hl := Nat.find_min' existsValue (he.trans bp)
    change p ≤ p-1 at hl
    omega
  have const (r : ℕ) (hr : p ≤ r) (hr' : r ≤ j) : b r = b j :=
    le_antisymm (hb hr') (bp ▸ hb hr)
  have sum_gap : ∑ i ∈ Ioc p j, b i = ∑ i ∈ Ico p j, b i := by
    have co : ∑ i ∈ Ico p j, b i = ∑ _i ∈ Ico p j, b j :=
      sum_congr rfl fun i hi => const i (mem_Ico.mp hi).1 (mem_Ico.mp hi).2.le
    have oc : ∑ i ∈ Ioc p j, b i = ∑ _i ∈ Ioc p j, b j :=
      sum_congr rfl fun i hi => const i (mem_Ioc.mp hi).1.le (mem_Ioc.mp hi).2
    rw [co,oc]
    simp
  have norm : ¬ Distinct b p (p+1) := by
    rintro ⟨l,hl,hl',hlt⟩
    have : l = p := by omega
    exact (lt_irrefl _ (this ▸ hlt))
  refine ⟨p,p+1,hMp,hp,by omega,?_,iff_of_false norm hd,Or.inr hfirst⟩
  intro e he hrep
  obtain ⟨s,hs,hval⟩ := hrep
  have dis : Disjoint s (Ioc p j) := by
    apply disjoint_left.mpr
    intro i hi hI
    have hsi := mem_range.mp (hs hi)
    have hh := (mem_Ioc.mp hI).1
    omega
  apply hmiss e he
  refine ⟨s ∪ Ioc p j, union_subset (hs.trans (range_mono (by omega))) ?_, ?_⟩
  · intro i hi
    exact mem_range.mpr (lt_of_le_of_lt (mem_Ioc.mp hi).2 hjN)
  · rw [sum_union dis, sum_gap]
    have hsum : total b p + ∑ i ∈ Ico p j, b i = total b j := sum_range_add_sum_Ico b hp
    have hte := hE e he
    have htp := total_mono b hMp.le
    omega

end OMA.Central348

/- Geneson, arXiv:2609.25107, Sections 4.2–4.4: transitions on finite sets
of labels of gaps in the subset sums of a nondecreasing sequence. -/

namespace OMA.Central348
open Finset Filter

structure GapState (b : ℕ → ℕ) (T j N : ℕ) (E : Finset ℕ) : Prop where
  cut_lt : j < N
  ne : E.Nonempty
  small : ∀ e ∈ E, e < T
  global_gap : ∀ e ∈ E, e ∉ subseqSums' b
  prefix_gap : ∀ e ∈ E, ¬Rep b N (total b j - e)

theorem add_rep {b : ℕ → ℕ} {j k N x : ℕ} (hjk : j ≤ k) (hkN : k < N)
    (hx : Rep b j x) : Rep b N (x + b k) := by
  obtain ⟨s, hs, he⟩ := hx
  have hks : k ∉ s := fun h => (Nat.not_lt.mpr hjk) (mem_range.mp (hs h))
  exact ⟨insert k s, insert_subset (mem_range.mpr hkN) (hs.trans (range_mono (by omega))),
    by rw [sum_insert hks]; omega⟩

/-- The gap to the first strictly larger value is at most every gap label. -/
theorem jump_le {b : ℕ → ℕ} (hm : Monotone b) {T j N : ℕ} {E : Finset ℕ}
    (hs : GapState b T j N E) (hg : ∀ y, T ≤ y → y ∈ subseqSums' b) (ha : T ≤ b j)
    (l : ℕ) (hstep : ∀ i, j ≤ i → i < l → b i = b j) (e : ℕ) (he : e ∈ E) :
    b l ≤ b j + e := by
  by_contra! hbig
  obtain ⟨s, hx⟩ := hg (b j + e) (by omega)
  have hsub : s ⊆ range j := by
    intro i hi
    apply mem_range.mpr
    by_contra! hji
    have hle := single_le_sum (f := b) (fun i _ => Nat.zero_le _) hi
    have hil : i < l := lt_of_not_ge fun h => (by have := hm h; omega : False)
    have hval := hstep i hji hil
    have hsum := sum_erase_add s b hi
    exact hs.global_gap e he ⟨s.erase i, by omega⟩
  have hr := add_rep (b := b) (j := j) le_rfl hs.cut_lt (reflect_rep (show Rep b j (b j+e) from ⟨s,hsub,hx⟩))
  have hh : (∑ i ∈ s, b i) ≤ total b j := sum_le_sum_of_subset hsub
  exact hs.prefix_gap e he (by convert hr using 1; omega)

noncomputable def gapScore (b : ℕ → ℕ) (T j N : ℕ) (E : Finset ℕ) : ℕ := by
  classical
  exact (T+1)*E.card + if Distinct b j N then T else E.sup id

theorem score_bound {b : ℕ → ℕ} {T j N : ℕ} {E : Finset ℕ}
    (hs : GapState b T j N E) : gapScore b T j N E ≤ (T+1)*T + T := by
  classical
  have hcard : E.card ≤ T := (card_le_card (show E ⊆ range T from fun i hi =>
    mem_range.mpr (hs.small i hi))).trans_eq (card_range T)
  have hm := Nat.mul_le_mul_left (T+1) hcard
  have hsup : E.sup id ≤ T := Finset.sup_le fun i hi => (hs.small i hi).le
  simp only [gapScore]
  split <;> omega

/-- Pull a cluster back across either of two available terms (possibly equal).
The two maps give the new labels and track their exact changes. -/
theorem pull_cluster {b : ℕ → ℕ} (hm : Monotone b) {T M j N k : ℕ} {E : Finset ℕ}
    (hT : 0 < T) (hg : ∀ y, T ≤ y → y ∈ subseqSums' b)
    (hcap : ∀ e < T, e ∈ subseqSums' b → Rep b M e) (hbM : 3*T < b M)
    (hs : GapState b T j N E) (hjk : j ≤ k) (hkN : k < N)
    (hbjk : b k ≤ b j+T) (ha : T ≤ b j)
    (hspace : b j + (total b M + 4*T + 1) ≤ total b j) :
    ∃ (l : ℕ) (F : Finset ℕ) (f g : ℕ → ℕ), M < l ∧ GapState b T l j F ∧
      (∀ e ∈ E, f e ∈ F ∧ f e + total b j = total b l + b j + e) ∧
      (∀ e ∈ E, g e ∈ F ∧ g e + total b j = total b l + b k + e) := by
  classical
  let u (r e : ℕ) := total b j - b r - e
  let R := E.image (u j) ∪ E.image (u k)
  have hsource {x : ℕ} (hx : x ∈ R) : ∃ r, (r = j ∨ r = k) ∧ ∃ e ∈ E, x = u r e := by
    rcases mem_union.mp hx with h | h
    · obtain ⟨e, he, rfl⟩ := mem_image.mp h
      exact ⟨j, Or.inl rfl, e, he, rfl⟩
    · obtain ⟨e, he, rfl⟩ := mem_image.mp h
      exact ⟨k, Or.inr rfl, e, he, rfl⟩
  have hbnd {r : ℕ} (hr : r = j ∨ r = k) : b j ≤ b r ∧ b r ≤ b j + T := by
    rcases hr with rfl | rfl
    · omega
    · exact ⟨hm hjk, hbjk⟩
  have hbnds {x : ℕ} (hx : x ∈ R) :
      total b j ≤ x + b j + 2*T ∧ x + b j ≤ total b j ∧ total b M < x ∧ T ≤ x := by
    obtain ⟨r, hr, e, he, rfl⟩ := hsource hx
    have := hbnd hr
    have := hs.small e he
    dsimp [u]
    omega
  have hgap {x : ℕ} (hx : x ∈ R) : ¬Rep b j x := by
    obtain ⟨r, hr, e, he, rfl⟩ := hsource hx
    have hbounds := hbnd hr
    have := hs.small e he
    have hidx : j ≤ r ∧ r < N := by rcases hr with h | h <;> omega
    intro hrep
    have hh := add_rep hidx.1 hidx.2 hrep
    apply hs.prefix_gap e he
    convert hh using 1
    dsimp [u]
    omega
  have hR : R.Nonempty := by
    obtain ⟨e, he⟩ := hs.ne
    exact ⟨u j e, mem_union_left _ (mem_image_of_mem _ he)⟩
  obtain ⟨l, hlj, hMl, hloc⟩ := localize_cluster hm hT hg hcap hbM R hR
    (fun x hx => by have := hbnds hx; omega)
    (fun _ => hgap)
    (fun x hx y hy => by have := hbnds hx; have := hbnds hy; omega)
  let reflect (x : ℕ) := total b l - x
  let F := R.image reflect
  have hF : GapState b T l j F := by
    refine ⟨hlj, hR.image _, ?_, ?_, ?_⟩
    · intro v hv
      obtain ⟨x, hx, rfl⟩ := mem_image.mp hv
      obtain ⟨_, hh, _⟩ := hloc x hx
      dsimp [reflect]
      omega
    · intro v hv
      obtain ⟨x, hx, rfl⟩ := mem_image.mp hv
      exact (hloc x hx).2.2
    · intro v hv
      obtain ⟨x, hx, rfl⟩ := mem_image.mp hv
      have hb := (hloc x hx).1
      apply (show total b l - reflect x = x by dsimp [reflect]; omega) ▸ hgap hx
  refine ⟨l, F, fun e => reflect (u j e), fun e => reflect (u k e), hMl, hF, ?_, ?_⟩
  · intro e he
    have hu : u j e ∈ R := mem_union_left _ (mem_image_of_mem _ he)
    refine ⟨mem_image_of_mem _ hu, ?_⟩
    have := (hloc _ hu).1
    have := hs.small e he
    dsimp [reflect, u] at *
    omega
  · intro e he
    have hu : u k e ∈ R := mem_union_right _ (mem_image_of_mem _ he)
    refine ⟨mem_image_of_mem _ hu, ?_⟩
    have := (hloc _ hu).1
    have := hs.small e he
    dsimp [reflect, u] at *
    omega

end OMA.Central348

/- Pulling a normalized family of gaps back to an earlier cut strictly raises its score. -/

namespace OMA.Central348
open Finset

theorem score_after_pull {b : ℕ → ℕ} (hm : Monotone b) {T j N l k : ℕ}
    {E F : Finset ℕ} {f g : ℕ → ℕ}
    (hg : ∀ y, T ≤ y → y ∈ subseqSums' b)
    (hs : GapState b T j N E) (hF : GapState b T l j F) (hbl : T < b l)
    (hk : Distinct b j N → b j < b k)
    (hnorm : Distinct b j N ∨ b (j-1) < b j)
    (hf : ∀ e ∈ E, f e ∈ F ∧ f e + total b j = total b l + b j + e)
    (hgmap : ∀ e ∈ E, g e ∈ F ∧ g e + total b j = total b l + b k + e) :
    gapScore b T j N E < gapScore b T l j F := by
  classical
  have inj : Set.InjOn f E := by
    intro x hx y hy h
    have := (hf x hx).2
    have := (hf y hy).2
    omega
  have sub : E.image f ⊆ F := image_subset_iff.mpr fun e he => (hf e he).1
  have him : (E.image f).card = E.card := card_image_of_injOn inj
  have hc : E.card ≤ F.card := him ▸ card_le_card sub
  have hmul := Nat.mul_le_mul_left (T+1) hc
  obtain ⟨m,hmE,hmMax⟩ := exists_mem_eq_sup E hs.ne id
  change E.sup id = m at hmMax
  have hsmall := hs.small m hmE
  have hmF := (hf m hmE).1
  have hmaxF : f m ≤ F.sup id := le_sup (f := id) hmF
  by_cases hD : Distinct b j N
  · have hnew : g m ∉ E.image f := by
      intro hh
      obtain ⟨e,he,heq⟩ := mem_image.mp hh
      have he_le : e ≤ m := hmMax ▸ (le_sup (f := id) he)
      have := (hgmap m hmE).2
      have := (hf e he).2
      have := hk hD
      omega
    have hstrict : (E.image f).card < F.card :=
      card_lt_card (ssubset_iff_exists_subset_erase.mpr
        ⟨g m, (hgmap m hmE).1, fun e he =>
          mem_erase.mpr ⟨fun h => hnew (h ▸ he), sub he⟩⟩)
    have hstep := Nat.mul_le_mul_left (T+1) (show E.card + 1 ≤ F.card by omega)
    rw [Nat.mul_add, Nat.mul_one] at hstep
    simp only [gapScore, if_pos hD]
    split <;> omega
  · have hbefore := hnorm.resolve_left hD
    by_cases distinct' : Distinct b l j
    · simp only [gapScore, if_neg hD, if_pos distinct', hmMax]
      omega
    · have hconstant (i : ℕ) (hli : l ≤ i) (hij : i < j) : b i = b l := by
        apply le_antisymm _ (hm hli)
        exact le_of_not_gt fun h => distinct' ⟨i,hli,hij,h⟩
      have jump := jump_le hm hF hg hbl.le j hconstant (f m) hmF
      have label := (hf m hmE).2
      have hcut := hF.cut_lt
      have hj : j = l+1 := by
        by_contra h
        have hfirst := total_gap b (Nat.lt_succ_self l)
        have hsecond := total_gap b (show l+1 < j by omega)
        have hmono := hm (Nat.le_succ l)
        change total b l + b l ≤ total b (l+1) at hfirst
        change b l ≤ b (l+1) at hmono
        omega
      have hp : j - 1 = l := by omega
      rw [hp] at hbefore
      have hsum : total b j = total b l + b l := by
        rw [hj]; exact sum_range_succ _ _
      simp only [gapScore, if_neg hD, if_neg distinct',hmMax]
      omega

end OMA.Central348

/- The two transitions of Geneson's central-interval proof strictly increase
a bounded integer. We work with arbitrarily large cut indices directly. -/

namespace OMA.Central348
open Finset Filter

private theorem lower_total (b : ℕ → ℕ) (hp : ∀ i, 0 < b i) (k : ℕ) :
    k ≤ total b k := by
  induction k with
  | zero => omega
  | succ k ih =>
    have h := hp k
    have ht : total b (k+1) = total b k + b k := sum_range_succ ..
    omega

private theorem capture_far {b : ℕ → ℕ} (hm : Monotone b) (hu : ∀ C, ∃ i, C ≤ b i)
    (T M : ℕ) : ∃ J, b M < b J ∧ 3*T < b J ∧
      ∀ e < T, e ∈ subseqSums' b → Rep b J e := by
  obtain ⟨L, hL⟩ := finite_capture b T
  obtain ⟨i, hi⟩ := hu (max (b M) (3*T)+1)
  have hij := hm (le_max_left i L)
  exact ⟨max i L, by omega, by omega, fun e he hh => rep_mono (le_max_right _ _) (hL e he hh)⟩

private theorem choose_available {b : ℕ → ℕ} (hm : Monotone b) {T j N : ℕ} {E : Finset ℕ}
    (hs : GapState b T j N E) (hg : ∀ y, T ≤ y → y ∈ subseqSums' b) (ha : T ≤ b j) :
    ∃ k, j ≤ k ∧ k < N ∧ b k ≤ b j + T ∧ (Distinct b j N → b j < b k) := by
  classical
  by_cases hd : Distinct b j N
  · let h : ∃ k, j ≤ k ∧ k < N ∧ b j < b k := hd
    obtain ⟨hjk, hkN, hv⟩ := Nat.find_spec h
    have hp : ∀ i, j ≤ i → i < Nat.find h → b i = b j := by
      intro i hji hik
      apply le_antisymm _ (hm hji)
      by_contra! hr
      exact (not_le_of_gt hik) (Nat.find_min' h ⟨hji, by omega, hr⟩)
    obtain ⟨e, he⟩ := hs.ne
    have := jump_le hm hs hg ha _ hp e he
    have := hs.small e he
    exact ⟨Nat.find h, hjk, hkN, by omega, fun _ => hv⟩
  · exact ⟨j, le_rfl, hs.cut_lt, by omega, fun h => (hd h).elim⟩

private theorem normalized_after {b : ℕ → ℕ} (hm : Monotone b) {T M j N : ℕ} {E : Finset ℕ}
    (hTM : T ≤ total b M) (hb : b M < b j) (hs : GapState b T j N E) :
    ∃ p N', M < p ∧ GapState b T p N' E ∧
      (Distinct b p N' ∨ b (p-1) < b p) ∧ gapScore b T p N' E = gapScore b T j N E := by
  classical
  obtain ⟨p, N', hMp, _, hpN, hgaps, hequiv, hnorm⟩ :=
    normalize_cut hm hTM hs.cut_lt hb E hs.small hs.prefix_gap
  exact ⟨p, N', hMp, ⟨hpN, hs.ne, hs.small, hs.global_gap, hgaps⟩, hnorm,
    by simp only [gapScore, hequiv]⟩

private theorem initial_large {b : ℕ → ℕ} (hm : Monotone b) (hp : ∀ i, 0 < b i)
    (hu : ∀ C, ∃ i, C ≤ b i) {T : ℕ} (hT : 0 < T)
    (hg : ∀ y, T ≤ y → y ∈ subseqSums' b)
    (hbad : ∀ K, ∃ N x, K ≤ N ∧ T ≤ x ∧ x+T ≤ total b N ∧ ¬Rep b N x) (M : ℕ) :
    ∃ (j N : ℕ) (E : Finset ℕ), M ≤ j ∧ GapState b T j N E ∧
      (Distinct b j N ∨ b (j-1) < b j) := by
  classical
  let M' := max M T
  obtain ⟨J, hMJ, hbJ, hcap⟩ := capture_far hm hu T M'
  obtain ⟨K, hK⟩ := hu (total b J+1)
  obtain ⟨N, x, hKN, hTx, hxT, hmiss⟩ := hbad K
  have hNx : b N ≤ x := le_of_not_gt fun h => hmiss (small_rep hm h (hg _ hTx))
  have hJx := hm hKN
  have hbig : total b J < x := by omega
  obtain ⟨j, hjN, hJj, hj⟩ := localize_cluster hm hT hg hcap hbJ {x} (by simp)
    (by simpa using And.intro hbig (And.intro hTx hxT)) (by simpa using hmiss) (by simp)
  obtain ⟨hxl, hlt, hglob⟩ := hj x (by simp)
  let e := total b j - x
  have hs : GapState b T j N {e} := by
    refine ⟨hjN, by simp, ?_, ?_, ?_⟩
    · simpa [e] using (show total b j - x < T by omega)
    · simpa [e] using hglob
    · have he : total b j - e = x := by dsimp [e]; omega
      simpa [he] using hmiss
  obtain ⟨j', N', hMj, hnew, hnorm, _⟩ := normalized_after hm (M := M')
    ((le_max_right M T).trans (lower_total b hp M')) (hMJ.trans_le (hm hJj.le)) hs
  exact ⟨j', N', {e}, (le_max_left _ _).trans hMj.le, hnew, hnorm⟩

private theorem step_large {b : ℕ → ℕ} (hm : Monotone b) (hp : ∀ i, 0 < b i)
    (hu : ∀ C, ∃ i, C ≤ b i) {T : ℕ} (hT : 0 < T)
    (hg : ∀ y, T ≤ y → y ∈ subseqSums' b)
    (hslack : ∀ C, ∀ᶠ k in atTop, b k + C ≤ total b k) (M : ℕ) :
    ∃ K, ∀ {j N : ℕ} {E : Finset ℕ}, K ≤ j → GapState b T j N E →
      (Distinct b j N ∨ b (j-1) < b j) →
      ∃ (p N' : ℕ) (F : Finset ℕ), M ≤ p ∧ GapState b T p N' F ∧
        (Distinct b p N' ∨ b (p-1) < b p) ∧ gapScore b T j N E < gapScore b T p N' F := by
  classical
  let M' := max M T
  obtain ⟨J, hMJ, hbJ, hcap⟩ := capture_far hm hu T M'
  obtain ⟨K, hK⟩ := eventually_atTop.mp (hslack (total b J + 4*T + 1))
  refine ⟨max K J, ?_⟩
  intro j N E hKj hs hnorm
  have hbj := hm (show J ≤ j by omega)
  have hspace := hK j (by omega)
  obtain ⟨k, hjk, hkN, hbk, hdiff⟩ := choose_available hm hs hg (by omega)
  obtain ⟨l, F, f, g, hJl, hF, hf, hgm⟩ :=
    pull_cluster hm hT hg hcap hbJ hs hjk hkN hbk (by omega) hspace
  have hbl := hm hJl.le
  have hscore := score_after_pull hm hg hs hF (by omega : T < b l) hdiff hnorm hf hgm
  obtain ⟨p, N', hMp, hnew, hnorm', heq⟩ := normalized_after hm (M := M')
    ((le_max_right M T).trans (lower_total b hp M')) (hMJ.trans_le hbl) hF
  exact ⟨p, N', F, (le_max_left _ _).trans hMp.le, hnew, hnorm', heq ▸ hscore⟩

/-- Geneson's Theorem 2 for unbounded positive sequences: the original
completeness threshold works for the central intervals of all late prefixes. -/
theorem central_same_threshold {b : ℕ → ℕ} (hm : Monotone b) (hp : ∀ i, 0 < b i)
    (hu : ∀ C, ∃ i, C ≤ b i) {T : ℕ} (hT : 0 < T)
    (hg : ∀ y, T ≤ y → y ∈ subseqSums' b) (hslack : ∀ C, ∀ᶠ k in atTop, b k + C ≤ total b k) :
    ∀ᶠ N in atTop, ∀ x, T ≤ x → x+T ≤ total b N → Rep b N x := by
  classical
  by_contra hn
  have hbad (K : ℕ) : ∃ N x, K ≤ N ∧ T ≤ x ∧ x+T ≤ total b N ∧ ¬Rep b N x := by
    by_contra h
    apply hn
    exact eventually_atTop.mpr ⟨K, fun N hKN x hx hh => by
      by_contra hnr
      exact h ⟨N, x, hKN, hx, hh, hnr⟩⟩
  have many (s : ℕ) : ∀ M, ∃ (j N : ℕ) (E : Finset ℕ), M ≤ j ∧ GapState b T j N E ∧
      (Distinct b j N ∨ b (j-1) < b j) ∧ s ≤ gapScore b T j N E := by
    induction s with
    | zero =>
      intro M
      obtain ⟨j, N, E, hj, hE, hn⟩ := initial_large hm hp hu hT hg hbad M
      exact ⟨j, N, E, hj, hE, hn, Nat.zero_le _⟩
    | succ s ih =>
      intro M
      obtain ⟨K, hstep⟩ := step_large hm hp hu hT hg hslack M
      obtain ⟨j, N, E, hj, hE, hn, hscore⟩ := ih K
      obtain ⟨p, N', F, hp, hF, hn', hscore'⟩ := hstep hj hE hn
      exact ⟨p, N', F, hp, hF, hn', by omega⟩
  obtain ⟨j, N, E, _, hE, _, hh⟩ := many ((T+1)*T + T + 1) 0
  have := score_bound hE
  omega

theorem plain_intervals (b : ℕ → ℕ) (hm : Monotone b) (hp : ∀ i, 0 < b i)
    (hu : ∀ C, ∃ i, C ≤ b i) (hc : IsAddCompleteNatSeq' b)
    (hslack : ∀ C, ∀ᶠ k in atTop, b k + C ≤ ∑ i ∈ range k, b i) :
    ∃ T, ∀ᶠ k in atTop, ∀ u, T ≤ u → u+T ≤ ∑ i ∈ range k, b i →
      ∃ s : Finset ℕ, s ⊆ range k ∧ u = ∑ i ∈ s, b i := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp hc
  exact ⟨T+1, central_same_threshold hm hp hu (by omega) (fun y hy => hT y (by omega)) hslack⟩

end OMA.Central348

/- The binary and Fibonacci constructions of Erdős–Graham. The Fibonacci gap
induction follows Graham as presented in §3 of Geneson, arXiv:2609.25107. -/

namespace OMA.Constructions348
open Finset Filter

private theorem prefix_covers (a : ℕ → ℕ)
    (h : ∀ k, a k ≤ (∑ i ∈ range k, a i) + 1) (k n : ℕ)
    (hn : n ≤ ∑ i ∈ range k, a i) :
    ∃ s : Finset ℕ, s ⊆ range k ∧ n = ∑ i ∈ s, a i := by
  induction k generalizing n with
  | zero =>
    exact ⟨∅, by simp, by simpa using hn⟩
  | succ k ih =>
    rw [sum_range_succ] at hn
    by_cases hs : n ≤ ∑ i ∈ range k, a i
    · obtain ⟨s, hsub, heq⟩ := ih n hs
      exact ⟨s, hsub.trans (range_mono (by omega)), heq⟩
    · have hk := h k
      obtain ⟨s, hsub, heq⟩ := ih (n - a k) (by omega)
      have hks : k ∉ s := fun hh => (by simpa using hsub hh : False)
      exact ⟨insert k s, insert_subset (by simp) (hsub.trans (range_mono (by omega))),
        by rw [sum_insert hks]; omega⟩

private theorem represented_survivors {a : ℕ → ℕ} {D : Finset ℕ} {v : ℕ}
    (hv : v ∈ subseqSums' (Function.updateFinset a D 0)) :
    ∃ S : Finset ℕ, Disjoint S D ∧ v = ∑ i ∈ S, a i := by
  obtain ⟨s, hs⟩ := hv
  refine ⟨s.filter (fun i => i ∉ D), ?_, ?_⟩
  · exact disjoint_left.mpr fun i hi => (mem_filter.mp hi).2
  · simpa [sum_filter, Function.updateFinset_def, ite_not] using hs

private theorem total_with_omitted {a : ℕ → ℕ} {s : Finset ℕ} {j k : ℕ}
    (hsub : s ⊆ range k) (hj : j < k) (hjs : j ∉ s) :
    (∑ i ∈ s, a i) + a j ≤ ∑ i ∈ range k, a i := by
  have hh : insert j s ⊆ range k := insert_subset (mem_range.mpr hj) hsub
  simpa [sum_insert hjs, Nat.add_comm] using sum_le_sum_of_subset (f := a) hh

private theorem prefix_for_sum {a : ℕ → ℕ} (ha : Monotone a) {s : Finset ℕ} {k : ℕ}
    (h : (∑ i ∈ s, a i) < a k) : s ⊆ range k := by
  intro i hi
  apply mem_range.mpr
  by_contra! hki
  exact (h.not_ge ((ha hki).trans (single_le_sum (fun j _ => Nat.zero_le (a j)) hi)))

private theorem binary_prefix (k : ℕ) : (∑ i ∈ range k, 2 ^ i : ℕ) + 1 = 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [sum_range_succ, pow_succ]; omega

theorem binary_witness (n : ℕ) (hn : 0 < n) :
    ∃ a : ℕ → ℕ, Monotone a ∧
      (∀ s : Finset ℕ, s.card = 0 → IsAddCompleteNatSeq' (Function.updateFinset a s 0)) ∧
      ∀ t : Finset ℕ, t.card = n → ¬ IsAddCompleteNatSeq' (Function.updateFinset a t 0) := by
  let a (i : ℕ) : ℕ := 2 ^ i
  have hmono : Monotone a := fun _ _ hij => Nat.pow_le_pow_right (by decide) hij
  refine ⟨a, hmono, ?_, ?_⟩
  · intro s hs
    have hs' : s = ∅ := card_eq_zero.mp hs
    subst s
    rw [Function.updateFinset_empty]
    apply Eventually.of_forall
    intro u
    have hsum := binary_prefix (u+1)
    have hpow := Nat.lt_two_pow_self (n := u+1)
    obtain ⟨S, _, hS⟩ := prefix_covers a (fun j => (binary_prefix j).symm.le)
      (u+1) u (by dsimp [a]; omega)
    exact ⟨S, hS⟩
  · intro t ht hc
    obtain ⟨j, hj⟩ := card_pos.mp (ht ▸ hn : 0 < t.card)
    obtain ⟨N, hN⟩ := eventually_atTop.1 hc
    let k := N+j+1
    have hpow := Nat.lt_two_pow_self (n := k)
    have hbig : N ≤ a k - 1 := by dsimp [a, k] at *; omega
    obtain ⟨S, hdis, hS⟩ := represented_survivors (hN _ hbig)
    have hlt : (∑ i ∈ S, a i) < a k := by rw [← hS]; dsimp [a]; omega
    have hbound := total_with_omitted (a := a) (prefix_for_sum hmono hlt)
      (show j < k by dsimp [k]; omega) (fun h => disjoint_left.mp hdis h hj)
    have hsum := binary_prefix k
    have hpos : 0 < a j := Nat.pow_pos (by decide)
    change (∑ i ∈ range k, a i) + 1 = a k at hsum
    omega

private def fibTerm (i : ℕ) := Nat.fib (i+1)

private theorem fib_rec (k : ℕ) : fibTerm (k+2) = fibTerm k + fibTerm (k+1) :=
  Nat.fib_add_two

private theorem fib_pos (j : ℕ) : 0 < fibTerm j := Nat.fib_pos.mpr (by omega)

private theorem fib_mono : Monotone fibTerm :=
  fun _ _ hij => Nat.fib_mono (Nat.succ_le_succ hij)

private theorem fib_prefix (k : ℕ) : (∑ i ∈ range k, fibTerm i) + 1 = fibTerm (k+1) := by
  induction k with
  | zero => simp [fibTerm]
  | succ k ih => rw [sum_range_succ, fib_rec]; omega

private theorem fib_deleted_total (j k : ℕ) :
    (∑ i ∈ range k, Function.updateFinset fibTerm {j} 0 i) +
      (if j < k then fibTerm j else 0) = ∑ i ∈ range k, fibTerm i := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, sum_range_succ]
    rcases lt_trichotomy j k with h | rfl | h
    · simp [h, h.trans_le (Nat.le_succ _), Function.updateFinset, h.ne'] at ih ⊢
      omega
    · simp [Function.updateFinset] at ih ⊢
      omega
    · simp [not_lt.mpr h.le, Nat.not_le.mpr h, Function.updateFinset, h.ne] at ih ⊢
      omega

private theorem fib_one_complete (j : ℕ) :
    IsAddCompleteNatSeq' (Function.updateFinset fibTerm {j} 0) := by
  let a := Function.updateFinset fibTerm {j} 0
  have hinter : ∀ k, a k ≤ (∑ i ∈ range k, a i) + 1 := by
    intro k
    have hp := fib_prefix k
    have hs := fib_deleted_total j k
    change (∑ i ∈ range k, a i) + _ = _ at hs
    rcases lt_trichotomy j k with h | rfl | h
    · obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
      have hl := fib_mono (show j ≤ l by omega)
      rw [if_pos h] at hs
      rw [fib_rec] at hp
      have hval : a (l+1) = fibTerm (l+1) := by simp [a, Function.updateFinset, h.ne']
      change a (l+1) ≤ _
      omega
    · simp [a, Function.updateFinset]
    · rw [if_neg (not_lt.mpr h.le)] at hs
      have hm := fib_mono (show k ≤ k+1 by omega)
      have hval : a k = fibTerm k := by simp [a, Function.updateFinset, h.ne]
      omega
  apply Eventually.of_forall
  intro u
  let k := u + fibTerm j + 3
  have hp := fib_prefix k
  have hs := fib_deleted_total j k
  change (∑ i ∈ range k, a i) + _ = _ at hs
  have hhigh := Nat.le_fib_add_one (k+1+1)
  change k+1+1 ≤ fibTerm (k+1) + 1 at hhigh
  have hupper : (if j < k then fibTerm j else 0) ≤ fibTerm j := by split <;> omega
  obtain ⟨s, _, heq⟩ := prefix_covers a hinter k u (by dsimp [k] at *; omega)
  exact ⟨s, heq⟩

private theorem fib_missing {D : Finset ℕ} {i j : ℕ} (hij : i < j)
    (hi : i ∈ D) (hj : j ∈ D) (t : ℕ) :
    fibTerm (j+2*t+1) - 1 ∉ subseqSums' (Function.updateFinset fibTerm D 0) := by
  suffices h : ∀ S : Finset ℕ, Disjoint S D →
      fibTerm (j+2*t+1) - 1 ≠ ∑ r ∈ S, fibTerm r by
    intro hr
    obtain ⟨S, hd, heq⟩ := represented_survivors hr
    exact h S hd heq
  induction t with
  | zero =>
    simp only [Nat.mul_zero, Nat.add_zero]
    intro S hd heq
    have hp := fib_pos (j+1)
    have hsub := prefix_for_sum fib_mono (show (∑ r ∈ S, fibTerm r) < fibTerm (j+1) by omega)
    have hsj : j ∉ S := fun h => disjoint_left.mp hd h hj
    have hsub' : S ⊆ range j := by
      intro r hr
      have := mem_range.mp (hsub hr)
      have : r ≠ j := fun he => hsj (he ▸ hr)
      exact mem_range.mpr (by omega)
    have hb := total_with_omitted (a := fibTerm) hsub' hij (fun h => disjoint_left.mp hd h hi)
    have := fib_prefix j
    have := fib_pos i
    omega
  | succ t ih =>
    let k := j+2*(t+1)
    intro S hd heq
    change fibTerm (k+1) - 1 = ∑ r ∈ S, fibTerm r at heq
    have hp := fib_pos (k+1)
    have hsub := prefix_for_sum fib_mono (show (∑ r ∈ S, fibTerm r) < fibTerm (k+1) by omega)
    have hkS : k ∈ S := by
      by_contra hn
      have hsub' : S ⊆ range k := fun r hr => mem_range.mpr (by
        have := mem_range.mp (hsub hr)
        have : r ≠ k := fun he => hn (he ▸ hr)
        omega)
      have hb := total_with_omitted (a := fibTerm) hsub' (show i < k by dsimp [k]; omega)
        (fun h => disjoint_left.mp hd h hi)
      have := fib_prefix k
      have := fib_pos i
      omega
    have hrec : fibTerm (k+1) = fibTerm (j+2*t+1) + fibTerm k := by
      have hk : k = (j+2*t+1)+1 := by dsimp [k]; omega
      rw [hk, fib_rec]
    have herase := sum_erase_add _ fibTerm hkS
    have hprior := fib_pos (j+2*t+1)
    exact ih (S.erase k) (hd.mono_left (erase_subset ..)) (by omega)

theorem fibonacci_witness (n : ℕ) (hn : 1 < n) :
    ∃ a : ℕ → ℕ, Monotone a ∧
      (∀ s : Finset ℕ, s.card = 1 → IsAddCompleteNatSeq' (Function.updateFinset a s 0)) ∧
      ∀ t : Finset ℕ, t.card = n → ¬ IsAddCompleteNatSeq' (Function.updateFinset a t 0) := by
  refine ⟨fibTerm, fib_mono, ?_, ?_⟩
  · intro s hs
    obtain ⟨j, rfl⟩ := card_eq_one.mp hs
    exact fib_one_complete j
  · intro D hD hc
    obtain ⟨i, j, hi, hj, hij⟩ := one_lt_card_iff.mp (hD ▸ hn : 1 < D.card)
    obtain ⟨i, j, hi, hj, hlt⟩ : ∃ i j, i ∈ D ∧ j ∈ D ∧ i < j := by
      rcases lt_or_gt_of_ne hij with h | h
      · exact ⟨i, j, hi, hj, h⟩
      · exact ⟨j, i, hj, hi, h⟩
    obtain ⟨N, hN⟩ := eventually_atTop.1 hc
    have hb := Nat.le_fib_add_one (j+2*(N+1)+1+1)
    change _ ≤ fibTerm (j+2*(N+1)+1) + 1 at hb
    exact fib_missing hlt hi hj (N+1) (hN _ (by omega))

end OMA.Constructions348

/- A direct interval-shift argument for the deletion-extension conclusion of
Geneson, arXiv:2609.25107, Proposition 5, conditional on its central intervals. -/

namespace OMA.Extend348
open Finset Filter

theorem reps_iff (a : ℕ → ℕ) (D : Finset ℕ) (v : ℕ) :
    v ∈ subseqSums' (Function.updateFinset a D 0) ↔
    ∃ S : Finset ℕ, Disjoint S D ∧ v = ∑ i ∈ S, a i := by
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨s.filter (fun i => i ∉ D), disjoint_left.mpr (fun i hi => (mem_filter.mp hi).2), ?_⟩
    simpa [sum_filter, Function.updateFinset_def, ite_not] using hs
  · rintro ⟨s, hd, hs⟩
    refine ⟨s, hs.trans (sum_congr rfl fun i hi => ?_)⟩
    simp [Function.updateFinset, disjoint_left.mp hd hi]

def Central (a : ℕ → ℕ) (D : Finset ℕ) (T k : ℕ) :=
  ∀ u, T ≤ u → u + T ≤ ∑ r ∈ range k \ D, a r →
    ∃ s : Finset ℕ, s ⊆ range k \ D ∧ u = ∑ r ∈ s, a r

/-- Transfer an eventual representation after a pair deletion by changing only
the prefix. The translated sum has a representation after deleting D and j. -/
theorem extend_at (a : ℕ → ℕ) (D : Finset ℕ) (T k i j : ℕ)
    (hD : D ⊆ range k) (hi : i < k) (hj : k ≤ j)
    (hlarge : (∑ r ∈ D, a r) + 2*T ≤ a i) (hcentral : Central a D T k)
    (hpair : IsAddCompleteNatSeq' (Function.updateFinset a {i,j} 0)) :
    IsAddCompleteNatSeq' (Function.updateFinset a (insert j D) 0) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hpair
  apply eventually_atTop.mpr
  refine ⟨N+T, fun x hx => ?_⟩
  obtain ⟨s, hdis, hs⟩ := (reps_iff a {i,j} _).mp (hN (x-T) (by omega))
  let p := s ∩ range k
  let q := s \ range k
  have hp_sub : p ⊆ range k := inter_subset_right
  have hi_not : i ∉ p := fun h => disjoint_left.mp hdis (mem_inter.mp h).1 (by simp)
  have hp_bound : (∑ r ∈ p, a r) + a i ≤ ∑ r ∈ range k, a r := by
    have hsub := insert_subset (mem_range.mpr hi) hp_sub
    simpa [sum_insert hi_not, Nat.add_comm] using sum_le_sum_of_subset (f := a) hsub
  have hsplit := sum_sdiff (f := a) hD
  obtain ⟨p', hsub, hp'⟩ := hcentral ((∑ r ∈ p, a r)+T) (by omega) (by omega)
  have hsep : Disjoint p' q := disjoint_left.mpr fun r hr hrq =>
    (mem_sdiff.mp hrq).2 (mem_sdiff.mp (hsub hr)).1
  apply (reps_iff ..).mpr
  refine ⟨p' ∪ q, disjoint_left.mpr ?_, ?_⟩
  · intro r hr hbad
    rcases mem_union.mp hr with hp' | hq
    · obtain ⟨hrk, hrd⟩ := mem_sdiff.mp (hsub hp')
      rcases mem_insert.mp hbad with rfl | h
      · exact (Nat.not_lt.mpr hj) (mem_range.mp hrk)
      · exact hrd h
    · obtain ⟨hrs, hrk⟩ := mem_sdiff.mp hq
      rcases mem_insert.mp hbad with rfl | h
      · exact disjoint_left.mp hdis hrs (by simp)
      · exact hrk (hD h)
  · rw [sum_union hsep]
    have hsum : (∑ r ∈ p, a r) + (∑ r ∈ q, a r) = ∑ r ∈ s, a r :=
      sum_inter_add_sum_sdiff s (range k) a
    omega

/-- Every complete finite deletion of an unbounded sequence can be enlarged if
it has central intervals and every pair deletion preserves completeness. -/
theorem extend_complete (a : ℕ → ℕ) (ha : ∀ C, ∃ i, C ≤ a i) (D : Finset ℕ)
    (hc : ∃ T, ∀ᶠ k in atTop, Central a D T k)
    (hpair : ∀ E : Finset ℕ, E.card = 2 →
      IsAddCompleteNatSeq' (Function.updateFinset a E 0)) :
    ∃ j ∉ D, IsAddCompleteNatSeq' (Function.updateFinset a (insert j D) 0) := by
  obtain ⟨T, hT⟩ := hc
  obtain ⟨K, hK⟩ := eventually_atTop.mp hT
  obtain ⟨i, hi⟩ := ha ((∑ r ∈ D, a r)+2*T)
  obtain ⟨d, hd⟩ := exists_nat_subset_range D
  let k := max (max K d) (i+1)
  have hdk : D ⊆ range k := hd.trans (range_mono (by dsimp [k]; omega))
  have hik : i < k := by dsimp [k]; omega
  exact ⟨k, fun hk => (lt_irrefl _ (mem_range.mp (hdk hk))),
    extend_at a D T k i k hdk hik le_rfl hi (hK k (by dsimp [k]; omega))
      (hpair {i,k} (by simp [hik.ne]))⟩

theorem complete_restore {a : ℕ → ℕ} {D E : Finset ℕ} (hDE : D ⊆ E)
    (h : IsAddCompleteNatSeq' (Function.updateFinset a E 0)) :
    IsAddCompleteNatSeq' (Function.updateFinset a D 0) :=
  h.mono fun v hv => by
    obtain ⟨s, hs, heq⟩ := (reps_iff ..).mp hv
    exact (reps_iff ..).mpr ⟨s, hs.mono_right hDE, heq⟩

theorem complete_of_card_le {a : ℕ → ℕ} {m : ℕ}
    (hm : ∀ E : Finset ℕ, E.card = m → IsAddCompleteNatSeq' (Function.updateFinset a E 0))
    {D : Finset ℕ} (hD : D.card ≤ m) :
    IsAddCompleteNatSeq' (Function.updateFinset a D 0) := by
  obtain ⟨E, hDE, hE⟩ := Infinite.exists_superset_card_eq D m hD
  exact complete_restore hDE (hm E hE)

/-- Geneson, Lemma 3 in original-index coordinates: zeros and deletions need
not be reindexed. The natural-number inequality expresses divergent slack. -/
theorem slack_of_singletons (a : ℕ → ℕ) (hm : Monotone a)
    (ha : ∀ C, ∃ i, C ≤ a i)
    (hsingle : ∀ i : ℕ, IsAddCompleteNatSeq' (Function.updateFinset a {i} 0))
    (D : Finset ℕ) (C : ℕ) :
    ∀ᶠ k in atTop, a k + C ≤ ∑ r ∈ range k \ D, a r := by
  obtain ⟨i, hi⟩ := ha (C + (∑ r ∈ D, a r) + 1)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hsingle i)
  obtain ⟨l, hl⟩ := ha N
  let b := max l (i+1)
  have hNb := hl.trans (hm (show l ≤ b by dsimp [b]; omega))
  obtain ⟨d, hd⟩ := exists_nat_subset_range D
  refine eventually_atTop.mpr ⟨max d (b+1), fun k hk => ?_⟩
  have hD : D ⊆ range k := hd.trans (range_mono (by omega))
  have hiK : i ∈ range k := mem_range.mpr (by dsimp [b] at *; omega)
  let P := range k \ {i}
  have hbP : b ∈ P := mem_sdiff.mpr ⟨mem_range.mpr (by omega), by dsimp [b]; simp; omega⟩
  have hNS := hNb.trans (single_le_sum (f := a) (fun r _ => Nat.zero_le _) hbP)
  obtain ⟨s, hs, hsum⟩ := (reps_iff ..).mp (hN ((∑ r ∈ P, a r)+1) (by omega))
  have hnext : a k ≤ (∑ r ∈ P, a r)+1 := by
    by_contra! hsmall
    have hsub : s ⊆ P := by
      intro r hr
      have hbound := single_le_sum (f := a) (fun r _ => Nat.zero_le _) hr
      refine mem_sdiff.mpr ⟨mem_range.mpr ?_, fun h => disjoint_left.mp hs hr h⟩
      by_contra! hkr
      have := hm hkr
      omega
    have := sum_le_sum_of_subset (f := a) hsub
    omega
  have hsplit₁ := sum_sdiff (f := a) (singleton_subset_iff.mpr hiK)
  change (∑ r ∈ P, a r) + _ = _ at hsplit₁
  rw [sum_singleton] at hsplit₁
  have hsplit₂ := sum_sdiff (f := a) hD
  omega

private theorem bounded_deletion (a : ℕ → ℕ) (hm : Monotone a) (hb : BddAbove (Set.range a))
    (hc : IsAddCompleteNatSeq' a) (n : ℕ) :
    ∃ D : Finset ℕ, D.card = n ∧ IsAddCompleteNatSeq' (Function.updateFinset a D 0) := by
  obtain ⟨k, hk⟩ := Nat.sSup_mem (Set.range_nonempty a) hb
  have hconst (i : ℕ) (hi : k ≤ i) : a i = a k :=
    le_antisymm (hk ▸ le_csSup hb (Set.mem_range_self i)) (hm hi)
  let f : ℕ ↪ ℕ := ⟨fun i => if i < k then i else i+n, by
    intro p q heq
    dsimp only at heq
    split_ifs at heq <;> omega⟩
  have hval (i : ℕ) : a (f i) = a i := by
    change a (if i < k then i else i+n) = a i
    split_ifs with h
    · rfl
    · exact (hconst _ (by omega)).trans (hconst _ (by omega)).symm
  refine ⟨Ico k (k+n), by simp, hc.mono (fun x hx => ?_)⟩
  obtain ⟨s, heq⟩ := hx
  apply (reps_iff ..).mpr
  refine ⟨s.map f, disjoint_left.mpr ?_, ?_⟩
  · intro r hr hrD
    obtain ⟨i, _, rfl⟩ := mem_map.mp hr
    obtain ⟨hlo, hhi⟩ := mem_Ico.mp hrD
    change k ≤ (if i < k then i else i+n) at hlo
    change (if i < k then i else i+n) < k+n at hhi
    split_ifs at hlo hhi <;> omega
  · simpa [sum_map, hval] using heq

theorem exclusion_of_central (a : ℕ → ℕ) (hm : Monotone a) (m n : ℕ) (hm2 : 2 ≤ m)
    (hcomplete : ∀ E : Finset ℕ, E.card = m → IsAddCompleteNatSeq' (Function.updateFinset a E 0))
    (hcentral : (∀ C, ∃ i, C ≤ a i) → ∀ D : Finset ℕ,
      IsAddCompleteNatSeq' (Function.updateFinset a D 0) →
      (∀ C, ∀ᶠ k in atTop, a k + C ≤ ∑ r ∈ range k \ D, a r) →
      ∃ T, ∀ᶠ k in atTop, Central a D T k) :
    ∃ D : Finset ℕ, D.card = n ∧ IsAddCompleteNatSeq' (Function.updateFinset a D 0) := by
  have hzero : IsAddCompleteNatSeq' (Function.updateFinset a ∅ 0) :=
    complete_of_card_le hcomplete (by simp)
  by_cases hu : ∀ C, ∃ i, C ≤ a i
  · induction n with
    | zero => exact ⟨∅, by simp, hzero⟩
    | succ n ih =>
      obtain ⟨D, hcard, hD⟩ := ih
      have hs (i : ℕ) : IsAddCompleteNatSeq' (Function.updateFinset a {i} 0) :=
        complete_of_card_le hcomplete (by simp; omega)
      obtain ⟨j, hj, hnew⟩ := extend_complete a hu D
        (hcentral hu D hD (slack_of_singletons a hm hu hs D)) fun E hE =>
          complete_of_card_le hcomplete (by omega)
      exact ⟨insert j D, by simp [hj, hcard], hnew⟩
  · push Not at hu
    obtain ⟨C, hC⟩ := hu
    have hbounded : BddAbove (Set.range a) := by
      refine ⟨C, ?_⟩
      rintro v ⟨i, rfl⟩
      exact (hC i).le
    exact bounded_deletion a hm hbounded (by simpa using hzero) n

end OMA.Extend348

namespace OMA.Extend348
open Finset Filter

/-- The interval property: the unbounded case of Geneson's
central-interval theorem, stated for an ordinary positive monotone sequence. -/
def PlainIntervals : Prop :=
  ∀ b : ℕ → ℕ, Monotone b → (∀ i, 0 < b i) → (∀ C, ∃ i, C ≤ b i) →
    IsAddCompleteNatSeq' b → (∀ C, ∀ᶠ k in atTop, b k + C ≤ ∑ i ∈ range k, b i) →
    ∃ T, ∀ᶠ k in atTop, ∀ u, T ≤ u → u + T ≤ ∑ i ∈ range k, b i →
      ∃ s : Finset ℕ, s ⊆ range k ∧ u = ∑ i ∈ s, b i

theorem central_after_deletion (main : PlainIntervals) (a : ℕ → ℕ) (hm : Monotone a)
    (hu : ∀ C, ∃ i, C ≤ a i) (D : Finset ℕ)
    (hc : IsAddCompleteNatSeq' (Function.updateFinset a D 0))
    (hslack : ∀ C, ∀ᶠ k in atTop, a k + C ≤ ∑ r ∈ range k \ D, a r) :
    ∃ T, ∀ᶠ k in atTop, Central a D T k := by
  classical
  let P (i : ℕ) := i ∉ D ∧ 0 < a i
  obtain ⟨K, hK⟩ := exists_nat_subset_range D
  obtain ⟨p, hp⟩ := hu 1
  have htail : ∀ i ≥ max K p, P i := by
    intro i hi
    exact ⟨fun hiD => (by have := mem_range.mp (hK hiD); omega),
      hp.trans (hm (by omega))⟩
  have hinf : (Set.ofPred P).Infinite := (Set.Ici_infinite (max K p)).mono fun i hi => htail i hi
  let f : ℕ ↪ ℕ := ⟨Nat.nth P, Nat.nth_injective hinf⟩
  let b (i : ℕ) := a (f i)
  have hf (i : ℕ) : P (f i) := Nat.nth_mem_of_infinite hinf i
  have hstrict : StrictMono f := Nat.nth_strictMono hinf
  have hfcount {i : ℕ} (hi : P i) : f (Nat.count P i) = i := Nat.nth_count hi
  have hmap (k : ℕ) : (range (Nat.count P k)).map f =
      (range k \ D).filter (fun r => 0 < a r) := by
    ext r
    constructor
    · intro hr
      obtain ⟨l, hl, rfl⟩ := mem_map.mp hr
      have hlt : f l < k := (Nat.lt_nth_iff_count_lt hinf).mp (mem_range.mp hl)
      exact mem_filter.mpr ⟨mem_sdiff.mpr ⟨mem_range.mpr hlt, (hf l).1⟩, (hf l).2⟩
    · intro hr
      obtain ⟨hr, hpos⟩ := mem_filter.mp hr
      obtain ⟨hr, hD⟩ := mem_sdiff.mp hr
      have he := hfcount ⟨hD, hpos⟩
      apply Finset.mem_map.mpr
      exact ⟨Nat.count P r, mem_range.mpr ((Nat.lt_nth_iff_count_lt hinf).mpr
        (by change f _ < k; rw [he]; exact mem_range.mp hr)), he⟩
  have htrim (S : Finset ℕ) : (∑ i ∈ S.filter (fun r => 0 < a r), a i) = ∑ i ∈ S, a i := by
    apply sum_subset (filter_subset _ _)
    intro i hi hn
    simpa [hi] using hn
  have hsum (k : ℕ) : (∑ i ∈ range (Nat.count P k), b i) = ∑ r ∈ range k \ D, a r := by
    calc
      _ = ∑ r ∈ (range (Nat.count P k)).map f, a r := by simp [sum_map, b]
      _ = _ := (congrArg (fun s : Finset ℕ => ∑ i ∈ s, a i) (hmap k)).trans (htrim _)
  have hcomp : IsAddCompleteNatSeq' b := hc.mono fun x hx => by
    obtain ⟨S, hD, hS⟩ := (reps_iff ..).mp hx
    let A := S.filter (fun i => 0 < a i)
    have hP {r : ℕ} (hr : r ∈ A) : P r :=
      ⟨disjoint_left.mp hD (mem_filter.mp hr).1, (mem_filter.mp hr).2⟩
    refine ⟨A.image (Nat.count P), ?_⟩
    rw [sum_image (fun i hi j hj hij => by
      have := congrArg f hij
      simpa [hfcount (hP hi), hfcount (hP hj)] using this)]
    exact (hS.trans (htrim _).symm).trans (sum_congr rfl fun i hi => by
      change a i = a (f (Nat.count P i))
      rw [hfcount (hP hi)])
  have hbs (C : ℕ) : ∀ᶠ k in atTop, b k + C ≤ ∑ i ∈ range k, b i := by
    obtain ⟨K, hK⟩ := eventually_atTop.mp (hslack C)
    apply eventually_atTop.mpr
    refine ⟨K, fun k hk => ?_⟩
    have he := hsum (f k)
    rw [show Nat.count P (f k) = k from Nat.count_nth_of_infinite hinf k] at he
    exact he.symm ▸ hK (f k) (hk.trans (hstrict.id_le k))
  have hbu (C : ℕ) : ∃ i, C ≤ b i := by
    obtain ⟨i, hi⟩ := hu C
    exact ⟨i, hi.trans (hm (hstrict.id_le i))⟩
  obtain ⟨T, hT⟩ := main b (hm.comp hstrict.monotone) (fun i => (hf i).2) hbu hcomp hbs
  obtain ⟨L, hL⟩ := eventually_atTop.mp hT
  refine ⟨T, eventually_atTop.mpr ⟨f L, fun k hk => ?_⟩⟩
  intro u huT hbudget
  have hLk : L ≤ Nat.count P k := by
    have := Nat.count_monotone P hk
    rwa [show Nat.count P (f L) = L from Nat.count_nth_of_infinite hinf L] at this
  obtain ⟨s, hs, heq⟩ := hL _ hLk u huT (by rw [hsum]; exact hbudget)
  have hs' : s.map f ⊆ (range (Nat.count P k)).map f := by
    intro r hr
    obtain ⟨i, hi, rfl⟩ := mem_map.mp hr
    exact mem_map_of_mem f (hs hi)
  rw [hmap k] at hs'
  exact ⟨s.map f, hs'.trans (filter_subset _ _), by simpa [sum_map, b] using heq⟩

end OMA.Extend348

/- Classification after the unbounded positive-sequence central-interval theorem. -/

namespace OMA.Extend348

/-- The Fibonacci construction, for every deletion size greater than one. -/
def FibonacciWitnesses : Prop :=
  ∀ n : ℕ, 1 < n → ∃ a : ℕ → ℕ, Monotone a ∧
    (∀ s : Finset ℕ, s.card = 1 → IsAddCompleteNatSeq' (Function.updateFinset a s 0)) ∧
    ∀ t : Finset ℕ, t.card = n → ¬ IsAddCompleteNatSeq' (Function.updateFinset a t 0)

theorem classification_of_witness_and_intervals (hFib : FibonacciWitnesses) (main : PlainIntervals) :
    type_of% @Erdos348.erdos_348 := by
  ext ⟨m,n⟩
  constructor
  · rintro ⟨m', n', hmn, a, hm, hgood, hbad, heq⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
    refine ⟨hmn, ?_⟩
    by_contra! hlarge
    obtain ⟨D, hcard, hD⟩ := exclusion_of_central a hm m' n' (by omega) hgood
      (central_after_deletion main a hm)
    exact hbad D hcard hD
  · rintro ⟨hmn, hsmall⟩
    rcases (by omega : m = 0 ∨ m = 1) with rfl | rfl
    · obtain ⟨a, hm, hgood, hbad⟩ := OMA.Constructions348.binary_witness n hmn
      exact ⟨0, n, hmn, a, hm, hgood, hbad, rfl⟩
    · obtain ⟨a, hm, hgood, hbad⟩ := hFib n hmn
      exact ⟨1, n, hmn, a, hm, hgood, hbad, rfl⟩

theorem classification_of_plain_intervals (main : PlainIntervals) : type_of% @Erdos348.erdos_348 :=
  classification_of_witness_and_intervals OMA.Constructions348.fibonacci_witness main

end OMA.Extend348

theorem OMA.solution : type_of% @Erdos348.erdos_348 :=
  OMA.Extend348.classification_of_plain_intervals OMA.Central348.plain_intervals
