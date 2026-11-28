import OMAStatements.S_oeis_a381717

/-! Credit: @unserus

Constant blocks with distinct sums exist iff some ordering has distinct run-sums.
Take a blocking with the fewest blocks; merging any two blocks of one value v would
repeat a sum, which bounds the number of v-blocks by half the total plus one, so the
blocks can be ordered with no two equal values adjacent; then the runs are the blocks. -/

namespace OMAA381717Helpers

theorem arrange {α : Type*} [DecidableEq α] : ∀ (n : ℕ) (S : Multiset α), Multiset.card S = n →
    ∀ x : Option α, (∀ a, 2 * S.count a ≤ n + 1) → (∀ y, x = some y → 2 * S.count y ≤ n) →
    ∃ l : List α, (l : Multiset α) = S ∧ l.IsChain (· ≠ ·) ∧ ∀ y, x = some y → l.head? ≠ some y := by
  intro n
  induction n with
  | zero =>
    intro S hS x _ _
    refine ⟨[], ?_, List.isChain_nil, by simp⟩
    simpa using (Multiset.card_eq_zero.mp hS).symm
  | succ n ih =>
    intro S hS x h1 h2
    -- candidates: elements of S different from x
    let T := S.filter (fun a => x ≠ some a)
    have hT : T ≠ 0 := by
      intro hT0
      have hall : ∀ a ∈ S, x = some a := by
        intro a ha
        by_contra hne
        have : a ∈ T := Multiset.mem_filter.mpr ⟨ha, hne⟩
        rw [hT0] at this; simp at this
      obtain ⟨b, hb⟩ := Multiset.card_pos_iff_exists_mem.mp (by omega : 0 < Multiset.card S)
      have hxb := hall b hb
      have : S = Multiset.replicate (n+1) b := by
        rw [Multiset.eq_replicate]; refine ⟨hS, fun c hc => ?_⟩
        have := hall c hc; rw [hxb] at this; exact (Option.some_inj.mp this).symm
      have h := h2 b hxb
      rw [this, Multiset.count_replicate_self] at h; omega
    obtain ⟨a, haT, hamax⟩ := Finset.exists_max_image T.toFinset (fun a => S.count a)
      (Multiset.toFinset_nonempty.mpr hT)
    rw [Multiset.mem_toFinset] at haT
    have haS : a ∈ S := (Multiset.mem_filter.mp haT).1
    have hax : x ≠ some a := (Multiset.mem_filter.mp haT).2
    have hA : ∀ c, 2 * (S.erase a).count c ≤ n + 1 := by
      intro c
      by_cases hca : c = a
      · subst hca
        have := h1 c
        rw [Multiset.count_erase_self]; omega
      · rw [Multiset.count_erase_of_ne hca]
        by_cases hxc : x = some c
        · have := h2 c hxc; omega
        · have hcS : c ∈ S ∨ c ∉ S := em _
          rcases hcS with hcS | hcS
          · have hcT : c ∈ T := Multiset.mem_filter.mpr ⟨hcS, hxc⟩
            have hle := hamax c (Multiset.mem_toFinset.mpr hcT)
            have hsum : S.count a + S.count c ≤ n + 1 := by
              rw [← hS]
              have hle2 : Multiset.replicate (S.count a) a + Multiset.replicate (S.count c) c ≤ S := by
                rw [Multiset.le_iff_count]
                intro z
                rw [Multiset.count_add, Multiset.count_replicate, Multiset.count_replicate]
                split_ifs <;> simp_all
              have := Multiset.card_le_card hle2
              simpa using this
            omega
          · rw [Multiset.count_eq_zero_of_notMem hcS]; omega
    have hB : ∀ y, some a = some y → 2 * (S.erase a).count y ≤ n := by
      intro y hy
      obtain rfl : a = y := Option.some_inj.mp hy
      have := h1 a
      rw [Multiset.count_erase_self]
      omega
    obtain ⟨l, hl, hc, hh⟩ := ih (S.erase a) (by rw [Multiset.card_erase_of_mem haS]; simp [hS])
      (some a) hA hB
    refine ⟨a :: l, ?_, ?_, ?_⟩
    · rw [← Multiset.cons_coe, hl, Multiset.cons_erase haS]
    · cases l with
      | nil => exact List.isChain_singleton a
      | cons b l =>
        refine List.IsChain.cons_cons ?_ hc
        intro hab; exact hh a rfl (by simp [hab])
    · intro y hy; rw [hy] at hax; simpa using fun h => hax (by rw [h])

theorem group_rep (g : List ℕ) (h : g.IsChain fun x y => (x == y) = true) (hn : g ≠ []) :
    ∃ v, (Multiset.ofList g) = Multiset.replicate (Multiset.card (Multiset.ofList g)) v := by
  have h' : g.IsChain (· = ·) := by
    refine List.IsChain.imp ?_ h
    intro a b hab; simpa using hab
  obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil hn
  refine ⟨a, ?_⟩
  rw [List.isChain_cons_eq_iff_eq_replicate] at h'
  rw [h', ← List.replicate_succ, Multiset.coe_card, List.length_replicate, Multiset.coe_replicate]

theorem sum_map_coe (L : List (List ℕ)) :
    (Multiset.ofList (L.map Multiset.ofList)).sum = Multiset.ofList L.flatten := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.map_cons, ← Multiset.cons_coe, Multiset.sum_cons, ih, List.flatten_cons,
      ← Multiset.coe_add]

theorem back (l : List ℕ) (h : ((l.splitBy (· == ·)).map List.sum).Nodup) :
    ∃ P : Multiset (Multiset ℕ), P.sum = (l : Multiset ℕ) ∧
    (∀ b ∈ P, b ≠ 0 ∧ ∃ v, b = Multiset.replicate (Multiset.card b) v) ∧
    (P.map Multiset.sum).Nodup := by
  refine ⟨Multiset.ofList ((l.splitBy (· == ·)).map Multiset.ofList), ?_, ?_, ?_⟩
  · rw [sum_map_coe, List.flatten_splitBy]
  · intro b hb
    rw [Multiset.mem_coe, List.mem_map] at hb
    obtain ⟨g, hg, rfl⟩ := hb
    refine ⟨?_, group_rep g (List.isChain_of_mem_splitBy hg) (List.ne_nil_of_mem_splitBy hg)⟩
    simpa using List.ne_nil_of_mem_splitBy hg
  · rw [Multiset.map_coe, Multiset.coe_nodup, List.map_map]
    convert h using 2
    funext g
    exact Multiset.sum_coe g

section Fwd

def sm (p : ℕ × ℕ) : ℕ := p.2 * p.1

def tot (L : List (ℕ × ℕ)) : Multiset ℕ := (L.map (fun p => Multiset.replicate p.2 p.1)).sum

def Valid (L : List (ℕ × ℕ)) : Prop := (∀ p ∈ L, 0 < p.1 ∧ 0 < p.2) ∧ (L.map sm).Nodup

def MC (L : List (ℕ × ℕ)) : Prop :=
  ∀ p ∈ L, ∀ q ∈ L, p ≠ q → p.1 = q.1 → sm p + sm q ∈ L.map sm

theorem tot_perm {L L' : List (ℕ × ℕ)} (h : List.Perm L L') : tot L = tot L' :=
  (h.map _).sum_eq

theorem tot_cons (p : ℕ × ℕ) (L : List (ℕ × ℕ)) :
    tot (p :: L) = Multiset.replicate p.2 p.1 + tot L := by
  simp [tot]

theorem reduce : ∀ (n : ℕ) (L : List (ℕ × ℕ)), L.length = n → Valid L →
    ∃ L' : List (ℕ × ℕ), Valid L' ∧ tot L' = tot L ∧ MC L' := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro L hn hV
    by_cases hM : MC L
    · exact ⟨L, hV, rfl, hM⟩
    · simp only [MC, not_forall] at hM
      obtain ⟨p, hp, q, hq, hpq, hv, hnot⟩ := hM
      have hq' : q ∈ L.erase p := (List.mem_erase_of_ne (Ne.symm hpq)).mpr hq
      set R := (L.erase p).erase q with hR
      have hperm : List.Perm L (p :: q :: R) :=
        (List.perm_cons_erase hp).trans (List.Perm.cons p (List.perm_cons_erase hq'))
      have hsub : R.Sublist L := ((L.erase p).erase_sublist).trans (L.erase_sublist)
      have hlen : (p :: q :: R).length = n := by rw [← hn]; exact hperm.length_eq.symm
      let new : ℕ × ℕ := (p.1, p.2 + q.2)
      have hsm : sm new = sm p + sm q := by simp only [sm, new]; rw [hv]; ring
      have hV' : Valid (new :: R) := by
        refine ⟨?_, ?_⟩
        · intro r hr
          rcases List.mem_cons.mp hr with rfl | hr
          · have := hV.1 p hp; have := hV.1 q hq; exact ⟨by simp [new]; omega, by simp [new]; omega⟩
          · exact hV.1 r (hsub.subset hr)
        · rw [List.map_cons, List.nodup_cons]
          refine ⟨?_, (hsub.map sm).nodup hV.2⟩
          rw [hsm]; intro h; exact hnot ((hsub.map sm).subset h)
      obtain ⟨L', h1, h2, h3⟩ := ih (new :: R).length (by simp at hlen ⊢; omega) (new :: R) rfl hV'
      refine ⟨L', h1, ?_, h3⟩
      rw [h2, tot_perm hperm, tot_cons, tot_cons, tot_cons, ← add_assoc]
      congr 1
      simp only [new]; rw [Multiset.replicate_add, hv]

theorem count_bound (L : List (ℕ × ℕ)) (hV : Valid L) (hM : MC L) (v : ℕ) :
    2 * (L.filter (fun p => p.1 = v)).length ≤ L.length + 1 := by
  set A := L.filter (fun p => p.1 = v) with hA
  set B := L.filter (fun p => ¬ p.1 = v) with hB
  have hlen : L.length = A.length + B.length := by
    rw [hA, hB, ← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
    have := List.length_eq_countP_add_countP (l := L) (fun p : ℕ × ℕ => decide (p.1 = v))
    simpa using this
  have hAs : A.Sublist L := List.filter_sublist
  have hBs : B.Sublist L := List.filter_sublist
  have hAn : (A.map sm).Nodup := (hAs.map sm).nodup hV.2
  have hBn : (B.map sm).Nodup := (hBs.map sm).nodup hV.2
  rcases Nat.eq_zero_or_pos A.length with h0 | hpos
  · omega
  set SA := (A.map sm).toFinset
  set SB := (B.map sm).toFinset
  have hcA : SA.card = A.length := by rw [List.toFinset_card_of_nodup hAn, List.length_map]
  have hcB : SB.card = B.length := by rw [List.toFinset_card_of_nodup hBn, List.length_map]
  have hne : SA.Nonempty := by
    rw [← Finset.card_pos, hcA]; exact hpos
  set Mx := SA.max' hne
  have hMx : Mx ∈ SA := Finset.max'_mem SA hne
  obtain ⟨m, hmA, hmMx⟩ := List.mem_map.mp (List.mem_toFinset.mp hMx)
  have key : ∀ s ∈ SA.erase Mx, s + Mx ∈ SB := by
    intro s hs
    obtain ⟨hsM, hsA⟩ := Finset.mem_erase.mp hs
    obtain ⟨p, hpA, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hsA)
    have hpL := hAs.subset hpA
    have hmL := hAs.subset hmA
    have hpv : p.1 = v := by simpa [hA] using (List.mem_filter.mp hpA).2
    have hmv : m.1 = v := by simpa [hA] using (List.mem_filter.mp hmA).2
    have hpm : p ≠ m := by intro h; apply hsM; rw [h, hmMx]
    have hin := hM p hpL m hmL hpm (by rw [hpv, hmv])
    obtain ⟨r, hrL, hr⟩ := List.mem_map.mp hin
    have hppos := hV.1 p hpL
    have hsmpos : 0 < sm p := by simp only [sm]; exact Nat.mul_pos hppos.2 hppos.1
    by_cases hrv : r.1 = v
    · exfalso
      have hrA : r ∈ A := List.mem_filter.mpr ⟨hrL, by simpa using hrv⟩
      have : sm r ∈ SA := List.mem_toFinset.mpr (List.mem_map_of_mem hrA)
      have hle : sm r ≤ Mx := Finset.le_max' SA (sm r) this
      omega
    · have hrB : r ∈ B := List.mem_filter.mpr ⟨hrL, by simpa using hrv⟩
      rw [← hmMx, ← hr]
      exact List.mem_toFinset.mpr (List.mem_map_of_mem hrB)
  have hinj : Set.InjOn (fun s => s + Mx) (SA.erase Mx : Set ℕ) := by
    intro a _ b _ h; simpa using h
  have := Finset.card_le_card_of_injOn (fun s => s + Mx) key hinj
  rw [Finset.card_erase_of_mem hMx, hcA, hcB] at this
  omega

theorem lift : ∀ (lv : List ℕ) (L : List (ℕ × ℕ)),
    (lv : Multiset ℕ) = ((L.map Prod.fst : List ℕ) : Multiset ℕ) →
    ∃ L' : List (ℕ × ℕ), List.Perm L' L ∧ L'.map Prod.fst = lv := by
  intro lv
  induction lv with
  | nil =>
    intro L h
    have : L.map Prod.fst = [] := by
      have := congrArg Multiset.card h; simp at this
      rw [List.length_eq_zero_iff.mp this.symm]; rfl
    exact ⟨L, List.Perm.refl _, this⟩
  | cons a lv ih =>
    intro L h
    have ha : a ∈ L.map Prod.fst := by
      rw [← Multiset.mem_coe, ← h]; simp
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
    have hperm := List.perm_cons_erase hp
    have h2 : ((p.1 :: lv : List ℕ) : Multiset ℕ) =
        ((p.1 :: (L.erase p).map Prod.fst : List ℕ) : Multiset ℕ) := by
      rw [h]; exact Multiset.coe_eq_coe.mpr ((hperm.map Prod.fst).trans (by simp))
    rw [← Multiset.cons_coe, ← Multiset.cons_coe, Multiset.cons_inj_right] at h2
    obtain ⟨L'', h3, h4⟩ := ih (L.erase p) h2
    exact ⟨p :: L'', (List.Perm.cons p h3).trans hperm.symm, by simp [h4]⟩

theorem coe_flatten (L : List (List ℕ)) :
    Multiset.ofList L.flatten = (L.map Multiset.ofList).sum := by
  induction L with
  | nil => rfl
  | cons a L ih => rw [List.flatten_cons, List.map_cons, List.sum_cons, ← ih, Multiset.coe_add]

theorem fwd_pairs (L : List (ℕ × ℕ)) (hV : Valid L) :
    ∃ l : List ℕ, (l : Multiset ℕ) = tot L ∧ ((l.splitBy (· == ·)).map List.sum).Nodup := by
  obtain ⟨L1, hV1, htot, hM⟩ := reduce L.length L rfl hV
  have hcnt : ∀ a, 2 * (((L1.map Prod.fst : List ℕ) : Multiset ℕ)).count a ≤ L1.length + 1 := by
    intro a
    rw [Multiset.coe_count, List.count_eq_countP, List.countP_map, List.countP_eq_length_filter]
    have := count_bound L1 hV1 hM a
    convert this using 4
    funext p
    by_cases h : p.1 = a
    · simp [h]
    · have h' : a ≠ p.1 := Ne.symm h
      simp [h, h']
  obtain ⟨lv, hlv, hch, -⟩ := arrange L1.length ((L1.map Prod.fst : List ℕ) : Multiset ℕ)
    (by simp) none hcnt (by simp)
  obtain ⟨L2, hperm, hmap⟩ := lift lv L1 hlv
  have hpos : ∀ p ∈ L2, 0 < p.1 ∧ 0 < p.2 := fun p hp => hV1.1 p (hperm.subset hp)
  have hch2 : L2.IsChain (fun p q => p.1 ≠ q.1) := by
    rw [← hmap] at hch; exact (List.isChain_map Prod.fst).mp hch
  refine ⟨(L2.map (fun p => List.replicate p.2 p.1)).flatten, ?_, ?_⟩
  · rw [coe_flatten, ← htot, ← tot_perm hperm, tot, List.map_map]
    congr 1
  · rw [List.splitBy_flatten]
    · rw [List.map_map]
      have : (List.sum ∘ fun p : ℕ × ℕ => List.replicate p.2 p.1) = sm := by
        funext p; simp [sm]
      rw [this]
      exact (hperm.map sm).nodup_iff.mpr hV1.2
    · intro h
      obtain ⟨p, hp, hp0⟩ := List.mem_map.mp h
      have := (hpos p hp).2
      rw [List.replicate_eq_nil_iff] at hp0; omega
    · intro m hm
      obtain ⟨p, -, rfl⟩ := List.mem_map.mp hm
      exact List.isChain_replicate_of_rel _ (by simp)
    · rw [List.isChain_map]
      refine List.IsChain.imp_of_mem_imp ?_ hch2
      intro p q hp hq hpq
      have hp0 : List.replicate p.2 p.1 ≠ [] := by
        have := (hpos p hp).2; rw [Ne, List.replicate_eq_nil_iff]; omega
      have hq0 : List.replicate q.2 q.1 ≠ [] := by
        have := (hpos q hq).2; rw [Ne, List.replicate_eq_nil_iff]; omega
      refine ⟨hp0, hq0, ?_⟩
      simpa using hpq

end Fwd
section Core

theorem toPairs (P : Multiset (Multiset ℕ))
    (h : ∀ b ∈ P, b ≠ 0 ∧ ∃ v, b = Multiset.replicate (Multiset.card b) v) :
    ∃ L : List (ℕ × ℕ), (∀ p ∈ L, 0 < p.2) ∧
      P = ((L.map (fun p => Multiset.replicate p.2 p.1) : List (Multiset ℕ)) : Multiset (Multiset ℕ)) := by
  induction P using Multiset.induction_on with
  | empty => exact ⟨[], by simp, rfl⟩
  | cons b P ih =>
    obtain ⟨hb0, v, hv⟩ := h b (Multiset.mem_cons_self b P)
    obtain ⟨L, hL, hPL⟩ := ih (fun c hc => h c (Multiset.mem_cons_of_mem hc))
    refine ⟨(v, Multiset.card b) :: L, ?_, ?_⟩
    · intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact Multiset.card_pos.mpr hb0
      · exact hL p hp
    · rw [List.map_cons, ← Multiset.cons_coe, ← hPL]
      congr 1

theorem mem_tot (L : List (ℕ × ℕ)) (p : ℕ × ℕ) (hp : p ∈ L) (h2 : 0 < p.2) : p.1 ∈ tot L := by
  induction L with
  | nil => simp at hp
  | cons q L ih =>
    rw [tot_cons, Multiset.mem_add]
    rcases List.mem_cons.mp hp with rfl | hp
    · left; exact Multiset.mem_replicate.mpr ⟨by omega, rfl⟩
    · right; exact ih hp

theorem core (M : Multiset ℕ) (hpos : ∀ x ∈ M, 0 < x) :
    (∃ P : Multiset (Multiset ℕ), P.sum = M ∧
      (∀ b ∈ P, b ≠ 0 ∧ ∃ v, b = Multiset.replicate (Multiset.card b) v) ∧
      (P.map Multiset.sum).Nodup) ↔
    ∃ l : List ℕ, (l : Multiset ℕ) = M ∧ ((l.splitBy (· == ·)).map List.sum).Nodup := by
  constructor
  · rintro ⟨P, hsum, hb, hnd⟩
    obtain ⟨L, hL, rfl⟩ := toPairs P hb
    have htot : tot L = M := by rw [← hsum, Multiset.sum_coe]; rfl
    have hV : Valid L := by
      refine ⟨fun p hp => ⟨hpos _ (htot ▸ mem_tot L p hp (hL p hp)), hL p hp⟩, ?_⟩
      rw [Multiset.map_coe, Multiset.coe_nodup, List.map_map] at hnd
      convert hnd using 1
      apply List.map_congr_left
      intro p _
      simp [sm]
    obtain ⟨l, hl, hnd'⟩ := fwd_pairs L hV
    exact ⟨l, hl.trans htot, hnd'⟩
  · rintro ⟨l, rfl, hnd⟩
    exact back l hnd

theorem primeCounting_pos_of_prime (p : ℕ) (hp : p.Prime) : 0 < Nat.primeCounting p := by
  have h2 : Nat.primeCounting 2 = 1 := by decide
  have := Nat.monotone_primeCounting hp.two_le
  omega

end Core

end OMAA381717Helpers

open OMAA381717Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a381717.main := by
  intro n y
  unfold OMA.S_oeis_a381717.HasConstBlockPartition OMA.S_oeis_a381717.HasDistinctRunSumPerm
    OMA.S_oeis_a381717.runSums
  exact not_congr (core y.parts (fun x hx => y.parts_pos hx))

