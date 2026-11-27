import OMAReductions.R_opg_forcing_a_2_regular_minor_R1

-- Problem: Forcing a 2-regular minor (step R1.H2)
-- Credit: @luciusacarr

section

open SimpleGraph OMA.S_opg_forcing_a_2_regular_minor

private lemma support_getElem {V : Type*} {G : SimpleGraph V} :
    ∀ {u v : V} (w : G.Walk u v) (i : ℕ) (hi : i ≤ w.length),
      w.support[i]'(by rw [w.length_support]; omega) = w.getVert i
  | _, _, .nil, 0, _ => rfl
  | _, _, .cons _ p, 0, _ => rfl
  | _, _, .cons _ p, i + 1, hi => by
      simpa [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.getVert_cons] using
        support_getElem p i (by simp at hi; exact hi)

private lemma mem_support_iff_getVert {V : Type*} {G : SimpleGraph V} {u v : V}
    (w : G.Walk u v) (x : V) :
    x ∈ w.support ↔ ∃ i ≤ w.length, w.getVert i = x := by
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨i, hi, rfl⟩
    have hi' : i ≤ w.length := by rw [w.length_support] at hi; omega
    exact ⟨i, hi', (support_getElem w i hi').symm⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, by rw [w.length_support]; omega, support_getElem w i hi⟩

private lemma getVert_mem_support {V : Type*} {G : SimpleGraph V} {u v : V}
    (w : G.Walk u v) {i : ℕ} (hi : i ≤ w.length) :
    w.getVert i ∈ w.support :=
  (mem_support_iff_getVert w _).2 ⟨i, hi, rfl⟩

private lemma getVert_inj_of_nodup {V : Type*} {G : SimpleGraph V} {u v : V}
    (w : G.Walk u v) (hnodup : w.support.Nodup) {i j : ℕ}
    (hi : i ≤ w.length) (hj : j ≤ w.length) (heq : w.getVert i = w.getVert j) :
    i = j := by
  have h1 : i < w.support.length := by rw [w.length_support]; omega
  have h2 : j < w.support.length := by rw [w.length_support]; omega
  have helem : w.support[i]'h1 = w.support[j]'h2 := by
    rw [support_getElem w i hi, support_getElem w j hj, heq]
  exact List.Nodup.getElem_inj_iff hnodup |>.1 helem

private lemma cycle_getVert_inj {V : Type*} {G : SimpleGraph V} {u : V}
    (c : G.Walk u u) (hcyc : c.IsCycle) (hc0 : 0 < c.length) {i j : ℕ}
    (hi : i < c.length) (hj : j < c.length) (heq : c.getVert i = c.getVert j) :
    i = j := by
  have hnodup : c.support.tail.Nodup := hcyc.support_nodup
  have htail_len : c.support.tail.length = c.length := by
    rw [List.length_tail, c.length_support]; omega
  have htail_get : ∀ k, (hk : k < c.length) →
      c.support.tail[k]'(by rw [htail_len]; exact hk) = c.getVert (k + 1) := by
    intro k hk
    have hk' : k + 1 < c.support.length := by rw [c.length_support]; omega
    rw [List.getElem_tail]
    exact support_getElem c (k + 1) hk
  rcases Nat.eq_zero_or_pos i with rfl | hi_pos <;>
  rcases Nat.eq_zero_or_pos j with rfl | hj_pos
  · rfl
  · exfalso
    have h0L : c.getVert 0 = c.getVert c.length := by
      rw [c.getVert_zero, c.getVert_length]
    have helem : c.support.tail[c.length - 1]'(by rw [htail_len]; omega) =
        c.support.tail[j - 1]'(by rw [htail_len]; omega) := by
      rw [htail_get _ (by omega), htail_get _ (by omega),
        Nat.sub_add_cancel hc0, Nat.sub_add_cancel hj_pos, ← h0L, heq]
    have hidx := (List.Nodup.getElem_inj_iff hnodup).1 helem
    omega
  · exfalso
    have h0L : c.getVert 0 = c.getVert c.length := by
      rw [c.getVert_zero, c.getVert_length]
    have helem : c.support.tail[i - 1]'(by rw [htail_len]; omega) =
        c.support.tail[c.length - 1]'(by rw [htail_len]; omega) := by
      rw [htail_get _ (by omega), htail_get _ (by omega),
        Nat.sub_add_cancel hi_pos, Nat.sub_add_cancel hc0, ← h0L, ← heq]
    have hidx := (List.Nodup.getElem_inj_iff hnodup).1 helem
    omega
  · have helem : c.support.tail[i - 1]'(by rw [htail_len]; omega) =
        c.support.tail[j - 1]'(by rw [htail_len]; omega) := by
      rw [htail_get _ (by omega), htail_get _ (by omega),
        Nat.sub_add_cancel hi_pos, Nat.sub_add_cancel hj_pos, heq]
    have hidx := (List.Nodup.getElem_inj_iff hnodup).1 helem
    omega

private lemma exists_hamiltonian_cycle {t : ℕ} (H : SimpleGraph (Fin t)) [DecidableRel H.Adj]
    (hreg : H.IsRegularOfDegree 2) (hconn : H.Connected) :
    ∃ (ht : 3 ≤ t) (e : Fin t ≃ Fin t),
      ∀ i : Fin t, H.Adj (e i) (e ⟨(i.val + 1) % t, Nat.mod_lt _ (by omega)⟩) := by
  classical
  have : Nonempty (Fin t) := hconn.nonempty
  let lengths : Finset ℕ := (Finset.range (t + 1)).filter fun n =>
    ∃ (a b : Fin t) (w : H.Walk a b), w.IsPath ∧ w.length = n
  have hpath_le : ∀ {a b : Fin t} (w : H.Walk a b), w.IsPath → w.length + 1 ≤ t := by
    intro a b w hw
    have hcard : w.support.toFinset.card = w.support.length := List.toFinset_card_of_nodup hw.support_nodup
    have huniv : w.support.toFinset.card ≤ Fintype.card (Fin t) := Finset.card_le_univ _
    rw [Fintype.card_fin] at huniv
    rw [w.length_support] at hcard
    omega
  have h2_mem : 2 ∈ lengths := by
    obtain ⟨u0⟩ := hconn.nonempty
    have hc0 : (H.neighborFinset u0).card = 2 := by
      rw [card_neighborFinset_eq_degree, hreg u0]
    have hne0 : (H.neighborFinset u0).Nonempty := Finset.card_pos.1 (by omega)
    obtain ⟨u1, hu1⟩ := hne0
    have hc1 : (H.neighborFinset u1).card = 2 := by
      rw [card_neighborFinset_eq_degree, hreg u1]
    have hsub1 : ((H.neighborFinset u1).erase u0).card ≥ 1 := by
      have := Finset.pred_card_le_card_erase (s := H.neighborFinset u1) (a := u0)
      omega
    obtain ⟨u2, hu2⟩ := Finset.card_pos.1 (by omega : 0 < ((H.neighborFinset u1).erase u0).card)
    have hu2_ne : u2 ≠ u0 := (Finset.mem_erase.1 hu2).1
    have h01 : H.Adj u0 u1 := (mem_neighborFinset H u0 u1).1 hu1
    have h12 : H.Adj u1 u2 := (mem_neighborFinset H u1 u2).1 (Finset.mem_erase.1 hu2).2
    let w : H.Walk u0 u2 := .cons h01 (.cons h12 .nil)
    have hw : w.IsPath := by
      rw [SimpleGraph.Walk.isPath_def]
      simp [w, h01.ne, h12.ne, hu2_ne.symm]
    refine Finset.mem_filter.2 ⟨Finset.mem_range.2 ?_, ⟨u0, u2, w, hw, rfl⟩⟩
    have := hpath_le w hw
    simp [w] at this
    omega
  set L := lengths.max' ⟨2, h2_mem⟩
  have h2_le : 2 ≤ L := Finset.le_max' lengths 2 h2_mem
  have hL_mem : L ∈ lengths := Finset.max'_mem lengths ⟨2, h2_mem⟩
  obtain ⟨a, b, p, hp, hp_len⟩ := (Finset.mem_filter.1 hL_mem).2
  have hmax : ∀ {a' b' : Fin t} (w : H.Walk a' b'), w.IsPath → w.length ≤ L := by
    intro a' b' w hw
    apply Finset.le_max'
    refine Finset.mem_filter.2 ⟨Finset.mem_range.2 ?_, ⟨a', b', w, hw, rfl⟩⟩
    have := hpath_le w hw
    omega
  have hb_closed : ∀ z, H.Adj b z → z ∈ p.support := by
    intro z hbz
    by_contra hz
    have hlong := hmax (p.concat hbz) (hp.concat hz hbz)
    rw [SimpleGraph.Walk.length_concat, hp_len] at hlong
    omega
  have hba : H.Adj b a := by
    set prev := p.getVert (L - 1)
    have hprev_adj : H.Adj prev b := by
      have h0 := p.adj_getVert_succ (i := L - 1) (by omega)
      have h1 : p.getVert (L - 1 + 1) = b := by
        rw [Nat.sub_add_cancel (by omega), ← hp_len, p.getVert_length]
      rwa [h1] at h0
    have hcb : (H.neighborFinset b).card = 2 := by
      rw [card_neighborFinset_eq_degree, hreg b]
    have herase : 0 < ((H.neighborFinset b).erase prev).card := by
      have := Finset.pred_card_le_card_erase (s := H.neighborFinset b) (a := prev)
      omega
    obtain ⟨w, hw_mem⟩ := Finset.card_pos.1 herase
    have hw_ne_prev : w ≠ prev := (Finset.mem_erase.1 hw_mem).1
    have hbw : H.Adj b w := (mem_neighborFinset H b w).1 (Finset.mem_erase.1 hw_mem).2
    have hw_supp : w ∈ p.support := hb_closed w hbw
    obtain ⟨j, hj_le, rfl⟩ := (mem_support_iff_getVert p w).1 hw_supp
    have hj_ne_L : j ≠ L := by
      rintro rfl
      rw [← hp_len, p.getVert_length] at hbw
      exact hbw.ne rfl
    have hj_ne_L1 : j ≠ L - 1 := by
      rintro rfl
      exact hw_ne_prev rfl
    rcases Nat.eq_zero_or_pos j with rfl | hj_pos
    · rwa [p.getVert_zero] at hbw
    · exfalso
      have hj_lt : j < L - 1 := by omega
      let u1 := p.getVert (j - 1)
      let u2 := p.getVert (j + 1)
      let vj := p.getVert j
      have hu1_adj : H.Adj vj u1 := by
        have := p.adj_getVert_succ (i := j - 1) (by omega)
        rw [Nat.sub_add_cancel hj_pos] at this
        exact this.symm
      have hu2_adj : H.Adj vj u2 :=
        p.adj_getVert_succ (i := j) (by omega)
      have hjb_adj : H.Adj vj b := hbw.symm
      have h12_ne : u1 ≠ u2 := by
        intro h
        have := getVert_inj_of_nodup p hp.support_nodup (by omega) (by omega) h
        omega
      have h1b_ne : u1 ≠ b := by
        intro h
        rw [← p.getVert_length, hp_len] at h
        have := getVert_inj_of_nodup p hp.support_nodup (by omega) (by omega) h
        omega
      have h2b_ne : u2 ≠ b := by
        intro h
        rw [← p.getVert_length, hp_len] at h
        have := getVert_inj_of_nodup p hp.support_nodup (by omega) (by omega) h
        omega
      have hsub3 : ({u1, u2, b} : Finset (Fin t)) ⊆ H.neighborFinset vj := by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl | rfl
        · exact (mem_neighborFinset H vj _).2 hu1_adj
        · exact (mem_neighborFinset H vj _).2 hu2_adj
        · exact (mem_neighborFinset H vj _).2 hjb_adj
      have hcard3 : ({u1, u2, b} : Finset (Fin t)).card = 3 := by
        simp [h12_ne, h1b_ne, h2b_ne]
      have hcard_vj : (H.neighborFinset vj).card = 2 := by
        rw [card_neighborFinset_eq_degree, hreg vj]
      have hle := Finset.card_le_card hsub3
      omega
  have hclosed : ∀ x ∈ p.support, ∀ y, H.Adj x y → y ∈ p.support := by
    intro x hx y hxy
    obtain ⟨j, hj_le, rfl⟩ := (mem_support_iff_getVert p x).1 hx
    have hnb2 : ∀ n1 n2 : Fin t, n1 ≠ n2 → n1 ∈ p.support → n2 ∈ p.support →
        H.Adj (p.getVert j) n1 → H.Adj (p.getVert j) n2 → y ∈ p.support := by
      intro n1 n2 hne hn1 hn2 ha1 ha2
      have hpair_sub : ({n1, n2} : Finset (Fin t)) ⊆ H.neighborFinset (p.getVert j) := by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact (mem_neighborFinset H _ _).2 ha1
        · exact (mem_neighborFinset H _ _).2 ha2
      have hcard2 : ({n1, n2} : Finset (Fin t)).card = 2 := by simp [hne]
      have hcard_v : (H.neighborFinset (p.getVert j)).card = 2 := by
        rw [card_neighborFinset_eq_degree, hreg _]
      have heq := Finset.eq_of_subset_of_card_le hpair_sub (by omega)
      have hy_mem : y ∈ ({n1, n2} : Finset (Fin t)) := by
        rw [heq]
        exact (mem_neighborFinset H _ _).2 hxy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy_mem
      rcases hy_mem with rfl | rfl <;> assumption
    rcases Nat.eq_zero_or_pos j with rfl | hj_pos
    · refine hnb2 (p.getVert 1) b ?_ ?_ ?_ ?_ ?_
      · conv_rhs => rw [← p.getVert_length]
        intro h
        have := getVert_inj_of_nodup p hp.support_nodup (by omega) (by omega) h
        omega
      · exact getVert_mem_support p (by omega)
      · have hL : p.getVert p.length ∈ p.support := getVert_mem_support p le_rfl
        rwa [p.getVert_length] at hL
      · exact p.adj_getVert_succ (i := 0) (by omega)
      · rw [p.getVert_zero]
        exact hba.symm
    · by_cases hjL : j = L
      · subst hjL
        refine hnb2 (p.getVert (L - 1)) a ?_ ?_ ?_ ?_ ?_
        · conv_rhs => rw [← p.getVert_zero]
          intro h
          have := getVert_inj_of_nodup p hp.support_nodup (by omega) (by omega) h
          omega
        · exact getVert_mem_support p (by omega)
        · have h0 : p.getVert 0 ∈ p.support := getVert_mem_support p (Nat.zero_le _)
          rwa [p.getVert_zero] at h0
        · conv_lhs => rw [← hp_len, p.getVert_length]
          have h0 := p.adj_getVert_succ (i := L - 1) (by omega)
          have h1 : p.getVert (L - 1 + 1) = b := by
            rw [Nat.sub_add_cancel (by omega), ← hp_len, p.getVert_length]
          rw [h1] at h0
          exact h0.symm
        · conv_lhs => rw [← hp_len, p.getVert_length]
          exact hba
      · refine hnb2 (p.getVert (j - 1)) (p.getVert (j + 1)) ?_ ?_ ?_ ?_ ?_
        · intro h
          have := getVert_inj_of_nodup p hp.support_nodup (by omega) (by omega) h
          omega
        · exact getVert_mem_support p (by omega)
        · exact getVert_mem_support p (by omega)
        · have := p.adj_getVert_succ (i := j - 1) (by omega)
          rw [Nat.sub_add_cancel hj_pos] at this
          exact this.symm
        · exact p.adj_getVert_succ (i := j) (by omega)
  have hall : ∀ y : Fin t, y ∈ p.support := by
    intro y
    obtain ⟨q⟩ := hconn a y
    have ha_supp : a ∈ p.support := by
      have h0 : p.getVert 0 ∈ p.support := getVert_mem_support p (Nat.zero_le _)
      rwa [p.getVert_zero] at h0
    have hwalk : ∀ {u v : Fin t} (q : H.Walk u v), u ∈ p.support → v ∈ p.support := by
      intro u v q hu
      induction q with
      | nil => exact hu
      | cons huv _ ih => exact ih (hclosed _ hu _ huv)
    exact hwalk q ha_supp
  have hsupp_len : p.support.length = t := by
    have hto : p.support.toFinset = Finset.univ := by
      ext y; simp [hall y]
    have hc := List.toFinset_card_of_nodup hp.support_nodup
    rw [hto, Finset.card_univ, Fintype.card_fin] at hc
    exact hc.symm
  have ht3 : 3 ≤ t := by
    rw [p.length_support, hp_len] at hsupp_len
    omega
  have hp_len_t : p.length = t - 1 := by
    rw [p.length_support] at hsupp_len
    omega
  let f : Fin t → Fin t := fun i => p.getVert i.val
  have hf_inj : Function.Injective f := by
    intro i j hij
    exact Fin.ext (getVert_inj_of_nodup p hp.support_nodup (by omega) (by omega) hij)
  let e : Fin t ≃ Fin t :=
    Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).2 ⟨hf_inj, rfl⟩)
  refine ⟨ht3, e, fun i => ?_⟩
  change H.Adj (p.getVert i.val) (p.getVert ((i.val + 1) % t))
  by_cases hi : i.val + 1 < t
  · rw [Nat.mod_eq_of_lt hi]
    exact p.adj_getVert_succ (by omega)
  · have hi_eq : i.val = t - 1 := by omega
    rw [hi_eq, show (t - 1 + 1) % t = 0 by rw [Nat.sub_add_cancel (by omega), Nat.mod_self],
      ← hp_len_t, p.getVert_length, p.getVert_zero]
    exact hba

private lemma induced_connected_singleton {V : Type*} (G : SimpleGraph V) (v : V) :
    (G.induce ({v} : Set V)).Connected := by
  refine (SimpleGraph.connected_iff _).2 ⟨fun ⟨x, hx⟩ ⟨y, hy⟩ => ?_, ⟨⟨v, Set.mem_singleton v⟩⟩⟩
  have hx' : x = v := Set.mem_singleton_iff.1 hx
  have hy' : y = v := Set.mem_singleton_iff.1 hy
  subst hx' hy'
  exact SimpleGraph.Reachable.refl _

end

theorem OMA.solution : OMA.R_opg_forcing_a_2_regular_minor_R1.H2 := by
  classical
  intro t H _ hreg hconn V G u c hcyc hlen
  obtain ⟨ht3, e, hedge⟩ := exists_hamiltonian_cycle H hreg hconn
  have hc0 : 0 < c.length := by omega
  let L := c.length
  let A : Fin t → Set V := fun i =>
    if i.val + 1 < t then {c.getVert i.val}
    else {z : V | ∃ k, t - 1 ≤ k ∧ k < L ∧ z = c.getVert k}
  refine ⟨fun x => A (e.symm x), ?_, ?_, ?_⟩
  · intro x
    set i := e.symm x
    by_cases hi : i.val + 1 < t
    · simp only [A]; rw [if_pos hi]
      exact induced_connected_singleton G (c.getVert i.val)
    · simp only [A]; rw [if_neg hi]
      refine (SimpleGraph.connected_iff _).2 ⟨fun ⟨x1, hx1⟩ ⟨x2, hx2⟩ => ?_,
        ⟨⟨c.getVert (t - 1), t - 1, le_rfl, by omega, rfl⟩⟩⟩
      have hreach : ∀ k, (hk_ge : t - 1 ≤ k) → (hk : k < L) →
          (G.induce {z : V | ∃ m, t - 1 ≤ m ∧ m < L ∧ z = c.getVert m}).Reachable
            ⟨c.getVert (t - 1), t - 1, le_rfl, by omega, rfl⟩
            ⟨c.getVert k, k, hk_ge, hk, rfl⟩ := by
        intro k hk_ge hk_lt
        obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le' hk_ge
        induction d with
        | zero => simp
        | succ d ih =>
            have hprev_lt : d + (t - 1) < L := by omega
            have hstep : (G.induce {z : V | ∃ m, t - 1 ≤ m ∧ m < L ∧ z = c.getVert m}).Adj
                ⟨c.getVert (d + (t - 1)), d + (t - 1), by omega, hprev_lt, rfl⟩
                ⟨c.getVert (d + 1 + (t - 1)), d + 1 + (t - 1), by omega, hk_lt, rfl⟩ := by
              rw [SimpleGraph.induce_adj]
              have := c.adj_getVert_succ (i := d + (t - 1)) hprev_lt
              simpa [Nat.add_assoc, Nat.add_comm 1 (t - 1)] using this
            exact (ih (by omega) hprev_lt).trans hstep.reachable
      obtain ⟨k1, hk1_ge, hk1_lt, rfl⟩ := hx1
      obtain ⟨k2, hk2_ge, hk2_lt, rfl⟩ := hx2
      exact (hreach k1 hk1_ge hk1_lt).symm.trans (hreach k2 hk2_ge hk2_lt)
  · intro x y hxy
    have hij : e.symm x ≠ e.symm y := fun h => hxy (e.symm.injective h)
    rw [Set.disjoint_left]
    intro z hzx hzy
    set i := e.symm x
    set j := e.symm y
    have extract : ∀ a : Fin t, z ∈ A a → ∃ k < L, z = c.getVert k ∧
        (if a.val + 1 < t then k = a.val else t - 1 ≤ k) := by
      intro a ha
      by_cases hlt : a.val + 1 < t
      · simp only [A, hlt, ↓reduceIte, Set.mem_singleton_iff] at ha
        exact ⟨a.val, by omega, ha, by simp [hlt]⟩
      · simp only [A, hlt, ↓reduceIte, Set.mem_ofPred_eq] at ha
        obtain ⟨k, hk1, hk2, hzk⟩ := ha
        exact ⟨k, hk2, hzk, by simp [hlt, hk1]⟩
    obtain ⟨k1, hk1_lt, hzk1, hcond1⟩ := extract i hzx
    obtain ⟨k2, hk2_lt, hzk2, hcond2⟩ := extract j hzy
    have hk_eq : k1 = k2 := cycle_getVert_inj c hcyc hc0 hk1_lt hk2_lt (hzk1.symm.trans hzk2)
    subst hk_eq
    apply hij
    apply Fin.ext
    by_cases hi : i.val + 1 < t <;> by_cases hj : j.val + 1 < t
    · simp [hi] at hcond1; simp [hj] at hcond2; omega
    · simp [hi] at hcond1; simp [hj] at hcond2; omega
    · simp [hi] at hcond1; simp [hj] at hcond2; omega
    · omega
  · intro x y hadj
    set i := e.symm x
    let succ : Fin t → Fin t := fun k => ⟨(k.val + 1) % t, Nat.mod_lt _ (by omega)⟩
    let pred : Fin t → Fin t := fun k => ⟨(k.val + (t - 1)) % t, Nat.mod_lt _ (by omega)⟩
    have hsucc_pred : ∀ k : Fin t, succ (pred k) = k := by
      intro k
      apply Fin.ext
      dsimp [succ, pred]
      rw [Nat.mod_add_mod]
      have : k.val + (t - 1) + 1 = k.val + t := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt k.isLt]
    have hi_nb : H.neighborFinset (e i) = {e (succ i), e (pred i)} := by
      have hne_idx : succ i ≠ pred i := by
        intro h
        have hval := congrArg Fin.val h
        dsimp [succ, pred] at hval
        rcases Nat.lt_or_ge (i.val + 1) t with h1 | h1
        · rw [Nat.mod_eq_of_lt h1] at hval
          rcases Nat.eq_zero_or_pos i.val with h0 | hpos
          · rw [h0, zero_add, Nat.mod_eq_of_lt (by omega)] at hval
            omega
          · have hsub : i.val + (t - 1) = (i.val - 1) + t := by omega
            rw [hsub, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at hval
            omega
        · have hi_eq : i.val = t - 1 := by omega
          rw [hi_eq, Nat.sub_add_cancel (by omega), Nat.mod_self,
            show t - 1 + (t - 1) = (t - 2) + t by omega, Nat.add_mod_right,
            Nat.mod_eq_of_lt (by omega)] at hval
          omega
      have hsub : ({e (succ i), e (pred i)} : Finset (Fin t)) ⊆ H.neighborFinset (e i) := by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact (SimpleGraph.mem_neighborFinset H _ _).2 (hedge i)
        · have h_adj := hedge (pred i)
          change H.Adj (e (pred i)) (e (succ (pred i))) at h_adj
          rw [hsucc_pred] at h_adj
          exact (SimpleGraph.mem_neighborFinset H _ _).2 h_adj.symm
      have hcard2 : ({e (succ i), e (pred i)} : Finset (Fin t)).card = 2 := by
        simp [e.injective.ne hne_idx]
      have hdeg : (H.neighborFinset (e i)).card = 2 := by
        rw [SimpleGraph.card_neighborFinset_eq_degree, hreg (e i)]
      exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
    have hy_mem : y ∈ H.neighborFinset (e i) := by
      rw [Equiv.apply_symm_apply]
      exact (SimpleGraph.mem_neighborFinset H x y).2 hadj
    rw [hi_nb, Finset.mem_insert, Finset.mem_singleton] at hy_mem
    have hadj_succ : ∀ k : Fin t, ∃ a ∈ A k, ∃ b ∈ A (succ k), G.Adj a b := by
      intro k
      by_cases hk1 : k.val + 2 < t
      · have hk_lt : k.val + 1 < t := by omega
        have hk_succ : (succ k).val = k.val + 1 := Nat.mod_eq_of_lt hk_lt
        have hk_succ_lt : (succ k).val + 1 < t := by omega
        refine ⟨c.getVert k.val, ?_, c.getVert (k.val + 1), ?_, c.adj_getVert_succ (by omega)⟩
        · simp [A, hk_lt]
        · dsimp only [A]; rw [if_pos hk_succ_lt, hk_succ]; rfl
      · by_cases hk2 : k.val + 1 < t
        · have hk_succ : (succ k).val = t - 1 := by
            dsimp [succ]
            rw [Nat.mod_eq_of_lt hk2]
            omega
          have hk_succ_nlt : ¬ (succ k).val + 1 < t := by omega
          refine ⟨c.getVert k.val, ?_, c.getVert (t - 1), ?_, ?_⟩
          · simp [A, hk2]
          · simp only [A, hk_succ_nlt, ↓reduceIte, Set.mem_ofPred_eq]
            exact ⟨t - 1, le_rfl, by omega, rfl⟩
          · have hk_eq : k.val + 1 = t - 1 := by omega
            simpa [hk_eq] using c.adj_getVert_succ (i := k.val) (by omega)
        · have hk_eq : k.val = t - 1 := by omega
          have hk_succ : (succ k).val = 0 := by
            dsimp [succ]
            rw [hk_eq, Nat.sub_add_cancel (by omega), Nat.mod_self]
          have hk_succ_lt : (succ k).val + 1 < t := by omega
          refine ⟨c.getVert (L - 1), ?_, c.getVert 0, ?_, ?_⟩
          · simp only [A, hk2, ↓reduceIte, Set.mem_ofPred_eq]
            exact ⟨L - 1, by omega, by omega, rfl⟩
          · dsimp only [A]; rw [if_pos hk_succ_lt, hk_succ]; rfl
          · have h0L : c.getVert 0 = c.getVert L := by rw [c.getVert_zero, c.getVert_length]
            rw [h0L]
            have := c.adj_getVert_succ (i := L - 1) (by omega)
            rwa [Nat.sub_add_cancel hc0] at this
    rcases hy_mem with rfl | hy_prev
    · obtain ⟨a, ha, b, hb, hab⟩ := hadj_succ i
      refine ⟨a, ha, b, ?_, hab⟩
      simpa [Equiv.symm_apply_apply] using hb
    · dsimp only
      rw [hy_prev, Equiv.symm_apply_apply]
      obtain ⟨a, ha, b, hb, hab⟩ := hadj_succ (pred i)
      rw [hsucc_pred] at hb
      exact ⟨b, hb, a, ha, hab.symm⟩
