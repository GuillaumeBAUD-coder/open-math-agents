import OMAReductions.R_Erdos1162_erdos_1162_variants_roney_dougal_tracey_R1_H2_R2_H1_R1_H2_R1

namespace OMAHelp

open MulAction

theorem decomp {G : Type} [Group G] [Finite G] [Group.IsNilpotent G] {p : ℕ} [hp : Fact p.Prime]
    (P : Sylow p G) (g : G) :
    ∃ c ∈ (P : Subgroup G), ∃ b : G, (∀ y ∈ (P : Subgroup G), Commute b y) ∧ g = c * b := by
  classical
  let C := Subgroup.centralizer ((P : Subgroup G) : Set G)
  have hM : (P : Subgroup G) ⊔ C = ⊤ := by
    rw [← Subgroup.index_eq_one, Nat.eq_one_iff_not_exists_prime_dvd]
    intro q hq hdvd
    have : Fact q.Prime := ⟨hq⟩
    by_cases hqp : q = p
    · subst hqp
      have := Subgroup.index_dvd_of_le (le_sup_left : (P : Subgroup G) ≤ (P : Subgroup G) ⊔ C)
      exact P.not_dvd_index (dvd_trans hdvd this)
    · let Q : Sylow q G := default
      have hQC : (Q : Subgroup G) ≤ C := by
        intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        exact (Subgroup.commute_of_normal_of_disjoint _ _ inferInstance inferInstance
          (IsPGroup.disjoint_of_ne q p hqp _ _ Q.isPGroup' P.isPGroup') x y hx hy).symm
      have := Subgroup.index_dvd_of_le (le_trans hQC (le_sup_right : C ≤ (P : Subgroup G) ⊔ C))
      exact Q.not_dvd_index (dvd_trans hdvd this)
  have hg : g ∈ (((P : Subgroup G) ⊔ C : Subgroup G) : Set G) := by rw [hM]; trivial
  rw [Subgroup.normal_mul] at hg
  obtain ⟨c, hc, b, hb, rfl⟩ := hg
  refine ⟨c, hc, b, fun y hy => ?_, rfl⟩
  exact ((Subgroup.mem_centralizer_iff.mp hb) y hy).symm

theorem kernel {G : Type} [Group G] [Finite G] [Group.IsNilpotent G] {p : ℕ} [hp : Fact p.Prime]
    (P : Sylow p G) {α : Type} [MulAction G α] (x : α) (a : G) (ha : a ∈ (P : Subgroup G))
    (hfix : ∀ c ∈ (P : Subgroup G), a • (c • x) = c • x) (g : G) : a • (g • x) = g • x := by
  obtain ⟨c, hc, b, hb, rfl⟩ := decomp P g
  have h1 : c * b = b * c := ((hb c hc).eq).symm
  rw [h1, mul_smul, ← mul_smul a b, ← (hb a ha).eq, mul_smul, hfix c hc]

theorem orbit_dvd {G : Type} [Group G] {α : Type} [MulAction G α] (H : Subgroup G) [H.Normal]
    (x : α) [Finite G] : Nat.card (orbit H x) ∣ Nat.card (orbit G x) := by
  rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq, ← index_stabilizer, ← index_stabilizer]
  set S := stabilizer G x
  have hS : stabilizer H x = S.subgroupOf H := by
    ext h; simp [S, Subgroup.mem_subgroupOf, mem_stabilizer_iff, Subgroup.smul_def]
  rw [hS, ← Subgroup.relIndex]
  rw [← Subgroup.relIndex_mul_index (le_sup_right : S ≤ H ⊔ S)]
  suffices e : S.relIndex (H ⊔ S) = S.relIndex H by rw [e]; exact dvd_mul_right _ _
  have h1 : H.relIndex (H ⊔ S) = H.relIndex S := Subgroup.relIndex_sup_left S H
  have cardle : ∀ A B : Subgroup G, A ≤ B → Nat.card A * A.relIndex B = Nat.card B := by
    intro A B hAB
    rw [← Subgroup.relIndex_bot_left, ← Subgroup.relIndex_bot_left,
      Subgroup.relIndex_mul_relIndex _ _ _ bot_le hAB]
  have cardinf : ∀ A B : Subgroup G, Nat.card (A ⊓ B : Subgroup G) * A.relIndex B = Nat.card B := by
    intro A B
    rw [← Subgroup.inf_relIndex_right A B]
    exact cardle _ _ inf_le_right
  have e1 := cardle H (H ⊔ S) le_sup_left
  have e2 := cardle S (H ⊔ S) le_sup_right
  have e3 := cardinf H S
  have e4 := cardinf S H
  rw [h1] at e1
  have hinf : (H ⊓ S : Subgroup G) = S ⊓ H := inf_comm _ _
  rw [hinf] at e3
  have hpos : 0 < Nat.card (S ⊓ H : Subgroup G) := Nat.card_pos
  have hr : 0 < H.relIndex S := by
    rcases Nat.eq_zero_or_pos (H.relIndex S) with h | h
    · rw [h, mul_zero] at e3; exact absurd e3.symm (Nat.card_pos).ne'
    · exact h
  have : Nat.card (S ⊓ H : Subgroup G) * H.relIndex S * S.relIndex (H ⊔ S) =
      Nat.card (S ⊓ H : Subgroup G) * H.relIndex S * S.relIndex H := by
    calc _ = Nat.card S * S.relIndex (H ⊔ S) := by rw [← e3]
      _ = Nat.card H * H.relIndex S := by rw [e2, e1]
      _ = _ := by rw [← e4]; ring
  exact Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hpos hr) this

theorem sum_le {ι : Type} (t : Finset ι) (f : ι → ℕ) (N : ℕ) (hN : 0 < N)
    (h2 : ∀ i ∈ t, 2 ≤ f i) (hc : ∀ i ∈ t, ∀ j ∈ t, i ≠ j → Nat.Coprime (f i) (f j))
    (hd : ∀ i ∈ t, f i ∣ N) : ∑ i ∈ t, f i ≤ N := by
  classical
  suffices H : (∑ i ∈ t, f i ≤ ∏ i ∈ t, f i) ∧ (∏ i ∈ t, f i) ∣ N from
    H.1.trans (Nat.le_of_dvd hN H.2)
  induction t using Finset.induction_on with
  | empty => simp
  | insert a r har ih =>
    obtain ⟨ih1, ih2⟩ := ih (fun i hi => h2 i (Finset.mem_insert_of_mem hi))
      (fun i hi j hj => hc i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj))
      (fun i hi => hd i (Finset.mem_insert_of_mem hi))
    rw [Finset.sum_insert har, Finset.prod_insert har]
    have ha2 := h2 a (Finset.mem_insert_self a r)
    refine ⟨?_, ?_⟩
    · rcases r.eq_empty_or_nonempty with rfl | ⟨i, hi⟩
      · simp
      · have hpos : 0 < ∏ i ∈ r, f i := Finset.prod_pos (fun i hi => by
          have := h2 i (Finset.mem_insert_of_mem hi); omega)
        have hge : f i ≤ ∏ i ∈ r, f i := Nat.le_of_dvd hpos (Finset.dvd_prod_of_mem f hi)
        have := h2 i (Finset.mem_insert_of_mem hi)
        nlinarith
    · apply Nat.Coprime.mul_dvd_of_dvd_of_dvd _ (hd a (Finset.mem_insert_self a r)) ih2
      apply Nat.Coprime.prod_right
      intro i hi
      exact hc a (Finset.mem_insert_self a r) i (Finset.mem_insert_of_mem hi)
        (fun h => har (h ▸ hi))


theorem general {G : Type} [Group G] [Finite G] [Group.IsNilpotent G] {α : Type} [Fintype α]
    [MulAction G α] (hfaith : ∀ g : G, (∀ x : α, g • x = x) → g = 1)
    (P : (p : (Nat.card G).primeFactors) → Sylow p G) :
    ∃ m : ℕ → ℕ, (∀ p ∈ (Nat.card G).primeFactors, p ≤ m p) ∧
      (∑ p ∈ (Nat.card G).primeFactors, m p) ≤ Fintype.card α ∧
      ∀ p, ∃ f : P p →* Equiv.Perm (Fin (m p)), Function.Injective f := by
  classical
  have hfact : ∀ p : (Nat.card G).primeFactors, Fact (p : ℕ).Prime := fun p => ⟨Nat.prime_of_mem_primeFactors p.2⟩
  let moved (p : (Nat.card G).primeFactors) (x : α) : Prop := ∃ a ∈ ((P p : Subgroup G)), a • x ≠ x
  let X (p : (Nat.card G).primeFactors) : Finset α :=
    (Finset.univ.filter (fun ω : orbitRel.Quotient G α => moved p ω.out)).biUnion
      (fun ω => (orbit ((P p : Subgroup G)) ω.out).toFinset)
  let m : ℕ → ℕ := fun p => if h : p ∈ (Nat.card G).primeFactors then (X ⟨p, h⟩).card else 0
  have hm : ∀ p : (Nat.card G).primeFactors, m p = (X p).card := fun p => by
    show (if h : (p : ℕ) ∈ (Nat.card G).primeFactors then (X ⟨p, h⟩).card else 0) = _
    rw [dif_pos p.2]
  -- F1
  have F1 : ∀ p : (Nat.card G).primeFactors, ∀ a ∈ (P p : Subgroup G), (∀ y ∈ X p, a • y = y) → ∀ z : α, a • z = z := by
    intro p a ha hX z
    have := hfact p
    let ω : orbitRel.Quotient G α := Quotient.mk _ z
    have hx : ω.out ∈ orbit G z := orbitRel_apply.mp (Quotient.mk_out (s := orbitRel G α) z)
    obtain ⟨g, hg⟩ := mem_orbit_symm.mp hx
    rw [← hg]
    apply kernel (P p) ω.out a ha _ g
    intro c hc
    by_cases hmv : moved p ω.out
    · apply hX
      rw [Finset.mem_biUnion]
      refine ⟨ω, by simpa using hmv, ?_⟩
      rw [Set.mem_toFinset]
      exact ⟨⟨c, hc⟩, rfl⟩
    · simp only [moved, not_exists, not_and, not_not] at hmv
      rw [hmv c hc, hmv a ha]
  have F0 : ∀ p : (Nat.card G).primeFactors, ∀ x : α, moved p x → 2 ≤ Nat.card (orbit ((P p : Subgroup G)) x) := by
    intro p x hp
    obtain ⟨a, ha, hax⟩ := hp
    rw [Nat.card_coe_set_eq]
    have : 1 < (orbit ((P p : Subgroup G)) x).ncard := by
      rw [Set.one_lt_ncard_iff]
      exact ⟨a • x, x, ⟨⟨a, ha⟩, rfl⟩, mem_orbit_self x, hax⟩
    omega
  -- F2
  have F2 : ∀ x : α, ∑ p ∈ Finset.univ.filter (fun p : (Nat.card G).primeFactors => moved p x),
      Nat.card (orbit ((P p : Subgroup G)) x) ≤ Nat.card (orbit G x) := by
    intro x
    apply sum_le
    · have : Nonempty (orbit G x) := ⟨⟨x, mem_orbit_self x⟩⟩
      exact Nat.card_pos
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      obtain ⟨a, ha, hax⟩ := hp
      rw [Nat.card_coe_set_eq]
      have : 1 < (orbit ((P p : Subgroup G)) x).ncard := by
        rw [Set.one_lt_ncard_iff]
        exact ⟨a • x, x, ⟨⟨a, ha⟩, rfl⟩, mem_orbit_self x, hax⟩
      omega
    · intro p _ q _ hpq
      have := hfact p
      have := hfact q
      obtain ⟨k, hk⟩ := (P p).isPGroup'.card_orbit x
      obtain ⟨l, hl⟩ := (P q).isPGroup'.card_orbit x
      rw [hk, hl]
      apply Nat.Coprime.pow
      rw [Nat.coprime_primes (hfact p).out (hfact q).out]
      exact fun h => hpq (Subtype.ext h)
    · intro p _
      have := hfact p
      exact orbit_dvd _ x
  refine ⟨m, ?_, ?_, ?_⟩
  · intro p hp
    let p' : (Nat.card G).primeFactors := ⟨p, hp⟩
    have := hfact p'
    show p'.1 ≤ m p'.1
    rw [hm p']
    have hne : (P p' : Subgroup G) ≠ ⊥ := by
      rw [← Subgroup.one_lt_card_iff_ne_bot, Sylow.card_eq_multiplicity]
      have h0 : (Nat.card G).factorization p ≠ 0 := by
        have := Nat.mem_primeFactors.mp hp
        exact (Nat.Prime.factorization_pos_of_dvd this.1 this.2.2 this.2.1).ne'
      exact Nat.one_lt_pow h0 (hfact p').out.one_lt
    obtain ⟨a, ha, ha1⟩ := (Subgroup.bot_or_exists_ne_one _).resolve_left hne
    obtain ⟨y, hy⟩ : (X p').Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hX
      exact ha1 (hfaith a (F1 p' a ha (by simp [hX])))
    have hy' := hy
    simp only [X, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and] at hy'
    obtain ⟨ω, hω, -⟩ := hy'
    have hsub : (orbit ((P p' : Subgroup G)) ω.out).toFinset ⊆ X p' := by
      intro z hz
      simp only [X, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨ω, hω, hz⟩
    have hc := Finset.card_le_card hsub
    rw [← Set.ncard_eq_toFinset_card', ← Nat.card_coe_set_eq] at hc
    have h2 := F0 p' _ hω
    obtain ⟨k, hk⟩ := (P p').isPGroup'.card_orbit ω.out
    rw [hk] at hc h2
    have hk0 : k ≠ 0 := by rintro rfl; simp at h2
    exact (Nat.le_self_pow hk0 _).trans hc
  · calc ∑ p ∈ (Nat.card G).primeFactors, m p = ∑ p : (Nat.card G).primeFactors, (X p).card := by
          rw [← Finset.sum_coe_sort]; simp_rw [hm]
      _ ≤ ∑ p : (Nat.card G).primeFactors, ∑ ω : orbitRel.Quotient G α,
            if moved p ω.out then Nat.card (orbit ((P p : Subgroup G)) ω.out) else 0 := by
          gcongr with p
          refine (Finset.card_biUnion_le).trans ?_
          rw [Finset.sum_filter]
          gcongr with ω
          split_ifs
          · rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card']
          · exact le_rfl
      _ = ∑ ω : orbitRel.Quotient G α, ∑ p : (Nat.card G).primeFactors,
            if moved p ω.out then Nat.card (orbit ((P p : Subgroup G)) ω.out) else 0 :=
          Finset.sum_comm
      _ ≤ ∑ ω : orbitRel.Quotient G α, Nat.card (orbit G ω.out) := by
          gcongr with ω
          rw [← Finset.sum_filter]
          exact F2 _
      _ = Fintype.card α := by
          rw [← Nat.card_eq_fintype_card, Nat.card_congr (selfEquivSigmaOrbits G α), Nat.card_sigma]
  · intro p
    rw [hm p]
    have horb : ∀ (x y : α) (a : G) (ha : a ∈ (P p : Subgroup G)),
        a • y ∈ orbit ((P p : Subgroup G)) x ↔ y ∈ orbit ((P p : Subgroup G)) x := by
      intro x y a ha
      have e : (a • y) = ((⟨a, ha⟩ : (P p : Subgroup G)) • y) := rfl
      rw [e, ← orbit_eq_iff, orbit_smul, orbit_eq_iff]
    have hinv : ∀ a : P p, ∀ y, (a : G) • y ∈ X p ↔ y ∈ X p := by
      intro a y
      simp only [X, Finset.mem_biUnion, Set.mem_toFinset]
      constructor
      · rintro ⟨ω, hω, h⟩; exact ⟨ω, hω, (horb _ _ _ a.2).mp h⟩
      · rintro ⟨ω, hω, h⟩; exact ⟨ω, hω, (horb _ _ _ a.2).mpr h⟩
    let φ : P p →* Equiv.Perm {y // y ∈ X p} :=
      { toFun := fun a => (MulAction.toPerm (a : G) : Equiv.Perm α).subtypePerm
          (fun y => hinv a y)
        map_one' := by ext y; simp
        map_mul' := by
          intro a b; ext y
          show ((a * b : P p) : G) • (y : α) = (a : G) • ((b : G) • (y : α))
          simp [mul_smul] }
    refine ⟨(Fintype.equivFinOfCardEq (Fintype.card_coe (X p))).permCongrHom.toMonoidHom.comp φ,
      ?_⟩
    rw [injective_iff_map_eq_one]
    intro a ha
    have h1 : φ a = 1 :=
      (MulEquiv.map_eq_one_iff (Fintype.equivFinOfCardEq (Fintype.card_coe (X p))).permCongrHom).mp ha
    have h2 : ∀ y ∈ X p, (a : G) • y = y := by
      intro y hy
      have := congrArg (fun σ => ((σ ⟨y, hy⟩ : {y // y ∈ X p}) : α)) h1
      exact this
    have h3 := hfaith _ (F1 p a a.2 h2)
    ext
    simpa using h3

end OMAHelp

theorem OMA.solution :
    OMA.R_Erdos1162_erdos_1162_variants_roney_dougal_tracey_R1_H2_R2_H1_R1_H2_R1.H2 := by
  intro n D hD P
  have : Group.IsNilpotent D := hD
  have hfaith : ∀ g : D, (∀ x : Fin n, g • x = x) → g = 1 := by
    intro g hg
    apply Subtype.ext
    apply Equiv.ext
    intro x
    exact hg x
  have := OMAHelp.general hfaith P
  simpa using this
