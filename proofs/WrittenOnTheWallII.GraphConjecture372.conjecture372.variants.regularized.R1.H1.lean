import OMAReductions.R_WrittenOnTheWallII_GraphConjecture372_conjecture372_variants_regularized_R1

-- Step WrittenOnTheWallII.GraphConjecture372.conjecture372.variants.regularized.R1.H1:
-- hypothesis H1 of reduction WrittenOnTheWallII.GraphConjecture372.conjecture372.variants.regularized.R1
-- Credit: @kirinzhang

open SimpleGraph

/- ### Section 1: Arm predicate and total-domination lower bound -/

private def IsArm {α : Type*} (T : SimpleGraph α) : α → List α → Prop
  | _, [] => True
  | w, [x] => x ≠ w ∧ ∀ y, T.Adj x y → y = w
  | w, x₀ :: x₁ :: rest =>
      w ∉ (x₀ :: x₁ :: rest) ∧
      (∀ y, T.Adj x₀ y → y = w ∨ y = x₁) ∧
      IsArm T x₀ (x₁ :: rest)

private lemma isArm_head_notMem {α : Type*} {T : SimpleGraph α} :
    ∀ (w : α) (L : List α), IsArm T w L → w ∉ L
  | _, [], _ => by simp
  | w, [x], h => by simp [h.1.symm]
  | _, _ :: _ :: _, h => h.1

private lemma isArm_tail {α : Type*} {T : SimpleGraph α}
    {w x₀ x₁ : α} {rest : List α} (h : IsArm T w (x₀ :: x₁ :: rest)) :
    IsArm T x₁ rest := by
  cases rest with
  | nil => trivial
  | cons x₂ rest' => exact h.2.2.2.2

private lemma isArm_adj_snd {α : Type*} {T : SimpleGraph α}
    {w x₀ x₁ : α} {rest : List α} (h : IsArm T w (x₀ :: x₁ :: rest)) :
    (rest = [] ∧ ∀ y, T.Adj x₁ y → y = x₀) ∨
    (∃ x₂ rest', rest = x₂ :: rest' ∧ ∀ y, T.Adj x₁ y → y = x₀ ∨ y = x₂) := by
  cases rest with
  | nil => exact Or.inl ⟨rfl, h.2.2.2⟩
  | cons x₂ rest' => exact Or.inr ⟨x₂, rest', rfl, h.2.2.2.1⟩

private def armCard {α : Type*} [DecidableEq α] (D : Finset α) (L : List α) : ℕ :=
  (L.toFinset ∩ D).card

private lemma armCard_cons {α : Type*} [DecidableEq α] (D : Finset α) {x : α} {L : List α}
    (hx : x ∉ L) :
    armCard D (x :: L) = (if x ∈ D then 1 else 0) + armCard D L := by
  unfold armCard
  rw [List.toFinset_cons]
  have hx' : x ∉ L.toFinset ∩ D := by
    intro hmem
    exact hx (List.mem_toFinset.mp (Finset.mem_inter.mp hmem).1)
  by_cases hxD : x ∈ D
  · have hset : insert x L.toFinset ∩ D = insert x (L.toFinset ∩ D) := by
      ext y
      simp only [Finset.mem_inter, Finset.mem_insert]
      constructor
      · rintro ⟨rfl | hyL, hyD⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨hyL, hyD⟩
      · rintro (rfl | ⟨hyL, hyD⟩)
        · exact ⟨Or.inl rfl, hxD⟩
        · exact ⟨Or.inr hyL, hyD⟩
    rw [hset, Finset.card_insert_of_notMem hx', if_pos hxD, Nat.add_comm]
  · have hset : insert x L.toFinset ∩ D = L.toFinset ∩ D := by
      ext y
      simp only [Finset.mem_inter, Finset.mem_insert]
      constructor
      · rintro ⟨rfl | hyL, hyD⟩
        · exact False.elim (hxD hyD)
        · exact ⟨hyL, hyD⟩
      · rintro ⟨hyL, hyD⟩
        exact ⟨Or.inr hyL, hyD⟩
    rw [hset, if_neg hxD, Nat.zero_add]

private lemma arm_bound {α : Type*} [DecidableEq α] (T : SimpleGraph α) (D : Finset α)
    (hD : T.IsTotalDominating (D : Set α)) :
    ∀ (n : ℕ) (L : List α) (w : α), L.length = n → IsArm T w L →
      L.length / 2 ≤ armCard D L ∧
      (L.length % 2 = 1 → w ∉ D → L.length / 2 + 1 ≤ armCard D L) ∧
      (∀ x₀ rest, L = x₀ :: rest → L.length % 2 = 0 → w ∉ D → x₀ ∈ D →
        L.length / 2 + 1 ≤ armCard D L) ∧
      (∀ x₀ rest, L = x₀ :: rest → L.length % 2 = 1 → x₀ ∈ D →
        L.length / 2 + 1 ≤ armCard D L) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro L w hlen harm
    match L with
    | [] =>
      refine ⟨by simp, by simp, ?_, ?_⟩ <;> (intro _ _ h; cases h)
    | [x] =>
      obtain ⟨y, hyD, hxy⟩ := hD x
      have hwD : w ∈ D := harm.2 y hxy ▸ Finset.mem_coe.mp hyD
      refine ⟨by simp, fun _ hnw => False.elim (hnw hwD), fun _ _ _ hmod => by simp at hmod, ?_⟩
      intro x₀ rest heq _ hx₀D
      cases heq
      have hcard1 : armCard D [x] = 1 := by
        rw [armCard_cons D (by simp), if_pos hx₀D]
        simp [armCard]
      simp [hcard1]
    | x₀ :: x₁ :: rest =>
      have hx₀_notMem : x₀ ∉ x₁ :: rest := isArm_head_notMem x₀ (x₁ :: rest) harm.2.2
      have hx₁_notMem : x₁ ∉ rest := isArm_head_notMem x₁ rest (isArm_tail harm)
      have hcard : armCard D (x₀ :: x₁ :: rest) =
          (if x₀ ∈ D then 1 else 0) + (if x₁ ∈ D then 1 else 0) + armCard D rest := by
        rw [armCard_cons D hx₀_notMem, armCard_cons D hx₁_notMem, Nat.add_assoc]
      have hlt : rest.length < n := by simp at hlen; omega
      obtain ⟨ih1, ih2, ih3, ih4⟩ := ih rest.length hlt rest x₁ rfl (isArm_tail harm)
      have hx₁_of_hnw : w ∉ D → x₁ ∈ D := by
        intro hnw
        obtain ⟨y, hyD, hxy⟩ := hD x₀
        have hyD' : y ∈ D := Finset.mem_coe.mp hyD
        rcases harm.2.1 y hxy with rfl | rfl
        · exact False.elim (hnw hyD')
        · exact hyD'
      refine ⟨?_, ?_, ?_, ?_⟩
      · by_cases hx₀ : x₀ ∈ D
        · simp only [hcard, if_pos hx₀, List.length_cons]; omega
        · by_cases hx₁ : x₁ ∈ D
          · simp only [hcard, if_pos hx₁, List.length_cons]; omega
          · obtain ⟨y, hyD, hxy⟩ := hD x₁
            have hyD' : y ∈ D := Finset.mem_coe.mp hyD
            rcases isArm_adj_snd harm with ⟨rfl, hy0⟩ | ⟨x₂, rest', rfl, hy02⟩
            · exact False.elim (hx₀ (hy0 y hxy ▸ hyD'))
            · rcases hy02 y hxy with rfl | rfl
              · exact False.elim (hx₀ hyD')
              · by_cases hmod : (x₂ :: rest').length % 2 = 1
                · have := ih2 hmod hx₁
                  simp only [hcard, List.length_cons] at *; omega
                · have hmod0 : (x₂ :: rest').length % 2 = 0 := by omega
                  have := ih3 x₂ rest' rfl hmod0 hx₁ hyD'
                  simp only [hcard, List.length_cons] at *; omega
      · intro hmod hnw
        have hx₁ : x₁ ∈ D := hx₁_of_hnw hnw
        by_cases hx₀ : x₀ ∈ D
        · simp only [hcard, if_pos hx₀, if_pos hx₁, List.length_cons]; omega
        · obtain ⟨y, hyD, hxy⟩ := hD x₁
          have hyD' : y ∈ D := Finset.mem_coe.mp hyD
          rcases isArm_adj_snd harm with ⟨rfl, hy0⟩ | ⟨x₂, rest', rfl, hy02⟩
          · exact False.elim (hx₀ (hy0 y hxy ▸ hyD'))
          · rcases hy02 y hxy with rfl | rfl
            · exact False.elim (hx₀ hyD')
            · have hmod' : (x₂ :: rest').length % 2 = 1 := by
                simp only [List.length_cons] at hmod ⊢; omega
              have := ih4 x₂ rest' rfl hmod' hyD'
              simp only [hcard, if_pos hx₁, List.length_cons] at *; omega
      · intro a b heq _ hnw haD
        cases heq
        have hx₁ : x₁ ∈ D := hx₁_of_hnw hnw
        simp only [hcard, if_pos haD, if_pos hx₁, List.length_cons]; omega
      · intro a b heq hmod haD
        cases heq
        by_cases hx₁ : x₁ ∈ D
        · simp only [hcard, if_pos haD, if_pos hx₁, List.length_cons]; omega
        · have hmod' : rest.length % 2 = 1 := by
            simp only [List.length_cons] at hmod; omega
          have := ih2 hmod' hx₁
          simp only [hcard, if_pos haD, List.length_cons]; omega

/- ### Section 2: Explicit vertex cover on an arm -/

private def armVC {α : Type*} [DecidableEq α] : List α → Finset α
  | [] => ∅
  | [_] => ∅
  | x₀ :: x₁ :: rest =>
      if rest.length % 2 = 0 then insert x₀ (armVC rest) else insert x₁ (armVC rest)

private lemma armVC_card_le {α : Type*} [DecidableEq α] :
    ∀ L : List α, (armVC L).card ≤ L.length / 2
  | [] => by simp [armVC]
  | [_] => by simp [armVC]
  | x₀ :: x₁ :: rest => by
      have ih := armVC_card_le rest
      unfold armVC
      split_ifs
      · have h1 := Finset.card_insert_le x₀ (armVC rest)
        simp only [List.length_cons]; omega
      · have h1 := Finset.card_insert_le x₁ (armVC rest)
        simp only [List.length_cons]; omega

private lemma armVC_head_mem_of_even {α : Type*} [DecidableEq α] :
    ∀ {x₀ : α} {rest : List α}, (x₀ :: rest).length % 2 = 0 → x₀ ∈ armVC (x₀ :: rest)
  | _, [], h => by simp at h
  | x₀, x₁ :: rest', h => by
      have h0 : rest'.length % 2 = 0 := by simp only [List.length_cons] at h; omega
      simp [armVC, h0]

private lemma armVC_covers {α : Type*} [DecidableEq α] {T : SimpleGraph α} :
    ∀ (n : ℕ) (L : List α) (w : α), L.length = n → IsArm T w L →
      ∀ x ∈ L, ∀ y, T.Adj x y →
        x ∈ armVC L ∨ y ∈ armVC L ∨ (L.length % 2 = 1 ∧ y = w) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro L w hlen harm x hx y hxy
    match L with
    | [] => simp at hx
    | [z] =>
      simp only [List.mem_singleton] at hx
      subst hx
      exact Or.inr (Or.inr ⟨by simp, harm.2 y hxy⟩)
    | x₀ :: x₁ :: rest =>
      have hlt : rest.length < n := by simp at hlen; omega
      have hih := ih rest.length hlt rest x₁ rfl (isArm_tail harm)
      by_cases hmod : rest.length % 2 = 0
      · have hvc : armVC (x₀ :: x₁ :: rest) = insert x₀ (armVC rest) := by simp [armVC, hmod]
        simp only [List.mem_cons] at hx
        rcases hx with rfl | rfl | hxrest
        · exact Or.inl (hvc ▸ Finset.mem_insert_self x₀ _)
        · rcases isArm_adj_snd harm with ⟨rfl, hy0⟩ | ⟨x₂, rest', rfl, hy02⟩
          · rw [hy0 y hxy]
            exact Or.inr (Or.inl (hvc ▸ Finset.mem_insert_self x₀ _))
          · rcases hy02 y hxy with rfl | rfl
            · exact Or.inr (Or.inl (hvc ▸ Finset.mem_insert_self x₀ _))
            · exact Or.inr (Or.inl (hvc ▸ Finset.mem_insert_of_mem (armVC_head_mem_of_even hmod)))
        · rcases hih x hxrest y hxy with hx' | hy' | ⟨hodd, _⟩
          · exact Or.inl (hvc ▸ Finset.mem_insert_of_mem hx')
          · exact Or.inr (Or.inl (hvc ▸ Finset.mem_insert_of_mem hy'))
          · omega
      · have hodd : rest.length % 2 = 1 := by omega
        have hvc : armVC (x₀ :: x₁ :: rest) = insert x₁ (armVC rest) := by simp [armVC, hmod]
        simp only [List.mem_cons] at hx
        rcases hx with rfl | rfl | hxrest
        · rcases harm.2.1 y hxy with rfl | rfl
          · exact Or.inr (Or.inr ⟨by simp only [List.length_cons]; omega, rfl⟩)
          · exact Or.inr (Or.inl (hvc ▸ Finset.mem_insert_self x₁ _))
        · exact Or.inl (hvc ▸ Finset.mem_insert_self x₁ _)
        · rcases hih x hxrest y hxy with hx' | hy' | ⟨_, rfl⟩
          · exact Or.inl (hvc ▸ Finset.mem_insert_of_mem hx')
          · exact Or.inr (Or.inl (hvc ▸ Finset.mem_insert_of_mem hy'))
          · exact Or.inr (Or.inl (hvc ▸ Finset.mem_insert_self x₁ _))

/- ### Section 3: Tree path-cover decomposition into 4 arms -/

private lemma walk_support_eq_cons {α : Type*} {T : SimpleGraph α} {u b : α} (q : T.Walk u b) :
    q.support = u :: q.support.tail := by
  cases q <;> rfl

private lemma isArm_support_tail_of_path {α : Type*} {T : SimpleGraph α} (hT : T.IsTree) :
    ∀ {u b : α} (q : T.Walk u b), q.IsPath →
      (∀ x ∈ q.support.tail, ∀ y, T.Adj x y → y ∈ q.support) →
      IsArm T u q.support.tail
  | _, _, .nil, _, _ => trivial
  | u, _, .cons huv .nil, _, hclosed => by
      simp only [Walk.support_cons, Walk.support_nil, List.tail_cons] at hclosed ⊢
      refine ⟨huv.ne', fun y hy => ?_⟩
      have hmem := hclosed _ (List.mem_singleton_self _) y hy
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | rfl | hfalse
      · rfl
      · exact False.elim (hy.ne rfl)
      · cases hfalse
  | _, _, @Walk.cons _ _ u v _ huv (@Walk.cons _ _ _ w _ hvw q'), hq, hclosed => by
      have hnd : (u :: (Walk.cons hvw q').support).Nodup := by
        simpa only [Walk.support_cons] using hq.support_nodup
      obtain ⟨hu_not, hv_nd⟩ := List.nodup_cons.mp hnd
      have hq' : (Walk.cons hvw q').IsPath := hq.of_cons
      have hq'_supp : q'.support = w :: q'.support.tail := walk_support_eq_cons q'
      have htail_eq : (Walk.cons huv (Walk.cons hvw q')).support.tail =
          v :: w :: q'.support.tail := by
        rw [Walk.support_cons, List.tail_cons, Walk.support_cons, hq'_supp]
      rw [htail_eq]
      refine ⟨?_, ?_, ?_⟩
      · rw [Walk.support_cons, hq'_supp] at hu_not
        exact hu_not
      · intro y hy
        have hv_mem : v ∈ (Walk.cons huv (Walk.cons hvw q')).support.tail := by
          simp [Walk.support_cons]
        have hy_mem := hclosed v hv_mem y hy
        simp only [Walk.support_cons, List.mem_cons] at hy_mem
        rcases hy_mem with rfl | hy_rest
        · exact Or.inl rfl
        · right
          have hy_supp : y ∈ (Walk.cons hvw q').support := by
            simpa only [Walk.support_cons, List.mem_cons] using hy_rest
          simpa using hT.isAcyclic.eq_snd_of_adj_start hq' hy hy_supp
      · have hclosed' : ∀ x ∈ (Walk.cons hvw q').support.tail, ∀ y,
            T.Adj x y → y ∈ (Walk.cons hvw q').support := by
          intro x hx y hxy
          have hx_in : x ∈ (Walk.cons huv (Walk.cons hvw q')).support.tail := by
            simp only [Walk.support_cons, List.tail_cons] at hx ⊢
            exact List.mem_cons_of_mem v hx
          have hy_mem := hclosed x hx_in y hxy
          simp only [Walk.support_cons, List.mem_cons] at hy_mem
          rcases hy_mem with rfl | hy_rest
          · have hx_supp : x ∈ (Walk.cons huv (Walk.cons hvw q')).support := by
              rw [walk_support_eq_cons]
              exact List.mem_cons_of_mem u hx_in
            have hxv : x = v := by
              simpa using hT.isAcyclic.eq_snd_of_adj_start hq hxy.symm hx_supp
            have hv_not : v ∉ (Walk.cons hvw q').support.tail := by
              simp only [Walk.support_cons, List.nodup_cons] at hv_nd
              simpa only [Walk.support_cons, List.tail_cons] using hv_nd.1
            exact False.elim (hv_not (hxv ▸ hx))
          · simpa only [Walk.support_cons, List.mem_cons] using hy_rest
        have ih := isArm_support_tail_of_path hT (Walk.cons hvw q') hq' hclosed'
        rw [Walk.support_cons, List.tail_cons, hq'_supp] at ih
        exact ih

private lemma walk_support_tail_eq_cons_of_adj {α : Type*} {T : SimpleGraph α} (hT : T.IsTree)
    {u a y : α} (p : T.Walk u a) (hp : p.IsPath)
    (hy : y ∈ p.support.tail) (huy : T.Adj u y) :
    ∃ rest : List α, p.support.tail = y :: rest := by
  cases p with
  | nil => simp at hy
  | @cons _ v _ huv p' =>
    have hy_supp : y ∈ (Walk.cons huv p').support := by
      rw [Walk.support_cons]
      exact List.mem_cons_of_mem u hy
    have hyv : y = v := by
      simpa using hT.isAcyclic.eq_snd_of_adj_start hp huy hy_supp
    refine ⟨p'.support.tail, ?_⟩
    rw [Walk.support_cons, List.tail_cons, hyv]
    exact walk_support_eq_cons p'

private lemma exists_subpath_of_mem_support {α : Type*} {T : SimpleGraph α}
    {a b x y : α} {p : T.Walk a b} (hp : p.IsPath)
    (hx : x ∈ p.support) (hy : y ∈ p.support) :
    ∃ r : T.Walk x y, r.IsPath ∧ ∀ z ∈ r.support, z ∈ p.support := by
  obtain ⟨pL, pR, hpL, hpR, rfl⟩ := hp.mem_support_iff_exists_append.mp hx
  rw [Walk.mem_support_append_iff] at hy
  rcases hy with hyL | hyR
  · obtain ⟨_, r, _, hr, hr_eq⟩ := hpL.mem_support_iff_exists_append.mp hyL
    refine ⟨r.reverse, hr.reverse, fun z hz => ?_⟩
    rw [Walk.mem_support_append_iff]
    left
    rw [hr_eq, Walk.mem_support_append_iff]
    right
    simpa only [Walk.support_reverse, List.mem_reverse] using hz
  · obtain ⟨r, _, hr, _, hr_eq⟩ := hpR.mem_support_iff_exists_append.mp hyR
    refine ⟨r, hr, fun z hz => ?_⟩
    rw [Walk.mem_support_append_iff]
    right
    rw [hr_eq, Walk.mem_support_append_iff]
    exact Or.inl hz

private lemma exists_cross_adj {α : Type*} [DecidableEq α] {T : SimpleGraph α} (S : Finset α)
    {a b : α} (q : T.Walk a b) (ha : a ∈ S) (hb : b ∉ S) :
    ∃ u v : α, u ∈ S ∧ v ∉ S ∧ T.Adj u v := by
  induction q with
  | nil => exact False.elim (hb ha)
  | @cons x y z hxy q' ih =>
    by_cases hy : y ∈ S
    · exact ih hy hb
    · exact ⟨x, y, ha, hy, hxy⟩

private lemma cross_adj_unique {α : Type*} {T : SimpleGraph α} (hT : T.IsTree)
    {a₁ b₁ a₂ b₂ : α} {p₁ : T.Walk a₁ b₁} {p₂ : T.Walk a₂ b₂}
    (hp₁ : p₁.IsPath) (hp₂ : p₂.IsPath)
    (hdisj : ∀ z, z ∈ p₁.support → z ∉ p₂.support)
    {u v x y : α} (hu : u ∈ p₁.support) (hv : v ∈ p₂.support)
    (hx : x ∈ p₁.support) (hy : y ∈ p₂.support)
    (huv : T.Adj u v) (hxy : T.Adj x y) :
    x = u ∧ y = v := by
  obtain ⟨r₁, hr₁, hr₁_sub⟩ := exists_subpath_of_mem_support hp₁ hu hx
  obtain ⟨r₂, hr₂, hr₂_sub⟩ := exists_subpath_of_mem_support hp₂ hv hy
  have hy_not : y ∉ r₁.support := fun h => hdisj y (hr₁_sub y h) hy
  have hu_not : u ∉ r₂.support := fun h => hdisj u hu (hr₂_sub u h)
  have hw₁ : (r₁.concat hxy).IsPath := hr₁.concat hy_not hxy
  have hw₂ : (Walk.cons huv r₂).IsPath := hr₂.cons hu_not
  have heq : r₁.concat hxy = Walk.cons huv r₂ :=
    Subtype.mk.inj ((hT.isAcyclic.subsingleton_path u y).elim ⟨_, hw₁⟩ ⟨_, hw₂⟩)
  cases r₁ with
  | nil =>
    have hsnd : y = v := by simpa using congrArg Walk.snd heq
    exact ⟨rfl, hsnd⟩
  | @cons _ z _ hadj r₁' =>
    have hsnd : z = v := by simpa using congrArg Walk.snd heq
    have hz1 : z ∈ p₁.support := hr₁_sub z (by simp [Walk.support_cons])
    exact False.elim (hdisj z hz1 (hsnd ▸ hv))

private lemma no_adj_between_tails {α : Type*} {T : SimpleGraph α} (hT : T.IsTree)
    {u a b : α} {pa : T.Walk u a} {pb : T.Walk u b}
    (hpa : pa.IsPath) (hpb : pb.IsPath)
    (hdisj : ∀ z, z ∈ pa.support.tail → z ∉ pb.support.tail)
    {x y : α} (hx : x ∈ pa.support.tail) (hy : y ∈ pb.support.tail)
    (hxy : T.Adj x y) : False := by
  have hpa_eq : pa.support = u :: pa.support.tail := walk_support_eq_cons pa
  have hpb_eq : pb.support = u :: pb.support.tail := walk_support_eq_cons pb
  have hu_not_a : u ∉ pa.support.tail := (List.nodup_cons.mp (hpa_eq ▸ hpa.support_nodup)).1
  have hu_not_b : u ∉ pb.support.tail := (List.nodup_cons.mp (hpb_eq ▸ hpb.support_nodup)).1
  have hx_ne : x ≠ u := fun h => hu_not_a (h ▸ hx)
  have hy_ne : y ≠ u := fun h => hu_not_b (h ▸ hy)
  have hx_supp : x ∈ pa.support := hpa_eq ▸ List.mem_cons_of_mem u hx
  have hy_supp : y ∈ pb.support := hpb_eq ▸ List.mem_cons_of_mem u hy
  obtain ⟨sx, _, hsx, _, hpa_app⟩ := hpa.mem_support_iff_exists_append.mp hx_supp
  obtain ⟨sy, _, hsy, _, hpb_app⟩ := hpb.mem_support_iff_exists_append.mp hy_supp
  have hsx_sub : ∀ z ∈ sx.support, z ∈ pa.support := fun z hz => by
    rw [hpa_app, Walk.mem_support_append_iff]; exact Or.inl hz
  have hsy_sub : ∀ z ∈ sy.support, z ∈ pb.support := fun z hz => by
    rw [hpb_app, Walk.mem_support_append_iff]; exact Or.inl hz
  have hy_not_sx : y ∉ sx.support := by
    intro h
    have hya : y ∈ pa.support := hsx_sub y h
    rw [hpa_eq, List.mem_cons] at hya
    exact hdisj y (hya.resolve_left hy_ne) hy
  have hw₁ : (sx.concat hxy).IsPath := hsx.concat hy_not_sx hxy
  have heq : sx.concat hxy = sy :=
    Subtype.mk.inj ((hT.isAcyclic.subsingleton_path u y).elim ⟨_, hw₁⟩ ⟨_, hsy⟩)
  cases sx with
  | nil => exact hx_ne rfl
  | @cons _ vx _ hvx sx_rest =>
    cases sy with
    | nil => exact hy_ne rfl
    | @cons _ vy _ hvy sy_rest =>
      have hv_eq : vx = vy := by simpa using congrArg Walk.snd heq
      have hvx_a : vx ∈ pa.support := hsx_sub vx (by simp [Walk.support_cons])
      rw [hpa_eq, List.mem_cons] at hvx_a
      have hvx_tail : vx ∈ pa.support.tail := hvx_a.resolve_left hvx.ne'
      have hvy_b : vy ∈ pb.support := hsy_sub vy (by simp [Walk.support_cons])
      rw [hpb_eq, List.mem_cons] at hvy_b
      have hvy_tail : vy ∈ pb.support.tail := hvy_b.resolve_left hvy.ne'
      exact hdisj vx hvx_tail (hv_eq ▸ hvy_tail)

private lemma exists_two_paths_cover {α : Type*} [Fintype α] [DecidableEq α]
    (T : SimpleGraph α) (hn : 2 ≤ Fintype.card α) (hp : T.pathCoverNumber ≤ 2) :
    ∃ (a₁ b₁ a₂ b₂ : α) (p₁ : T.Walk a₁ b₁) (p₂ : T.Walk a₂ b₂),
      p₁.IsPath ∧ p₂.IsPath ∧
      (∀ z, z ∈ p₁.support → z ∉ p₂.support) ∧
      (∀ x : α, x ∈ p₁.support ∨ x ∈ p₂.support) := by
  have hne : {k | ∃ P : Finset (Finset α), P.card = k ∧ T.IsPathCover P}.Nonempty := by
    refine ⟨(Finset.univ.image (fun v : α => ({v} : Finset α))).card,
      Finset.univ.image (fun v : α => ({v} : Finset α)), rfl, ?_, ?_, ?_⟩
    · intro s₁ hs₁ s₂ hs₂ hne'
      obtain ⟨v₁, _, rfl⟩ := Finset.mem_image.mp hs₁
      obtain ⟨v₂, _, rfl⟩ := Finset.mem_image.mp hs₂
      have hv : v₁ ≠ v₂ := fun h => hne' (h ▸ rfl)
      exact Finset.disjoint_singleton.mpr hv
    · intro v _
      exact Finset.mem_biUnion.mpr
        ⟨{v}, Finset.mem_image_of_mem _ (Finset.mem_univ v), Finset.mem_singleton_self v⟩
    · intro s hs
      obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hs
      exact ⟨v, v, Walk.nil, Walk.IsPath.nil, by simp⟩
  obtain ⟨Pcov, hPcard, hPdisj, hPcov, hPpath⟩ := Nat.sInf_mem hne
  have hcard_le : Pcov.card ≤ 2 := hPcard.le.trans hp
  have hcard_cases : Pcov.card = 0 ∨ Pcov.card = 1 ∨ Pcov.card = 2 := by omega
  rcases hcard_cases with h0 | h1 | h2
  · have hPempty : Pcov = ∅ := Finset.card_eq_zero.mp h0
    have : Nonempty α := Fintype.card_pos_iff.mp (by omega)
    obtain ⟨v⟩ := ‹Nonempty α›
    have hv := hPcov (Finset.mem_univ v)
    simp [hPempty] at hv
  · obtain ⟨s, rfl⟩ := Finset.card_eq_one.mp h1
    obtain ⟨a, b, p, hp_path, hs_eq⟩ := hPpath s (Finset.mem_singleton_self s)
    have hcov_p : ∀ x : α, x ∈ p.support := by
      intro x
      obtain ⟨t, ht, hxt⟩ := Finset.mem_biUnion.mp (hPcov (Finset.mem_univ x))
      rw [Finset.mem_singleton] at ht
      subst ht
      rw [id, hs_eq, List.mem_toFinset] at hxt
      exact hxt
    cases p with
    | nil =>
      have hle1 : Fintype.card α ≤ 1 := by
        refine Fintype.card_le_one_iff.mpr fun x y => ?_
        have hx := hcov_p x
        have hy := hcov_p y
        simp only [Walk.support_nil, List.mem_singleton] at hx hy
        exact hx.trans hy.symm
      omega
    | @cons _ b' _ hadj p' =>
      refine ⟨a, a, b', b, Walk.nil, p', Walk.IsPath.nil, hp_path.of_cons, ?_, ?_⟩
      · intro z hz
        simp only [Walk.support_nil, List.mem_singleton] at hz
        subst hz
        have hnd := hp_path.support_nodup
        rw [Walk.support_cons, List.nodup_cons] at hnd
        exact hnd.1
      · intro x
        have hx := hcov_p x
        simp only [Walk.support_cons, List.mem_cons] at hx
        rcases hx with rfl | hx'
        · exact Or.inl (by simp)
        · exact Or.inr hx'
  · obtain ⟨s₁, s₂, hsne, rfl⟩ := Finset.card_eq_two.mp h2
    obtain ⟨a₁, b₁, p₁, hp₁, hs₁⟩ := hPpath s₁ (by simp)
    obtain ⟨a₂, b₂, p₂, hp₂, hs₂⟩ := hPpath s₂ (by simp)
    have hd : Disjoint s₁ s₂ := hPdisj s₁ (by simp) s₂ (by simp) hsne
    refine ⟨a₁, b₁, a₂, b₂, p₁, p₂, hp₁, hp₂, ?_, ?_⟩
    · intro z hz1 hz2
      have h1' : z ∈ s₁ := hs₁ ▸ List.mem_toFinset.mpr hz1
      have h2' : z ∈ s₂ := hs₂ ▸ List.mem_toFinset.mpr hz2
      exact Finset.disjoint_left.mp hd h1' h2'
    · intro x
      obtain ⟨t, ht, hxt⟩ := Finset.mem_biUnion.mp (hPcov (Finset.mem_univ x))
      rw [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl
      · exact Or.inl (List.mem_toFinset.mp (hs₁ ▸ hxt))
      · exact Or.inr (List.mem_toFinset.mp (hs₂ ▸ hxt))

private lemma exists_min_totalDominating {α : Type*} [Fintype α] [DecidableEq α]
    (T : SimpleGraph α) (hT : T.IsTree) (hn : 2 ≤ Fintype.card α) :
    ∃ D : Finset α, T.IsTotalDominating (D : Set α) ∧ D.card = T.totalDominationNumber := by
  have : Nontrivial α := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have huniv : T.IsTotalDominating ((Finset.univ : Finset α) : Set α) := by
    intro v
    obtain ⟨x, hxv⟩ := exists_ne v
    obtain ⟨p, _⟩ := hT.connected.exists_isPath v x
    have hnil : ¬ p.Nil := Walk.not_nil_of_ne hxv.symm
    exact ⟨p.snd, Finset.mem_coe.mpr (Finset.mem_univ p.snd), p.adj_snd hnil⟩
  have hne : {n | ∃ D : Finset α, T.IsTotalNDominatingSet n D}.Nonempty :=
    ⟨Finset.univ.card, Finset.univ, ⟨huniv, rfl⟩⟩
  obtain ⟨D, hD⟩ := Nat.sInf_mem hne
  exact ⟨D, hD.isTotalDominating, hD.card_eq⟩

/- ### Section 4: Main theorem (`R1.H1`) -/

set_option maxHeartbeats 800000 in
theorem OMA.solution : OMA.R_WrittenOnTheWallII_GraphConjecture372_conjecture372_variants_regularized_R1.H1 := by
  intro α _ _ T hT hn hp
  classical
  obtain ⟨D, hD_td, hD_card⟩ := exists_min_totalDominating T hT hn
  obtain ⟨a₁, b₁, a₂, b₂, p₁, p₂, hp₁, hp₂, hdisj12, hcov12⟩ :=
    exists_two_paths_cover T hn hp
  have ha₁ : a₁ ∈ p₁.support.toFinset := List.mem_toFinset.mpr p₁.start_mem_support
  have ha₂ : a₂ ∉ p₁.support.toFinset := fun h =>
    hdisj12 a₂ (List.mem_toFinset.mp h) p₂.start_mem_support
  obtain ⟨u, v, hu_fs, hv_not_fs, huv⟩ :=
    exists_cross_adj p₁.support.toFinset (hT.connected a₁ a₂).some ha₁ ha₂
  have hu : u ∈ p₁.support := List.mem_toFinset.mp hu_fs
  have hv_not1 : v ∉ p₁.support := fun h => hv_not_fs (List.mem_toFinset.mpr h)
  have hv : v ∈ p₂.support := (hcov12 v).resolve_left hv_not1
  obtain ⟨q₁, r₁, hq₁, hr₁, hp₁_eq⟩ := hp₁.mem_support_iff_exists_append.mp hu
  obtain ⟨q₂, r₂, hq₂, hr₂, hp₂_eq⟩ := hp₂.mem_support_iff_exists_append.mp hv
  let pa : T.Walk u a₁ := q₁.reverse
  let pb : T.Walk u b₁ := r₁
  let pc : T.Walk v a₂ := q₂.reverse
  let pe : T.Walk v b₂ := r₂
  have hpa : pa.IsPath := hq₁.reverse
  have hpb : pb.IsPath := hr₁
  have hpc : pc.IsPath := hq₂.reverse
  have hpe : pe.IsPath := hr₂
  let A : List α := pa.support.tail
  let B : List α := pb.support.tail
  let C : List α := pc.support.tail
  let E : List α := pe.support.tail
  have hpa_supp : pa.support = u :: A := walk_support_eq_cons pa
  have hpb_supp : pb.support = u :: B := walk_support_eq_cons pb
  have hpc_supp : pc.support = v :: C := walk_support_eq_cons pc
  have hpe_supp : pe.support = v :: E := walk_support_eq_cons pe
  have hp₁_mem : ∀ z, z ∈ p₁.support ↔ z = u ∨ z ∈ A ∨ z ∈ B := by
    intro z
    rw [hp₁_eq, Walk.mem_support_append_iff]
    have hq₁_iff : z ∈ q₁.support ↔ z = u ∨ z ∈ A := by
      have : z ∈ q₁.support ↔ z ∈ pa.support := by
        simp only [pa, Walk.support_reverse, List.mem_reverse]
      rw [this, hpa_supp, List.mem_cons]
    have hr₁_iff : z ∈ r₁.support ↔ z = u ∨ z ∈ B := by
      rw [show r₁.support = pb.support from rfl, hpb_supp, List.mem_cons]
    rw [hq₁_iff, hr₁_iff]
    constructor
    · rintro ((rfl | h) | (rfl | h))
      · exact Or.inl rfl
      · exact Or.inr (Or.inl h)
      · exact Or.inl rfl
      · exact Or.inr (Or.inr h)
    · rintro (rfl | h | h)
      · exact Or.inl (Or.inl rfl)
      · exact Or.inl (Or.inr h)
      · exact Or.inr (Or.inr h)
  have hp₂_mem : ∀ z, z ∈ p₂.support ↔ z = v ∨ z ∈ C ∨ z ∈ E := by
    intro z
    rw [hp₂_eq, Walk.mem_support_append_iff]
    have hq₂_iff : z ∈ q₂.support ↔ z = v ∨ z ∈ C := by
      have : z ∈ q₂.support ↔ z ∈ pc.support := by
        simp only [pc, Walk.support_reverse, List.mem_reverse]
      rw [this, hpc_supp, List.mem_cons]
    have hr₂_iff : z ∈ r₂.support ↔ z = v ∨ z ∈ E := by
      rw [show r₂.support = pe.support from rfl, hpe_supp, List.mem_cons]
    rw [hq₂_iff, hr₂_iff]
    constructor
    · rintro ((rfl | h) | (rfl | h))
      · exact Or.inl rfl
      · exact Or.inr (Or.inl h)
      · exact Or.inl rfl
      · exact Or.inr (Or.inr h)
    · rintro (rfl | h | h)
      · exact Or.inl (Or.inl rfl)
      · exact Or.inl (Or.inr h)
      · exact Or.inr (Or.inr h)
  have hu_notA : u ∉ A := (List.nodup_cons.mp (hpa_supp ▸ hpa.support_nodup)).1
  have hu_notB : u ∉ B := (List.nodup_cons.mp (hpb_supp ▸ hpb.support_nodup)).1
  have hv_notC : v ∉ C := (List.nodup_cons.mp (hpc_supp ▸ hpc.support_nodup)).1
  have hv_notE : v ∉ E := (List.nodup_cons.mp (hpe_supp ▸ hpe.support_nodup)).1
  have hdisjAB : ∀ z, z ∈ A → z ∉ B := by
    intro z hzA hzB
    have hnd := hp₁.support_nodup
    rw [hp₁_eq, Walk.support_append] at hnd
    have hqB := List.disjoint_of_nodup_append hnd
    have hz_q₁ : z ∈ q₁.support := by
      have : z ∈ pa.support := hpa_supp ▸ List.mem_cons_of_mem u hzA
      simpa only [pa, Walk.support_reverse, List.mem_reverse] using this
    exact hqB hz_q₁ hzB
  have hdisjCE : ∀ z, z ∈ C → z ∉ E := by
    intro z hzC hzE
    have hnd := hp₂.support_nodup
    rw [hp₂_eq, Walk.support_append] at hnd
    have hqE := List.disjoint_of_nodup_append hnd
    have hz_q₂ : z ∈ q₂.support := by
      have : z ∈ pc.support := hpc_supp ▸ List.mem_cons_of_mem v hzC
      simpa only [pc, Walk.support_reverse, List.mem_reverse] using this
    exact hqE hz_q₂ hzE
  have hA_arm : IsArm T u A := by
    refine isArm_support_tail_of_path hT pa hpa fun x hx y hxy => ?_
    have hx1 : x ∈ p₁.support := (hp₁_mem x).mpr (Or.inr (Or.inl hx))
    have hx_ne_u : x ≠ u := fun h => hu_notA (h ▸ hx)
    rcases hcov12 y with hy1 | hy2
    · rcases (hp₁_mem y).mp hy1 with rfl | hyA | hyB
      · exact hpa_supp ▸ List.mem_cons.mpr (Or.inl rfl)
      · exact hpa_supp ▸ List.mem_cons_of_mem u hyA
      · exact False.elim (no_adj_between_tails hT hpa hpb hdisjAB hx hyB hxy)
    · have hxu := (cross_adj_unique hT hp₁ hp₂ hdisj12 hu hv hx1 hy2 huv hxy).1
      exact False.elim (hx_ne_u hxu)
  have hB_arm : IsArm T u B := by
    refine isArm_support_tail_of_path hT pb hpb fun x hx y hxy => ?_
    have hx1 : x ∈ p₁.support := (hp₁_mem x).mpr (Or.inr (Or.inr hx))
    have hx_ne_u : x ≠ u := fun h => hu_notB (h ▸ hx)
    rcases hcov12 y with hy1 | hy2
    · rcases (hp₁_mem y).mp hy1 with rfl | hyA | hyB
      · exact hpb_supp ▸ List.mem_cons.mpr (Or.inl rfl)
      · exact False.elim (no_adj_between_tails hT hpb hpa (fun z h1 h2 => hdisjAB z h2 h1) hx hyA hxy)
      · exact hpb_supp ▸ List.mem_cons_of_mem u hyB
    · have hxu := (cross_adj_unique hT hp₁ hp₂ hdisj12 hu hv hx1 hy2 huv hxy).1
      exact False.elim (hx_ne_u hxu)
  have hC_arm : IsArm T v C := by
    refine isArm_support_tail_of_path hT pc hpc fun x hx y hxy => ?_
    have hx2 : x ∈ p₂.support := (hp₂_mem x).mpr (Or.inr (Or.inl hx))
    have hx_ne_v : x ≠ v := fun h => hv_notC (h ▸ hx)
    rcases hcov12 y with hy1 | hy2
    · have hxv := (cross_adj_unique hT hp₁ hp₂ hdisj12 hu hv hy1 hx2 huv hxy.symm).2
      exact False.elim (hx_ne_v hxv)
    · rcases (hp₂_mem y).mp hy2 with rfl | hyC | hyE
      · exact hpc_supp ▸ List.mem_cons.mpr (Or.inl rfl)
      · exact hpc_supp ▸ List.mem_cons_of_mem v hyC
      · exact False.elim (no_adj_between_tails hT hpc hpe hdisjCE hx hyE hxy)
  have hE_arm : IsArm T v E := by
    refine isArm_support_tail_of_path hT pe hpe fun x hx y hxy => ?_
    have hx2 : x ∈ p₂.support := (hp₂_mem x).mpr (Or.inr (Or.inr hx))
    have hx_ne_v : x ≠ v := fun h => hv_notE (h ▸ hx)
    rcases hcov12 y with hy1 | hy2
    · have hxv := (cross_adj_unique hT hp₁ hp₂ hdisj12 hu hv hy1 hx2 huv hxy.symm).2
      exact False.elim (hx_ne_v hxv)
    · rcases (hp₂_mem y).mp hy2 with rfl | hyC | hyE
      · exact hpe_supp ▸ List.mem_cons.mpr (Or.inl rfl)
      · exact False.elim (no_adj_between_tails hT hpe hpc (fun z h1 h2 => hdisjCE z h2 h1) hx hyC hxy)
      · exact hpe_supp ▸ List.mem_cons_of_mem v hyE
  -- Explicit vertex cover VC
  let uOdd : Prop := A.length % 2 = 1 ∨ B.length % 2 = 1
  let vOdd : Prop := C.length % 2 = 1 ∨ E.length % 2 = 1
  let anchors : Finset α :=
    if uOdd ∧ vOdd then {u, v} else if uOdd then {u} else {v}
  let VC : Finset α := anchors ∪ armVC A ∪ armVC B ∪ armVC C ∪ armVC E
  have hu_anc : uOdd → u ∈ anchors := by
    intro huo
    dsimp only [anchors]
    by_cases hvo : vOdd
    · rw [if_pos ⟨huo, hvo⟩]; simp
    · rw [if_neg (fun h => hvo h.2), if_pos huo]; simp
  have hv_anc : vOdd → v ∈ anchors := by
    intro hvo
    dsimp only [anchors]
    by_cases huo : uOdd
    · rw [if_pos ⟨huo, hvo⟩]; simp
    · rw [if_neg (fun h => huo h.1), if_neg huo]; simp
  have huv_anc : u ∈ anchors ∨ v ∈ anchors := by
    dsimp only [anchors]
    split_ifs <;> simp
  have harm_edge : ∀ x y, T.Adj x y → (x ∈ A ∨ x ∈ B ∨ x ∈ C ∨ x ∈ E) → x ∈ VC ∨ y ∈ VC := by
    intro x y hxy hxarm
    rcases hxarm with hxA | hxB | hxC | hxE
    · rcases armVC_covers A.length A u rfl hA_arm x hxA y hxy with h1 | h2 | ⟨hodd, rfl⟩
      · exact Or.inl (by simp [VC, h1])
      · exact Or.inr (by simp [VC, h2])
      · exact Or.inr (by simp [VC, hu_anc (Or.inl hodd)])
    · rcases armVC_covers B.length B u rfl hB_arm x hxB y hxy with h1 | h2 | ⟨hodd, rfl⟩
      · exact Or.inl (by simp [VC, h1])
      · exact Or.inr (by simp [VC, h2])
      · exact Or.inr (by simp [VC, hu_anc (Or.inr hodd)])
    · rcases armVC_covers C.length C v rfl hC_arm x hxC y hxy with h1 | h2 | ⟨hodd, rfl⟩
      · exact Or.inl (by simp [VC, h1])
      · exact Or.inr (by simp [VC, h2])
      · exact Or.inr (by simp [VC, hv_anc (Or.inl hodd)])
    · rcases armVC_covers E.length E v rfl hE_arm x hxE y hxy with h1 | h2 | ⟨hodd, rfl⟩
      · exact Or.inl (by simp [VC, h1])
      · exact Or.inr (by simp [VC, h2])
      · exact Or.inr (by simp [VC, hv_anc (Or.inr hodd)])
  have hVC_cov : T.IsVertexCover (VC : Set α) := by
    intro x y hxy
    have hx_all : x = u ∨ x = v ∨ x ∈ A ∨ x ∈ B ∨ x ∈ C ∨ x ∈ E := by
      rcases hcov12 x with h1 | h2
      · rcases (hp₁_mem x).mp h1 with rfl | h | h
        · exact Or.inl rfl
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · rcases (hp₂_mem x).mp h2 with rfl | h | h
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
    have hy_all : y = u ∨ y = v ∨ y ∈ A ∨ y ∈ B ∨ y ∈ C ∨ y ∈ E := by
      rcases hcov12 y with h1 | h2
      · rcases (hp₁_mem y).mp h1 with rfl | h | h
        · exact Or.inl rfl
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · rcases (hp₂_mem y).mp h2 with rfl | h | h
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
    rcases hx_all with rfl | rfl | hxarm
    · rcases hy_all with rfl | rfl | hyarm
      · exact False.elim (hxy.ne rfl)
      · rcases huv_anc with huA | hvA
        · exact Or.inl (Finset.mem_coe.mpr (by simp [VC, huA]))
        · exact Or.inr (Finset.mem_coe.mpr (by simp [VC, hvA]))
      · exact (harm_edge y u hxy.symm hyarm).symm.imp Finset.mem_coe.mpr Finset.mem_coe.mpr
    · rcases hy_all with rfl | rfl | hyarm
      · rcases huv_anc with huA | hvA
        · exact Or.inr (Finset.mem_coe.mpr (by simp [VC, huA]))
        · exact Or.inl (Finset.mem_coe.mpr (by simp [VC, hvA]))
      · exact False.elim (hxy.ne rfl)
      · exact (harm_edge y v hxy.symm hyarm).symm.imp Finset.mem_coe.mpr Finset.mem_coe.mpr
    · exact (harm_edge x y hxy hxarm).imp Finset.mem_coe.mpr Finset.mem_coe.mpr
  -- Upper bound on VC.card
  have hanc_card : anchors.card ≤ if uOdd ∧ vOdd then 2 else 1 := by
    dsimp only [anchors]
    by_cases h : uOdd ∧ vOdd
    · rw [if_pos h, if_pos h]
      exact Finset.card_le_two
    · rw [if_neg h, if_neg h]
      split_ifs <;> simp
  have hVC_card : VC.card ≤
      (if uOdd ∧ vOdd then 2 else 1) + A.length / 2 + B.length / 2 + C.length / 2 + E.length / 2 := by
    have h1 := Finset.card_union_le (anchors ∪ armVC A ∪ armVC B ∪ armVC C) (armVC E)
    have h2 := Finset.card_union_le (anchors ∪ armVC A ∪ armVC B) (armVC C)
    have h3 := Finset.card_union_le (anchors ∪ armVC A) (armVC B)
    have h4 := Finset.card_union_le anchors (armVC A)
    have hA := armVC_card_le A
    have hB := armVC_card_le B
    have hC := armVC_card_le C
    have hE := armVC_card_le E
    dsimp only [VC]
    omega
  -- Lower bound on D.card via disjoint subsets
  let Suv : Finset α := ({u, v} : Finset α) ∩ D
  let SA : Finset α := A.toFinset ∩ D
  let SB : Finset α := B.toFinset ∩ D
  let SC : Finset α := C.toFinset ∩ D
  let SE : Finset α := E.toFinset ∩ D
  have hSuv_card : Suv.card = (if u ∈ D then 1 else 0) + (if v ∈ D then 1 else 0) := by
    have huv_ne : u ≠ v := huv.ne
    have h1 : Suv = (if u ∈ D then {u} else ∅) ∪ (if v ∈ D then {v} else ∅) := by
      ext z
      by_cases huD : u ∈ D <;> by_cases hvD : v ∈ D <;>
        simp only [Suv, if_pos, if_neg, huD, hvD, Finset.mem_inter, Finset.mem_insert,
          Finset.mem_singleton, Finset.mem_union, Finset.notMem_empty, or_false, false_or]
      · constructor
        · exact fun h => h.1
        · rintro (rfl | rfl)
          · exact ⟨Or.inl rfl, huD⟩
          · exact ⟨Or.inr rfl, hvD⟩
      · constructor
        · rintro ⟨rfl | rfl, hzD⟩
          · rfl
          · exact False.elim (hvD hzD)
        · rintro rfl
          exact ⟨Or.inl rfl, huD⟩
      · constructor
        · rintro ⟨rfl | rfl, hzD⟩
          · exact False.elim (huD hzD)
          · rfl
        · rintro rfl
          exact ⟨Or.inr rfl, hvD⟩
      · constructor
        · rintro ⟨rfl | rfl, hzD⟩
          · exact huD hzD
          · exact hvD hzD
        · exact False.elim
    rw [h1, Finset.card_union_of_disjoint]
    · by_cases huD : u ∈ D <;> by_cases hvD : v ∈ D <;> simp [huD, hvD]
    · by_cases huD : u ∈ D <;> by_cases hvD : v ∈ D <;> simp [huD, hvD, huv_ne]
  have hd_uv_A : Disjoint Suv SA := Finset.disjoint_left.mpr fun z h1 h2 => by
    have hz1 := (Finset.mem_inter.mp h1).1
    have hzA := List.mem_toFinset.mp (Finset.mem_inter.mp h2).1
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz1
    rcases hz1 with rfl | rfl
    · exact hu_notA hzA
    · exact hdisj12 v ((hp₁_mem v).mpr (Or.inr (Or.inl hzA))) hv
  have hd_uvA_B : Disjoint (Suv ∪ SA) SB := Finset.disjoint_left.mpr fun z h1 h2 => by
    have hzB := List.mem_toFinset.mp (Finset.mem_inter.mp h2).1
    rcases Finset.mem_union.mp h1 with h1' | h1'
    · have hz1 := (Finset.mem_inter.mp h1').1
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz1
      rcases hz1 with rfl | rfl
      · exact hu_notB hzB
      · exact hdisj12 v ((hp₁_mem v).mpr (Or.inr (Or.inr hzB))) hv
    · exact hdisjAB z (List.mem_toFinset.mp (Finset.mem_inter.mp h1').1) hzB
  have hd_uvAB_C : Disjoint (Suv ∪ SA ∪ SB) SC := Finset.disjoint_left.mpr fun z h1 h2 => by
    have hzC := List.mem_toFinset.mp (Finset.mem_inter.mp h2).1
    have hz2 : z ∈ p₂.support := (hp₂_mem z).mpr (Or.inr (Or.inl hzC))
    rcases Finset.mem_union.mp h1 with h1' | h1'
    · rcases Finset.mem_union.mp h1' with h1'' | h1''
      · have hz1 := (Finset.mem_inter.mp h1'').1
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz1
        rcases hz1 with rfl | rfl
        · exact hdisj12 u hu hz2
        · exact hv_notC hzC
      · exact hdisj12 z ((hp₁_mem z).mpr (Or.inr (Or.inl (List.mem_toFinset.mp (Finset.mem_inter.mp h1'').1)))) hz2
    · exact hdisj12 z ((hp₁_mem z).mpr (Or.inr (Or.inr (List.mem_toFinset.mp (Finset.mem_inter.mp h1').1)))) hz2
  have hd_uvABC_E : Disjoint (Suv ∪ SA ∪ SB ∪ SC) SE := Finset.disjoint_left.mpr fun z h1 h2 => by
    have hzE := List.mem_toFinset.mp (Finset.mem_inter.mp h2).1
    have hz2 : z ∈ p₂.support := (hp₂_mem z).mpr (Or.inr (Or.inr hzE))
    rcases Finset.mem_union.mp h1 with h1' | h1'
    · rcases Finset.mem_union.mp h1' with h1'' | h1''
      · rcases Finset.mem_union.mp h1'' with h1''' | h1'''
        · have hz1 := (Finset.mem_inter.mp h1''').1
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz1
          rcases hz1 with rfl | rfl
          · exact hdisj12 u hu hz2
          · exact hv_notE hzE
        · exact hdisj12 z ((hp₁_mem z).mpr (Or.inr (Or.inl (List.mem_toFinset.mp (Finset.mem_inter.mp h1''').1)))) hz2
      · exact hdisj12 z ((hp₁_mem z).mpr (Or.inr (Or.inr (List.mem_toFinset.mp (Finset.mem_inter.mp h1'').1)))) hz2
    · exact hdisjCE z (List.mem_toFinset.mp (Finset.mem_inter.mp h1').1) hzE
  have hD_decomp :
      (if u ∈ D then 1 else 0) + (if v ∈ D then 1 else 0) +
      armCard D A + armCard D B + armCard D C + armCard D E ≤ D.card := by
    have hsub : Suv ∪ SA ∪ SB ∪ SC ∪ SE ⊆ D := by
      intro z hz
      simp only [Suv, SA, SB, SC, SE, Finset.mem_union, Finset.mem_inter] at hz
      rcases hz with (((⟨_, h⟩ | ⟨_, h⟩) | ⟨_, h⟩) | ⟨_, h⟩) | ⟨_, h⟩ <;> exact h
    have hle := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hd_uvABC_E,
        Finset.card_union_of_disjoint hd_uvAB_C,
        Finset.card_union_of_disjoint hd_uvA_B,
        Finset.card_union_of_disjoint hd_uv_A,
        hSuv_card] at hle
    exact hle
  obtain ⟨hA1, hA2, hA3, _⟩ := arm_bound T D hD_td A.length A u rfl hA_arm
  obtain ⟨hB1, hB2, hB3, _⟩ := arm_bound T D hD_td B.length B u rfl hB_arm
  obtain ⟨hC1, hC2, _, _⟩ := arm_bound T D hD_td C.length C v rfl hC_arm
  obtain ⟨hE1, hE2, _, _⟩ := arm_bound T D hD_td E.length E v rfl hE_arm
  have hVC_le_D : VC.card ≤ D.card := by
    by_cases hboth : uOdd ∧ vOdd
    · have hu_side : A.length / 2 + B.length / 2 + 1 ≤
          (if u ∈ D then 1 else 0) + armCard D A + armCard D B := by
        by_cases huD : u ∈ D
        · simp only [if_pos huD]; omega
        · rcases hboth.1 with hAo | hBo
          · have := hA2 hAo huD; omega
          · have := hB2 hBo huD; omega
      have hv_side : C.length / 2 + E.length / 2 + 1 ≤
          (if v ∈ D then 1 else 0) + armCard D C + armCard D E := by
        by_cases hvD : v ∈ D
        · simp only [if_pos hvD]; omega
        · rcases hboth.2 with hCo | hEo
          · have := hC2 hCo hvD; omega
          · have := hE2 hEo hvD; omega
      rw [if_pos hboth] at hVC_card
      omega
    · rw [if_neg hboth] at hVC_card
      by_cases huD : u ∈ D
      · simp only [if_pos huD] at hD_decomp; omega
      · by_cases hvD : v ∈ D
        · simp only [if_pos hvD] at hD_decomp; omega
        · obtain ⟨y, hyD, huy⟩ := hD_td u
          have hyD' : y ∈ D := Finset.mem_coe.mp hyD
          rcases hcov12 y with hy1 | hy2
          · rcases (hp₁_mem y).mp hy1 with rfl | hyA | hyB
            · exact False.elim (huy.ne rfl)
            · obtain ⟨restA, hA_cons⟩ := walk_support_tail_eq_cons_of_adj hT pa hpa hyA huy
              by_cases hAo : A.length % 2 = 1
              · have := hA2 hAo huD; omega
              · have hAe : A.length % 2 = 0 := by omega
                have := hA3 y restA hA_cons hAe huD hyD'
                omega
            · obtain ⟨restB, hB_cons⟩ := walk_support_tail_eq_cons_of_adj hT pb hpb hyB huy
              by_cases hBo : B.length % 2 = 1
              · have := hB2 hBo huD; omega
              · have hBe : B.length % 2 = 0 := by omega
                have := hB3 y restB hB_cons hBe huD hyD'
                omega
          · have hyv := (cross_adj_unique hT hp₁ hp₂ hdisj12 hu hv hu hy2 huv huy).2
            exact False.elim (hvD (hyv ▸ hyD'))
  have hvc_enat : (T.vertexCoverNum.toNat : ℕ∞) ≤ (VC.card : ℕ∞) := by
    rw [ENat.natCast_toNat (SimpleGraph.vertexCoverNum_ne_top_of_finite (G := T))]
    have h := hVC_cov.vertexCoverNum_le
    simpa only [Set.encard_coe_eq_coe_finsetCard] using h
  have hvc_nat : T.vertexCoverNum.toNat ≤ VC.card := Nat.cast_le.mp hvc_enat
  exact hvc_nat.trans (hVC_le_D.trans hD_card.le)
