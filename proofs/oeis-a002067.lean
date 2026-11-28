import OMAStatements.S_oeis_a002067

-- Problem: A002067: a(n) = Sum_{k=0..n-1} binomial(2*n,2*k)*a(k)*a(n-k-1).
-- Upstream: formal-conjectures statements/oeis-a002067.lean:0 (declaration OMA.S_oeis_a002067.main)
-- Credit: @marcelopierry (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open scoped Nat

namespace A002067Proof

open Finset

/-! ### Part 1: Rooted parented matchings (triangular cacti) -/

/-- A fixed-point-free involution `σ` on a finite set `S ⊆ ℕ` paired with a parent map
`par : S → insert r S` constant on `σ`-pairs and strictly decreasing (`par x < x`). -/
structure CactusS (r : ℕ) (S : Finset ℕ) where
  σ : S → S
  par : S → ℕ
  hneq : ∀ x : S, σ x ≠ x
  hinv : ∀ x : S, σ (σ x) = x
  hpar_mem : ∀ x : S, par x ∈ insert r S
  hpar_symm : ∀ x : S, par (σ x) = par x
  hpar_lt : ∀ x : S, par x < (x : ℕ)

private lemma CactusS.ext {r : ℕ} {S : Finset ℕ} {x y : CactusS r S}
    (hσ : x.σ = y.σ) (hpar : x.par = y.par) : x = y := by
  cases x
  cases y
  cases hσ
  cases hpar
  rfl

private noncomputable def cactusSEquivSubtype (r : ℕ) (S : Finset ℕ) :
    CactusS r S ≃ { p : (S → S) × (S → (insert r S : Finset ℕ)) //
      (∀ x, p.1 x ≠ x) ∧ (∀ x, p.1 (p.1 x) = x) ∧
      (∀ x, (p.2 (p.1 x) : ℕ) = (p.2 x : ℕ)) ∧ (∀ x, (p.2 x : ℕ) < (x : ℕ)) } where
  toFun c :=
    ⟨(c.σ, fun x => ⟨c.par x, c.hpar_mem x⟩),
      c.hneq, c.hinv, c.hpar_symm, c.hpar_lt⟩
  invFun p :=
    ⟨p.1.1, fun x => (p.1.2 x : ℕ),
      p.2.1, p.2.2.1, fun x => (p.1.2 x).2, p.2.2.2.1, p.2.2.2.2⟩
  left_inv c := by cases c; rfl
  right_inv p := by rcases p with ⟨⟨σ, par⟩, h⟩; rfl

private noncomputable instance instFintypeCactusS (r : ℕ) (S : Finset ℕ) :
    Fintype (CactusS r S) := by
  classical
  exact Fintype.ofEquiv _ (cactusSEquivSubtype r S).symm

/-- Number of parented matchings on `{1, …, 2n}` with root `0`. -/
private noncomputable def c (n : ℕ) : ℕ :=
  Fintype.card (CactusS 0 (Icc 1 (2 * n)))

private lemma c_zero : c 0 = 1 := by
  unfold c
  have hEmpty : Icc 1 (2 * 0) = (∅ : Finset ℕ) := by decide
  rw [hEmpty]
  refine Fintype.card_eq_one_iff.mpr ⟨
    { σ := fun x => nomatch x.2
      par := fun x => nomatch x.2
      hneq := fun x => nomatch x.2
      hinv := fun x => nomatch x.2
      hpar_mem := fun x => nomatch x.2
      hpar_symm := fun x => nomatch x.2
      hpar_lt := fun x => nomatch x.2 },
    fun a => by
      apply CactusS.ext
      · funext x; exact nomatch x.2
      · funext x; exact nomatch x.2 ⟩

private lemma even_card_of_fpf_invol (S : Finset ℕ) (σ : S → S)
    (hneq : ∀ x, σ x ≠ x) (hinv : ∀ x, σ (σ x) = x) : Even S.card := by
  classical
  let L : Finset ℕ := S.filter (fun a => ∃ ha : a ∈ S, a < (σ ⟨a, ha⟩ : ℕ))
  let R : Finset ℕ := S.filter (fun a => ∃ ha : a ∈ S, (σ ⟨a, ha⟩ : ℕ) < a)
  have hdisj : Disjoint L R := by
    rw [Finset.disjoint_left]
    intro a haL haR
    rcases (Finset.mem_filter.mp haL).2 with ⟨ha1, hlt1⟩
    rcases (Finset.mem_filter.mp haR).2 with ⟨ha2, hlt2⟩
    omega
  have hunion : L ∪ R = S := by
    ext a
    simp only [Finset.mem_union, L, R, Finset.mem_filter]
    constructor
    · rintro (⟨ha, _⟩ | ⟨ha, _⟩) <;> exact ha
    · intro ha
      have hne : (σ ⟨a, ha⟩ : ℕ) ≠ a := by
        intro heq
        apply hneq ⟨a, ha⟩
        exact Subtype.ext heq
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact Or.inr ⟨ha, ha, hlt⟩
      · exact Or.inl ⟨ha, ha, hgt⟩
  have hcardEq : L.card = R.card := by
    refine Finset.card_bij (fun a ha => (σ ⟨a, (Finset.mem_filter.mp ha).1⟩ : ℕ)) ?_ ?_ ?_
    · intro a ha
      rcases Finset.mem_filter.mp ha with ⟨haS, _, hlt⟩
      refine Finset.mem_filter.mpr ⟨(σ ⟨a, haS⟩).2, (σ ⟨a, haS⟩).2, ?_⟩
      simpa [hinv ⟨a, haS⟩] using hlt
    · intro a₁ ha₁ a₂ ha₂ heq
      have h1 : a₁ ∈ S := (Finset.mem_filter.mp ha₁).1
      have h2 : a₂ ∈ S := (Finset.mem_filter.mp ha₂).1
      have hsub : σ ⟨a₁, h1⟩ = σ ⟨a₂, h2⟩ := Subtype.ext heq
      have := congrArg σ hsub
      rw [hinv, hinv] at this
      exact congrArg Subtype.val this
    · intro b hb
      rcases Finset.mem_filter.mp hb with ⟨hbS, _, hlt⟩
      let a : S := σ ⟨b, hbS⟩
      refine ⟨a.1, ?_, ?_⟩
      · refine Finset.mem_filter.mpr ⟨a.2, a.2, ?_⟩
        simpa [a, hinv ⟨b, hbS⟩] using hlt
      · simpa [a] using congrArg Subtype.val (hinv ⟨b, hbS⟩)
  refine ⟨L.card, ?_⟩
  rw [← hunion, Finset.card_union_of_disjoint hdisj, hcardEq]

/-! ### Part 2: Order-isomorphism invariance of `CactusS` -/

private def cactusSOrderIsoEquiv {r₁ r₂ : ℕ} {S₁ S₂ : Finset ℕ}
    (hr₁ : ∀ x ∈ S₁, r₁ < x) (hr₂ : ∀ x ∈ S₂, r₂ < x) (hcard : S₁.card = S₂.card) :
    CactusS r₁ S₁ ≃ CactusS r₂ S₂ := by
  classical
  let e : S₁ ≃o S₂ := (S₁.orderIsoOfFin rfl).symm.trans (S₂.orderIsoOfFin hcard.symm)
  let liftVal : ℕ → ℕ := fun x => if hx : x ∈ S₁ then (e ⟨x, hx⟩ : ℕ) else r₂
  let unliftVal : ℕ → ℕ := fun y => if hy : y ∈ S₂ then (e.symm ⟨y, hy⟩ : ℕ) else r₁
  have hr₁_not : r₁ ∉ S₁ := fun h => Nat.lt_irrefl r₁ (hr₁ r₁ h)
  have hr₂_not : r₂ ∉ S₂ := fun h => Nat.lt_irrefl r₂ (hr₂ r₂ h)
  have hlift_mem : ∀ {x}, x ∈ insert r₁ S₁ → liftVal x ∈ insert r₂ S₂ := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hxS
    · simp [liftVal, hr₁_not]
    · simp only [liftVal, dif_pos hxS]
      exact Finset.mem_insert_of_mem (e ⟨x, hxS⟩).2
  have hunlift_mem : ∀ {y}, y ∈ insert r₂ S₂ → unliftVal y ∈ insert r₁ S₁ := by
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hyS
    · simp [unliftVal, hr₂_not]
    · simp only [unliftVal, dif_pos hyS]
      exact Finset.mem_insert_of_mem (e.symm ⟨y, hyS⟩).2
  have hlift_lt : ∀ {u} {v : S₁}, u ∈ insert r₁ S₁ → u < (v : ℕ) → liftVal u < (e v : ℕ) := by
    intro u v hu hlt
    rcases Finset.mem_insert.mp hu with rfl | huS
    · simp only [liftVal, dif_neg hr₁_not]
      exact hr₂ (e v : ℕ) (e v).2
    · simp only [liftVal, dif_pos huS]
      exact e.strictMono (show (⟨u, huS⟩ : S₁) < v from hlt)
  have hunlift_lt : ∀ {u} {v : S₂}, u ∈ insert r₂ S₂ → u < (v : ℕ) → unliftVal u < (e.symm v : ℕ) := by
    intro u v hu hlt
    rcases Finset.mem_insert.mp hu with rfl | huS
    · simp only [unliftVal, dif_neg hr₂_not]
      exact hr₁ (e.symm v : ℕ) (e.symm v).2
    · simp only [unliftVal, dif_pos huS]
      exact e.symm.strictMono (show (⟨u, huS⟩ : S₂) < v from hlt)
  have hunlift_lift : ∀ {u}, u ∈ insert r₁ S₁ → unliftVal (liftVal u) = u := by
    intro u hu
    rcases Finset.mem_insert.mp hu with rfl | huS
    · simp [liftVal, unliftVal, hr₁_not, hr₂_not]
    · simp only [liftVal, dif_pos huS, unliftVal, dif_pos (e ⟨u, huS⟩).2]
      simp
  have hlift_unlift : ∀ {v}, v ∈ insert r₂ S₂ → liftVal (unliftVal v) = v := by
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hvS
    · simp [liftVal, unliftVal, hr₁_not, hr₂_not]
    · simp only [unliftVal, dif_pos hvS, liftVal, dif_pos (e.symm ⟨v, hvS⟩).2]
      simp
  exact
    { toFun := fun c =>
        { σ := fun y => e (c.σ (e.symm y))
          par := fun y => liftVal (c.par (e.symm y))
          hneq := fun y h => c.hneq (e.symm y) (e.injective (by simpa using h))
          hinv := fun y => by simp [c.hinv]
          hpar_mem := fun y => hlift_mem (c.hpar_mem (e.symm y))
          hpar_symm := fun y => by simp [c.hpar_symm]
          hpar_lt := fun y => by
            simpa using hlift_lt (c.hpar_mem (e.symm y)) (c.hpar_lt (e.symm y)) }
      invFun := fun d =>
        { σ := fun x => e.symm (d.σ (e x))
          par := fun x => unliftVal (d.par (e x))
          hneq := fun x h => d.hneq (e x) (e.symm.injective (by simpa using h))
          hinv := fun x => by simp [d.hinv]
          hpar_mem := fun x => hunlift_mem (d.hpar_mem (e x))
          hpar_symm := fun x => by simp [d.hpar_symm]
          hpar_lt := fun x => by
            simpa using hunlift_lt (d.hpar_mem (e x)) (d.hpar_lt (e x)) }
      left_inv := fun c => by
        apply CactusS.ext
        · funext x; simp
        · funext x; simp [hunlift_lift (c.hpar_mem x)]
      right_inv := fun d => by
        apply CactusS.ext
        · funext y; simp
        · funext y; simp [hlift_unlift (d.hpar_mem y)] }

private lemma card_cactusS_eq_c {r : ℕ} {S : Finset ℕ} {m : ℕ}
    (hr : ∀ x ∈ S, r < x) (hcard : S.card = 2 * m) :
    Fintype.card (CactusS r S) = c m := by
  unfold c
  refine Fintype.card_congr (cactusSOrderIsoEquiv hr ?_ ?_)
  · intro x hx
    have := (Finset.mem_Icc.mp hx).1
    omega
  · rw [hcard, Nat.card_Icc]
    omega

/-! ### Part 3: `c n = haf n` -/

private def finToIcc (n : ℕ) : Fin (2 * n) ≃ (Icc 1 (2 * n) : Finset ℕ) where
  toFun i := ⟨i.1 + 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩
  invFun x := ⟨x.1 - 1, by have := Finset.mem_Icc.mp x.2; omega⟩
  left_inv i := by ext; simp
  right_inv x := by ext; have := Finset.mem_Icc.mp x.2; dsimp; omega

private lemma c_eq_haf (n : ℕ) : c n = OMA.S_oeis_a002067.haf n := by
  classical
  let e := finToIcc n
  let M : Finset (Equiv.Perm (Fin (2 * n))) :=
    Finset.univ.filter (fun σ => ∀ i, σ i ≠ i ∧ σ (σ i) = i)
  let L : M → Finset (Fin (2 * n)) :=
    fun τ => Finset.univ.filter (fun i => i < τ.1 i)
  have hEquiv : CactusS 0 (Icc 1 (2 * n)) ≃
      (Σ τ : M, (i : L τ) → Fin ((i.1 : ℕ) + 1)) :=
    { toFun := fun g =>
        let σPerm : Equiv.Perm (Fin (2 * n)) :=
          { toFun := fun i => e.symm (g.σ (e i))
            invFun := fun i => e.symm (g.σ (e i))
            left_inv := fun i => by simp [g.hinv]
            right_inv := fun i => by simp [g.hinv] }
        have hM : σPerm ∈ M := by
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun i => ⟨?_, ?_⟩⟩
          · intro h
            have h' : g.σ (e i) = e i := by
              have := congrArg e h
              simpa [σPerm] using this
            exact g.hneq (e i) h'
          · simp [σPerm, g.hinv]
        ⟨⟨σPerm, hM⟩, fun i =>
          ⟨g.par (e i.1), by
            have hlt := g.hpar_lt (e i.1)
            simpa [e, finToIcc] using hlt⟩⟩
      invFun := fun ⟨τ, f⟩ =>
        have hτ := (Finset.mem_filter.mp τ.2).2
        let parFin : Fin (2 * n) → ℕ := fun i =>
          if hi : i < τ.1 i then
            (f ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩).1
          else
            (f ⟨τ.1 i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
              have hne : τ.1 i ≠ i := (hτ i).1
              have hinv : τ.1 (τ.1 i) = i := (hτ i).2
              rw [hinv]
              exact lt_of_le_of_ne (not_lt.mp hi) hne⟩⟩).1
        have hpar_symm' : ∀ i : Fin (2 * n), parFin (τ.1 i) = parFin i := by
          intro i
          have hne : τ.1 i ≠ i := (hτ i).1
          have hinv : τ.1 (τ.1 i) = i := (hτ i).2
          by_cases hi : i < τ.1 i
          · have hnot : ¬ τ.1 i < τ.1 (τ.1 i) := by rw [hinv]; exact not_lt.mpr (le_of_lt hi)
            simp only [parFin, dif_pos hi, dif_neg hnot]
            exact congrArg (fun x => (f x).1) (Subtype.ext hinv)
          · have hlt : τ.1 i < τ.1 (τ.1 i) := by
              rw [hinv]
              exact lt_of_le_of_ne (not_lt.mp hi) hne
            simp only [parFin, dif_neg hi, dif_pos hlt]
        have hpar_lt' : ∀ i : Fin (2 * n), parFin i < i.1 + 1 := by
          intro i
          have hne : τ.1 i ≠ i := (hτ i).1
          have hinv : τ.1 (τ.1 i) = i := (hτ i).2
          by_cases hi : i < τ.1 i
          · simp only [parFin, dif_pos hi]
            exact (f _).2
          · simp only [parFin, dif_neg hi]
            have hlt : τ.1 i < i := lt_of_le_of_ne (not_lt.mp hi) hne
            have hf : (f ⟨τ.1 i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [hinv]; exact hlt⟩⟩).1 < (τ.1 i : ℕ) + 1 :=
              (f ⟨τ.1 i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [hinv]; exact hlt⟩⟩).2
            have : (τ.1 i : ℕ) < (i : ℕ) := hlt
            omega
        { σ := fun x => e (τ.1 (e.symm x))
          par := fun x => parFin (e.symm x)
          hneq := fun x h => (hτ (e.symm x)).1 (e.injective (by simpa using h))
          hinv := fun x => by simp [(hτ (e.symm x)).2]
          hpar_mem := fun x => by
            have hlt : parFin (e.symm x) < (x : ℕ) := by
              have h1 := hpar_lt' (e.symm x)
              have hx := Finset.mem_Icc.mp x.2
              have hev : (e.symm x : ℕ) + 1 = (x : ℕ) := by simp [e, finToIcc]; omega
              omega
            have hx := Finset.mem_Icc.mp x.2
            rcases Nat.eq_zero_or_pos (parFin (e.symm x)) with h0 | hpos
            · simp [h0]
            · exact Finset.mem_insert_of_mem (Finset.mem_Icc.mpr ⟨hpos, by omega⟩)
          hpar_symm := fun x => by simpa using hpar_symm' (e.symm x)
          hpar_lt := fun x => by
            have h1 := hpar_lt' (e.symm x)
            have hx := Finset.mem_Icc.mp x.2
            have hev : (e.symm x : ℕ) + 1 = (x : ℕ) := by simp [e, finToIcc]; omega
            omega }
      left_inv := fun g => by
        apply CactusS.ext
        · funext x; simp
        · funext x
          dsimp only
          split_ifs with hi
          · simp
          · simp [g.hpar_symm]
      right_inv := fun ⟨τ, f⟩ => by
        have h_sigma_eq :
            ∀ {τ₁ τ₂ : M} (h : τ₁ = τ₂)
              (f₁ : (i : L τ₁) → Fin ((i.1 : ℕ) + 1))
              (f₂ : (i : L τ₂) → Fin ((i.1 : ℕ) + 1)),
              (∀ (i : Fin (2 * n)) (hi₁ : i ∈ L τ₁) (hi₂ : i ∈ L τ₂),
                (f₁ ⟨i, hi₁⟩ : ℕ) = (f₂ ⟨i, hi₂⟩ : ℕ)) →
              (⟨τ₁, f₁⟩ : Σ τ : M, (i : L τ) → Fin ((i.1 : ℕ) + 1)) = ⟨τ₂, f₂⟩ := by
          rintro τ₁ _ rfl f₁ f₂ hval
          congr 1
          funext ⟨i, hi⟩
          exact Fin.ext (hval i hi hi)
        refine h_sigma_eq ?_ _ _ ?_
        · apply Subtype.ext
          ext i
          simp
        · intro i hi₁ hi₂
          have hlt : i < τ.1 i := (Finset.mem_filter.mp hi₂).2
          have hsub : (⟨e.symm (e i), by simpa [e.symm_apply_apply] using hi₂⟩ : L τ) = ⟨i, hi₂⟩ :=
            Subtype.ext (e.symm_apply_apply i)
          simpa [hlt] using congrArg (fun x => (f x).1) hsub }
  unfold c OMA.S_oeis_a002067.haf
  rw [Fintype.card_congr hEquiv, Fintype.card_sigma]
  have h1 : ∀ τ : M,
      Fintype.card ((i : L τ) → Fin ((i.1 : ℕ) + 1)) =
        ∏ i ∈ L τ, ((i : ℕ) + 1) := by
    intro τ
    rw [Fintype.card_pi]
    simp only [Fintype.card_fin]
    exact Finset.prod_coe_sort (L τ) (fun i => (i : ℕ) + 1)
  simp_rw [h1]
  exact Finset.sum_coe_sort M (fun σ => ∏ i ∈ Finset.univ.filter (fun i => i < σ i), ((i : ℕ) + 1))

/-! ### Part 4: Three-way decomposition bijection at the triangle `{0, 1, σ 1}` -/

private def rootOfAux {V : Finset ℕ} (c : CactusS 0 V) (j : ℕ) : ℕ → ℕ → Fin 3
  | 0, _ => 0
  | fuel + 1, x =>
    if x = 0 then 0
    else if x = 1 then 1
    else if x = j then 2
    else if hx : x ∈ V then rootOfAux c j fuel (c.par ⟨x, hx⟩)
    else 0

private lemma rootOfAux_indep {V : Finset ℕ} (c : CactusS 0 V) (j : ℕ) :
    ∀ x, ∀ fuel₁ fuel₂, x ∈ insert 0 V → x < fuel₁ → x < fuel₂ →
      rootOfAux c j fuel₁ x = rootOfAux c j fuel₂ x := by
  intro x
  induction x using Nat.strongRecOn with
  | ind x ih =>
    intro fuel₁ fuel₂ hx h1 h2
    obtain ⟨f₁, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : fuel₁ ≠ 0)
    obtain ⟨f₂, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : fuel₂ ≠ 0)
    simp only [rootOfAux]
    split_ifs with h0 h1' hj hxV
    · rfl
    · rfl
    · rfl
    · have hlt : c.par ⟨x, hxV⟩ < x := c.hpar_lt ⟨x, hxV⟩
      exact ih (c.par ⟨x, hxV⟩) hlt f₁ f₂
        (c.hpar_mem ⟨x, hxV⟩) (by omega) (by omega)
    · rfl

private def rootOf {V : Finset ℕ} (c : CactusS 0 V) (j x : ℕ) : Fin 3 :=
  rootOfAux c j (x + 1) x

private lemma rootOf_zero {V : Finset ℕ} (c : CactusS 0 V) (j : ℕ) :
    rootOf c j 0 = 0 := by
  simp [rootOf, rootOfAux]

private lemma rootOf_one {V : Finset ℕ} (c : CactusS 0 V) (j : ℕ) :
    rootOf c j 1 = 1 := by
  simp [rootOf, rootOfAux]

private lemma rootOf_j {V : Finset ℕ} (c : CactusS 0 V) {j : ℕ} (hj : 2 ≤ j) :
    rootOf c j j = 2 := by
  unfold rootOf rootOfAux
  have h0 : j ≠ 0 := by omega
  have h1 : j ≠ 1 := by omega
  simp [h0, h1]

private lemma rootOf_step {V : Finset ℕ} (c : CactusS 0 V) (j : ℕ)
    {x : ℕ} (hx : x ∈ V) (hx0 : x ≠ 0) (hx1 : x ≠ 1) (hxj : x ≠ j) :
    rootOf c j x = rootOf c j (c.par ⟨x, hx⟩) := by
  unfold rootOf
  simp only [rootOfAux, if_neg hx0, if_neg hx1, if_neg hxj, dif_pos hx]
  exact rootOfAux_indep c j (c.par ⟨x, hx⟩) x (c.par ⟨x, hx⟩ + 1)
    (c.hpar_mem ⟨x, hx⟩) (c.hpar_lt ⟨x, hx⟩) (Nat.lt_succ_self _)

private lemma le_of_rootOf_eq_two {V : Finset ℕ} (c : CactusS 0 V) (j : ℕ) :
    ∀ x, x ∈ insert 0 V → rootOf c j x = 2 → j ≤ x := by
  intro x
  induction x using Nat.strongRecOn with
  | ind x ih =>
    intro hx h2
    by_cases h0 : x = 0
    · subst h0; rw [rootOf_zero] at h2; contradiction
    by_cases h1 : x = 1
    · subst h1; rw [rootOf_one] at h2; contradiction
    by_cases hxj : x = j
    · omega
    have hxV : x ∈ V := by
      rcases Finset.mem_insert.mp hx with rfl | h
      · exact absurd rfl h0
      · exact h
    rw [rootOf_step c j hxV h0 h1 hxj] at h2
    have hlt : c.par ⟨x, hxV⟩ < x := c.hpar_lt ⟨x, hxV⟩
    have hle := ih (c.par ⟨x, hxV⟩) hlt (c.hpar_mem ⟨x, hxV⟩) h2
    omega

private abbrev Vset (n : ℕ) : Finset ℕ := Icc 1 (2 * (n + 1))

private abbrev Uset (n : ℕ) : Finset ℕ := Icc 2 (2 * (n + 1))

private def T2Finset (n : ℕ) : Finset (Finset ℕ) :=
  (Uset n).powerset.filter (fun T => T.card % 2 = 1)

private abbrev T2Type (n : ℕ) := { T : Finset ℕ // T ∈ T2Finset n }

private def S0Finset (n : ℕ) (T : T2Type n) : Finset (Finset ℕ) :=
  (Uset n \ T.1).powerset.filter (fun S => S.card % 2 = 0)

private abbrev S0Type (n : ℕ) (T : T2Type n) := { S : Finset ℕ // S ∈ S0Finset n T }

private lemma T2Type.sub_Uset {n : ℕ} (T : T2Type n) : T.1 ⊆ Uset n :=
  Finset.mem_powerset.mp (Finset.mem_filter.mp T.2).1

private lemma T2Type.card_mod {n : ℕ} (T : T2Type n) : T.1.card % 2 = 1 :=
  (Finset.mem_filter.mp T.2).2

private lemma S0Type.sub_sdiff {n : ℕ} {T : T2Type n} (S0 : S0Type n T) : S0.1 ⊆ Uset n \ T.1 :=
  Finset.mem_powerset.mp (Finset.mem_filter.mp S0.2).1

private lemma S0Type.card_mod {n : ℕ} {T : T2Type n} (S0 : S0Type n T) : S0.1.card % 2 = 0 :=
  (Finset.mem_filter.mp S0.2).2

private def minT {n : ℕ} (T : T2Type n) : ℕ :=
  T.1.min' (Finset.card_pos.mp (by have := T.card_mod; omega))

private abbrev DecompTarget (n : ℕ) :=
  Σ T : T2Type n, Σ S0 : S0Type n T,
    CactusS 0 S0.1 × CactusS 1 ((Uset n \ T.1) \ S0.1) × CactusS (minT T) (T.1.erase (minT T))

private lemma one_mem_Vset (n : ℕ) : (1 : ℕ) ∈ Vset n :=
  Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩

private lemma Uset_sub_Vset (n : ℕ) : Uset n ⊆ Vset n := by
  intro x hx
  have := Finset.mem_Icc.mp hx
  exact Finset.mem_Icc.mpr ⟨by omega, this.2⟩

private lemma card_Uset (n : ℕ) : (Uset n).card = 2 * n + 1 := by
  simp only [Uset, Nat.card_Icc]
  omega

private lemma minT_mem {n : ℕ} (T : T2Type n) : minT T ∈ T.1 :=
  Finset.min'_mem T.1 (Finset.card_pos.mp (by have := T.card_mod; omega))

private lemma minT_mem_Uset {n : ℕ} (T : T2Type n) : minT T ∈ Uset n :=
  T.sub_Uset (minT_mem T)

private lemma minT_mem_Vset {n : ℕ} (T : T2Type n) : minT T ∈ Vset n :=
  Uset_sub_Vset n (minT_mem_Uset T)

private lemma minT_ge_two {n : ℕ} (T : T2Type n) : 2 ≤ minT T :=
  (Finset.mem_Icc.mp (minT_mem_Uset T)).1

private lemma minT_lt_of_mem_erase {n : ℕ} (T : T2Type n) {x : ℕ}
    (hx : x ∈ T.1.erase (minT T)) : minT T < x := by
  rcases Finset.mem_erase.mp hx with ⟨hne, hxT⟩
  exact lt_of_le_of_ne (Finset.min'_le T.1 x hxT) (Ne.symm hne)

private lemma decompTarget_ext {n : ℕ} {d₁ d₂ : DecompTarget n}
    (hT : d₁.1 = d₂.1)
    (hS0 : d₁.2.1.1 = d₂.2.1.1)
    (hC0σ : ∀ (x : ℕ) (h1 : x ∈ d₁.2.1.1) (h2 : x ∈ d₂.2.1.1),
      (d₁.2.2.1.σ ⟨x, h1⟩ : ℕ) = (d₂.2.2.1.σ ⟨x, h2⟩ : ℕ))
    (hC0p : ∀ (x : ℕ) (h1 : x ∈ d₁.2.1.1) (h2 : x ∈ d₂.2.1.1),
      d₁.2.2.1.par ⟨x, h1⟩ = d₂.2.2.1.par ⟨x, h2⟩)
    (hC1σ : ∀ (x : ℕ) (h1 : x ∈ (Uset n \ d₁.1.1) \ d₁.2.1.1) (h2 : x ∈ (Uset n \ d₂.1.1) \ d₂.2.1.1),
      (d₁.2.2.2.1.σ ⟨x, h1⟩ : ℕ) = (d₂.2.2.2.1.σ ⟨x, h2⟩ : ℕ))
    (hC1p : ∀ (x : ℕ) (h1 : x ∈ (Uset n \ d₁.1.1) \ d₁.2.1.1) (h2 : x ∈ (Uset n \ d₂.1.1) \ d₂.2.1.1),
      d₁.2.2.2.1.par ⟨x, h1⟩ = d₂.2.2.2.1.par ⟨x, h2⟩)
    (hC2σ : ∀ (x : ℕ) (h1 : x ∈ d₁.1.1.erase (minT d₁.1)) (h2 : x ∈ d₂.1.1.erase (minT d₂.1)),
      (d₁.2.2.2.2.σ ⟨x, h1⟩ : ℕ) = (d₂.2.2.2.2.σ ⟨x, h2⟩ : ℕ))
    (hC2p : ∀ (x : ℕ) (h1 : x ∈ d₁.1.1.erase (minT d₁.1)) (h2 : x ∈ d₂.1.1.erase (minT d₂.1)),
      d₁.2.2.2.2.par ⟨x, h1⟩ = d₂.2.2.2.2.par ⟨x, h2⟩) :
    d₁ = d₂ := by
  rcases d₁ with ⟨T₁, ⟨S0₁, hS0₁⟩, C0₁, C1₁, C2₁⟩
  rcases d₂ with ⟨T₂, ⟨S0₂, hS0₂⟩, C0₂, C1₂, C2₂⟩
  dsimp only at hT hS0
  subst hT
  subst hS0
  have hC0 : C0₁ = C0₂ := CactusS.ext (funext fun ⟨x, hx⟩ => Subtype.ext (hC0σ x hx hx))
    (funext fun ⟨x, hx⟩ => hC0p x hx hx)
  have hC1 : C1₁ = C1₂ := CactusS.ext (funext fun ⟨x, hx⟩ => Subtype.ext (hC1σ x hx hx))
    (funext fun ⟨x, hx⟩ => hC1p x hx hx)
  have hC2 : C2₁ = C2₂ := CactusS.ext (funext fun ⟨x, hx⟩ => Subtype.ext (hC2σ x hx hx))
    (funext fun ⟨x, hx⟩ => hC2p x hx hx)
  simp [hC0, hC1, hC2]

private lemma σ_preserves_root {n : ℕ} (g : CactusS 0 (Vset n)) {x : ℕ}
    (hx : x ∈ Uset n) (hxj : x ≠ (g.σ ⟨1, one_mem_Vset n⟩ : ℕ)) :
    (g.σ ⟨x, Uset_sub_Vset n hx⟩ : ℕ) ∈ Uset n ∧
    (g.σ ⟨x, Uset_sub_Vset n hx⟩ : ℕ) ≠ (g.σ ⟨1, one_mem_Vset n⟩ : ℕ) ∧
    rootOf g (g.σ ⟨1, one_mem_Vset n⟩ : ℕ) (g.σ ⟨x, Uset_sub_Vset n hx⟩ : ℕ) =
      rootOf g (g.σ ⟨1, one_mem_Vset n⟩ : ℕ) x := by
  let v1 : Vset n := ⟨1, one_mem_Vset n⟩
  let j : ℕ := (g.σ v1 : ℕ)
  have hxV : x ∈ Vset n := Uset_sub_Vset n hx
  have hx0 : x ≠ 0 := by have := (Finset.mem_Icc.mp hx).1; omega
  have hx1 : x ≠ 1 := by have := (Finset.mem_Icc.mp hx).1; omega
  let y : Vset n := g.σ ⟨x, hxV⟩
  have hy1 : y.1 ≠ 1 := by
    intro hy1
    have hy_eq : y = v1 := Subtype.ext hy1
    have := congrArg g.σ hy_eq
    rw [g.hinv] at this
    exact hxj (congrArg Subtype.val this)
  have hyj : y.1 ≠ j := by
    intro hyj
    have hy_eq : y = g.σ v1 := Subtype.ext hyj
    have := congrArg g.σ hy_eq
    rw [g.hinv, g.hinv] at this
    exact hx1 (congrArg Subtype.val this)
  have hyU : y.1 ∈ Uset n := by
    have hyV := Finset.mem_Icc.mp y.2
    exact Finset.mem_Icc.mpr ⟨by omega, hyV.2⟩
  have hy0 : y.1 ≠ 0 := by have := (Finset.mem_Icc.mp hyU).1; omega
  refine ⟨hyU, hyj, ?_⟩
  rw [rootOf_step g j y.2 hy0 hy1 hyj, rootOf_step g j hxV hx0 hx1 hxj]
  exact congrArg (rootOf g j) (g.hpar_symm ⟨x, hxV⟩)

private noncomputable def decompFwd (n : ℕ) (g : CactusS 0 (Vset n)) : DecompTarget n := by
  classical
  let v1 : Vset n := ⟨1, one_mem_Vset n⟩
  let j : ℕ := (g.σ v1 : ℕ)
  have hj_ne1 : j ≠ 1 := fun h => g.hneq v1 (Subtype.ext h)
  have hj_U : j ∈ Uset n := by
    have hjV := Finset.mem_Icc.mp (g.σ v1).2
    exact Finset.mem_Icc.mpr ⟨by omega, hjV.2⟩
  have hj_ge2 : 2 ≤ j := (Finset.mem_Icc.mp hj_U).1
  let T2 : Finset ℕ := (Uset n).filter (fun x => rootOf g j x = 2)
  let S0 : Finset ℕ := (Uset n).filter (fun x => rootOf g j x = 0)
  let S1 : Finset ℕ := (Uset n).filter (fun x => rootOf g j x = 1)
  let S2 : Finset ℕ := T2.erase j
  have hj_T2 : j ∈ T2 := Finset.mem_filter.mpr ⟨hj_U, rootOf_j g hj_ge2⟩
  have hT2_nonempty : T2.Nonempty := ⟨j, hj_T2⟩
  have hmin_T2 : T2.min' hT2_nonempty = j := by
    apply le_antisymm
    · exact Finset.min'_le T2 j hj_T2
    · have hmem := Finset.min'_mem T2 hT2_nonempty
      rcases Finset.mem_filter.mp hmem with ⟨hmU, hm2⟩
      exact le_of_rootOf_eq_two g j _ (Finset.mem_insert_of_mem (Uset_sub_Vset n hmU)) hm2
  have hS0_even : S0.card % 2 = 0 := by
    have hEv := even_card_of_fpf_invol S0
      (fun x =>
        ⟨(g.σ ⟨x.1, Uset_sub_Vset n (Finset.mem_filter.mp x.2).1⟩ : ℕ), by
          have hxF := Finset.mem_filter.mp x.2
          have hxj : x.1 ≠ j := fun h => by
            rw [h, rootOf_j g hj_ge2] at hxF
            exact absurd hxF.2 (by decide)
          have hσ := σ_preserves_root g hxF.1 hxj
          exact Finset.mem_filter.mpr ⟨hσ.1, by rw [hσ.2.2, hxF.2]⟩⟩)
      (fun x h => by
        have hv : (g.σ ⟨x.1, Uset_sub_Vset n (Finset.mem_filter.mp x.2).1⟩ : ℕ) = x.1 :=
          congrArg Subtype.val h
        exact g.hneq _ (Subtype.ext hv))
      (fun x => by
        have hv := congrArg (Subtype.val : Vset n → ℕ)
          (g.hinv ⟨x.1, Uset_sub_Vset n (Finset.mem_filter.mp x.2).1⟩)
        exact Subtype.ext hv)
    rcases hEv with ⟨k, hk⟩
    omega
  have hS2_even : Even S2.card := by
    refine even_card_of_fpf_invol S2
      (fun x =>
        ⟨(g.σ ⟨x.1, Uset_sub_Vset n (Finset.mem_filter.mp (Finset.mem_erase.mp x.2).2).1⟩ : ℕ), by
          have hxE := Finset.mem_erase.mp x.2
          have hxF := Finset.mem_filter.mp hxE.2
          have hσ := σ_preserves_root g hxF.1 hxE.1
          exact Finset.mem_erase.mpr ⟨hσ.2.1, Finset.mem_filter.mpr ⟨hσ.1, by rw [hσ.2.2, hxF.2]⟩⟩⟩)
      (fun x h => by
        have hv : (g.σ ⟨x.1, Uset_sub_Vset n (Finset.mem_filter.mp (Finset.mem_erase.mp x.2).2).1⟩ : ℕ) = x.1 :=
          congrArg Subtype.val h
        exact g.hneq _ (Subtype.ext hv))
      (fun x => by
        have hv := congrArg (Subtype.val : Vset n → ℕ)
          (g.hinv ⟨x.1, Uset_sub_Vset n (Finset.mem_filter.mp (Finset.mem_erase.mp x.2).2).1⟩)
        exact Subtype.ext hv)
  have hT2_odd : T2.card % 2 = 1 := by
    have hcardS2 : S2.card + 1 = T2.card := by
      simpa [S2] using Finset.card_erase_add_one hj_T2
    rcases hS2_even with ⟨k, hk⟩
    omega
  let T2' : T2Type n :=
    ⟨T2, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.filter_subset _ _), hT2_odd⟩⟩
  have hminT_T2' : minT T2' = j := hmin_T2
  have hS0_sub : S0 ⊆ Uset n \ T2 := by
    intro x hx
    rcases Finset.mem_filter.mp hx with ⟨hxU, hx0⟩
    refine Finset.mem_sdiff.mpr ⟨hxU, ?_⟩
    intro hx2
    have h2 := (Finset.mem_filter.mp hx2).2
    rw [hx0] at h2
    contradiction
  let S0' : S0Type n T2' :=
    ⟨S0, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hS0_sub, hS0_even⟩⟩
  have hS1_eq : (Uset n \ T2) \ S0 = S1 := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_filter, T2, S0, S1]
    constructor
    · rintro ⟨⟨hxU, hn2⟩, hn0⟩
      refine ⟨hxU, ?_⟩
      have hne2 : rootOf g j x ≠ 2 := fun h => hn2 ⟨hxU, h⟩
      have hne0 : rootOf g j x ≠ 0 := fun h => hn0 ⟨hxU, h⟩
      match h : rootOf g j x with
      | 0 => exact absurd h hne0
      | 1 => rfl
      | 2 => exact absurd h hne2
    · rintro ⟨hxU, hx1⟩
      exact ⟨⟨hxU, fun h => by rw [hx1] at h; exact absurd h.2 (by decide)⟩,
        fun h => by rw [hx1] at h; exact absurd h.2 (by decide)⟩
  have hmem_S1 : ∀ {x}, x ∈ (Uset n \ T2) \ S0 ↔ x ∈ S1 := fun {x} => Finset.ext_iff.mp hS1_eq x
  let C0 : CactusS 0 S0 :=
    { σ := fun x =>
        ⟨(g.σ ⟨x.1, Uset_sub_Vset n (Finset.mem_filter.mp x.2).1⟩ : ℕ), by
          have hxF := Finset.mem_filter.mp x.2
          have hxj : x.1 ≠ j := fun h => by
            rw [h, rootOf_j g hj_ge2] at hxF
            exact absurd hxF.2 (by decide)
          have hσ := σ_preserves_root g hxF.1 hxj
          exact Finset.mem_filter.mpr ⟨hσ.1, by rw [hσ.2.2, hxF.2]⟩⟩
      par := fun x => g.par ⟨x.1, Uset_sub_Vset n (Finset.mem_filter.mp x.2).1⟩
      hneq := fun x h => by
        have hv : (g.σ ⟨x.1, Uset_sub_Vset n (Finset.mem_filter.mp x.2).1⟩ : ℕ) = x.1 :=
          congrArg Subtype.val h
        exact g.hneq _ (Subtype.ext hv)
      hinv := fun x => by
        have hv := congrArg (Subtype.val : Vset n → ℕ)
          (g.hinv ⟨x.1, Uset_sub_Vset n (Finset.mem_filter.mp x.2).1⟩)
        exact Subtype.ext hv
      hpar_mem := fun x => by
        rcases Finset.mem_filter.mp x.2 with ⟨hxU, hx0⟩
        have hxV := Uset_sub_Vset n hxU
        have hxne0 : x.1 ≠ 0 := by have := (Finset.mem_Icc.mp hxU).1; omega
        have hxne1 : x.1 ≠ 1 := by have := (Finset.mem_Icc.mp hxU).1; omega
        have hxnej : x.1 ≠ j := fun h => by
          rw [h, rootOf_j g hj_ge2] at hx0
          exact absurd hx0 (by decide)
        have hproot : rootOf g j (g.par ⟨x.1, hxV⟩) = 0 := by
          rw [← rootOf_step g j hxV hxne0 hxne1 hxnej, hx0]
        rcases Finset.mem_insert.mp (g.hpar_mem ⟨x.1, hxV⟩) with hp0 | hpV
        · exact Finset.mem_insert.mpr (Or.inl hp0)
        · have hp1 : g.par ⟨x.1, hxV⟩ ≠ 1 := fun h => by rw [h, rootOf_one] at hproot; contradiction
          have hpU : g.par ⟨x.1, hxV⟩ ∈ Uset n := by
            have h := Finset.mem_Icc.mp hpV
            exact Finset.mem_Icc.mpr ⟨by omega, h.2⟩
          exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hpU, hproot⟩)
      hpar_symm := fun x => g.hpar_symm ⟨x.1, Uset_sub_Vset n (Finset.mem_filter.mp x.2).1⟩
      hpar_lt := fun x => g.hpar_lt ⟨x.1, Uset_sub_Vset n (Finset.mem_filter.mp x.2).1⟩ }
  let C1 : CactusS 1 ((Uset n \ T2) \ S0) :=
    { σ := fun x =>
        ⟨(g.σ ⟨x.1, Uset_sub_Vset n (Finset.mem_filter.mp (hmem_S1.mp x.2)).1⟩ : ℕ), by
          have hxF := Finset.mem_filter.mp (hmem_S1.mp x.2)
          have hxj : x.1 ≠ j := fun h => by
            rw [h, rootOf_j g hj_ge2] at hxF
            exact absurd hxF.2 (by decide)
          have hσ := σ_preserves_root g hxF.1 hxj
          exact hmem_S1.mpr (Finset.mem_filter.mpr ⟨hσ.1, by rw [hσ.2.2, hxF.2]⟩)⟩
      par := fun x => g.par ⟨x.1, Uset_sub_Vset n (Finset.mem_filter.mp (hmem_S1.mp x.2)).1⟩
      hneq := fun x h => by
        have hv : (g.σ ⟨x.1, Uset_sub_Vset n (Finset.mem_filter.mp (hmem_S1.mp x.2)).1⟩ : ℕ) = x.1 :=
          congrArg Subtype.val h
        exact g.hneq _ (Subtype.ext hv)
      hinv := fun x => by
        have hv := congrArg (Subtype.val : Vset n → ℕ)
          (g.hinv ⟨x.1, Uset_sub_Vset n (Finset.mem_filter.mp (hmem_S1.mp x.2)).1⟩)
        exact Subtype.ext hv
      hpar_mem := fun x => by
        rcases Finset.mem_filter.mp (hmem_S1.mp x.2) with ⟨hxU, hx1⟩
        have hxV := Uset_sub_Vset n hxU
        have hxne0 : x.1 ≠ 0 := by have := (Finset.mem_Icc.mp hxU).1; omega
        have hxne1 : x.1 ≠ 1 := by have := (Finset.mem_Icc.mp hxU).1; omega
        have hxnej : x.1 ≠ j := fun h => by
          rw [h, rootOf_j g hj_ge2] at hx1
          exact absurd hx1 (by decide)
        have hproot : rootOf g j (g.par ⟨x.1, hxV⟩) = 1 := by
          rw [← rootOf_step g j hxV hxne0 hxne1 hxnej, hx1]
        rcases Finset.mem_insert.mp (g.hpar_mem ⟨x.1, hxV⟩) with hp0 | hpV
        · rw [hp0, rootOf_zero] at hproot; contradiction
        · by_cases hp1 : g.par ⟨x.1, hxV⟩ = 1
          · exact Finset.mem_insert.mpr (Or.inl hp1)
          · have hpU : g.par ⟨x.1, hxV⟩ ∈ Uset n := by
              have h := Finset.mem_Icc.mp hpV
              exact Finset.mem_Icc.mpr ⟨by omega, h.2⟩
            exact Finset.mem_insert_of_mem (hmem_S1.mpr (Finset.mem_filter.mpr ⟨hpU, hproot⟩))
      hpar_symm := fun x => g.hpar_symm ⟨x.1, Uset_sub_Vset n (Finset.mem_filter.mp (hmem_S1.mp x.2)).1⟩
      hpar_lt := fun x => g.hpar_lt ⟨x.1, Uset_sub_Vset n (Finset.mem_filter.mp (hmem_S1.mp x.2)).1⟩ }
  let C2 : CactusS (minT T2') (T2.erase (minT T2')) :=
    { σ := fun x =>
        ⟨(g.σ ⟨x.1, Uset_sub_Vset n (Finset.mem_filter.mp (Finset.mem_erase.mp x.2).2).1⟩ : ℕ), by
          have hxE := Finset.mem_erase.mp x.2
          have hxF := Finset.mem_filter.mp hxE.2
          have hxj : x.1 ≠ j := fun h => hxE.1 (h.trans hminT_T2'.symm)
          have hσ := σ_preserves_root g hxF.1 hxj
          exact Finset.mem_erase.mpr ⟨fun h => hσ.2.1 (h.trans hminT_T2'),
            Finset.mem_filter.mpr ⟨hσ.1, by rw [hσ.2.2, hxF.2]⟩⟩⟩
      par := fun x => g.par ⟨x.1, Uset_sub_Vset n (Finset.mem_filter.mp (Finset.mem_erase.mp x.2).2).1⟩
      hneq := fun x h => by
        have hv : (g.σ ⟨x.1, Uset_sub_Vset n (Finset.mem_filter.mp (Finset.mem_erase.mp x.2).2).1⟩ : ℕ) = x.1 :=
          congrArg Subtype.val h
        exact g.hneq _ (Subtype.ext hv)
      hinv := fun x => by
        have hv := congrArg (Subtype.val : Vset n → ℕ)
          (g.hinv ⟨x.1, Uset_sub_Vset n (Finset.mem_filter.mp (Finset.mem_erase.mp x.2).2).1⟩)
        exact Subtype.ext hv
      hpar_mem := fun x => by
        have hxE := Finset.mem_erase.mp x.2
        rcases Finset.mem_filter.mp hxE.2 with ⟨hxU, hx2⟩
        have hxV := Uset_sub_Vset n hxU
        have hxne0 : x.1 ≠ 0 := by have := (Finset.mem_Icc.mp hxU).1; omega
        have hxne1 : x.1 ≠ 1 := by have := (Finset.mem_Icc.mp hxU).1; omega
        have hxnej : x.1 ≠ j := fun h => hxE.1 (h.trans hminT_T2'.symm)
        have hproot : rootOf g j (g.par ⟨x.1, hxV⟩) = 2 := by
          rw [← rootOf_step g j hxV hxne0 hxne1 hxnej, hx2]
        rcases Finset.mem_insert.mp (g.hpar_mem ⟨x.1, hxV⟩) with hp0 | hpV
        · rw [hp0, rootOf_zero] at hproot; contradiction
        · have hp1 : g.par ⟨x.1, hxV⟩ ≠ 1 := fun h => by rw [h, rootOf_one] at hproot; contradiction
          have hpU : g.par ⟨x.1, hxV⟩ ∈ Uset n := by
            have h := Finset.mem_Icc.mp hpV
            exact Finset.mem_Icc.mpr ⟨by omega, h.2⟩
          have hpT2 : g.par ⟨x.1, hxV⟩ ∈ T2 := Finset.mem_filter.mpr ⟨hpU, hproot⟩
          rw [Finset.insert_erase (minT_mem T2')]
          exact hpT2
      hpar_symm := fun x => g.hpar_symm ⟨x.1, Uset_sub_Vset n (Finset.mem_filter.mp (Finset.mem_erase.mp x.2).2).1⟩
      hpar_lt := fun x => g.hpar_lt ⟨x.1, Uset_sub_Vset n (Finset.mem_filter.mp (Finset.mem_erase.mp x.2).2).1⟩ }
  exact ⟨T2', S0', C0, C1, C2⟩

private noncomputable def decompBwd (n : ℕ) (d : DecompTarget n) : CactusS 0 (Vset n) := by
  classical
  rcases d with ⟨T, S0, C0, C1, C2⟩
  let j : ℕ := minT T
  let S1 : Finset ℕ := (Uset n \ T.1) \ S0.1
  let S2 : Finset ℕ := T.1.erase j
  have h1V : (1 : ℕ) ∈ Vset n := one_mem_Vset n
  have hj_ne1 : j ≠ 1 := by have := minT_ge_two T; omega
  have hj_V : j ∈ Vset n := minT_mem_Vset T
  have hS0_sub_U : S0.1 ⊆ Uset n := Subset.trans S0.sub_sdiff Finset.sdiff_subset
  have hS1_sub_U : S1 ⊆ Uset n := Subset.trans Finset.sdiff_subset Finset.sdiff_subset
  have hS2_sub_U : S2 ⊆ Uset n := Subset.trans (Finset.erase_subset _ _) T.sub_Uset
  have hS0_not_1 : (1 : ℕ) ∉ S0.1 := fun h => by have := (Finset.mem_Icc.mp (hS0_sub_U h)).1; omega
  have hS1_not_1 : (1 : ℕ) ∉ S1 := fun h => by have := (Finset.mem_Icc.mp (hS1_sub_U h)).1; omega
  have hS2_not_1 : (1 : ℕ) ∉ S2 := fun h => by have := (Finset.mem_Icc.mp (hS2_sub_U h)).1; omega
  have hS0_not_j : j ∉ S0.1 := fun h => (Finset.mem_sdiff.mp (S0.sub_sdiff h)).2 (minT_mem T)
  have hS1_not_j : j ∉ S1 := fun h => (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp h).1).2 (minT_mem T)
  have hS2_not_j : j ∉ S2 := Finset.notMem_erase j T.1
  have hS0_S1 : Disjoint S0.1 S1 := by
    rw [Finset.disjoint_left]; intro x hx0 hx1; exact (Finset.mem_sdiff.mp hx1).2 hx0
  have hS0_S2 : Disjoint S0.1 S2 := by
    rw [Finset.disjoint_left]; intro x hx0 hx2
    exact (Finset.mem_sdiff.mp (S0.sub_sdiff hx0)).2 (Finset.mem_of_mem_erase hx2)
  have hS1_S2 : Disjoint S1 S2 := by
    rw [Finset.disjoint_left]; intro x hx1 hx2
    exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hx1).1).2 (Finset.mem_of_mem_erase hx2)
  have hcover : ∀ x : Vset n, x.1 ≠ 1 → x.1 ≠ j → x.1 ∉ S0.1 → x.1 ∉ S1 → x.1 ∈ S2 := by
    intro x hx1 hxj h0 h1
    have hxU : x.1 ∈ Uset n := by
      have := Finset.mem_Icc.mp x.2
      exact Finset.mem_Icc.mpr ⟨by omega, this.2⟩
    have hxT : x.1 ∈ T.1 := by
      by_contra hnT
      exact h1 (Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨hxU, hnT⟩, h0⟩)
    exact Finset.mem_erase.mpr ⟨hxj, hxT⟩
  let σFun : Vset n → Vset n := fun x =>
    if h1 : x.1 = 1 then ⟨j, hj_V⟩
    else if hj : x.1 = j then ⟨1, h1V⟩
    else if h0 : x.1 ∈ S0.1 then ⟨(C0.σ ⟨x.1, h0⟩).1, Uset_sub_Vset n (hS0_sub_U (C0.σ ⟨x.1, h0⟩).2)⟩
    else if h1' : x.1 ∈ S1 then ⟨(C1.σ ⟨x.1, h1'⟩).1, Uset_sub_Vset n (hS1_sub_U (C1.σ ⟨x.1, h1'⟩).2)⟩
    else
      have h2 : x.1 ∈ S2 := hcover x h1 hj h0 h1'
      ⟨(C2.σ ⟨x.1, h2⟩).1, Uset_sub_Vset n (hS2_sub_U (C2.σ ⟨x.1, h2⟩).2)⟩
  let parFun : Vset n → ℕ := fun x =>
    if h1 : x.1 = 1 then 0
    else if hj : x.1 = j then 0
    else if h0 : x.1 ∈ S0.1 then C0.par ⟨x.1, h0⟩
    else if h1' : x.1 ∈ S1 then C1.par ⟨x.1, h1'⟩
    else
      have h2 : x.1 ∈ S2 := hcover x h1 hj h0 h1'
      C2.par ⟨x.1, h2⟩
  exact
    { σ := σFun
      par := parFun
      hneq := fun x => by
        by_cases h1 : x.1 = 1
        · intro heq; simp only [σFun, dif_pos h1] at heq
          exact hj_ne1 (by simpa [h1] using congrArg Subtype.val heq)
        by_cases hj : x.1 = j
        · intro heq; simp only [σFun, dif_neg h1, dif_pos hj] at heq
          exact hj_ne1 (by simpa [hj] using (congrArg Subtype.val heq).symm)
        by_cases h0 : x.1 ∈ S0.1
        · intro heq; simp only [σFun, dif_neg h1, dif_neg hj, dif_pos h0] at heq
          have hv : (C0.σ ⟨x.1, h0⟩ : ℕ) = x.1 := congrArg Subtype.val heq
          exact C0.hneq ⟨x.1, h0⟩ (Subtype.ext hv)
        by_cases h1' : x.1 ∈ S1
        · intro heq; simp only [σFun, dif_neg h1, dif_neg hj, dif_neg h0, dif_pos h1'] at heq
          have hv : (C1.σ ⟨x.1, h1'⟩ : ℕ) = x.1 := congrArg Subtype.val heq
          exact C1.hneq ⟨x.1, h1'⟩ (Subtype.ext hv)
        · intro heq; simp only [σFun, dif_neg h1, dif_neg hj, dif_neg h0, dif_neg h1'] at heq
          have hv : (C2.σ ⟨x.1, hcover x h1 hj h0 h1'⟩ : ℕ) = x.1 := congrArg Subtype.val heq
          exact C2.hneq ⟨x.1, hcover x h1 hj h0 h1'⟩ (Subtype.ext hv)
      hinv := fun x => by
        by_cases h1 : x.1 = 1
        · simp only [σFun, dif_pos h1, dif_neg hj_ne1]
          exact Subtype.ext h1.symm
        by_cases hj : x.1 = j
        · simp only [σFun, dif_neg h1, dif_pos hj, dif_pos rfl]
          exact Subtype.ext hj.symm
        by_cases h0 : x.1 ∈ S0.1
        · have hm := (C0.σ ⟨x.1, h0⟩).2
          have hne1 : (C0.σ ⟨x.1, h0⟩).1 ≠ 1 := fun h => hS0_not_1 (h ▸ hm)
          have hnej : (C0.σ ⟨x.1, h0⟩).1 ≠ j := fun h => hS0_not_j (h ▸ hm)
          have h1s : σFun x = ⟨(C0.σ ⟨x.1, h0⟩).1, Uset_sub_Vset n (hS0_sub_U hm)⟩ := by
            simp only [σFun, dif_neg h1, dif_neg hj, dif_pos h0]
          rw [h1s]
          simp only [σFun, dif_neg hne1, dif_neg hnej, dif_pos hm]
          have hv := congrArg (Subtype.val : S0.1 → ℕ) (C0.hinv ⟨x.1, h0⟩)
          exact Subtype.ext hv
        by_cases h1' : x.1 ∈ S1
        · have hm : (C1.σ ⟨x.1, h1'⟩).1 ∈ S1 := (C1.σ ⟨x.1, h1'⟩).2
          have hne1 : (C1.σ ⟨x.1, h1'⟩).1 ≠ 1 := fun h => hS1_not_1 (h ▸ hm)
          have hnej : (C1.σ ⟨x.1, h1'⟩).1 ≠ j := fun h => hS1_not_j (h ▸ hm)
          have hn0 : (C1.σ ⟨x.1, h1'⟩).1 ∉ S0.1 := Finset.disjoint_right.mp hS0_S1 hm
          have h1s : σFun x = ⟨(C1.σ ⟨x.1, h1'⟩).1, Uset_sub_Vset n (hS1_sub_U hm)⟩ := by
            simp only [σFun, dif_neg h1, dif_neg hj, dif_neg h0, dif_pos h1']
          rw [h1s]
          simp only [σFun, dif_neg hne1, dif_neg hnej, dif_neg hn0, dif_pos hm]
          have hv := congrArg (Subtype.val : S1 → ℕ) (C1.hinv ⟨x.1, h1'⟩)
          exact Subtype.ext hv
        · have h2 := hcover x h1 hj h0 h1'
          have hm := (C2.σ ⟨x.1, h2⟩).2
          have hne1 : (C2.σ ⟨x.1, h2⟩).1 ≠ 1 := fun h => hS2_not_1 (h ▸ hm)
          have hnej : (C2.σ ⟨x.1, h2⟩).1 ≠ j := fun h => hS2_not_j (h ▸ hm)
          have hn0 : (C2.σ ⟨x.1, h2⟩).1 ∉ S0.1 := Finset.disjoint_right.mp hS0_S2 hm
          have hn1 : (C2.σ ⟨x.1, h2⟩).1 ∉ S1 := Finset.disjoint_right.mp hS1_S2 hm
          have h1s : σFun x = ⟨(C2.σ ⟨x.1, h2⟩).1, Uset_sub_Vset n (hS2_sub_U hm)⟩ := by
            simp only [σFun, dif_neg h1, dif_neg hj, dif_neg h0, dif_neg h1']
          rw [h1s]
          simp only [σFun, dif_neg hne1, dif_neg hnej, dif_neg hn0, dif_neg hn1]
          have hv := congrArg (Subtype.val : S2 → ℕ) (C2.hinv ⟨x.1, h2⟩)
          exact Subtype.ext hv
      hpar_mem := fun x => by
        by_cases h1 : x.1 = 1
        · simp only [parFun, dif_pos h1]; exact Finset.mem_insert_self 0 (Vset n)
        by_cases hj : x.1 = j
        · simp only [parFun, dif_neg h1, dif_pos hj]; exact Finset.mem_insert_self 0 (Vset n)
        by_cases h0 : x.1 ∈ S0.1
        · simp only [parFun, dif_neg h1, dif_neg hj, dif_pos h0]
          rcases Finset.mem_insert.mp (C0.hpar_mem ⟨x.1, h0⟩) with hp | hp
          · rw [hp]; exact Finset.mem_insert_self 0 (Vset n)
          · exact Finset.mem_insert_of_mem (Uset_sub_Vset n (hS0_sub_U hp))
        by_cases h1' : x.1 ∈ S1
        · simp only [parFun, dif_neg h1, dif_neg hj, dif_neg h0, dif_pos h1']
          rcases Finset.mem_insert.mp (C1.hpar_mem ⟨x.1, h1'⟩) with hp | hp
          · rw [hp]; exact Finset.mem_insert_of_mem h1V
          · exact Finset.mem_insert_of_mem (Uset_sub_Vset n (hS1_sub_U hp))
        · simp only [parFun, dif_neg h1, dif_neg hj, dif_neg h0, dif_neg h1']
          rcases Finset.mem_insert.mp (C2.hpar_mem ⟨x.1, hcover x h1 hj h0 h1'⟩) with hp | hp
          · rw [hp]; exact Finset.mem_insert_of_mem hj_V
          · exact Finset.mem_insert_of_mem (Uset_sub_Vset n (hS2_sub_U hp))
      hpar_symm := fun x => by
        by_cases h1 : x.1 = 1
        · have h1s : σFun x = ⟨j, hj_V⟩ := by simp only [σFun, dif_pos h1]
          rw [h1s]; simp only [parFun, dif_pos h1, dif_neg hj_ne1, dite_true]
        by_cases hj : x.1 = j
        · have h1s : σFun x = ⟨1, h1V⟩ := by simp only [σFun, dif_neg h1, dif_pos hj]
          rw [h1s]; simp only [parFun, dif_neg h1, dif_pos hj, dif_pos rfl]
        by_cases h0 : x.1 ∈ S0.1
        · have hm := (C0.σ ⟨x.1, h0⟩).2
          have hne1 : (C0.σ ⟨x.1, h0⟩).1 ≠ 1 := fun h => hS0_not_1 (h ▸ hm)
          have hnej : (C0.σ ⟨x.1, h0⟩).1 ≠ j := fun h => hS0_not_j (h ▸ hm)
          have h1s : σFun x = ⟨(C0.σ ⟨x.1, h0⟩).1, Uset_sub_Vset n (hS0_sub_U hm)⟩ := by
            simp only [σFun, dif_neg h1, dif_neg hj, dif_pos h0]
          rw [h1s]
          simp only [parFun, dif_neg h1, dif_neg hj, dif_pos h0, dif_neg hne1, dif_neg hnej, dif_pos hm]
          exact C0.hpar_symm ⟨x.1, h0⟩
        by_cases h1' : x.1 ∈ S1
        · have hm : (C1.σ ⟨x.1, h1'⟩).1 ∈ S1 := (C1.σ ⟨x.1, h1'⟩).2
          have hne1 : (C1.σ ⟨x.1, h1'⟩).1 ≠ 1 := fun h => hS1_not_1 (h ▸ hm)
          have hnej : (C1.σ ⟨x.1, h1'⟩).1 ≠ j := fun h => hS1_not_j (h ▸ hm)
          have hn0 : (C1.σ ⟨x.1, h1'⟩).1 ∉ S0.1 := Finset.disjoint_right.mp hS0_S1 hm
          have h1s : σFun x = ⟨(C1.σ ⟨x.1, h1'⟩).1, Uset_sub_Vset n (hS1_sub_U hm)⟩ := by
            simp only [σFun, dif_neg h1, dif_neg hj, dif_neg h0, dif_pos h1']
          rw [h1s]
          simp only [parFun, dif_neg h1, dif_neg hj, dif_neg h0, dif_pos h1',
            dif_neg hne1, dif_neg hnej, dif_neg hn0, dif_pos hm]
          exact C1.hpar_symm ⟨x.1, h1'⟩
        · have h2 := hcover x h1 hj h0 h1'
          have hm := (C2.σ ⟨x.1, h2⟩).2
          have hne1 : (C2.σ ⟨x.1, h2⟩).1 ≠ 1 := fun h => hS2_not_1 (h ▸ hm)
          have hnej : (C2.σ ⟨x.1, h2⟩).1 ≠ j := fun h => hS2_not_j (h ▸ hm)
          have hn0 : (C2.σ ⟨x.1, h2⟩).1 ∉ S0.1 := Finset.disjoint_right.mp hS0_S2 hm
          have hn1 : (C2.σ ⟨x.1, h2⟩).1 ∉ S1 := Finset.disjoint_right.mp hS1_S2 hm
          have h1s : σFun x = ⟨(C2.σ ⟨x.1, h2⟩).1, Uset_sub_Vset n (hS2_sub_U hm)⟩ := by
            simp only [σFun, dif_neg h1, dif_neg hj, dif_neg h0, dif_neg h1']
          rw [h1s]
          simp only [parFun, dif_neg h1, dif_neg hj, dif_neg h0, dif_neg h1',
            dif_neg hne1, dif_neg hnej, dif_neg hn0, dif_neg hn1]
          exact C2.hpar_symm ⟨x.1, h2⟩
      hpar_lt := fun x => by
        by_cases h1 : x.1 = 1
        · simp only [parFun, dif_pos h1]; omega
        by_cases hj : x.1 = j
        · simp only [parFun, dif_neg h1, dif_pos hj]; have := minT_ge_two T; omega
        by_cases h0 : x.1 ∈ S0.1
        · simp only [parFun, dif_neg h1, dif_neg hj, dif_pos h0]; exact C0.hpar_lt ⟨x.1, h0⟩
        by_cases h1' : x.1 ∈ S1
        · simp only [parFun, dif_neg h1, dif_neg hj, dif_neg h0, dif_pos h1']; exact C1.hpar_lt ⟨x.1, h1'⟩
        · simp only [parFun, dif_neg h1, dif_neg hj, dif_neg h0, dif_neg h1']
          exact C2.hpar_lt ⟨x.1, hcover x h1 hj h0 h1'⟩ }

private lemma decomp_left_inv (n : ℕ) (g : CactusS 0 (Vset n)) :
    decompBwd n (decompFwd n g) = g := by
  let v1 : Vset n := ⟨1, one_mem_Vset n⟩
  let j : ℕ := (g.σ v1 : ℕ)
  have hpar1 : g.par v1 = 0 := by have h : g.par v1 < 1 := g.hpar_lt v1; omega
  have hparj : g.par (g.σ v1) = 0 := by rw [g.hpar_symm, hpar1]
  have hj_ne1 : j ≠ 1 := fun h => g.hneq v1 (Subtype.ext h)
  have hj_U : j ∈ Uset n := by
    have hjV := Finset.mem_Icc.mp (g.σ v1).2
    exact Finset.mem_Icc.mpr ⟨by omega, hjV.2⟩
  have hj_ge2 : 2 ≤ j := (Finset.mem_Icc.mp hj_U).1
  have hmin_eq : minT (decompFwd n g).1 = j := by
    apply le_antisymm
    · exact Finset.min'_le _ j (Finset.mem_filter.mpr ⟨hj_U, rootOf_j g hj_ge2⟩)
    · have hmem := minT_mem (decompFwd n g).1
      rcases Finset.mem_filter.mp hmem with ⟨hmU, hm2⟩
      exact le_of_rootOf_eq_two g j _ (Finset.mem_insert_of_mem (Uset_sub_Vset n hmU)) hm2
  apply CactusS.ext
  · funext x
    unfold decompBwd decompFwd
    dsimp only
    split_ifs with h1 hj h0 h1'
    · apply Subtype.ext
      have hx1 : x = v1 := Subtype.ext h1
      rw [hx1]
      exact hmin_eq
    · apply Subtype.ext
      have hxj : x = g.σ v1 := Subtype.ext (hj.trans hmin_eq)
      rw [hxj, g.hinv]
    · rfl
    · rfl
    · rfl
  · funext x
    unfold decompBwd decompFwd
    dsimp only
    split_ifs with h1 hj h0 h1'
    · have hx1 : x = v1 := Subtype.ext h1
      rw [hx1, hpar1]
    · have hxj : x = g.σ v1 := Subtype.ext (hj.trans hmin_eq)
      rw [hxj, hparj]
    · rfl
    · rfl
    · rfl

private lemma decomp_right_inv (n : ℕ) (d : DecompTarget n) :
    decompFwd n (decompBwd n d) = d := by
  classical
  rcases d with ⟨T, S0, C0, C1, C2⟩
  let d : DecompTarget n := ⟨T, S0, C0, C1, C2⟩
  let g : CactusS 0 (Vset n) := decompBwd n d
  let j : ℕ := minT T
  let S1 : Finset ℕ := (Uset n \ T.1) \ S0.1
  let S2 : Finset ℕ := T.1.erase j
  have hj_ge2 : 2 ≤ j := minT_ge_two T
  have hj_ne1 : j ≠ 1 := by omega
  have hσ1 : (g.σ ⟨1, one_mem_Vset n⟩ : ℕ) = j := by
    simp [g, d, decompBwd, j]
  have hS0_sub_U : S0.1 ⊆ Uset n := Subset.trans S0.sub_sdiff Finset.sdiff_subset
  have hS1_sub_U : S1 ⊆ Uset n := Subset.trans Finset.sdiff_subset Finset.sdiff_subset
  have hS2_sub_U : S2 ⊆ Uset n := Subset.trans (Finset.erase_subset _ _) T.sub_Uset
  have hS0_not_j : j ∉ S0.1 := fun h => (Finset.mem_sdiff.mp (S0.sub_sdiff h)).2 (minT_mem T)
  have hS1_not_j : j ∉ S1 := fun h => (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp h).1).2 (minT_mem T)
  have hS0_S1 : Disjoint S0.1 S1 := by
    rw [Finset.disjoint_left]; intro x hx0 hx1; exact (Finset.mem_sdiff.mp hx1).2 hx0
  have hS0_S2 : Disjoint S0.1 S2 := by
    rw [Finset.disjoint_left]; intro x hx0 hx2
    exact (Finset.mem_sdiff.mp (S0.sub_sdiff hx0)).2 (Finset.mem_of_mem_erase hx2)
  have hS1_S2 : Disjoint S1 S2 := by
    rw [Finset.disjoint_left]; intro x hx1 hx2
    exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hx1).1).2 (Finset.mem_of_mem_erase hx2)
  have hroot0 : ∀ x, x ∈ S0.1 → rootOf g j x = 0 := by
    intro x
    induction x using Nat.strongRecOn with
    | ind x ih =>
      intro hx0
      have hxU : x ∈ Uset n := hS0_sub_U hx0
      have hxV : x ∈ Vset n := Uset_sub_Vset n hxU
      have hxne0 : x ≠ 0 := by have := (Finset.mem_Icc.mp hxU).1; omega
      have hxne1 : x ≠ 1 := by have := (Finset.mem_Icc.mp hxU).1; omega
      have hxnej : x ≠ j := fun h => hS0_not_j (h ▸ hx0)
      rw [rootOf_step g j hxV hxne0 hxne1 hxnej]
      have hparEq : g.par ⟨x, hxV⟩ = C0.par ⟨x, hx0⟩ := by
        simp [g, d, decompBwd, hxne1, hxnej, hx0, j]
      rw [hparEq]
      rcases Finset.mem_insert.mp (C0.hpar_mem ⟨x, hx0⟩) with hp0 | hpS0
      · rw [hp0, rootOf_zero]
      · exact ih _ (C0.hpar_lt ⟨x, hx0⟩) hpS0
  have hroot1 : ∀ x, x ∈ S1 → rootOf g j x = 1 := by
    intro x
    induction x using Nat.strongRecOn with
    | ind x ih =>
      intro hx1
      have hxU : x ∈ Uset n := hS1_sub_U hx1
      have hxV : x ∈ Vset n := Uset_sub_Vset n hxU
      have hxne0 : x ≠ 0 := by have := (Finset.mem_Icc.mp hxU).1; omega
      have hxne1 : x ≠ 1 := by have := (Finset.mem_Icc.mp hxU).1; omega
      have hxnej : x ≠ j := fun h => hS1_not_j (h ▸ hx1)
      have hxn0 : x ∉ S0.1 := Finset.disjoint_right.mp hS0_S1 hx1
      have hxnT : x ∉ T.1 := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hx1).1).2
      have hxb := Finset.mem_Icc.mp hxU
      rw [rootOf_step g j hxV hxne0 hxne1 hxnej]
      have hparEq : g.par ⟨x, hxV⟩ = C1.par ⟨x, hx1⟩ := by
        simp [g, d, decompBwd, hxne1, hxnej, hxn0, hxnT, hxb.1, hxb.2, j]
      rw [hparEq]
      rcases Finset.mem_insert.mp (C1.hpar_mem ⟨x, hx1⟩) with hp1 | hpS1
      · rw [hp1, rootOf_one]
      · exact ih _ (C1.hpar_lt ⟨x, hx1⟩) hpS1
  have hroot2 : ∀ x, x ∈ S2 → rootOf g j x = 2 := by
    intro x
    induction x using Nat.strongRecOn with
    | ind x ih =>
      intro hx2
      have hxU : x ∈ Uset n := hS2_sub_U hx2
      have hxV : x ∈ Vset n := Uset_sub_Vset n hxU
      have hxne0 : x ≠ 0 := by have := (Finset.mem_Icc.mp hxU).1; omega
      have hxne1 : x ≠ 1 := by have := (Finset.mem_Icc.mp hxU).1; omega
      have hxnej : x ≠ j := (Finset.mem_erase.mp hx2).1
      have hxn0 : x ∉ S0.1 := Finset.disjoint_right.mp hS0_S2 hx2
      have hxT : x ∈ T.1 := Finset.mem_of_mem_erase hx2
      rw [rootOf_step g j hxV hxne0 hxne1 hxnej]
      have hparEq : g.par ⟨x, hxV⟩ = C2.par ⟨x, hx2⟩ := by
        simp [g, d, decompBwd, hxne1, hxnej, hxn0, hxT, j]
      rw [hparEq]
      rcases Finset.mem_insert.mp (C2.hpar_mem ⟨x, hx2⟩) with hpj | hpS2
      · rw [hpj, rootOf_j g hj_ge2]
      · exact ih _ (C2.hpar_lt ⟨x, hx2⟩) hpS2
  have hT_eq : (decompFwd n g).1 = T := by
    apply Subtype.ext
    ext x
    change x ∈ (Uset n).filter (fun y => rootOf g (g.σ ⟨1, one_mem_Vset n⟩ : ℕ) y = 2) ↔ x ∈ T.1
    rw [hσ1, Finset.mem_filter]
    constructor
    · rintro ⟨hxU, hx2⟩
      by_contra hnT
      by_cases hx0 : x ∈ S0.1
      · rw [hroot0 x hx0] at hx2; contradiction
      · have hx1 : x ∈ S1 := Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨hxU, hnT⟩, hx0⟩
        rw [hroot1 x hx1] at hx2; contradiction
    · intro hxT
      refine ⟨T.sub_Uset hxT, ?_⟩
      by_cases hxj : x = j
      · rw [hxj, rootOf_j g hj_ge2]
      · exact hroot2 x (Finset.mem_erase.mpr ⟨hxj, hxT⟩)
  have hS0_eq : (decompFwd n g).2.1.1 = S0.1 := by
    ext x
    change x ∈ (Uset n).filter (fun y => rootOf g (g.σ ⟨1, one_mem_Vset n⟩ : ℕ) y = 0) ↔ x ∈ S0.1
    rw [hσ1, Finset.mem_filter]
    constructor
    · rintro ⟨hxU, hx0⟩
      by_contra hxn0
      by_cases hxT : x ∈ T.1
      · by_cases hxj : x = j
        · rw [hxj, rootOf_j g hj_ge2] at hx0; contradiction
        · rw [hroot2 x (Finset.mem_erase.mpr ⟨hxj, hxT⟩)] at hx0; contradiction
      · have hx1 : x ∈ S1 := Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨hxU, hxT⟩, hxn0⟩
        rw [hroot1 x hx1] at hx0; contradiction
    · intro hx0
      exact ⟨hS0_sub_U hx0, hroot0 x hx0⟩
  refine decompTarget_ext hT_eq hS0_eq ?_ ?_ ?_ ?_ ?_ ?_
  · intro x h1 h2
    have hxU := hS0_sub_U h2
    have hxne1 : x ≠ 1 := by have := (Finset.mem_Icc.mp hxU).1; omega
    have hxnej : x ≠ j := fun h => hS0_not_j (h ▸ h2)
    change (g.σ ⟨x, Uset_sub_Vset n (Finset.mem_filter.mp h1).1⟩ : ℕ) = (C0.σ ⟨x, h2⟩ : ℕ)
    simp [g, d, decompBwd, hxne1, hxnej, h2, j]
  · intro x h1 h2
    have hxU := hS0_sub_U h2
    have hxne1 : x ≠ 1 := by have := (Finset.mem_Icc.mp hxU).1; omega
    have hxnej : x ≠ j := fun h => hS0_not_j (h ▸ h2)
    change g.par ⟨x, Uset_sub_Vset n (Finset.mem_filter.mp h1).1⟩ = C0.par ⟨x, h2⟩
    simp [g, d, decompBwd, hxne1, hxnej, h2, j]
  · intro x h1 h2
    have hxU := hS1_sub_U h2
    have hxne1 : x ≠ 1 := by have := (Finset.mem_Icc.mp hxU).1; omega
    have hxnej : x ≠ j := fun h => hS1_not_j (h ▸ h2)
    have hxn0 : x ∉ S0.1 := Finset.disjoint_right.mp hS0_S1 h2
    have hxnT : x ∉ T.1 := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp h2).1).2
    have hxb := Finset.mem_Icc.mp hxU
    change (g.σ ⟨x, _⟩ : ℕ) = (C1.σ ⟨x, h2⟩ : ℕ)
    simp [g, d, decompBwd, hxne1, hxnej, hxn0, hxnT, hxb.1, hxb.2, j]
  · intro x h1 h2
    have hxU := hS1_sub_U h2
    have hxne1 : x ≠ 1 := by have := (Finset.mem_Icc.mp hxU).1; omega
    have hxnej : x ≠ j := fun h => hS1_not_j (h ▸ h2)
    have hxn0 : x ∉ S0.1 := Finset.disjoint_right.mp hS0_S1 h2
    have hxnT : x ∉ T.1 := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp h2).1).2
    have hxb := Finset.mem_Icc.mp hxU
    change g.par ⟨x, _⟩ = C1.par ⟨x, h2⟩
    simp [g, d, decompBwd, hxne1, hxnej, hxn0, hxnT, hxb.1, hxb.2, j]
  · intro x h1 h2
    have hxU := hS2_sub_U h2
    have hxne1 : x ≠ 1 := by have := (Finset.mem_Icc.mp hxU).1; omega
    have hxnej : x ≠ j := (Finset.mem_erase.mp h2).1
    have hxn0 : x ∉ S0.1 := Finset.disjoint_right.mp hS0_S2 h2
    have hxT : x ∈ T.1 := Finset.mem_of_mem_erase h2
    change (g.σ ⟨x, _⟩ : ℕ) = (C2.σ ⟨x, h2⟩ : ℕ)
    simp [g, d, decompBwd, hxne1, hxnej, hxn0, hxT, j]
  · intro x h1 h2
    have hxU := hS2_sub_U h2
    have hxne1 : x ≠ 1 := by have := (Finset.mem_Icc.mp hxU).1; omega
    have hxnej : x ≠ j := (Finset.mem_erase.mp h2).1
    have hxn0 : x ∉ S0.1 := Finset.disjoint_right.mp hS0_S2 h2
    have hxT : x ∈ T.1 := Finset.mem_of_mem_erase h2
    change g.par ⟨x, _⟩ = C2.par ⟨x, h2⟩
    simp [g, d, decompBwd, hxne1, hxnej, hxn0, hxT, j]

private lemma decomp_card_eq (n : ℕ) :
    c (n + 1) =
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal (2 * n + 1),
        if p.2 % 2 = 1 then
          (2 * n + 1).choose p.2 * c (p.2 / 2) *
            ∑ q ∈ Finset.HasAntidiagonal.antidiagonal p.1,
              if q.1 % 2 = 0 then
                p.1.choose q.1 * c (q.1 / 2) * c (q.2 / 2)
              else 0
        else 0 := by
  classical
  let U := Uset n
  have hU_card : U.card = 2 * n + 1 := card_Uset n
  have hEquiv : CactusS 0 (Vset n) ≃ DecompTarget n :=
    { toFun := decompFwd n
      invFun := decompBwd n
      left_inv := decomp_left_inv n
      right_inv := decomp_right_inv n }
  have hcardTarget : c (n + 1) = Fintype.card (DecompTarget n) := by
    simpa [c, Vset] using Fintype.card_congr hEquiv
  rw [hcardTarget]
  rw [Fintype.card_sigma]
  simp_rw [Fintype.card_sigma, Fintype.card_prod]
  have hInner : ∀ T : T2Type n,
      (∑ S0 : S0Type n T,
        Fintype.card (CactusS 0 S0.1) *
          (Fintype.card (CactusS 1 ((Uset n \ T.1) \ S0.1)) *
            Fintype.card (CactusS (minT T) (T.1.erase (minT T))))) =
        c (T.1.card / 2) *
          ∑ q ∈ Finset.HasAntidiagonal.antidiagonal (Uset n \ T.1).card,
            if q.1 % 2 = 0 then
              (Uset n \ T.1).card.choose q.1 * c (q.1 / 2) * c (q.2 / 2)
            else 0 := by
    intro T
    have hT_sub_U := T.sub_Uset
    have hT_odd := T.card_mod
    have hUT_card : (Uset n \ T.1).card = 2 * n + 1 - T.1.card := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hT_sub_U, card_Uset]
    have hUT_even : (Uset n \ T.1).card % 2 = 0 := by
      have hle : T.1.card ≤ 2 * n + 1 := card_Uset n ▸ Finset.card_le_card hT_sub_U
      omega
    have hC2_card : Fintype.card (CactusS (minT T) (T.1.erase (minT T))) = c (T.1.card / 2) := by
      refine card_cactusS_eq_c (fun x hx => minT_lt_of_mem_erase T hx) ?_
      rw [Finset.card_erase_of_mem (minT_mem T)]
      omega
    have hTerm : ∀ S0 : S0Type n T,
        Fintype.card (CactusS 0 S0.1) *
          (Fintype.card (CactusS 1 ((Uset n \ T.1) \ S0.1)) *
            Fintype.card (CactusS (minT T) (T.1.erase (minT T)))) =
        c (T.1.card / 2) * (c (S0.1.card / 2) * c (((Uset n \ T.1).card - S0.1.card) / 2)) := by
      intro S0
      have hC0_card : Fintype.card (CactusS 0 S0.1) = c (S0.1.card / 2) := by
        refine card_cactusS_eq_c (fun x hx => ?_) (by have := S0.card_mod; omega)
        have := (Finset.mem_Icc.mp (Finset.sdiff_subset (S0.sub_sdiff hx))).1
        omega
      have hC1_card : Fintype.card (CactusS 1 ((Uset n \ T.1) \ S0.1)) =
          c (((Uset n \ T.1).card - S0.1.card) / 2) := by
        have hS1_card : ((Uset n \ T.1) \ S0.1).card = (Uset n \ T.1).card - S0.1.card := by
          rw [Finset.card_sdiff, Finset.inter_eq_left.mpr S0.sub_sdiff]
        have hle : S0.1.card ≤ (Uset n \ T.1).card := Finset.card_le_card S0.sub_sdiff
        refine card_cactusS_eq_c (fun x hx => ?_) (by have := S0.card_mod; omega)
        have := (Finset.mem_Icc.mp (Finset.sdiff_subset (Finset.sdiff_subset hx))).1
        omega
      rw [hC0_card, hC1_card, hC2_card]
      ring
    simp_rw [hTerm, ← Finset.mul_sum]
    congr 1
    have hSumSub :
        (∑ S0 : S0Type n T, c (S0.1.card / 2) * c (((Uset n \ T.1).card - S0.1.card) / 2)) =
          ∑ S ∈ (Uset n \ T.1).powerset.filter (fun S => S.card % 2 = 0),
            c (S.card / 2) * c (((Uset n \ T.1).card - S.card) / 2) :=
      Finset.sum_coe_sort (S0Finset n T) (fun S => c (S.card / 2) * c (((Uset n \ T.1).card - S.card) / 2))
    rw [hSumSub, Finset.sum_filter]
    have hByCard :
        (∑ S ∈ (Uset n \ T.1).powerset,
          if S.card % 2 = 0 then c (S.card / 2) * c (((Uset n \ T.1).card - S.card) / 2) else 0) =
        ∑ k ∈ Finset.range ((Uset n \ T.1).card + 1),
          if k % 2 = 0 then (Uset n \ T.1).card.choose k * c (k / 2) * c (((Uset n \ T.1).card - k) / 2) else 0 := by
      rw [Finset.sum_powerset_apply_card (f := fun k =>
        if k % 2 = 0 then c (k / 2) * c (((Uset n \ T.1).card - k) / 2) else 0)]
      refine Finset.sum_congr rfl fun k _ => ?_
      split_ifs <;> ring
    rw [hByCard]
    refine Finset.sum_bij (fun k hk => (k, (Uset n \ T.1).card - k)) ?_ ?_ ?_ ?_
    · intro k hk
      have hle : k ≤ (Uset n \ T.1).card := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      exact Finset.HasAntidiagonal.mem_antidiagonal.mpr (Nat.add_sub_cancel' hle)
    · intro k₁ _ k₂ _ h
      exact (Prod.mk.inj h).1
    · intro q hq
      have hsum := Finset.HasAntidiagonal.mem_antidiagonal.mp hq
      refine ⟨q.1, Finset.mem_range.mpr (by omega), Prod.ext rfl (by omega)⟩
    · intro _ _; rfl
  simp_rw [hInner]
  have hOuter :
      (∑ T : T2Type n,
        c (T.1.card / 2) *
          ∑ q ∈ Finset.HasAntidiagonal.antidiagonal (Uset n \ T.1).card,
            if q.1 % 2 = 0 then (Uset n \ T.1).card.choose q.1 * c (q.1 / 2) * c (q.2 / 2) else 0) =
      ∑ T ∈ (Uset n).powerset,
        if T.card % 2 = 1 then
          c (T.card / 2) *
            ∑ q ∈ Finset.HasAntidiagonal.antidiagonal (2 * n + 1 - T.card),
              if q.1 % 2 = 0 then (2 * n + 1 - T.card).choose q.1 * c (q.1 / 2) * c (q.2 / 2) else 0
        else 0 := by
    rw [← Finset.sum_filter]
    have hcoe := Finset.sum_coe_sort (T2Finset n) (fun T =>
      c (T.card / 2) *
        ∑ q ∈ Finset.HasAntidiagonal.antidiagonal (Uset n \ T).card,
          if q.1 % 2 = 0 then (Uset n \ T).card.choose q.1 * c (q.1 / 2) * c (q.2 / 2) else 0)
    rw [hcoe]
    refine Finset.sum_congr rfl fun T hT => ?_
    have hT_sub : T ⊆ Uset n := Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1
    have hUT : (Uset n \ T).card = 2 * n + 1 - T.card := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hT_sub, card_Uset]
    rw [hUT]
  rw [hOuter]
  rw [Finset.sum_powerset_apply_card (f := fun k =>
    if k % 2 = 1 then
      c (k / 2) *
        ∑ q ∈ Finset.HasAntidiagonal.antidiagonal (2 * n + 1 - k),
          if q.1 % 2 = 0 then (2 * n + 1 - k).choose q.1 * c (q.1 / 2) * c (q.2 / 2) else 0
    else 0)]
  rw [card_Uset]
  refine Finset.sum_bij (fun k hk => (2 * n + 1 - k, k)) ?_ ?_ ?_ ?_
  · intro k hk
    have hle : k ≤ 2 * n + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    exact Finset.HasAntidiagonal.mem_antidiagonal.mpr (Nat.sub_add_cancel hle)
  · intro k₁ _ k₂ _ h
    exact (Prod.mk.inj h).2
  · intro p hp
    have hsum := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    refine ⟨p.2, Finset.mem_range.mpr (by omega), Prod.ext (by omega) rfl⟩
  · intro k _
    dsimp only
    split_ifs <;> ring

/-! ### Part 5: Formal power series ODE and defining recurrence of `a` -/

private noncomputable def psA : PowerSeries ℚ :=
  PowerSeries.mk (fun k => if k % 2 = 0 then (c (k / 2) : ℚ) / (k ! : ℚ) else 0)

private noncomputable def psB : PowerSeries ℚ :=
  PowerSeries.mk (fun k => if k % 2 = 1 then (c (k / 2) : ℚ) / (k ! : ℚ) else 0)

private noncomputable def psC : PowerSeries ℚ :=
  PowerSeries.mk (fun k => if k % 2 = 0 ∧ 2 ≤ k then (c (k / 2 - 1) : ℚ) / (k ! : ℚ) else 0)

private lemma deriv_psB : PowerSeries.derivative ℚ psB = psA := by
  ext m
  rw [PowerSeries.coeff_derivative]
  simp only [psA, psB, PowerSeries.coeff_mk]
  by_cases hm : m % 2 = 0
  · have hm1 : (m + 1) % 2 = 1 := by omega
    have hdiv : (m + 1) / 2 = m / 2 := by omega
    rw [if_pos hm1, if_pos hm, hdiv, Nat.factorial_succ]
    have hne : ((m + 1 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero m)
    have hfac : ((m ! : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
    push_cast
    field_simp
  · have hm1 : ¬ (m + 1) % 2 = 1 := by omega
    rw [if_neg hm1, if_neg hm, zero_mul]

private lemma deriv_psC : PowerSeries.derivative ℚ psC = psB := by
  ext m
  rw [PowerSeries.coeff_derivative]
  simp only [psB, psC, PowerSeries.coeff_mk]
  by_cases hm : m % 2 = 1
  · have hm1 : (m + 1) % 2 = 0 ∧ 2 ≤ m + 1 := by omega
    have hdiv : (m + 1) / 2 - 1 = m / 2 := by omega
    rw [if_pos hm1, if_pos hm, hdiv, Nat.factorial_succ]
    have hne : ((m + 1 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero m)
    have hfac : ((m ! : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
    push_cast
    field_simp
  · have hm1 : ¬ ((m + 1) % 2 = 0 ∧ 2 ≤ m + 1) := by omega
    rw [if_neg hm1, if_neg hm, zero_mul]

private lemma choose_div_factorial_rat {m k : ℕ} (hk : k ≤ m) :
    ((m.choose k : ℕ) : ℚ) / ((m ! : ℕ) : ℚ) =
      1 / (((k ! : ℕ) : ℚ) * (((m - k)! : ℕ) : ℚ)) := by
  have hm : ((m ! : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
  have hk0 : ((k ! : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have hmk0 : (((m - k)! : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (m - k))
  have hnat : m.choose k * k ! * (m - k)! = m ! := Nat.choose_mul_factorial_mul_factorial hk
  have hq : ((m.choose k : ℕ) : ℚ) * ((k ! : ℕ) : ℚ) * (((m - k)! : ℕ) : ℚ) = ((m ! : ℕ) : ℚ) := by
    exact_mod_cast hnat
  field_simp
  linarith

private lemma deriv_psA : PowerSeries.derivative ℚ psA = psA * psA * psB := by
  ext m
  rw [PowerSeries.coeff_derivative]
  rcases Nat.even_or_odd' m with ⟨n, rfl | rfl⟩
  · -- Even index `2 * n`: both sides are 0
    have hLHS : PowerSeries.coeff (2 * n + 1) psA * (((2 * n : ℕ) : ℚ) + 1) = 0 := by
      simp [psA, PowerSeries.coeff_mk]
    rw [hLHS]
    symm
    rw [PowerSeries.coeff_mul]
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [PowerSeries.coeff_mul]
    have hsum := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    by_cases hp2 : p.2 % 2 = 1
    · have hp1_odd : p.1 % 2 = 1 := by omega
      have hInner0 : ∑ q ∈ Finset.HasAntidiagonal.antidiagonal p.1,
          PowerSeries.coeff q.1 psA * PowerSeries.coeff q.2 psA = 0 := by
        refine Finset.sum_eq_zero fun q hq => ?_
        have hqsum := Finset.HasAntidiagonal.mem_antidiagonal.mp hq
        by_cases hq1 : q.1 % 2 = 0
        · have hq2 : ¬ q.2 % 2 = 0 := by omega
          simp [psA, PowerSeries.coeff_mk, hq2]
        · simp [psA, PowerSeries.coeff_mk, hq1]
      rw [hInner0, zero_mul]
    · simp [psB, PowerSeries.coeff_mk, hp2]
  · -- Odd index `2 * n + 1`: follows from `decomp_card_eq n`
    have hLHS : PowerSeries.coeff (2 * n + 1 + 1) psA * (((2 * n + 1 : ℕ) : ℚ) + 1) =
        (c (n + 1) : ℚ) / (((2 * n + 1)! : ℕ) : ℚ) := by
      have hmod : (2 * n + 1 + 1) % 2 = 0 := by omega
      have hdiv : (2 * n + 1 + 1) / 2 = n + 1 := by omega
      simp only [psA, PowerSeries.coeff_mk, if_pos hmod, hdiv]
      rw [Nat.factorial_succ]
      have hne : (((2 * n + 1 : ℕ) : ℚ) + 1) ≠ 0 := by positivity
      have hfac : (((2 * n + 1)! : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      push_cast
      field_simp
    rw [hLHS]
    have hrec_q : (c (n + 1) : ℚ) =
        ∑ p ∈ Finset.HasAntidiagonal.antidiagonal (2 * n + 1),
          if p.2 % 2 = 1 then
            ((2 * n + 1).choose p.2 : ℚ) * (c (p.2 / 2) : ℚ) *
              ∑ q ∈ Finset.HasAntidiagonal.antidiagonal p.1,
                if q.1 % 2 = 0 then
                  (p.1.choose q.1 : ℚ) * (c (q.1 / 2) : ℚ) * (c (q.2 / 2) : ℚ)
                else 0
          else 0 := by
      have h := congrArg (Nat.cast (R := ℚ)) (decomp_card_eq n)
      push_cast at h
      simpa only [apply_ite (Nat.cast (R := ℚ)), Nat.cast_zero] using h
    rw [hrec_q, Finset.sum_div, PowerSeries.coeff_mul]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hpsum := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    rw [PowerSeries.coeff_mul]
    by_cases hp2 : p.2 % 2 = 1
    · rw [if_pos hp2]
      have hp1_even : p.1 % 2 = 0 := by omega
      have hp2_le : p.2 ≤ 2 * n + 1 := by omega
      have hsub_p : 2 * n + 1 - p.2 = p.1 := by omega
      have hch_p := choose_div_factorial_rat hp2_le
      rw [hsub_p] at hch_p
      have hB : PowerSeries.coeff p.2 psB = (c (p.2 / 2) : ℚ) / ((p.2 ! : ℕ) : ℚ) := by
        simp [psB, PowerSeries.coeff_mk, hp2]
      rw [hB]
      have hOuter :
          (((2 * n + 1).choose p.2 : ℚ) * (c (p.2 / 2) : ℚ) *
              ∑ q ∈ Finset.HasAntidiagonal.antidiagonal p.1,
                if q.1 % 2 = 0 then (p.1.choose q.1 : ℚ) * (c (q.1 / 2) : ℚ) * (c (q.2 / 2) : ℚ) else 0) /
            (((2 * n + 1)! : ℕ) : ℚ) =
          ((∑ q ∈ Finset.HasAntidiagonal.antidiagonal p.1,
              if q.1 % 2 = 0 then (p.1.choose q.1 : ℚ) * (c (q.1 / 2) : ℚ) * (c (q.2 / 2) : ℚ) else 0) /
            ((p.1 ! : ℕ) : ℚ)) * ((c (p.2 / 2) : ℚ) / ((p.2 ! : ℕ) : ℚ)) := by
        set S : ℚ := ∑ q ∈ Finset.HasAntidiagonal.antidiagonal p.1,
          if q.1 % 2 = 0 then (p.1.choose q.1 : ℚ) * (c (q.1 / 2) : ℚ) * (c (q.2 / 2) : ℚ) else 0
        have h1 : (((2 * n + 1).choose p.2 : ℚ) / (((2 * n + 1)! : ℕ) : ℚ)) =
            1 / (((p.2 ! : ℕ) : ℚ) * ((p.1 ! : ℕ) : ℚ)) := hch_p
        calc
          (((2 * n + 1).choose p.2 : ℚ) * (c (p.2 / 2) : ℚ) * S) / (((2 * n + 1)! : ℕ) : ℚ)
              = (((2 * n + 1).choose p.2 : ℚ) / (((2 * n + 1)! : ℕ) : ℚ)) * (c (p.2 / 2) : ℚ) * S := by ring
          _ = (1 / (((p.2 ! : ℕ) : ℚ) * ((p.1 ! : ℕ) : ℚ))) * (c (p.2 / 2) : ℚ) * S := by rw [h1]
          _ = (S / ((p.1 ! : ℕ) : ℚ)) * ((c (p.2 / 2) : ℚ) / ((p.2 ! : ℕ) : ℚ)) := by ring
      rw [hOuter]
      congr 1
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun q hq => ?_
      have hqsum := Finset.HasAntidiagonal.mem_antidiagonal.mp hq
      by_cases hq1 : q.1 % 2 = 0
      · have hq2 : q.2 % 2 = 0 := by omega
        have hq1_le : q.1 ≤ p.1 := by omega
        have hsub_q : p.1 - q.1 = q.2 := by omega
        have hch_q := choose_div_factorial_rat hq1_le
        rw [hsub_q] at hch_q
        rw [if_pos hq1]
        simp only [psA, PowerSeries.coeff_mk, if_pos hq1, if_pos hq2]
        calc
          ((p.1.choose q.1 : ℚ) * (c (q.1 / 2) : ℚ) * (c (q.2 / 2) : ℚ)) / ((p.1 ! : ℕ) : ℚ)
              = ((p.1.choose q.1 : ℚ) / ((p.1 ! : ℕ) : ℚ)) * (c (q.1 / 2) : ℚ) * (c (q.2 / 2) : ℚ) := by ring
          _ = (1 / (((q.1 ! : ℕ) : ℚ) * ((q.2 ! : ℕ) : ℚ))) * (c (q.1 / 2) : ℚ) * (c (q.2 / 2) : ℚ) := by rw [hch_q]
          _ = ((c (q.1 / 2) : ℚ) / ((q.1 ! : ℕ) : ℚ)) * ((c (q.2 / 2) : ℚ) / ((q.2 ! : ℕ) : ℚ)) := by ring
      · simp [psA, PowerSeries.coeff_mk, hq1]
    · simp [psB, PowerSeries.coeff_mk, hp2]

private lemma psA_sub_one_eq_mul_psC : psA - 1 = psA * psC := by
  let D : PowerSeries ℚ := psA * (1 - psC) - 1
  have hD0 : PowerSeries.coeff 0 D = 0 := by
    have hA0 : PowerSeries.coeff 0 psA = 1 := by simp [psA, PowerSeries.coeff_mk, c_zero]
    have hC0 : PowerSeries.coeff 0 psC = 0 := by simp [psC, PowerSeries.coeff_mk]
    have hmul0 : PowerSeries.coeff 0 (psA * (1 - psC)) =
        PowerSeries.coeff 0 psA * PowerSeries.coeff 0 (1 - psC) := by
      rw [PowerSeries.coeff_mul]
      simp
    simp only [D, map_sub, hmul0, hA0, hC0, PowerSeries.coeff_zero_one]
    ring
  have hDderiv : PowerSeries.derivative ℚ D = psA * psB * D := by
    dsimp only [D]
    rw [map_sub, Derivation.leibniz, map_sub, PowerSeries.derivative_one,
      deriv_psA, deriv_psC, smul_eq_mul, smul_eq_mul]
    ring
  have hD_coeff_zero : ∀ m : ℕ, PowerSeries.coeff m D = 0 := by
    intro m
    induction m using Nat.strongRecOn with
    | ind m ih =>
      cases m with
      | zero => exact hD0
      | succ k =>
        have hstep : PowerSeries.coeff (k + 1) D * ((k : ℚ) + 1) = 0 := by
          rw [← PowerSeries.coeff_derivative, hDderiv, PowerSeries.coeff_mul]
          refine Finset.sum_eq_zero fun p hp => ?_
          have hsum := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
          rw [ih p.2 (by omega), mul_zero]
        have hne : ((k : ℚ) + 1) ≠ 0 := by positivity
        exact (mul_eq_zero.mp hstep).resolve_right hne
  have hD_zero : D = 0 := by
    ext m
    rw [hD_coeff_zero m, map_zero]
  have hsub : psA * (1 - psC) = 1 := sub_eq_zero.mp hD_zero
  calc
    psA - 1 = psA - psA * (1 - psC) := by rw [hsub]
    _ = psA * psC := by ring

private lemma c_succ_rec (n : ℕ) :
    c (n + 1) = ∑ k : Fin (n + 1), (2 * (n + 1)).choose (2 * k) * c k * c (n - k) := by
  have hEq := congrArg (PowerSeries.coeff (2 * (n + 1))) psA_sub_one_eq_mul_psC
  have hLHS : PowerSeries.coeff (2 * (n + 1)) (psA - 1) =
      (c (n + 1) : ℚ) / (((2 * (n + 1))! : ℕ) : ℚ) := by
    rw [map_sub, PowerSeries.coeff_one, if_neg (by omega), sub_zero]
    simp [psA, PowerSeries.coeff_mk]
  rw [hLHS, PowerSeries.coeff_mul] at hEq
  have hfac_ne : (((2 * (n + 1))! : ℕ) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hMul : (c (n + 1) : ℚ) =
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal (2 * (n + 1)),
        (((2 * (n + 1))! : ℕ) : ℚ) * (PowerSeries.coeff p.1 psA * PowerSeries.coeff p.2 psC) := by
    rw [← Finset.mul_sum, ← hEq]
    field_simp
  -- Filter `antidiagonal (2 * (n + 1))` to nonzero terms `(2 * k, 2 * (n + 1) - 2 * k)` for `k : Fin (n + 1)`
  have hSumEq :
      (∑ p ∈ Finset.HasAntidiagonal.antidiagonal (2 * (n + 1)),
        (((2 * (n + 1))! : ℕ) : ℚ) * (PowerSeries.coeff p.1 psA * PowerSeries.coeff p.2 psC)) =
      ∑ k : Fin (n + 1),
        (((2 * (n + 1)).choose (2 * k) : ℕ) : ℚ) * (c k : ℚ) * (c (n - k) : ℚ) := by
    rw [← Finset.sum_filter_of_ne (p := fun p => p.1 % 2 = 0 ∧ 2 ≤ p.2)]
    · symm
      refine Finset.sum_bij (fun (k : Fin (n + 1)) _ => (2 * (k : ℕ), 2 * (n + 1) - 2 * (k : ℕ))) ?_ ?_ ?_ ?_
      · intro k _
        have hk := k.isLt
        refine Finset.mem_filter.mpr ⟨Finset.HasAntidiagonal.mem_antidiagonal.mpr (by omega), by omega, by omega⟩
      · intro k₁ _ k₂ _ h
        ext
        have := (Prod.mk.inj h).1
        omega
      · intro p hp
        rcases Finset.mem_filter.mp hp with ⟨hpa, hp1e, hp2ge⟩
        have hsum := Finset.HasAntidiagonal.mem_antidiagonal.mp hpa
        refine ⟨⟨p.1 / 2, by omega⟩, Finset.mem_univ _, ?_⟩
        ext <;> dsimp <;> omega
      · intro k _
        have hle : 2 * (k : ℕ) ≤ 2 * (n + 1) := by omega
        have hch := choose_div_factorial_rat hle
        have hmod1 : (2 * (k : ℕ)) % 2 = 0 := by omega
        have hmod2 : (2 * (n + 1) - 2 * (k : ℕ)) % 2 = 0 ∧ 2 ≤ 2 * (n + 1) - 2 * (k : ℕ) := by omega
        have hdiv1 : (2 * (k : ℕ)) / 2 = (k : ℕ) := by omega
        have hdiv2 : (2 * (n + 1) - 2 * (k : ℕ)) / 2 - 1 = n - (k : ℕ) := by omega
        simp only [psA, psC, PowerSeries.coeff_mk, if_pos hmod1, if_pos hmod2, hdiv1, hdiv2]
        have hnat : (2 * (n + 1)).choose (2 * (k : ℕ)) * (2 * (k : ℕ))! * (2 * (n + 1) - 2 * (k : ℕ))! =
            (2 * (n + 1))! := Nat.choose_mul_factorial_mul_factorial hle
        have hq : (((2 * (n + 1)).choose (2 * (k : ℕ)) : ℕ) : ℚ) *
            (((2 * (k : ℕ))! : ℕ) : ℚ) * (((2 * (n + 1) - 2 * (k : ℕ))! : ℕ) : ℚ) =
            (((2 * (n + 1))! : ℕ) : ℚ) := by
          exact_mod_cast hnat
        have h1ne : (((2 * (k : ℕ))! : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
        have h2ne : (((2 * (n + 1) - 2 * (k : ℕ))! : ℕ) : ℚ) ≠ 0 :=
          Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
        field_simp
        rw [← hq]
        ring
    · intro p hp hne
      have hsum := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
      by_contra hnot
      apply hne
      by_cases hp1 : p.1 % 2 = 0
      · have hp2 : ¬ (p.2 % 2 = 0 ∧ 2 ≤ p.2) := by omega
        simp [psC, PowerSeries.coeff_mk, hp2]
      · simp [psA, PowerSeries.coeff_mk, hp1]
  rw [hSumEq] at hMul
  exact_mod_cast hMul

private lemma a_eq_c : ∀ n : ℕ, OMA.S_oeis_a002067.a n = c n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero =>
      rw [OMA.S_oeis_a002067.a, c_zero]
    | succ m =>
      rw [OMA.S_oeis_a002067.a, c_succ_rec]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [ih k.1 (by omega), ih (m - k.1) (by omega)]

theorem main_proof : ∀ n : ℕ, OMA.S_oeis_a002067.a n = OMA.S_oeis_a002067.haf n := by
  intro n
  rw [a_eq_c n, c_eq_haf n]

end A002067Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a002067.main :=
  A002067Proof.main_proof
