import OMAStatements.S_oeis_a163704

-- Credit: @Dariusthedoggie
-- Proof: decompose by the topmost nonzero row into a top-to-bottom path grid (counted via a 4-state Fibonacci recurrence), yielding a(n) = F(n+4) + F(n+2) - n - 4 for n >= 2, and deduce the recurrence, g.f., and Binet closed form.

namespace OMA.P163704

open OMA.S_oeis_a163704 PowerSeries Finset

abbrev Grid (m : ℕ) := Fin m → Fin 2 → Fin 2

/-! ### Part 1: Local characterization of top-to-bottom valid grids -/

def isTopBotValid (n : ℕ) (A : Grid n) : Prop :=
  (∀ p q : Fin n × Fin 2, A p.1 p.2 = 1 → A q.1 q.2 = 1 →
    Relation.ReflTransGen (adjOne A) p q) ∧
  (∃ (hn : 0 < n) (c₁ c₂ : Fin 2),
    A ⟨0, hn⟩ c₁ = 1 ∧ A ⟨n - 1, Nat.sub_lt hn Nat.one_pos⟩ c₂ = 1 ∧
    Relation.ReflTransGen (adjOne A) (⟨0, hn⟩, c₁) (⟨n - 1, Nat.sub_lt hn Nat.one_pos⟩, c₂)) ∧
  (∀ p : Fin n × Fin 2, A p.1 p.2 = 1 →
    (Finset.univ.filter (fun q : Fin n × Fin 2 => A q.1 q.2 = 1 ∧ isAdj p q)).card ≤ 2)

def isLocal (n : ℕ) (A : Grid n) : Prop :=
  (∀ i : Fin n, A i 0 = 1 ∨ A i 1 = 1) ∧
  (∀ i : Fin (n - 1),
    ¬ (A ⟨i.1, by omega⟩ 0 = 1 ∧ A ⟨i.1, by omega⟩ 1 = 0 ∧
       A ⟨i.1 + 1, by omega⟩ 0 = 0 ∧ A ⟨i.1 + 1, by omega⟩ 1 = 1)) ∧
  (∀ i : Fin (n - 1),
    ¬ (A ⟨i.1, by omega⟩ 0 = 0 ∧ A ⟨i.1, by omega⟩ 1 = 1 ∧
       A ⟨i.1 + 1, by omega⟩ 0 = 1 ∧ A ⟨i.1 + 1, by omega⟩ 1 = 0)) ∧
  (∀ i : Fin (n - 1),
    ¬ (A ⟨i.1, by omega⟩ 0 = 1 ∧ A ⟨i.1, by omega⟩ 1 = 1 ∧
       A ⟨i.1 + 1, by omega⟩ 0 = 1 ∧ A ⟨i.1 + 1, by omega⟩ 1 = 1)) ∧
  (∀ i : Fin (n - 2),
    ¬ (A ⟨i.1, by omega⟩ 0 = 1 ∧ A ⟨i.1 + 1, by omega⟩ 0 = 1 ∧
       A ⟨i.1 + 1, by omega⟩ 1 = 1 ∧ A ⟨i.1 + 2, by omega⟩ 0 = 1)) ∧
  (∀ i : Fin (n - 2),
    ¬ (A ⟨i.1, by omega⟩ 1 = 1 ∧ A ⟨i.1 + 1, by omega⟩ 0 = 1 ∧
       A ⟨i.1 + 1, by omega⟩ 1 = 1 ∧ A ⟨i.1 + 2, by omega⟩ 1 = 1))

instance (n : ℕ) (A : Grid n) : Decidable (isLocal n A) := by
  unfold isLocal; infer_instance

def isLocalTail (L : ℕ) (B : Grid L) : Prop :=
  if h1 : L = 1 then B ⟨0, by omega⟩ 0 = 1 ∨ B ⟨0, by omega⟩ 1 = 1
  else if h2 : L = 2 then
    (B ⟨0, by omega⟩ 0 = 1 ∨ B ⟨0, by omega⟩ 1 = 1) ∧
    (B ⟨1, by omega⟩ 0 = 1 ∨ B ⟨1, by omega⟩ 1 = 1) ∧
    ¬ (B ⟨0, by omega⟩ 0 = 1 ∧ B ⟨0, by omega⟩ 1 = 0 ∧
       B ⟨1, by omega⟩ 0 = 0 ∧ B ⟨1, by omega⟩ 1 = 1) ∧
    ¬ (B ⟨0, by omega⟩ 0 = 0 ∧ B ⟨0, by omega⟩ 1 = 1 ∧
       B ⟨1, by omega⟩ 0 = 1 ∧ B ⟨1, by omega⟩ 1 = 0)
  else isLocal L B

instance (L : ℕ) (B : Grid L) : Decidable (isLocalTail L B) := by
  unfold isLocalTail; infer_instance

lemma fin2_cases (x : Fin 2) : x = 0 ∨ x = 1 := by
  fin_cases x <;> simp

lemma isAdj_symm {n : ℕ} {p q : Fin n × Fin 2} (h : isAdj p q) : isAdj q p := by
  rcases h with ⟨h1, h2 | h2⟩ | ⟨h1, h2 | h2⟩
  · left; exact ⟨h1.symm, Or.inr h2⟩
  · left; exact ⟨h1.symm, Or.inl h2⟩
  · right; exact ⟨h1.symm, Or.inr h2⟩
  · right; exact ⟨h1.symm, Or.inl h2⟩

lemma adjOne_symm {n : ℕ} {A : Grid n} {p q : Fin n × Fin 2}
    (h : adjOne A p q) : adjOne A q p :=
  ⟨h.2.1, h.1, isAdj_symm h.2.2⟩

lemma reach_symm {n : ℕ} {A : Grid n} {p q : Fin n × Fin 2}
    (h : Relation.ReflTransGen (adjOne A) p q) : Relation.ReflTransGen (adjOne A) q p := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact Relation.ReflTransGen.head (adjOne_symm hstep) ih

lemma reach_stays_lt {n : ℕ} {A : Grid n} (r : Fin n)
    (hr : A r 0 ≠ 1 ∧ A r 1 ≠ 1) {p q : Fin n × Fin 2}
    (h : Relation.ReflTransGen (adjOne A) p q) (hp : p.1.1 < r.1) : q.1.1 < r.1 := by
  induction h with
  | refl => exact hp
  | @tail b c _ hbc ih =>
    have hblt : b.1.1 < r.1 := ih
    have hcne : c.1 ≠ r := by
      intro hcr
      have h1 : A r c.2 = 1 := hcr ▸ hbc.2.1
      rcases fin2_cases c.2 with hc2 | hc2
      · rw [hc2] at h1; exact hr.1 h1
      · rw [hc2] at h1; exact hr.2 h1
    rcases hbc.2.2 with ⟨hrow, _⟩ | ⟨_, hrow | hrow⟩
    · omega
    · have : c.1.1 ≠ r.1 := fun heq => hcne (Fin.ext heq)
      omega
    · omega

lemma reach_stays_le_cut {n : ℕ} {A : Grid n} (i : ℕ) (hi : i + 1 < n)
    (hcut : ∀ c : Fin 2, ¬ (A ⟨i, by omega⟩ c = 1 ∧ A ⟨i + 1, hi⟩ c = 1))
    {p q : Fin n × Fin 2} (h : Relation.ReflTransGen (adjOne A) p q) (hp : p.1.1 ≤ i) :
    q.1.1 ≤ i := by
  induction h with
  | refl => exact hp
  | @tail b c _ hbc ih =>
    have hble : b.1.1 ≤ i := ih
    rcases hbc.2.2 with ⟨hrow, _⟩ | ⟨hcol, hrow | hrow⟩
    · omega
    · by_contra hgt
      have hb_eq : b.1 = ⟨i, by omega⟩ := Fin.ext (by (try dsimp only); (try simp only [Fin.val_mk, Fin.val_last, Fin.val_castSucc]); omega)
      have hc_eq : c.1 = ⟨i + 1, hi⟩ := Fin.ext (by (try dsimp only); (try simp only [Fin.val_mk, Fin.val_last, Fin.val_castSucc]); omega)
      have hcol_eq : b.2 = c.2 := Fin.ext hcol
      have hb1 : A ⟨i, by omega⟩ c.2 = 1 := by
        rw [← hb_eq, ← hcol_eq]; exact hbc.1
      have hc1 : A ⟨i + 1, hi⟩ c.2 = 1 := by
        rw [← hc_eq]; exact hbc.2.1
      exact hcut c.2 ⟨hb1, hc1⟩
    · omega

lemma card_ge_three_of_three_nbrs {n : ℕ} {A : Grid n}
    {p q1 q2 q3 : Fin n × Fin 2}
    (hq1 : A q1.1 q1.2 = 1 ∧ isAdj p q1)
    (hq2 : A q2.1 q2.2 = 1 ∧ isAdj p q2)
    (hq3 : A q3.1 q3.2 = 1 ∧ isAdj p q3)
    (h12 : q1 ≠ q2) (h13 : q1 ≠ q3) (h23 : q2 ≠ q3) :
    3 ≤ (Finset.univ.filter (fun q : Fin n × Fin 2 => A q.1 q.2 = 1 ∧ isAdj p q)).card := by
  let S : Finset (Fin n × Fin 2) := {q1, q2, q3}
  have hsub : S ⊆ Finset.univ.filter (fun q : Fin n × Fin 2 => A q.1 q.2 = 1 ∧ isAdj p q) := by
    intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl
    · exact hq1
    · exact hq2
    · exact hq3
  have hcard : S.card = 3 := by
    simp only [S]
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp [h23]
    · simp [h12, h13]
  calc 3 = S.card := hcard.symm
    _ ≤ _ := Finset.card_le_card hsub

lemma isTopBotValid_imp_isLocal {n : ℕ} (hn : 3 ≤ n) {A : Grid n}
    (hV : isTopBotValid n A) : isLocal n A := by
  obtain ⟨hconn, ⟨hn0, c1, c2, htop, hbot, hpath⟩, hdeg⟩ := hV
  have hrow_has_one : ∀ i : Fin n, A i 0 = 1 ∨ A i 1 = 1 := by
    intro r
    by_contra hr
    push Not at hr
    by_cases hr0 : r.1 = 0
    · have : r = ⟨0, hn0⟩ := Fin.ext hr0
      rw [this] at hr
      rcases fin2_cases c1 with hc1 | hc1 <;> rw [hc1] at htop
      · exact hr.1 htop
      · exact hr.2 htop
    · by_cases hrn : r.1 = n - 1
      · have : r = ⟨n - 1, Nat.sub_lt hn0 Nat.one_pos⟩ := Fin.ext hrn
        rw [this] at hr
        rcases fin2_cases c2 with hc2 | hc2 <;> rw [hc2] at hbot
        · exact hr.1 hbot
        · exact hr.2 hbot
      · have hlt := reach_stays_lt r hr hpath (by (try dsimp only); omega)
        dsimp only at hlt
        omega
  have hno10_01 : ∀ i : Fin (n - 1),
      ¬ (A ⟨i.1, by omega⟩ 0 = 1 ∧ A ⟨i.1, by omega⟩ 1 = 0 ∧
         A ⟨i.1 + 1, by omega⟩ 0 = 0 ∧ A ⟨i.1 + 1, by omega⟩ 1 = 1) := by
    rintro i ⟨h00, h01, h10, h11⟩
    have hcut : ∀ c : Fin 2, ¬ (A ⟨i.1, by omega⟩ c = 1 ∧ A ⟨i.1 + 1, by omega⟩ c = 1) := by
      intro c ⟨ha, hb⟩
      rcases fin2_cases c with rfl | rfl
      · rw [h10] at hb; exact absurd hb (by decide)
      · rw [h01] at ha; exact absurd ha (by decide)
    have hp := hconn (⟨i.1, by omega⟩, 0) (⟨i.1 + 1, by omega⟩, 1) h00 h11
    have hle := reach_stays_le_cut i.1 (by omega) hcut hp (by (try dsimp only); omega)
    dsimp only at hle
    omega
  have hno01_10 : ∀ i : Fin (n - 1),
      ¬ (A ⟨i.1, by omega⟩ 0 = 0 ∧ A ⟨i.1, by omega⟩ 1 = 1 ∧
         A ⟨i.1 + 1, by omega⟩ 0 = 1 ∧ A ⟨i.1 + 1, by omega⟩ 1 = 0) := by
    rintro i ⟨h00, h01, h10, h11⟩
    have hcut : ∀ c : Fin 2, ¬ (A ⟨i.1, by omega⟩ c = 1 ∧ A ⟨i.1 + 1, by omega⟩ c = 1) := by
      intro c ⟨ha, hb⟩
      rcases fin2_cases c with rfl | rfl
      · rw [h00] at ha; exact absurd ha (by decide)
      · rw [h11] at hb; exact absurd hb (by decide)
    have hp := hconn (⟨i.1, by omega⟩, 1) (⟨i.1 + 1, by omega⟩, 0) h01 h10
    have hle := reach_stays_le_cut i.1 (by omega) hcut hp (by (try dsimp only); omega)
    dsimp only at hle
    omega
  have hno_triple0 : ∀ i : Fin (n - 2),
      ¬ (A ⟨i.1, by omega⟩ 0 = 1 ∧ A ⟨i.1 + 1, by omega⟩ 0 = 1 ∧
         A ⟨i.1 + 1, by omega⟩ 1 = 1 ∧ A ⟨i.1 + 2, by omega⟩ 0 = 1) := by
    rintro i ⟨ha, hb0, hb1, hc⟩
    have h3 : 3 ≤ (Finset.univ.filter (fun q : Fin n × Fin 2 =>
        A q.1 q.2 = 1 ∧ isAdj (⟨i.1 + 1, by omega⟩, (0 : Fin 2)) q)).card := by
      refine card_ge_three_of_three_nbrs
        (q1 := (⟨i.1, by omega⟩, 0)) (q2 := (⟨i.1 + 2, by omega⟩, 0))
        (q3 := (⟨i.1 + 1, by omega⟩, 1)) ?_ ?_ ?_ ?_ ?_ ?_
      · exact ⟨ha, Or.inr ⟨rfl, Or.inr rfl⟩⟩
      · exact ⟨hc, Or.inr ⟨rfl, Or.inl rfl⟩⟩
      · exact ⟨hb1, Or.inl ⟨rfl, Or.inl rfl⟩⟩
      · intro heq; have := congrArg (fun x => x.1.1) heq; dsimp only at this; omega
      · intro heq; have := congrArg (fun x => x.1.1) heq; dsimp only at this; omega
      · intro heq; have := congrArg (fun x => x.1.1) heq; dsimp only at this; omega
    have h2 := hdeg (⟨i.1 + 1, by omega⟩, 0) hb0
    omega
  have hno_triple1 : ∀ i : Fin (n - 2),
      ¬ (A ⟨i.1, by omega⟩ 1 = 1 ∧ A ⟨i.1 + 1, by omega⟩ 0 = 1 ∧
         A ⟨i.1 + 1, by omega⟩ 1 = 1 ∧ A ⟨i.1 + 2, by omega⟩ 1 = 1) := by
    rintro i ⟨ha, hb0, hb1, hc⟩
    have h3 : 3 ≤ (Finset.univ.filter (fun q : Fin n × Fin 2 =>
        A q.1 q.2 = 1 ∧ isAdj (⟨i.1 + 1, by omega⟩, (1 : Fin 2)) q)).card := by
      refine card_ge_three_of_three_nbrs
        (q1 := (⟨i.1, by omega⟩, 1)) (q2 := (⟨i.1 + 2, by omega⟩, 1))
        (q3 := (⟨i.1 + 1, by omega⟩, 0)) ?_ ?_ ?_ ?_ ?_ ?_
      · exact ⟨ha, Or.inr ⟨rfl, Or.inr rfl⟩⟩
      · exact ⟨hc, Or.inr ⟨rfl, Or.inl rfl⟩⟩
      · exact ⟨hb0, Or.inl ⟨rfl, Or.inr rfl⟩⟩
      · intro heq; have := congrArg (fun x => x.1.1) heq; dsimp only at this; omega
      · intro heq; have := congrArg (fun x => x.1.1) heq; dsimp only at this; omega
      · intro heq; have := congrArg (fun x => x.1.1) heq; dsimp only at this; omega
    have h2 := hdeg (⟨i.1 + 1, by omega⟩, 1) hb1
    omega
  have hno11_11 : ∀ i : Fin (n - 1),
      ¬ (A ⟨i.1, by omega⟩ 0 = 1 ∧ A ⟨i.1, by omega⟩ 1 = 1 ∧
         A ⟨i.1 + 1, by omega⟩ 0 = 1 ∧ A ⟨i.1 + 1, by omega⟩ 1 = 1) := by
    rintro i ⟨h00, h01, h10, h11⟩
    by_cases hi0 : i.1 = 0
    · rcases hrow_has_one ⟨i.1 + 2, by omega⟩ with hr0 | hr1
      · exact hno_triple0 ⟨i.1, by omega⟩ ⟨h00, h10, h11, hr0⟩
      · exact hno_triple1 ⟨i.1, by omega⟩ ⟨h01, h10, h11, hr1⟩
    · rcases hrow_has_one ⟨i.1 - 1, by omega⟩ with hr0 | hr1
      · have h0' : A ⟨i.1 - 1 + 1, by omega⟩ 0 = 1 := by
          convert h00 using 2; exact Fin.ext (by (try dsimp only); omega)
        have h1' : A ⟨i.1 - 1 + 1, by omega⟩ 1 = 1 := by
          convert h01 using 2; exact Fin.ext (by (try dsimp only); omega)
        have h2' : A ⟨i.1 - 1 + 2, by omega⟩ 0 = 1 := by
          convert h10 using 2; exact Fin.ext (by (try dsimp only); omega)
        exact hno_triple0 ⟨i.1 - 1, by omega⟩ ⟨hr0, h0', h1', h2'⟩
      · have h0' : A ⟨i.1 - 1 + 1, by omega⟩ 0 = 1 := by
          convert h00 using 2; exact Fin.ext (by (try dsimp only); omega)
        have h1' : A ⟨i.1 - 1 + 1, by omega⟩ 1 = 1 := by
          convert h01 using 2; exact Fin.ext (by (try dsimp only); omega)
        have h2' : A ⟨i.1 - 1 + 2, by omega⟩ 1 = 1 := by
          convert h11 using 2; exact Fin.ext (by (try dsimp only); omega)
        exact hno_triple1 ⟨i.1 - 1, by omega⟩ ⟨hr1, h0', h1', h2'⟩
  exact ⟨hrow_has_one, hno10_01, hno01_10, hno11_11, hno_triple0, hno_triple1⟩

lemma isLocal_imp_isTopBotValid {n : ℕ} (hn : 1 ≤ n) {A : Grid n}
    (hL : isLocal n A) : isTopBotValid n A := by
  obtain ⟨hrow, hno10, hno01, _, htr0, htr1⟩ := hL
  have hsame_row : ∀ (i : Fin n) (c1 c2 : Fin 2), A i c1 = 1 → A i c2 = 1 →
      Relation.ReflTransGen (adjOne A) (i, c1) (i, c2) := by
    intro i c1 c2 h1 h2
    rcases fin2_cases c1 with rfl | rfl <;> rcases fin2_cases c2 with rfl | rfl
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single ⟨h1, h2, Or.inl ⟨rfl, Or.inl rfl⟩⟩
    · exact Relation.ReflTransGen.single ⟨h1, h2, Or.inl ⟨rfl, Or.inr rfl⟩⟩
    · exact Relation.ReflTransGen.refl
  have hadj_row : ∀ (i : ℕ) (hi : i + 1 < n),
      ∃ c : Fin 2, A ⟨i, by omega⟩ c = 1 ∧ A ⟨i + 1, hi⟩ c = 1 := by
    intro i hi
    rcases fin2_cases (A ⟨i, by omega⟩ 0) with h00 | h00 <;>
    rcases fin2_cases (A ⟨i, by omega⟩ 1) with h01 | h01 <;>
    rcases fin2_cases (A ⟨i + 1, hi⟩ 0) with h10 | h10 <;>
    rcases fin2_cases (A ⟨i + 1, hi⟩ 1) with h11 | h11
    · exfalso; rcases hrow ⟨i, by omega⟩ with h | h <;> simp_all
    · exfalso; rcases hrow ⟨i, by omega⟩ with h | h <;> simp_all
    · exfalso; rcases hrow ⟨i, by omega⟩ with h | h <;> simp_all
    · exfalso; rcases hrow ⟨i, by omega⟩ with h | h <;> simp_all
    · exfalso; rcases hrow ⟨i + 1, hi⟩ with h | h <;> simp_all
    · exact ⟨1, h01, h11⟩
    · exact absurd ⟨h00, h01, h10, h11⟩ (hno01 ⟨i, by omega⟩)
    · exact ⟨1, h01, h11⟩
    · exfalso; rcases hrow ⟨i + 1, hi⟩ with h | h <;> simp_all
    · exact absurd ⟨h00, h01, h10, h11⟩ (hno10 ⟨i, by omega⟩)
    · exact ⟨0, h00, h10⟩
    · exact ⟨0, h00, h10⟩
    · exfalso; rcases hrow ⟨i + 1, hi⟩ with h | h <;> simp_all
    · exact ⟨1, h01, h11⟩
    · exact ⟨0, h00, h10⟩
    · exact ⟨0, h00, h10⟩
  have htop_ex : ∃ c0 : Fin 2, A ⟨0, by omega⟩ c0 = 1 := by
    rcases hrow ⟨0, by omega⟩ with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  obtain ⟨c0, hc0⟩ := htop_ex
  have hreach_from_top : ∀ (k : ℕ) (hk : k < n) (c : Fin 2), A ⟨k, hk⟩ c = 1 →
      Relation.ReflTransGen (adjOne A) (⟨0, by omega⟩, c0) (⟨k, hk⟩, c) := by
    intro k
    induction k with
    | zero =>
      intro hk c hc
      exact hsame_row ⟨0, by omega⟩ c0 c hc0 hc
    | succ k ih =>
      intro hk c hc
      obtain ⟨cm, hm1, hm2⟩ := hadj_row k hk
      have h1 := ih (by omega) cm hm1
      have h2 : Relation.ReflTransGen (adjOne A) (⟨k, by omega⟩, cm) (⟨k + 1, hk⟩, cm) :=
        Relation.ReflTransGen.single ⟨hm1, hm2, Or.inr ⟨rfl, Or.inl rfl⟩⟩
      have h3 := hsame_row ⟨k + 1, hk⟩ cm c hm2 hc
      exact (h1.trans h2).trans h3
  have hconn : ∀ p q : Fin n × Fin 2, A p.1 p.2 = 1 → A q.1 q.2 = 1 →
      Relation.ReflTransGen (adjOne A) p q := by
    intro p q hp hq
    exact (reach_symm (hreach_from_top p.1.1 p.1.isLt p.2 hp)).trans
      (hreach_from_top q.1.1 q.1.isLt q.2 hq)
  refine ⟨hconn, ?_, ?_⟩
  · rcases hrow ⟨n - 1, by omega⟩ with hb0 | hb1
    · exact ⟨by omega, c0, 0, hc0, hb0, hconn _ _ hc0 hb0⟩
    · exact ⟨by omega, c0, 1, hc0, hb1, hconn _ _ hc0 hb1⟩
  · intro p hp
    by_contra hgt
    push Not at hgt
    let otherCol : Fin 2 := if p.2 = 0 then 1 else 0
    have hsub : ∀ q : Fin n × Fin 2, isAdj p q →
        q = (p.1, otherCol) ∨ (q.2 = p.2 ∧ (q.1.1 + 1 = p.1.1 ∨ p.1.1 + 1 = q.1.1)) := by
      intro q hq
      rcases hq with ⟨h1, h2 | h2⟩ | ⟨h1, h2 | h2⟩
      · left; refine Prod.ext (Fin.ext h1.symm) ?_
        rcases fin2_cases p.2 with hp2 | hp2 <;> rcases fin2_cases q.2 with hq2 | hq2 <;>
          simp [otherCol, hp2, hq2] at h2 ⊢
      · left; refine Prod.ext (Fin.ext h1.symm) ?_
        rcases fin2_cases p.2 with hp2 | hp2 <;> rcases fin2_cases q.2 with hq2 | hq2 <;>
          simp [otherCol, hp2, hq2] at h2 ⊢
      · right; exact ⟨Fin.ext h1.symm, Or.inr h2⟩
      · right; exact ⟨Fin.ext h1.symm, Or.inl h2⟩
    by_cases hp0 : p.1.1 = 0
    · let S : Finset (Fin n × Fin 2) :=
        if h : p.1.1 + 1 < n then {(p.1, otherCol), (⟨p.1.1 + 1, h⟩, p.2)} else {(p.1, otherCol)}
      have hsubS : Finset.univ.filter (fun q : Fin n × Fin 2 => A q.1 q.2 = 1 ∧ isAdj p q) ⊆ S := by
        intro q hq
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
        rcases hsub q hq.2 with rfl | ⟨hc, h1 | h1⟩
        · dsimp only [S]; split_ifs <;> simp
        · omega
        · have hlt : p.1.1 + 1 < n := by omega
          dsimp only [S]; rw [dif_pos hlt]
          simp only [Finset.mem_insert, Finset.mem_singleton]
          right; exact Prod.ext (Fin.ext (by (try dsimp only); (try simp only [Fin.val_mk, Fin.val_last, Fin.val_castSucc]); omega)) hc
      have hScard : S.card ≤ 2 := by
        dsimp only [S]; split_ifs
        · exact Finset.card_le_two
        · simp
      have := Finset.card_le_card hsubS
      omega
    · by_cases hpn : p.1.1 + 1 < n
      · let q1 : Fin n × Fin 2 := (⟨p.1.1 - 1, by omega⟩, p.2)
        let q2 : Fin n × Fin 2 := (⟨p.1.1 + 1, hpn⟩, p.2)
        let q3 : Fin n × Fin 2 := (p.1, otherCol)
        let S : Finset (Fin n × Fin 2) := {q1, q2, q3}
        let F := Finset.univ.filter (fun q : Fin n × Fin 2 => A q.1 q.2 = 1 ∧ isAdj p q)
        have hsubS : F ⊆ S := by
          intro q hq
          simp only [F, Finset.mem_filter, Finset.mem_univ, true_and] at hq
          simp only [S, Finset.mem_insert, Finset.mem_singleton]
          rcases hsub q hq.2 with rfl | ⟨hc, h1 | h1⟩
          · exact Or.inr (Or.inr rfl)
          · left; exact Prod.ext (Fin.ext (by dsimp only [q1]; omega)) hc
          · right; left; exact Prod.ext (Fin.ext (by dsimp only [q2]; omega)) hc
        have hScard : S.card ≤ 3 := Finset.card_le_three
        have hFcard : F.card = 3 := by
          have hFgt : 2 < F.card := hgt
          have := Finset.card_le_card hsubS; omega
        have hFeqS : F = S := Finset.eq_of_subset_of_card_le hsubS (by omega)
        have hq1 : q1 ∈ F := hFeqS ▸ Finset.mem_insert_self q1 {q2, q3}
        have hq2 : q2 ∈ F := hFeqS ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self q2 {q3})
        have hq3 : q3 ∈ F := hFeqS ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self q3))
        simp only [F, Finset.mem_filter, Finset.mem_univ, true_and] at hq1 hq2 hq3
        have hp1_eq : (⟨p.1.1 - 1 + 1, by omega⟩ : Fin n) = p.1 := Fin.ext (by (try dsimp only); omega)
        have hp2_eq : (⟨p.1.1 - 1 + 2, by omega⟩ : Fin n) = ⟨p.1.1 + 1, hpn⟩ := Fin.ext (by (try dsimp only); omega)
        rcases fin2_cases p.2 with hp2 | hp2
        · have hoc : otherCol = 1 := by simp [otherCol, hp2]
          have ha : A ⟨p.1.1 - 1, by omega⟩ 0 = 1 := by
            have := hq1.1; dsimp only [q1] at this; rwa [hp2] at this
          have hb0 : A ⟨p.1.1 - 1 + 1, by omega⟩ 0 = 1 := by
            rw [hp1_eq]; rwa [hp2] at hp
          have hb1 : A ⟨p.1.1 - 1 + 1, by omega⟩ 1 = 1 := by
            rw [hp1_eq]; have := hq3.1; dsimp only [q3] at this; rwa [hoc] at this
          have hc : A ⟨p.1.1 - 1 + 2, by omega⟩ 0 = 1 := by
            rw [hp2_eq]; have := hq2.1; dsimp only [q2] at this; rwa [hp2] at this
          exact htr0 ⟨p.1.1 - 1, by omega⟩ ⟨ha, hb0, hb1, hc⟩
        · have hoc : otherCol = 0 := by simp [otherCol, hp2]
          have ha : A ⟨p.1.1 - 1, by omega⟩ 1 = 1 := by
            have := hq1.1; dsimp only [q1] at this; rwa [hp2] at this
          have hb0 : A ⟨p.1.1 - 1 + 1, by omega⟩ 0 = 1 := by
            rw [hp1_eq]; have := hq3.1; dsimp only [q3] at this; rwa [hoc] at this
          have hb1 : A ⟨p.1.1 - 1 + 1, by omega⟩ 1 = 1 := by
            rw [hp1_eq]; rwa [hp2] at hp
          have hc : A ⟨p.1.1 - 1 + 2, by omega⟩ 1 = 1 := by
            rw [hp2_eq]; have := hq2.1; dsimp only [q2] at this; rwa [hp2] at this
          exact htr1 ⟨p.1.1 - 1, by omega⟩ ⟨ha, hb0, hb1, hc⟩
      · let S : Finset (Fin n × Fin 2) := {(p.1, otherCol), (⟨p.1.1 - 1, by omega⟩, p.2)}
        have hsubS : Finset.univ.filter (fun q : Fin n × Fin 2 => A q.1 q.2 = 1 ∧ isAdj p q) ⊆ S := by
          intro q hq
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
          simp only [S, Finset.mem_insert, Finset.mem_singleton]
          rcases hsub q hq.2 with rfl | ⟨hc, h1 | h1⟩
          · exact Or.inl rfl
          · exact Or.inr (Prod.ext (Fin.ext (by (try dsimp only); (try simp only [Fin.val_mk, Fin.val_last, Fin.val_castSucc]); omega)) hc)
          · omega
        have hScard : S.card ≤ 2 := Finset.card_le_two
        have := Finset.card_le_card hsubS
        omega

lemma isTopBotValid_iff_isLocalTail {L : ℕ} (hL : 0 < L) (B : Grid L) :
    isTopBotValid L B ↔ isLocalTail L B := by
  by_cases h1 : L = 1
  · subst h1
    simp only [isLocalTail, ↓reduceDIte]
    constructor
    · rintro ⟨_, ⟨_, c1, _, hc1, _, _⟩, _⟩
      rcases fin2_cases c1 with rfl | rfl <;> [exact Or.inl hc1; exact Or.inr hc1]
    · intro h
      refine isLocal_imp_isTopBotValid (by omega) ?_
      refine ⟨fun i => ?_, fun i => absurd i.isLt (by omega), fun i => absurd i.isLt (by omega),
        fun i => absurd i.isLt (by omega), fun i => absurd i.isLt (by omega),
        fun i => absurd i.isLt (by omega)⟩
      fin_cases i; exact h
  · by_cases h2 : L = 2
    · subst h2
      simp only [isLocalTail, OfNat.ofNat_ne_one, ↓reduceDIte]
      constructor
      · rintro ⟨hconn, ⟨_, c1, c2, htop, hbot, _⟩, _⟩
        refine ⟨?_, ?_, ?_, ?_⟩
        · rcases fin2_cases c1 with rfl | rfl <;> [exact Or.inl htop; exact Or.inr htop]
        · rcases fin2_cases c2 with rfl | rfl <;> [exact Or.inl hbot; exact Or.inr hbot]
        · rintro ⟨h00, h01, h10, h11⟩
          have hcut : ∀ c : Fin 2, ¬ (B ⟨0, by omega⟩ c = 1 ∧ B ⟨1, by omega⟩ c = 1) := by
            intro c ⟨ha, hb⟩
            rcases fin2_cases c with rfl | rfl
            · rw [h10] at hb; exact absurd hb (by decide)
            · rw [h01] at ha; exact absurd ha (by decide)
          have hle := reach_stays_le_cut 0 (by omega) hcut (hconn (0, 0) (1, 1) h00 h11) (by decide)
          exact absurd hle (by decide)
        · rintro ⟨h00, h01, h10, h11⟩
          have hcut : ∀ c : Fin 2, ¬ (B ⟨0, by omega⟩ c = 1 ∧ B ⟨1, by omega⟩ c = 1) := by
            intro c ⟨ha, hb⟩
            rcases fin2_cases c with rfl | rfl
            · rw [h00] at ha; exact absurd ha (by decide)
            · rw [h11] at hb; exact absurd hb (by decide)
          have hle := reach_stays_le_cut 0 (by omega) hcut (hconn (0, 1) (1, 0) h01 h10) (by decide)
          exact absurd hle (by decide)
      · rintro ⟨h0, h1', hno1, hno2⟩
        by_cases hall : B 0 0 = 1 ∧ B 0 1 = 1 ∧ B 1 0 = 1 ∧ B 1 1 = 1
        · obtain ⟨h00, h01, h10, h11⟩ := hall
          have hconn : ∀ p q : Fin 2 × Fin 2, B p.1 p.2 = 1 → B q.1 q.2 = 1 →
              Relation.ReflTransGen (adjOne B) p q := by
            have h00_01 : adjOne B (0, 0) (0, 1) := ⟨h00, h01, Or.inl ⟨rfl, Or.inl rfl⟩⟩
            have h00_10 : adjOne B (0, 0) (1, 0) := ⟨h00, h10, Or.inr ⟨rfl, Or.inl rfl⟩⟩
            have h10_11 : adjOne B (1, 0) (1, 1) := ⟨h10, h11, Or.inl ⟨rfl, Or.inl rfl⟩⟩
            have hreach0 : ∀ q : Fin 2 × Fin 2, Relation.ReflTransGen (adjOne B) (0, 0) q := by
              intro ⟨r, c⟩
              fin_cases r <;> fin_cases c
              · exact Relation.ReflTransGen.refl
              · exact Relation.ReflTransGen.single h00_01
              · exact Relation.ReflTransGen.single h00_10
              · exact (Relation.ReflTransGen.single h00_10).trans (Relation.ReflTransGen.single h10_11)
            intro p q _ _
            exact (reach_symm (hreach0 p)).trans (hreach0 q)
          refine ⟨hconn, ⟨by omega, 0, 0, h00, h10, hconn _ _ h00 h10⟩, ?_⟩
          intro ⟨r, c⟩ _
          fin_cases r <;> fin_cases c <;>
          · refine le_trans (Finset.card_le_card (t := Finset.univ.filter (fun q : Fin 2 × Fin 2 => isAdj _ q))
              (fun q hq => by simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢; exact hq.2)) ?_
            decide
        · refine isLocal_imp_isTopBotValid (by omega) ?_
          refine ⟨fun i => by fin_cases i <;> assumption, fun i => ?_, fun i => ?_, fun i => ?_,
            fun i => absurd i.isLt (by omega), fun i => absurd i.isLt (by omega)⟩
          · fin_cases i; exact hno1
          · fin_cases i; exact hno2
          · fin_cases i; exact hall
    · simp only [isLocalTail, dif_neg h1, dif_neg h2]
      exact ⟨isTopBotValid_imp_isLocal (by omega), isLocal_imp_isTopBotValid (by omega)⟩

/-! ### Part 2: Four-state Fibonacci counting of `isLocal (k + 2)` -/

def setL (k : ℕ) : Finset (Grid (k + 2)) :=
  Finset.univ.filter (fun A =>
    isLocal (k + 2) A ∧ A (Fin.last (k + 1)) 0 = 1 ∧ A (Fin.last (k + 1)) 1 = 0)

def setR (k : ℕ) : Finset (Grid (k + 2)) :=
  Finset.univ.filter (fun A =>
    isLocal (k + 2) A ∧ A (Fin.last (k + 1)) 0 = 0 ∧ A (Fin.last (k + 1)) 1 = 1)

def setBL (k : ℕ) : Finset (Grid (k + 2)) :=
  Finset.univ.filter (fun A =>
    isLocal (k + 2) A ∧
    A (Fin.last (k + 1)) 0 = 1 ∧ A (Fin.last (k + 1)) 1 = 1 ∧
    A ⟨k, by omega⟩ 0 = 1 ∧ A ⟨k, by omega⟩ 1 = 0)

def setBR (k : ℕ) : Finset (Grid (k + 2)) :=
  Finset.univ.filter (fun A =>
    isLocal (k + 2) A ∧
    A (Fin.last (k + 1)) 0 = 1 ∧ A (Fin.last (k + 1)) 1 = 1 ∧
    A ⟨k, by omega⟩ 0 = 0 ∧ A ⟨k, by omega⟩ 1 = 1)

def row10 : Fin 2 → Fin 2 := fun c => if c = 0 then 1 else 0
def row01 : Fin 2 → Fin 2 := fun c => if c = 0 then 0 else 1
def row11 : Fin 2 → Fin 2 := fun _ => 1

lemma isLocal_init {k : ℕ} {A : Grid (k + 3)} (h : isLocal (k + 3) A) :
    isLocal (k + 2) (Fin.init A) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨fun i => h1 i.castSucc, fun i => h2 ⟨i.1, by omega⟩, fun i => h3 ⟨i.1, by omega⟩,
    fun i => h4 ⟨i.1, by omega⟩, fun i => h5 ⟨i.1, by omega⟩, fun i => h6 ⟨i.1, by omega⟩⟩

lemma isLocal_snoc_row10 {k : ℕ} {A : Grid (k + 2)}
    (hA : A ∈ setL k ∨ A ∈ setBR k) :
    Fin.snoc A row10 ∈ setL (k + 1) := by
  simp only [setL, setBR, Finset.mem_filter, Finset.mem_univ, true_and] at hA ⊢
  have hL : isLocal (k + 2) A := by rcases hA with h | h <;> exact h.1
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hL
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro i
    refine Fin.lastCases ?_ ?_ i
    · left; simp [row10]
    · intro j; rw [Fin.snoc_castSucc]; exact h1 j
  · intro i
    by_cases hi : i.1 < k + 1
    · have e1 : (⟨i.1, by omega⟩ : Fin (k + 3)) = (⟨i.1, by omega⟩ : Fin (k + 2)).castSucc := rfl
      have e2 : (⟨i.1 + 1, by omega⟩ : Fin (k + 3)) = (⟨i.1 + 1, by omega⟩ : Fin (k + 2)).castSucc := rfl
      rw [e1, e2, Fin.snoc_castSucc, Fin.snoc_castSucc]
      exact h2 ⟨i.1, by omega⟩
    · have e2 : (⟨i.1 + 1, by omega⟩ : Fin (k + 3)) = Fin.last (k + 2) := Fin.ext (by (try dsimp only); (try simp only [Fin.val_mk, Fin.val_last, Fin.val_castSucc]); omega)
      rw [e2, Fin.snoc_last]; simp [row10]
  · intro i
    by_cases hi : i.1 < k + 1
    · have e1 : (⟨i.1, by omega⟩ : Fin (k + 3)) = (⟨i.1, by omega⟩ : Fin (k + 2)).castSucc := rfl
      have e2 : (⟨i.1 + 1, by omega⟩ : Fin (k + 3)) = (⟨i.1 + 1, by omega⟩ : Fin (k + 2)).castSucc := rfl
      rw [e1, e2, Fin.snoc_castSucc, Fin.snoc_castSucc]
      exact h3 ⟨i.1, by omega⟩
    · have e1 : (⟨i.1, by omega⟩ : Fin (k + 3)) = (Fin.last (k + 1)).castSucc := Fin.ext (by (try dsimp only); (try simp only [Fin.val_mk, Fin.val_last, Fin.val_castSucc]); omega)
      rw [e1, Fin.snoc_castSucc]
      rintro ⟨ha, _, _, _⟩
      rcases hA with ⟨_, h0, _⟩ | ⟨_, h0, _, _, _⟩ <;> (rw [h0] at ha; exact absurd ha (by decide))
  · intro i
    by_cases hi : i.1 < k + 1
    · have e1 : (⟨i.1, by omega⟩ : Fin (k + 3)) = (⟨i.1, by omega⟩ : Fin (k + 2)).castSucc := rfl
      have e2 : (⟨i.1 + 1, by omega⟩ : Fin (k + 3)) = (⟨i.1 + 1, by omega⟩ : Fin (k + 2)).castSucc := rfl
      rw [e1, e2, Fin.snoc_castSucc, Fin.snoc_castSucc]
      exact h4 ⟨i.1, by omega⟩
    · have e2 : (⟨i.1 + 1, by omega⟩ : Fin (k + 3)) = Fin.last (k + 2) := Fin.ext (by (try dsimp only); (try simp only [Fin.val_mk, Fin.val_last, Fin.val_castSucc]); omega)
      rw [e2, Fin.snoc_last]; simp [row10]
  · intro i
    by_cases hi : i.1 < k
    · have e1 : (⟨i.1, by omega⟩ : Fin (k + 3)) = (⟨i.1, by omega⟩ : Fin (k + 2)).castSucc := rfl
      have e2 : (⟨i.1 + 1, by omega⟩ : Fin (k + 3)) = (⟨i.1 + 1, by omega⟩ : Fin (k + 2)).castSucc := rfl
      have e3 : (⟨i.1 + 2, by omega⟩ : Fin (k + 3)) = (⟨i.1 + 2, by omega⟩ : Fin (k + 2)).castSucc := rfl
      rw [e1, e2, e3, Fin.snoc_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]
      exact h5 ⟨i.1, by omega⟩
    · have e1 : (⟨i.1, by omega⟩ : Fin (k + 3)) = (⟨k, by omega⟩ : Fin (k + 2)).castSucc := Fin.ext (by (try dsimp only); (try simp only [Fin.val_mk, Fin.val_last, Fin.val_castSucc]); omega)
      have e2 : (⟨i.1 + 1, by omega⟩ : Fin (k + 3)) = (Fin.last (k + 1)).castSucc := Fin.ext (by (try dsimp only); (try simp only [Fin.val_mk, Fin.val_last, Fin.val_castSucc]); omega)
      rw [e1, e2, Fin.snoc_castSucc, Fin.snoc_castSucc]
      rintro ⟨ha, _, hb1, _⟩
      rcases hA with ⟨_, _, h1'⟩ | ⟨_, _, _, hk0, _⟩
      · rw [h1'] at hb1; exact absurd hb1 (by decide)
      · rw [hk0] at ha; exact absurd ha (by decide)
  · intro i
    by_cases hi : i.1 < k
    · have e1 : (⟨i.1, by omega⟩ : Fin (k + 3)) = (⟨i.1, by omega⟩ : Fin (k + 2)).castSucc := rfl
      have e2 : (⟨i.1 + 1, by omega⟩ : Fin (k + 3)) = (⟨i.1 + 1, by omega⟩ : Fin (k + 2)).castSucc := rfl
      have e3 : (⟨i.1 + 2, by omega⟩ : Fin (k + 3)) = (⟨i.1 + 2, by omega⟩ : Fin (k + 2)).castSucc := rfl
      rw [e1, e2, e3, Fin.snoc_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]
      exact h6 ⟨i.1, by omega⟩
    · have e3 : (⟨i.1 + 2, by omega⟩ : Fin (k + 3)) = Fin.last (k + 2) := Fin.ext (by (try dsimp only); (try simp only [Fin.val_mk, Fin.val_last, Fin.val_castSucc]); omega)
      rw [e3, Fin.snoc_last]; simp [row10]
  · rw [Fin.snoc_last]; rfl
  · rw [Fin.snoc_last]; rfl

lemma isLocal_snoc_row01 {k : ℕ} {A : Grid (k + 2)}
    (hA : A ∈ setR k ∨ A ∈ setBL k) :
    Fin.snoc A row01 ∈ setR (k + 1) := by
  simp only [setR, setBL, Finset.mem_filter, Finset.mem_univ, true_and] at hA ⊢
  have hL : isLocal (k + 2) A := by rcases hA with h | h <;> exact h.1
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hL
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro i
    refine Fin.lastCases ?_ ?_ i
    · right; simp [row01]
    · intro j; rw [Fin.snoc_castSucc]; exact h1 j
  · intro i
    by_cases hi : i.1 < k + 1
    · have e1 : (⟨i.1, by omega⟩ : Fin (k + 3)) = (⟨i.1, by omega⟩ : Fin (k + 2)).castSucc := rfl
      have e2 : (⟨i.1 + 1, by omega⟩ : Fin (k + 3)) = (⟨i.1 + 1, by omega⟩ : Fin (k + 2)).castSucc := rfl
      rw [e1, e2, Fin.snoc_castSucc, Fin.snoc_castSucc]
      exact h2 ⟨i.1, by omega⟩
    · have e1 : (⟨i.1, by omega⟩ : Fin (k + 3)) = (Fin.last (k + 1)).castSucc := Fin.ext (by (try dsimp only); (try simp only [Fin.val_mk, Fin.val_last, Fin.val_castSucc]); omega)
      rw [e1, Fin.snoc_castSucc]
      rintro ⟨_, hb, _, _⟩
      rcases hA with ⟨_, _, h1'⟩ | ⟨_, _, h1', _, _⟩ <;> (rw [h1'] at hb; exact absurd hb (by decide))
  · intro i
    by_cases hi : i.1 < k + 1
    · have e1 : (⟨i.1, by omega⟩ : Fin (k + 3)) = (⟨i.1, by omega⟩ : Fin (k + 2)).castSucc := rfl
      have e2 : (⟨i.1 + 1, by omega⟩ : Fin (k + 3)) = (⟨i.1 + 1, by omega⟩ : Fin (k + 2)).castSucc := rfl
      rw [e1, e2, Fin.snoc_castSucc, Fin.snoc_castSucc]
      exact h3 ⟨i.1, by omega⟩
    · have e2 : (⟨i.1 + 1, by omega⟩ : Fin (k + 3)) = Fin.last (k + 2) := Fin.ext (by (try dsimp only); (try simp only [Fin.val_mk, Fin.val_last, Fin.val_castSucc]); omega)
      rw [e2, Fin.snoc_last]; simp [row01]
  · intro i
    by_cases hi : i.1 < k + 1
    · have e1 : (⟨i.1, by omega⟩ : Fin (k + 3)) = (⟨i.1, by omega⟩ : Fin (k + 2)).castSucc := rfl
      have e2 : (⟨i.1 + 1, by omega⟩ : Fin (k + 3)) = (⟨i.1 + 1, by omega⟩ : Fin (k + 2)).castSucc := rfl
      rw [e1, e2, Fin.snoc_castSucc, Fin.snoc_castSucc]
      exact h4 ⟨i.1, by omega⟩
    · have e2 : (⟨i.1 + 1, by omega⟩ : Fin (k + 3)) = Fin.last (k + 2) := Fin.ext (by (try dsimp only); (try simp only [Fin.val_mk, Fin.val_last, Fin.val_castSucc]); omega)
      rw [e2, Fin.snoc_last]; simp [row01]
  · intro i
    by_cases hi : i.1 < k
    · have e1 : (⟨i.1, by omega⟩ : Fin (k + 3)) = (⟨i.1, by omega⟩ : Fin (k + 2)).castSucc := rfl
      have e2 : (⟨i.1 + 1, by omega⟩ : Fin (k + 3)) = (⟨i.1 + 1, by omega⟩ : Fin (k + 2)).castSucc := rfl
      have e3 : (⟨i.1 + 2, by omega⟩ : Fin (k + 3)) = (⟨i.1 + 2, by omega⟩ : Fin (k + 2)).castSucc := rfl
      rw [e1, e2, e3, Fin.snoc_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]
      exact h5 ⟨i.1, by omega⟩
    · have e3 : (⟨i.1 + 2, by omega⟩ : Fin (k + 3)) = Fin.last (k + 2) := Fin.ext (by (try dsimp only); (try simp only [Fin.val_mk, Fin.val_last, Fin.val_castSucc]); omega)
      rw [e3, Fin.snoc_last]; simp [row01]
  · intro i
    by_cases hi : i.1 < k
    · have e1 : (⟨i.1, by omega⟩ : Fin (k + 3)) = (⟨i.1, by omega⟩ : Fin (k + 2)).castSucc := rfl
      have e2 : (⟨i.1 + 1, by omega⟩ : Fin (k + 3)) = (⟨i.1 + 1, by omega⟩ : Fin (k + 2)).castSucc := rfl
      have e3 : (⟨i.1 + 2, by omega⟩ : Fin (k + 3)) = (⟨i.1 + 2, by omega⟩ : Fin (k + 2)).castSucc := rfl
      rw [e1, e2, e3, Fin.snoc_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]
      exact h6 ⟨i.1, by omega⟩
    · have e1 : (⟨i.1, by omega⟩ : Fin (k + 3)) = (⟨k, by omega⟩ : Fin (k + 2)).castSucc := Fin.ext (by (try dsimp only); (try simp only [Fin.val_mk, Fin.val_last, Fin.val_castSucc]); omega)
      have e2 : (⟨i.1 + 1, by omega⟩ : Fin (k + 3)) = (Fin.last (k + 1)).castSucc := Fin.ext (by (try dsimp only); (try simp only [Fin.val_mk, Fin.val_last, Fin.val_castSucc]); omega)
      rw [e1, e2, Fin.snoc_castSucc, Fin.snoc_castSucc]
      rintro ⟨ha, hb0, _, _⟩
      rcases hA with ⟨_, h0', _⟩ | ⟨_, _, _, _, hk1⟩
      · rw [h0'] at hb0; exact absurd hb0 (by decide)
      · rw [hk1] at ha; exact absurd ha (by decide)
  · rw [Fin.snoc_last]; rfl
  · rw [Fin.snoc_last]; rfl

lemma isLocal_snoc_row11_from_L {k : ℕ} {A : Grid (k + 2)} (hA : A ∈ setL k) :
    Fin.snoc A row11 ∈ setBL (k + 1) := by
  simp only [setL, setBL, Finset.mem_filter, Finset.mem_univ, true_and] at hA ⊢
  obtain ⟨⟨h1, h2, h3, h4, h5, h6⟩, hL0, hL1⟩ := hA
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro i
    refine Fin.lastCases ?_ ?_ i
    · left; rw [Fin.snoc_last]; rfl
    · intro j; rw [Fin.snoc_castSucc]; exact h1 j
  · intro i
    by_cases hi : i.1 < k + 1
    · have e1 : (⟨i.1, by omega⟩ : Fin (k + 3)) = (⟨i.1, by omega⟩ : Fin (k + 2)).castSucc := rfl
      have e2 : (⟨i.1 + 1, by omega⟩ : Fin (k + 3)) = (⟨i.1 + 1, by omega⟩ : Fin (k + 2)).castSucc := rfl
      rw [e1, e2, Fin.snoc_castSucc, Fin.snoc_castSucc]
      exact h2 ⟨i.1, by omega⟩
    · have e2 : (⟨i.1 + 1, by omega⟩ : Fin (k + 3)) = Fin.last (k + 2) := Fin.ext (by (try dsimp only); (try simp only [Fin.val_mk, Fin.val_last, Fin.val_castSucc]); omega)
      rw [e2, Fin.snoc_last]; simp [row11]
  · intro i
    by_cases hi : i.1 < k + 1
    · have e1 : (⟨i.1, by omega⟩ : Fin (k + 3)) = (⟨i.1, by omega⟩ : Fin (k + 2)).castSucc := rfl
      have e2 : (⟨i.1 + 1, by omega⟩ : Fin (k + 3)) = (⟨i.1 + 1, by omega⟩ : Fin (k + 2)).castSucc := rfl
      rw [e1, e2, Fin.snoc_castSucc, Fin.snoc_castSucc]
      exact h3 ⟨i.1, by omega⟩
    · have e2 : (⟨i.1 + 1, by omega⟩ : Fin (k + 3)) = Fin.last (k + 2) := Fin.ext (by (try dsimp only); (try simp only [Fin.val_mk, Fin.val_last, Fin.val_castSucc]); omega)
      rw [e2, Fin.snoc_last]; simp [row11]
  · intro i
    by_cases hi : i.1 < k + 1
    · have e1 : (⟨i.1, by omega⟩ : Fin (k + 3)) = (⟨i.1, by omega⟩ : Fin (k + 2)).castSucc := rfl
      have e2 : (⟨i.1 + 1, by omega⟩ : Fin (k + 3)) = (⟨i.1 + 1, by omega⟩ : Fin (k + 2)).castSucc := rfl
      rw [e1, e2, Fin.snoc_castSucc, Fin.snoc_castSucc]
      exact h4 ⟨i.1, by omega⟩
    · have e1 : (⟨i.1, by omega⟩ : Fin (k + 3)) = (Fin.last (k + 1)).castSucc := Fin.ext (by (try dsimp only); (try simp only [Fin.val_mk, Fin.val_last, Fin.val_castSucc]); omega)
      rw [e1, Fin.snoc_castSucc]
      rintro ⟨_, hb, _, _⟩
      rw [hL1] at hb; exact absurd hb (by decide)
  · intro i
    by_cases hi : i.1 < k
    · have e1 : (⟨i.1, by omega⟩ : Fin (k + 3)) = (⟨i.1, by omega⟩ : Fin (k + 2)).castSucc := rfl
      have e2 : (⟨i.1 + 1, by omega⟩ : Fin (k + 3)) = (⟨i.1 + 1, by omega⟩ : Fin (k + 2)).castSucc := rfl
      have e3 : (⟨i.1 + 2, by omega⟩ : Fin (k + 3)) = (⟨i.1 + 2, by omega⟩ : Fin (k + 2)).castSucc := rfl
      rw [e1, e2, e3, Fin.snoc_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]
      exact h5 ⟨i.1, by omega⟩
    · have e2 : (⟨i.1 + 1, by omega⟩ : Fin (k + 3)) = (Fin.last (k + 1)).castSucc := Fin.ext (by (try dsimp only); (try simp only [Fin.val_mk, Fin.val_last, Fin.val_castSucc]); omega)
      rw [e2, Fin.snoc_castSucc]
      rintro ⟨_, _, hb1, _⟩
      rw [hL1] at hb1; exact absurd hb1 (by decide)
  · intro i
    by_cases hi : i.1 < k
    · have e1 : (⟨i.1, by omega⟩ : Fin (k + 3)) = (⟨i.1, by omega⟩ : Fin (k + 2)).castSucc := rfl
      have e2 : (⟨i.1 + 1, by omega⟩ : Fin (k + 3)) = (⟨i.1 + 1, by omega⟩ : Fin (k + 2)).castSucc := rfl
      have e3 : (⟨i.1 + 2, by omega⟩ : Fin (k + 3)) = (⟨i.1 + 2, by omega⟩ : Fin (k + 2)).castSucc := rfl
      rw [e1, e2, e3, Fin.snoc_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]
      exact h6 ⟨i.1, by omega⟩
    · have e2 : (⟨i.1 + 1, by omega⟩ : Fin (k + 3)) = (Fin.last (k + 1)).castSucc := Fin.ext (by (try dsimp only); (try simp only [Fin.val_mk, Fin.val_last, Fin.val_castSucc]); omega)
      rw [e2, Fin.snoc_castSucc]
      rintro ⟨_, _, hb1, _⟩
      rw [hL1] at hb1; exact absurd hb1 (by decide)
  · rw [Fin.snoc_last]; rfl
  · rw [Fin.snoc_last]; rfl
  · have e : (⟨k + 1, by omega⟩ : Fin (k + 3)) = (Fin.last (k + 1)).castSucc := rfl
    rw [e, Fin.snoc_castSucc]; exact hL0
  · have e : (⟨k + 1, by omega⟩ : Fin (k + 3)) = (Fin.last (k + 1)).castSucc := rfl
    rw [e, Fin.snoc_castSucc]; exact hL1

lemma isLocal_snoc_row11_from_R {k : ℕ} {A : Grid (k + 2)} (hA : A ∈ setR k) :
    Fin.snoc A row11 ∈ setBR (k + 1) := by
  simp only [setR, setBR, Finset.mem_filter, Finset.mem_univ, true_and] at hA ⊢
  obtain ⟨⟨h1, h2, h3, h4, h5, h6⟩, hR0, hR1⟩ := hA
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro i
    refine Fin.lastCases ?_ ?_ i
    · left; rw [Fin.snoc_last]; rfl
    · intro j; rw [Fin.snoc_castSucc]; exact h1 j
  · intro i
    by_cases hi : i.1 < k + 1
    · have e1 : (⟨i.1, by omega⟩ : Fin (k + 3)) = (⟨i.1, by omega⟩ : Fin (k + 2)).castSucc := rfl
      have e2 : (⟨i.1 + 1, by omega⟩ : Fin (k + 3)) = (⟨i.1 + 1, by omega⟩ : Fin (k + 2)).castSucc := rfl
      rw [e1, e2, Fin.snoc_castSucc, Fin.snoc_castSucc]
      exact h2 ⟨i.1, by omega⟩
    · have e2 : (⟨i.1 + 1, by omega⟩ : Fin (k + 3)) = Fin.last (k + 2) := Fin.ext (by (try dsimp only); (try simp only [Fin.val_mk, Fin.val_last, Fin.val_castSucc]); omega)
      rw [e2, Fin.snoc_last]; simp [row11]
  · intro i
    by_cases hi : i.1 < k + 1
    · have e1 : (⟨i.1, by omega⟩ : Fin (k + 3)) = (⟨i.1, by omega⟩ : Fin (k + 2)).castSucc := rfl
      have e2 : (⟨i.1 + 1, by omega⟩ : Fin (k + 3)) = (⟨i.1 + 1, by omega⟩ : Fin (k + 2)).castSucc := rfl
      rw [e1, e2, Fin.snoc_castSucc, Fin.snoc_castSucc]
      exact h3 ⟨i.1, by omega⟩
    · have e2 : (⟨i.1 + 1, by omega⟩ : Fin (k + 3)) = Fin.last (k + 2) := Fin.ext (by (try dsimp only); (try simp only [Fin.val_mk, Fin.val_last, Fin.val_castSucc]); omega)
      rw [e2, Fin.snoc_last]; simp [row11]
  · intro i
    by_cases hi : i.1 < k + 1
    · have e1 : (⟨i.1, by omega⟩ : Fin (k + 3)) = (⟨i.1, by omega⟩ : Fin (k + 2)).castSucc := rfl
      have e2 : (⟨i.1 + 1, by omega⟩ : Fin (k + 3)) = (⟨i.1 + 1, by omega⟩ : Fin (k + 2)).castSucc := rfl
      rw [e1, e2, Fin.snoc_castSucc, Fin.snoc_castSucc]
      exact h4 ⟨i.1, by omega⟩
    · have e1 : (⟨i.1, by omega⟩ : Fin (k + 3)) = (Fin.last (k + 1)).castSucc := Fin.ext (by (try dsimp only); (try simp only [Fin.val_mk, Fin.val_last, Fin.val_castSucc]); omega)
      rw [e1, Fin.snoc_castSucc]
      rintro ⟨ha, _, _, _⟩
      rw [hR0] at ha; exact absurd ha (by decide)
  · intro i
    by_cases hi : i.1 < k
    · have e1 : (⟨i.1, by omega⟩ : Fin (k + 3)) = (⟨i.1, by omega⟩ : Fin (k + 2)).castSucc := rfl
      have e2 : (⟨i.1 + 1, by omega⟩ : Fin (k + 3)) = (⟨i.1 + 1, by omega⟩ : Fin (k + 2)).castSucc := rfl
      have e3 : (⟨i.1 + 2, by omega⟩ : Fin (k + 3)) = (⟨i.1 + 2, by omega⟩ : Fin (k + 2)).castSucc := rfl
      rw [e1, e2, e3, Fin.snoc_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]
      exact h5 ⟨i.1, by omega⟩
    · have e2 : (⟨i.1 + 1, by omega⟩ : Fin (k + 3)) = (Fin.last (k + 1)).castSucc := Fin.ext (by (try dsimp only); (try simp only [Fin.val_mk, Fin.val_last, Fin.val_castSucc]); omega)
      rw [e2, Fin.snoc_castSucc]
      rintro ⟨_, hb0, _, _⟩
      rw [hR0] at hb0; exact absurd hb0 (by decide)
  · intro i
    by_cases hi : i.1 < k
    · have e1 : (⟨i.1, by omega⟩ : Fin (k + 3)) = (⟨i.1, by omega⟩ : Fin (k + 2)).castSucc := rfl
      have e2 : (⟨i.1 + 1, by omega⟩ : Fin (k + 3)) = (⟨i.1 + 1, by omega⟩ : Fin (k + 2)).castSucc := rfl
      have e3 : (⟨i.1 + 2, by omega⟩ : Fin (k + 3)) = (⟨i.1 + 2, by omega⟩ : Fin (k + 2)).castSucc := rfl
      rw [e1, e2, e3, Fin.snoc_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]
      exact h6 ⟨i.1, by omega⟩
    · have e2 : (⟨i.1 + 1, by omega⟩ : Fin (k + 3)) = (Fin.last (k + 1)).castSucc := Fin.ext (by (try dsimp only); (try simp only [Fin.val_mk, Fin.val_last, Fin.val_castSucc]); omega)
      rw [e2, Fin.snoc_castSucc]
      rintro ⟨_, hb0, _, _⟩
      rw [hR0] at hb0; exact absurd hb0 (by decide)
  · rw [Fin.snoc_last]; rfl
  · rw [Fin.snoc_last]; rfl
  · have e : (⟨k + 1, by omega⟩ : Fin (k + 3)) = (Fin.last (k + 1)).castSucc := rfl
    rw [e, Fin.snoc_castSucc]; exact hR0
  · have e : (⟨k + 1, by omega⟩ : Fin (k + 3)) = (Fin.last (k + 1)).castSucc := rfl
    rw [e, Fin.snoc_castSucc]; exact hR1

lemma snoc_eq_self_of_row {m : ℕ} {B : Grid (m + 1)} {r : Fin 2 → Fin 2}
    (h0 : B (Fin.last m) 0 = r 0) (h1 : B (Fin.last m) 1 = r 1) :
    Fin.snoc (Fin.init B) r = B := by
  have hr : B (Fin.last m) = r := by
    funext c; rcases fin2_cases c with rfl | rfl <;> assumption
  rw [← hr, Fin.snoc_init_self]

lemma card_setL_succ (k : ℕ) : (setL (k + 1)).card = (setL k).card + (setBR k).card := by
  have hdisj : Disjoint (setL k) (setBR k) := by
    rw [Finset.disjoint_left]
    intro A h1 h2
    simp only [setL, setBR, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    rw [h1.2.2] at h2; exact absurd h2.2.2.1 (by decide)
  rw [← Finset.card_union_of_disjoint hdisj]
  apply Finset.card_bij (fun B _ => Fin.init B)
  · intro B hB
    simp only [Finset.mem_union, setL, setBR, Finset.mem_filter, Finset.mem_univ, true_and] at hB ⊢
    obtain ⟨hloc, hB0, hB1⟩ := hB
    have hinit := isLocal_init hloc
    rcases fin2_cases (B ⟨k + 1, by omega⟩ 0) with hp0 | hp0 <;>
    rcases fin2_cases (B ⟨k + 1, by omega⟩ 1) with hp1 | hp1
    · exfalso; rcases hloc.1 ⟨k + 1, by omega⟩ with h | h <;> simp_all
    · exfalso; exact hloc.2.2.1 ⟨k + 1, by omega⟩ ⟨hp0, hp1, hB0, hB1⟩
    · left; exact ⟨hinit, hp0, hp1⟩
    · right
      rcases fin2_cases (B ⟨k, by omega⟩ 0) with hq0 | hq0 <;>
      rcases fin2_cases (B ⟨k, by omega⟩ 1) with hq1 | hq1
      · exfalso; rcases hloc.1 ⟨k, by omega⟩ with h | h <;> simp_all
      · exact ⟨hinit, hp0, hp1, hq0, hq1⟩
      · exfalso; exact hloc.2.2.2.2.1 ⟨k, by omega⟩ ⟨hq0, hp0, hp1, hB0⟩
      · exfalso; exact hloc.2.2.2.1 ⟨k, by omega⟩ ⟨hq0, hq1, hp0, hp1⟩
  · intro B1 hB1 B2 hB2 heq
    simp only [setL, Finset.mem_filter, Finset.mem_univ, true_and] at hB1 hB2
    rw [← snoc_eq_self_of_row (r := row10) hB1.2.1 hB1.2.2,
        ← snoc_eq_self_of_row (r := row10) hB2.2.1 hB2.2.2, heq]
  · intro A hA
    simp only [Finset.mem_union] at hA
    exact ⟨Fin.snoc A row10, isLocal_snoc_row10 hA, (by funext i; simp [Fin.init])⟩

lemma card_setR_succ (k : ℕ) : (setR (k + 1)).card = (setR k).card + (setBL k).card := by
  have hdisj : Disjoint (setR k) (setBL k) := by
    rw [Finset.disjoint_left]
    intro A h1 h2
    simp only [setR, setBL, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    rw [h1.2.1] at h2; exact absurd h2.2.1 (by decide)
  rw [← Finset.card_union_of_disjoint hdisj]
  apply Finset.card_bij (fun B _ => Fin.init B)
  · intro B hB
    simp only [Finset.mem_union, setR, setBL, Finset.mem_filter, Finset.mem_univ, true_and] at hB ⊢
    obtain ⟨hloc, hB0, hB1⟩ := hB
    have hinit := isLocal_init hloc
    rcases fin2_cases (B ⟨k + 1, by omega⟩ 0) with hp0 | hp0 <;>
    rcases fin2_cases (B ⟨k + 1, by omega⟩ 1) with hp1 | hp1
    · exfalso; rcases hloc.1 ⟨k + 1, by omega⟩ with h | h <;> simp_all
    · left; exact ⟨hinit, hp0, hp1⟩
    · exfalso; exact hloc.2.1 ⟨k + 1, by omega⟩ ⟨hp0, hp1, hB0, hB1⟩
    · right
      rcases fin2_cases (B ⟨k, by omega⟩ 0) with hq0 | hq0 <;>
      rcases fin2_cases (B ⟨k, by omega⟩ 1) with hq1 | hq1
      · exfalso; rcases hloc.1 ⟨k, by omega⟩ with h | h <;> simp_all
      · exfalso; exact hloc.2.2.2.2.2 ⟨k, by omega⟩ ⟨hq1, hp0, hp1, hB1⟩
      · exact ⟨hinit, hp0, hp1, hq0, hq1⟩
      · exfalso; exact hloc.2.2.2.1 ⟨k, by omega⟩ ⟨hq0, hq1, hp0, hp1⟩
  · intro B1 hB1 B2 hB2 heq
    simp only [setR, Finset.mem_filter, Finset.mem_univ, true_and] at hB1 hB2
    rw [← snoc_eq_self_of_row (r := row01) hB1.2.1 hB1.2.2,
        ← snoc_eq_self_of_row (r := row01) hB2.2.1 hB2.2.2, heq]
  · intro A hA
    simp only [Finset.mem_union] at hA
    exact ⟨Fin.snoc A row01, isLocal_snoc_row01 hA, (by funext i; simp [Fin.init])⟩

lemma card_setBL_succ (k : ℕ) : (setBL (k + 1)).card = (setL k).card := by
  apply Finset.card_bij (fun B _ => Fin.init B)
  · intro B hB
    simp only [setBL, setL, Finset.mem_filter, Finset.mem_univ, true_and] at hB ⊢
    exact ⟨isLocal_init hB.1, hB.2.2.2.1, hB.2.2.2.2⟩
  · intro B1 hB1 B2 hB2 heq
    simp only [setBL, Finset.mem_filter, Finset.mem_univ, true_and] at hB1 hB2
    rw [← snoc_eq_self_of_row (r := row11) hB1.2.1 hB1.2.2.1,
        ← snoc_eq_self_of_row (r := row11) hB2.2.1 hB2.2.2.1, heq]
  · intro A hA
    exact ⟨Fin.snoc A row11, isLocal_snoc_row11_from_L hA, (by funext i; simp [Fin.init])⟩

lemma card_setBR_succ (k : ℕ) : (setBR (k + 1)).card = (setR k).card := by
  apply Finset.card_bij (fun B _ => Fin.init B)
  · intro B hB
    simp only [setBR, setR, Finset.mem_filter, Finset.mem_univ, true_and] at hB ⊢
    exact ⟨isLocal_init hB.1, hB.2.2.2.1, hB.2.2.2.2⟩
  · intro B1 hB1 B2 hB2 heq
    simp only [setBR, Finset.mem_filter, Finset.mem_univ, true_and] at hB1 hB2
    rw [← snoc_eq_self_of_row (r := row11) hB1.2.1 hB1.2.2.1,
        ← snoc_eq_self_of_row (r := row11) hB2.2.1 hB2.2.2.1, heq]
  · intro A hA
    exact ⟨Fin.snoc A row11, isLocal_snoc_row11_from_R hA, (by funext i; simp [Fin.init])⟩

lemma base_cards :
    (setL 0).card = 2 ∧ (setR 0).card = 2 ∧ (setBL 0).card = 1 ∧ (setBR 0).card = 1 := by
  decide

lemma state_cards (k : ℕ) :
    (setL k).card = Nat.fib (k + 3) ∧
    (setR k).card = Nat.fib (k + 3) ∧
    (setBL k).card = Nat.fib (k + 2) ∧
    (setBR k).card = Nat.fib (k + 2) := by
  induction k with
  | zero =>
    obtain ⟨h1, h2, h3, h4⟩ := base_cards
    exact ⟨h1, h2, h3, h4⟩
  | succ k ih =>
    obtain ⟨hL, hR, hBL, hBR⟩ := ih
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [card_setL_succ, hL, hBR, show k + 1 + 3 = (k + 2) + 2 by omega, Nat.fib_add_two (n := k + 2)]; simp only [show k + 2 + 1 = k + 3 by omega]; omega
    · rw [card_setR_succ, hR, hBL, show k + 1 + 3 = (k + 2) + 2 by omega, Nat.fib_add_two (n := k + 2)]; simp only [show k + 2 + 1 = k + 3 by omega]; omega
    · rw [card_setBL_succ, hL]
    · rw [card_setBR_succ, hR]

/-! ### Part 3: Topmost nonzero row decomposition for A163704 -/

def tailGrid {n : ℕ} (k : Fin n) (A : Grid n) : Grid (n - k.1) :=
  fun i c => A ⟨k.1 + i.1, by omega⟩ c

def goodTail (L : ℕ) (hL : 0 < L) : Finset (Grid L) :=
  Finset.univ.filter (fun B =>
    isLocalTail L B ∧ B ⟨L - 1, by omega⟩ 1 = 1 ∧ ∃ i : Fin L, B i 0 = 1)

def isGoodGrid (n : ℕ) (hn : 0 < n) (A : Grid n) : Prop :=
  ∃ k : Fin n,
    (∀ i : Fin n, i.1 < k.1 → A i 0 = 0 ∧ A i 1 = 0) ∧
    tailGrid k A ∈ goodTail (n - k.1) (by omega)

instance (n : ℕ) (hn : 0 < n) (A : Grid n) : Decidable (isGoodGrid n hn A) := by
  unfold isGoodGrid; infer_instance

lemma shift_reach_fwd {n : ℕ} {k : Fin n} {A : Grid n}
    {p q : Fin (n - k.1) × Fin 2}
    (h : Relation.ReflTransGen (adjOne (tailGrid k A)) p q) :
    Relation.ReflTransGen (adjOne A) (⟨k.1 + p.1.1, by omega⟩, p.2) (⟨k.1 + q.1.1, by omega⟩, q.2) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c _ hbc ih =>
    refine ih.tail ⟨hbc.1, hbc.2.1, ?_⟩
    rcases hbc.2.2 with ⟨h1, h2⟩ | ⟨h1, h2 | h2⟩
    · left; exact ⟨by dsimp only at h1 ⊢; omega, h2⟩
    · right; exact ⟨h1, Or.inl (by dsimp only at h2 ⊢; omega)⟩
    · right; exact ⟨h1, Or.inr (by dsimp only at h2 ⊢; omega)⟩

lemma shift_reach_bwd {n : ℕ} {k : Fin n} {A : Grid n}
    (hzero : ∀ i : Fin n, i.1 < k.1 → A i 0 = 0 ∧ A i 1 = 0)
    {p q : Fin n × Fin 2} (h : Relation.ReflTransGen (adjOne A) p q)
    (hp : k.1 ≤ p.1.1) (hq : k.1 ≤ q.1.1) :
    Relation.ReflTransGen (adjOne (tailGrid k A))
      (⟨p.1.1 - k.1, by omega⟩, p.2) (⟨q.1.1 - k.1, by omega⟩, q.2) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c _ hbc ih =>
    have hbk : k.1 ≤ b.1.1 := by
      by_contra hlt
      have hz := hzero b.1 (by omega)
      rcases fin2_cases b.2 with hb2 | hb2 <;>
        (have := hbc.1; rw [hb2] at this; simp_all)
    have ih' := ih hbk
    refine ih'.tail ⟨?_, ?_, ?_⟩
    · change A ⟨k.1 + (b.1.1 - k.1), by omega⟩ b.2 = 1
      have : (⟨k.1 + (b.1.1 - k.1), by omega⟩ : Fin n) = b.1 := Fin.ext (by (try dsimp only); (try simp only [Fin.val_mk, Fin.val_last, Fin.val_castSucc]); omega)
      rw [this]; exact hbc.1
    · change A ⟨k.1 + (c.1.1 - k.1), by omega⟩ c.2 = 1
      have : (⟨k.1 + (c.1.1 - k.1), by omega⟩ : Fin n) = c.1 := Fin.ext (by (try dsimp only); (try simp only [Fin.val_mk, Fin.val_last, Fin.val_castSucc]); omega)
      rw [this]; exact hbc.2.1
    · rcases hbc.2.2 with ⟨h1, h2⟩ | ⟨h1, h2 | h2⟩
      · left; exact ⟨by dsimp only at h1 ⊢; omega, h2⟩
      · right; exact ⟨h1, Or.inl (by dsimp only at h2 ⊢; omega)⟩
      · right; exact ⟨h1, Or.inr (by dsimp only at h2 ⊢; omega)⟩

lemma shift_deg_eq {n : ℕ} {k : Fin n} {A : Grid n}
    (hzero : ∀ i : Fin n, i.1 < k.1 → A i 0 = 0 ∧ A i 1 = 0)
    (p : Fin (n - k.1) × Fin 2) :
    (Finset.univ.filter (fun q : Fin (n - k.1) × Fin 2 =>
      tailGrid k A q.1 q.2 = 1 ∧ isAdj p q)).card =
    (Finset.univ.filter (fun q : Fin n × Fin 2 =>
      A q.1 q.2 = 1 ∧ isAdj (⟨k.1 + p.1.1, by omega⟩, p.2) q)).card := by
  apply Finset.card_bij (fun q _ => (⟨k.1 + q.1.1, by omega⟩, q.2))
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    refine ⟨hq.1, ?_⟩
    rcases hq.2 with ⟨h1, h2⟩ | ⟨h1, h2 | h2⟩
    · left; exact ⟨by dsimp only at h1 ⊢; omega, h2⟩
    · right; exact ⟨h1, Or.inl (by dsimp only at h2 ⊢; omega)⟩
    · right; exact ⟨h1, Or.inr (by dsimp only at h2 ⊢; omega)⟩
  · intro q1 _ q2 _ heq
    apply Prod.ext
    · have := congrArg (fun x => x.1.1) heq; dsimp only at this; exact Fin.ext (by (try dsimp only); (try simp only [Fin.val_mk, Fin.val_last, Fin.val_castSucc]); omega)
    · exact congrArg (fun x : Fin n × Fin 2 => x.2) heq
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
    have hqk : k.1 ≤ q.1.1 := by
      by_contra hlt
      have hz := hzero q.1 (by omega)
      rcases fin2_cases q.2 with hq2 | hq2 <;>
        (have := hq.1; rw [hq2] at this; simp_all)
    refine ⟨(⟨q.1.1 - k.1, by omega⟩, q.2), ?_, Prod.ext (Fin.ext (by (try dsimp only); (try simp only [Fin.val_mk, Fin.val_last, Fin.val_castSucc]); omega)) rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨?_, ?_⟩
    · change A ⟨k.1 + (q.1.1 - k.1), by omega⟩ q.2 = 1
      have : (⟨k.1 + (q.1.1 - k.1), by omega⟩ : Fin n) = q.1 := Fin.ext (by (try dsimp only); (try simp only [Fin.val_mk, Fin.val_last, Fin.val_castSucc]); omega)
      rw [this]; exact hq.1
    · rcases hq.2 with ⟨h1, h2⟩ | ⟨h1, h2 | h2⟩
      · left; exact ⟨by dsimp only at h1 ⊢; omega, h2⟩
      · right; exact ⟨h1, Or.inl (by dsimp only at h2 ⊢; omega)⟩
      · right; exact ⟨h1, Or.inr (by dsimp only at h2 ⊢; omega)⟩

lemma isValid_iff_isGoodGrid {n : ℕ} (hn : 0 < n) (A : Grid n) :
    isValid n A ↔ isGoodGrid n hn A := by
  constructor
  · rintro ⟨hconn, ⟨_, r0, hr0, hbot, _⟩, hdeg⟩
    let nonZeroRows : Finset (Fin n) := Finset.univ.filter (fun i => A i 0 = 1 ∨ A i 1 = 1)
    have hne : nonZeroRows.Nonempty :=
      ⟨⟨n - 1, by omega⟩, by simp only [nonZeroRows, Finset.mem_filter, Finset.mem_univ, true_and]; exact Or.inr hbot⟩
    let k : Fin n := nonZeroRows.min' hne
    have hk_mem : k ∈ nonZeroRows := Finset.min'_mem nonZeroRows hne
    simp only [nonZeroRows, Finset.mem_filter, Finset.mem_univ, true_and] at hk_mem
    have hzero : ∀ i : Fin n, i.1 < k.1 → A i 0 = 0 ∧ A i 1 = 0 := by
      intro i hi
      have hnot : i ∉ nonZeroRows := by
        intro him
        have hle : k ≤ i := Finset.min'_le nonZeroRows i him
        exact absurd hle (not_le_of_gt hi)
      simp only [nonZeroRows, Finset.mem_filter, Finset.mem_univ, true_and] at hnot
      push Not at hnot
      rcases fin2_cases (A i 0) with h0 | h0 <;> rcases fin2_cases (A i 1) with h1 | h1
      · exact ⟨h0, h1⟩
      · exact absurd h1 hnot.2
      · exact absurd h0 hnot.1
      · exact absurd h0 hnot.1
    refine ⟨k, hzero, ?_⟩
    simp only [goodTail, Finset.mem_filter, Finset.mem_univ, true_and]
    have htb : isTopBotValid (n - k.1) (tailGrid k A) := by
      refine ⟨?_, ?_, ?_⟩
      · intro p q hp hq
        have hp' : A ⟨k.1 + p.1.1, by omega⟩ p.2 = 1 := hp
        have hq' : A ⟨k.1 + q.1.1, by omega⟩ q.2 = 1 := hq
        have hr := shift_reach_bwd hzero (hconn (⟨k.1 + p.1.1, by omega⟩, p.2) (⟨k.1 + q.1.1, by omega⟩, q.2) hp' hq') (by dsimp only; omega) (by dsimp only; omega)
        convert hr using 1 <;> exact Prod.ext (Fin.ext (by (try dsimp only); omega)) rfl
      · rcases hk_mem with hk0 | hk1
        · have htop' : tailGrid k A ⟨0, by omega⟩ 0 = 1 := by
            change A ⟨k.1 + 0, by omega⟩ 0 = 1
            convert hk0 using 2; exact Fin.ext (by (try dsimp only); (try simp only [Fin.val_mk, Fin.val_last, Fin.val_castSucc]); omega)
          have hbot' : tailGrid k A ⟨n - k.1 - 1, by omega⟩ 1 = 1 := by
            change A ⟨k.1 + (n - k.1 - 1), by omega⟩ 1 = 1
            convert hbot using 2; exact Fin.ext (by (try dsimp only); (try simp only [Fin.val_mk, Fin.val_last, Fin.val_castSucc]); omega)
          have hr := shift_reach_bwd hzero (hconn (⟨k.1 + 0, by omega⟩, 0) (⟨k.1 + (n - k.1 - 1), by omega⟩, 1) htop' hbot') (by dsimp only; omega) (by dsimp only; omega)
          refine ⟨by omega, 0, 1, htop', hbot', ?_⟩
          convert hr using 1 <;> exact Prod.ext (Fin.ext (by (try dsimp only); omega)) rfl
        · have htop' : tailGrid k A ⟨0, by omega⟩ 1 = 1 := by
            change A ⟨k.1 + 0, by omega⟩ 1 = 1
            convert hk1 using 2; exact Fin.ext (by (try dsimp only); (try simp only [Fin.val_mk, Fin.val_last, Fin.val_castSucc]); omega)
          have hbot' : tailGrid k A ⟨n - k.1 - 1, by omega⟩ 1 = 1 := by
            change A ⟨k.1 + (n - k.1 - 1), by omega⟩ 1 = 1
            convert hbot using 2; exact Fin.ext (by (try dsimp only); (try simp only [Fin.val_mk, Fin.val_last, Fin.val_castSucc]); omega)
          have hr := shift_reach_bwd hzero (hconn (⟨k.1 + 0, by omega⟩, 1) (⟨k.1 + (n - k.1 - 1), by omega⟩, 1) htop' hbot') (by dsimp only; omega) (by dsimp only; omega)
          refine ⟨by omega, 1, 1, htop', hbot', ?_⟩
          convert hr using 1 <;> exact Prod.ext (Fin.ext (by (try dsimp only); omega)) rfl
      · intro p hp
        rw [shift_deg_eq hzero p]
        exact hdeg (⟨k.1 + p.1.1, by omega⟩, p.2) hp
    refine ⟨(isTopBotValid_iff_isLocalTail (by omega) (tailGrid k A)).mp htb, ?_, ?_⟩
    · change A ⟨k.1 + (n - k.1 - 1), by omega⟩ 1 = 1
      convert hbot using 2; exact Fin.ext (by (try dsimp only); (try simp only [Fin.val_mk, Fin.val_last, Fin.val_castSucc]); omega)
    · have hr0k : k.1 ≤ r0.1 := by
        by_contra hlt
        have hz := hzero r0 (by omega)
        rw [hz.1] at hr0; exact absurd hr0 (by decide)
      refine ⟨⟨r0.1 - k.1, by omega⟩, ?_⟩
      change A ⟨k.1 + (r0.1 - k.1), by omega⟩ 0 = 1
      convert hr0 using 2; exact Fin.ext (by (try dsimp only); (try simp only [Fin.val_mk, Fin.val_last, Fin.val_castSucc]); omega)
  · rintro ⟨k, hzero, hgt⟩
    simp only [goodTail, Finset.mem_filter, Finset.mem_univ, true_and] at hgt
    obtain ⟨hloc, hbot, r0, hr0⟩ := hgt
    have htb : isTopBotValid (n - k.1) (tailGrid k A) :=
      (isTopBotValid_iff_isLocalTail (by omega) (tailGrid k A)).mpr hloc
    obtain ⟨hconnB, _, hdegB⟩ := htb
    have hconnA : ∀ p q : Fin n × Fin 2, A p.1 p.2 = 1 → A q.1 q.2 = 1 →
        Relation.ReflTransGen (adjOne A) p q := by
      intro p q hp hq
      have hpk : k.1 ≤ p.1.1 := by
        by_contra hlt; have hz := hzero p.1 (by omega)
        rcases fin2_cases p.2 with hp2 | hp2 <;> (rw [hp2] at hp; simp_all)
      have hqk : k.1 ≤ q.1.1 := by
        by_contra hlt; have hz := hzero q.1 (by omega)
        rcases fin2_cases q.2 with hq2 | hq2 <;> (rw [hq2] at hq; simp_all)
      have hp' : tailGrid k A ⟨p.1.1 - k.1, by omega⟩ p.2 = 1 := by
        change A ⟨k.1 + (p.1.1 - k.1), by omega⟩ p.2 = 1
        convert hp using 2; exact Fin.ext (by (try dsimp only); (try simp only [Fin.val_mk, Fin.val_last, Fin.val_castSucc]); omega)
      have hq' : tailGrid k A ⟨q.1.1 - k.1, by omega⟩ q.2 = 1 := by
        change A ⟨k.1 + (q.1.1 - k.1), by omega⟩ q.2 = 1
        convert hq using 2; exact Fin.ext (by (try dsimp only); (try simp only [Fin.val_mk, Fin.val_last, Fin.val_castSucc]); omega)
      have hr := shift_reach_fwd (hconnB (⟨p.1.1 - k.1, by omega⟩, p.2) (⟨q.1.1 - k.1, by omega⟩, q.2) hp' hq')
      convert hr using 1 <;> exact Prod.ext (Fin.ext (by (try dsimp only); omega)) rfl
    have hbotA : A ⟨n - 1, Nat.sub_lt hn Nat.one_pos⟩ 1 = 1 := by
      dsimp only [tailGrid] at hbot
      convert hbot using 2; exact Fin.ext (by (try dsimp only); omega)
    have hr0A : A ⟨k.1 + r0.1, by omega⟩ 0 = 1 := hr0
    refine ⟨hconnA, ⟨hn, ⟨k.1 + r0.1, by omega⟩, hr0A, hbotA, hconnA _ _ hr0A hbotA⟩, ?_⟩
    intro p hp
    have hpk : k.1 ≤ p.1.1 := by
      by_contra hlt; have hz := hzero p.1 (by omega)
      rcases fin2_cases p.2 with hp2 | hp2 <;> (rw [hp2] at hp; simp_all)
    have hp' : tailGrid k A ⟨p.1.1 - k.1, by omega⟩ p.2 = 1 := by
      change A ⟨k.1 + (p.1.1 - k.1), by omega⟩ p.2 = 1
      convert hp using 2; exact Fin.ext (by (try dsimp only); (try simp only [Fin.val_mk, Fin.val_last, Fin.val_castSucc]); omega)
    have hdeg' := hdegB (⟨p.1.1 - k.1, by omega⟩, p.2) hp'
    rw [shift_deg_eq hzero] at hdeg'
    have hpeq : (⟨k.1 + (p.1.1 - k.1), by omega⟩, p.2) = p := Prod.ext (Fin.ext (by (try dsimp only); omega)) rfl
    rwa [hpeq] at hdeg'

lemma isLocalTail_row0_has_one {L : ℕ} (hL : 0 < L) {B : Grid L} (h : isLocalTail L B) :
    B ⟨0, hL⟩ 0 = 1 ∨ B ⟨0, hL⟩ 1 = 1 := by
  by_cases h1 : L = 1
  · subst h1; simp only [isLocalTail, ↓reduceDIte] at h; exact h
  · by_cases h2 : L = 2
    · subst h2; simp only [isLocalTail, OfNat.ofNat_ne_one, ↓reduceDIte] at h; exact h.1
    · simp only [isLocalTail, dif_neg h1, dif_neg h2] at h; exact h.1 ⟨0, hL⟩

def sliceSet (n : ℕ) (k : Fin n) : Finset (Grid n) :=
  Finset.univ.filter (fun A =>
    (∀ i : Fin n, i.1 < k.1 → A i 0 = 0 ∧ A i 1 = 0) ∧
    tailGrid k A ∈ goodTail (n - k.1) (by omega))

lemma card_sliceSet (n : ℕ) (k : Fin n) :
    (sliceSet n k).card = (goodTail (n - k.1) (by omega)).card := by
  apply Finset.card_bij (fun A _ => tailGrid k A)
  · intro A hA
    simp only [sliceSet, Finset.mem_filter, Finset.mem_univ, true_and] at hA
    exact hA.2
  · intro A1 hA1 A2 hA2 heq
    simp only [sliceSet, Finset.mem_filter, Finset.mem_univ, true_and] at hA1 hA2
    funext i c
    by_cases hi : i.1 < k.1
    · rcases fin2_cases c with rfl | rfl
      · rw [(hA1.1 i hi).1, (hA2.1 i hi).1]
      · rw [(hA1.1 i hi).2, (hA2.1 i hi).2]
    · have h := congrFun (congrFun heq ⟨i.1 - k.1, by omega⟩) c
      dsimp only [tailGrid] at h
      have hi' : (⟨k.1 + (i.1 - k.1), by omega⟩ : Fin n) = i := Fin.ext (by (try dsimp only); (try simp only [Fin.val_mk, Fin.val_last, Fin.val_castSucc]); omega)
      rwa [hi'] at h
  · intro B hB
    let A : Grid n := fun i c =>
      if h : i.1 < k.1 then 0 else B ⟨i.1 - k.1, by omega⟩ c
    have htail : tailGrid k A = B := by
      funext i c
      dsimp only [tailGrid, A]
      rw [dif_neg (by (try dsimp only); omega)]
      have hi' : (⟨(⟨k.1 + i.1, by omega⟩ : Fin n).1 - k.1, by omega⟩ : Fin (n - k.1)) = i :=
        Fin.ext (by (try dsimp only); omega)
      rw [hi']
    refine ⟨A, ?_, htail⟩
    simp only [sliceSet, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨fun i hi => by dsimp only [A]; simp [hi], by rwa [htail]⟩

lemma a_eq_sum_goodTail {n : ℕ} (hn : 0 < n) :
    a n = ∑ j ∈ Finset.range n, (goodTail (j + 1) (by omega)).card := by
  unfold a
  rw [if_neg (by omega)]
  rw [Nat.card_congr (Equiv.subtypeEquivRight (isValid_iff_isGoodGrid hn)),
      Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hunion : Finset.univ.filter (isGoodGrid n hn) =
      Finset.univ.biUnion (sliceSet n) := by
    ext A
    simp only [isGoodGrid, sliceSet, Finset.mem_biUnion, Finset.mem_filter,
      Finset.mem_univ, true_and]
  rw [hunion, Finset.card_biUnion]
  · simp_rw [card_sliceSet]
    apply Finset.sum_bij (fun (k : Fin n) _ => n - 1 - k.1)
    · intro k _; simp only [Finset.mem_range]; omega
    · intro k1 _ k2 _ heq; exact Fin.ext (by (try dsimp only); (try simp only [Fin.val_mk, Fin.val_last, Fin.val_castSucc]); omega)
    · intro j hj
      simp only [Finset.mem_range] at hj
      exact ⟨⟨n - 1 - j, by omega⟩, Finset.mem_univ _, by dsimp only; omega⟩
    · intro k _
      have hcongr : ∀ {L1 L2 : ℕ} (h1 : 0 < L1) (h2 : 0 < L2), L1 = L2 →
          (goodTail L1 h1).card = (goodTail L2 h2).card := by
        rintro L1 L2 h1 h2 rfl; rfl
      exact hcongr (by omega) (by omega) (by omega)
  · intro k1 _ k2 _ hne
    change Disjoint (sliceSet n k1) (sliceSet n k2)
    rw [Finset.disjoint_left]
    intro A h1 h2
    simp only [sliceSet, goodTail, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    have hlt : k1.1 < k2.1 ∨ k2.1 < k1.1 := by
      have : k1.1 ≠ k2.1 := fun h => hne (Fin.ext h)
      omega
    rcases hlt with h12 | h21
    · have hz := h2.1 k1 h12
      have ho := isLocalTail_row0_has_one (by omega) h1.2.1
      dsimp only [tailGrid] at ho
      have hk1 : (⟨k1.1 + 0, by omega⟩ : Fin n) = k1 := Fin.ext (by (try dsimp only); (try simp only [Fin.val_mk, Fin.val_last, Fin.val_castSucc]); omega)
      rw [hk1] at ho
      rcases ho with h | h <;> simp_all
    · have hz := h1.1 k2 h21
      have ho := isLocalTail_row0_has_one (by omega) h2.2.1
      dsimp only [tailGrid] at ho
      have hk2 : (⟨k2.1 + 0, by omega⟩ : Fin n) = k2 := Fin.ext (by (try dsimp only); (try simp only [Fin.val_mk, Fin.val_last, Fin.val_castSucc]); omega)
      rw [hk2] at ho
      rcases ho with h | h <;> simp_all

/-! ### Part 4: Evaluating `goodTail` and deriving the exact Fibonacci formula -/

lemma card_goodTail_1 : (goodTail 1 (by omega)).card = 1 := by decide
lemma card_goodTail_2 : (goodTail 2 (by omega)).card = 4 := by decide

def const01 (L : ℕ) : Grid L := fun _ c => if c = 0 then 0 else 1

lemma const01_mem_setR (m : ℕ) : const01 (m + 3) ∈ setR (m + 1) := by
  simp only [setR, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨⟨fun _ => Or.inr rfl, fun _ => ?_, fun _ => ?_, fun _ => ?_, fun _ => ?_, fun _ => ?_⟩, rfl, rfl⟩
  all_goals simp [const01]

lemma card_goodTail_ge3 (m : ℕ) :
    (goodTail (m + 3) (by omega)).card = Nat.fib (m + 5) + Nat.fib (m + 3) - 1 := by
  let U : Finset (Grid (m + 3)) := (setR (m + 1) ∪ setBL (m + 1)) ∪ setBR (m + 1)
  have heq : goodTail (m + 3) (by omega) = U.erase (const01 (m + 3)) := by
    ext B
    simp only [goodTail, U, Finset.mem_erase, Finset.mem_union, setR, setBL, setBR,
      Finset.mem_filter, Finset.mem_univ, true_and]
    have hloc_iff : isLocalTail (m + 3) B ↔ isLocal (m + 3) B := by
      simp only [isLocalTail, show m + 3 ≠ 1 by omega, show m + 3 ≠ 2 by omega, ↓reduceDIte]
    rw [hloc_iff]
    constructor
    · rintro ⟨hloc, hbot1, i0, hi0⟩
      refine ⟨?_, ?_⟩
      · intro hB
        rw [hB] at hi0; simp [const01] at hi0
      · have hlast : (⟨m + 3 - 1, by omega⟩ : Fin (m + 3)) = Fin.last (m + 2) := Fin.ext (by (try dsimp only); (try simp only [Fin.val_mk, Fin.val_last, Fin.val_castSucc]); omega)
        rw [hlast] at hbot1
        rcases fin2_cases (B (Fin.last (m + 2)) 0) with h0 | h0
        · exact Or.inl (Or.inl ⟨hloc, h0, hbot1⟩)
        · rcases fin2_cases (B ⟨m + 1, by omega⟩ 0) with hp0 | hp0 <;>
          rcases fin2_cases (B ⟨m + 1, by omega⟩ 1) with hp1 | hp1
          · exfalso; rcases hloc.1 ⟨m + 1, by omega⟩ with h | h <;> simp_all
          · exact Or.inr ⟨hloc, h0, hbot1, hp0, hp1⟩
          · exact Or.inl (Or.inr ⟨hloc, h0, hbot1, hp0, hp1⟩)
          · exfalso; exact hloc.2.2.2.1 ⟨m + 1, by omega⟩ ⟨hp0, hp1, h0, hbot1⟩
    · rintro ⟨hne, hmem⟩
      have hloc : isLocal (m + 3) B := by rcases hmem with (h | h) | h <;> exact h.1
      have hbot1 : B ⟨m + 3 - 1, by omega⟩ 1 = 1 := by
        have hlast : (⟨m + 3 - 1, by omega⟩ : Fin (m + 3)) = Fin.last (m + 2) := Fin.ext (by (try dsimp only); (try simp only [Fin.val_mk, Fin.val_last, Fin.val_castSucc]); omega)
        rw [hlast]
        rcases hmem with (h | h) | h
        · exact h.2.2
        · exact h.2.2.1
        · exact h.2.2.1
      refine ⟨hloc, hbot1, ?_⟩
      by_contra hno0
      push Not at hno0
      apply hne
      funext i c
      rcases fin2_cases c with rfl | rfl
      · rcases fin2_cases (B i 0) with h0 | h0
        · exact h0
        · exact absurd h0 (hno0 i)
      · rcases hloc.1 i with h0 | h1
        · exact absurd h0 (hno0 i)
        · exact h1
  have hmemU : const01 (m + 3) ∈ U :=
    Finset.mem_union_left _ (Finset.mem_union_left _ (const01_mem_setR m))
  have hd1 : Disjoint (setR (m + 1)) (setBL (m + 1)) := by
    rw [Finset.disjoint_left]; intro A h1 h2
    simp only [setR, setBL, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    rw [h1.2.1] at h2; exact absurd h2.2.1 (by decide)
  have hd2 : Disjoint (setR (m + 1) ∪ setBL (m + 1)) (setBR (m + 1)) := by
    rw [Finset.disjoint_left]; intro A h1 h2
    simp only [Finset.mem_union, setR, setBL, setBR, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    rcases h1 with ⟨_, h, _⟩ | ⟨_, _, _, h, _⟩
    · rw [h] at h2; exact absurd h2.2.1 (by decide)
    · rw [h] at h2; exact absurd h2.2.2.2.1 (by decide)
  rw [heq, Finset.card_erase_of_mem hmemU]
  dsimp only [U]
  rw [Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1]
  obtain ⟨_, hR, hBL, hBR⟩ := state_cards (m + 1)
  rw [hR, hBL, hBR]
  simp only [show m + 1 + 3 = m + 4 by omega, show m + 1 + 2 = m + 3 by omega]
  have hfib : Nat.fib (m + 5) = Nat.fib (m + 3) + Nat.fib (m + 4) := by
    rw [show m + 5 = (m + 3) + 2 by omega, Nat.fib_add_two (n := m + 3)]
  omega

lemma fib_pos (k : ℕ) : 1 ≤ Nat.fib (k + 1) := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [Nat.fib_add_two (n := k)]
    omega

lemma fib_ge_self (n : ℕ) : n + 4 ≤ Nat.fib (n + 4) + Nat.fib (n + 2) := by
  induction n with
  | zero => decide
  | succ n ih =>
    have h1 : Nat.fib (n + 1 + 4) = Nat.fib (n + 3) + Nat.fib (n + 4) := by
      rw [show n + 1 + 4 = (n + 3) + 2 by omega, Nat.fib_add_two (n := n + 3)]
    have h2 : Nat.fib (n + 1 + 2) = Nat.fib (n + 1) + Nat.fib (n + 2) := by
      rw [show n + 1 + 2 = (n + 1) + 2 by omega, Nat.fib_add_two (n := n + 1)]
    have h3 : 1 ≤ Nat.fib (n + 3) := fib_pos (n + 2)
    omega

lemma a_0 : a 0 = 0 := by simp [a]

lemma a_1 : a 1 = 1 := by
  rw [a_eq_sum_goodTail (by omega), Finset.sum_range_one]
  exact card_goodTail_1

lemma a_closed_fib {n : ℕ} (hn : 2 ≤ n) :
    a n = Nat.fib (n + 4) + Nat.fib (n + 2) - n - 4 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  clear hn
  induction k with
  | zero =>
    rw [a_eq_sum_goodTail (by omega), Finset.sum_range_succ, Finset.sum_range_one,
        card_goodTail_1, card_goodTail_2]
    decide
  | succ k ih =>
    have hsum : a (k + 3) = a (k + 2) + (goodTail (k + 3) (by omega)).card := by
      rw [a_eq_sum_goodTail (by omega), a_eq_sum_goodTail (by omega), Finset.sum_range_succ]
    change a (k + 3) = Nat.fib (k + 7) + Nat.fib (k + 5) - (k + 3) - 4
    rw [hsum, ih, card_goodTail_ge3 k]
    have hge := fib_ge_self (k + 2)
    simp only [show k + 2 + 4 = k + 6 by omega, show k + 2 + 2 = k + 4 by omega] at hge ⊢
    have hf1 : Nat.fib (k + 7) = Nat.fib (k + 5) + Nat.fib (k + 6) := by
      rw [show k + 7 = (k + 5) + 2 by omega, Nat.fib_add_two (n := k + 5)]
    have hf2 : Nat.fib (k + 5) = Nat.fib (k + 3) + Nat.fib (k + 4) := by
      rw [show k + 5 = (k + 3) + 2 by omega, Nat.fib_add_two (n := k + 3)]
    have hge3 : 1 ≤ Nat.fib (k + 3) := fib_pos (k + 2)
    omega

lemma a_closed_fib_int {n : ℕ} (hn : 2 ≤ n) :
    (a n : ℤ) = (Nat.fib (n + 4) : ℤ) + (Nat.fib (n + 2) : ℤ) - (n : ℤ) - 4 := by
  have h := a_closed_fib hn
  have hge := fib_ge_self n
  omega

/-! ### Part 5: Recurrence, generating function, and Binet closed form -/

lemma a_rec (n : ℕ) (hn : 6 ≤ n) :
    (a n : ℤ) =
      3 * (a (n - 1) : ℤ) - 2 * (a (n - 2) : ℤ) - (a (n - 3) : ℤ) + (a (n - 4) : ℤ) := by
  rw [a_closed_fib_int (by omega), a_closed_fib_int (by omega), a_closed_fib_int (by omega),
      a_closed_fib_int (by omega), a_closed_fib_int (by omega)]
  have hfib : ∀ m : ℕ, (Nat.fib (m + 4) : ℤ) =
      3 * (Nat.fib (m + 3) : ℤ) - 2 * (Nat.fib (m + 2) : ℤ) - (Nat.fib (m + 1) : ℤ) + (Nat.fib m : ℤ) := by
    intro m
    have f2 : Nat.fib (m + 2) = Nat.fib m + Nat.fib (m + 1) := Nat.fib_add_two
    have f3 : Nat.fib (m + 3) = Nat.fib (m + 1) + Nat.fib (m + 2) := by
      rw [show m + 3 = (m + 1) + 2 by omega, Nat.fib_add_two (n := m + 1)]
    have f4 : Nat.fib (m + 4) = Nat.fib (m + 2) + Nat.fib (m + 3) := by
      rw [show m + 4 = (m + 2) + 2 by omega, Nat.fib_add_two (n := m + 2)]
    omega
  have ha := hfib n
  have hb := hfib (n - 2)
  have e1 : n - 1 + 4 = n + 3 := by omega
  have e2 : n - 2 + 4 = n + 2 := by omega
  have e3 : n - 3 + 4 = n + 1 := by omega
  have e4 : n - 4 + 4 = n := by omega
  have e5 : n - 2 + 4 = n + 2 := by omega
  have e6 : n - 2 + 3 = n + 1 := by omega
  have e7 : n - 2 + 2 = n := by omega
  have e8 : n - 2 + 1 = n - 1 := by omega
  have e9 : n - 1 + 2 = n + 1 := by omega
  have e10 : n - 3 + 2 = n - 1 := by omega
  have e11 : n - 4 + 2 = n - 2 := by omega
  rw [e5, e6, e7, e8] at hb
  rw [e1, e2, e3, e4, e9, e7, e10, e11]
  omega

lemma a_gf :
    ((1 - X) ^ 2 * (1 - X - X ^ 2) : PowerSeries ℤ) * PowerSeries.mk (fun n => (a n : ℤ)) =
      X * (1 + 2 * X - 2 * X ^ 2 - X ^ 3 + X ^ 4) := by
  have h2 : a 2 = 5 := by rw [a_closed_fib (by omega)]; decide
  have h3 : a 3 = 11 := by rw [a_closed_fib (by omega)]; decide
  have h4 : a 4 = 21 := by rw [a_closed_fib (by omega)]; decide
  have h5 : a 5 = 38 := by rw [a_closed_fib (by omega)]; decide
  have hpoly : ((1 - X) ^ 2 * (1 - X - X ^ 2) : PowerSeries ℤ) =
      1 - PowerSeries.C 3 * X ^ 1 + PowerSeries.C 2 * X ^ 2 + X ^ 3 - X ^ 4 := by
    simp only [map_ofNat, pow_one]; ring
  have hrhs : (X * (1 + 2 * X - 2 * X ^ 2 - X ^ 3 + X ^ 4) : PowerSeries ℤ) =
      X ^ 1 + PowerSeries.C 2 * X ^ 2 - PowerSeries.C 2 * X ^ 3 - X ^ 4 + X ^ 5 := by
    simp only [map_ofNat, pow_one]; ring
  rw [hpoly, hrhs]
  ext n
  have hlhs : (PowerSeries.coeff n)
      ((1 - PowerSeries.C 3 * X ^ 1 + PowerSeries.C 2 * X ^ 2 + X ^ 3 - X ^ 4 : PowerSeries ℤ) *
        PowerSeries.mk (fun k => (a k : ℤ))) =
      (a n : ℤ)
      - 3 * (if 1 ≤ n then (a (n - 1) : ℤ) else 0)
      + 2 * (if 2 ≤ n then (a (n - 2) : ℤ) else 0)
      + (if 3 ≤ n then (a (n - 3) : ℤ) else 0)
      - (if 4 ≤ n then (a (n - 4) : ℤ) else 0) := by
    have hmul : (1 - PowerSeries.C 3 * X ^ 1 + PowerSeries.C 2 * X ^ 2 + X ^ 3 - X ^ 4 : PowerSeries ℤ) *
          PowerSeries.mk (fun k => (a k : ℤ)) =
        PowerSeries.mk (fun k => (a k : ℤ))
        - PowerSeries.C 3 * (X ^ 1 * PowerSeries.mk (fun k => (a k : ℤ)))
        + PowerSeries.C 2 * (X ^ 2 * PowerSeries.mk (fun k => (a k : ℤ)))
        + (X ^ 3 * PowerSeries.mk (fun k => (a k : ℤ)))
        - (X ^ 4 * PowerSeries.mk (fun k => (a k : ℤ))) := by ring
    rw [hmul, map_sub, map_add, map_add, map_sub,
        PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul,
        PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow_mul',
        PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow_mul']
    simp only [PowerSeries.coeff_mk]
  have hrc : (PowerSeries.coeff n)
      (X ^ 1 + PowerSeries.C 2 * X ^ 2 - PowerSeries.C 2 * X ^ 3 - X ^ 4 + X ^ 5 : PowerSeries ℤ) =
      (if n = 1 then 1 else 0)
      + 2 * (if n = 2 then 1 else 0)
      - 2 * (if n = 3 then 1 else 0)
      - (if n = 4 then 1 else 0)
      + (if n = 5 then 1 else 0) := by
    rw [map_add, map_sub, map_sub, map_add,
        PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul,
        PowerSeries.coeff_X_pow, PowerSeries.coeff_X_pow,
        PowerSeries.coeff_X_pow, PowerSeries.coeff_X_pow, PowerSeries.coeff_X_pow]
  rw [hlhs, hrc]
  match n with
  | 0 => simp [a_0]
  | 1 => simp [a_0, a_1]
  | 2 => simp [a_0, a_1, h2]
  | 3 => simp [a_0, a_1, h2, h3]
  | 4 => simp [a_0, a_1, h2, h3, h4]
  | 5 => simp [a_1, h2, h3, h4, h5]
  | n + 6 =>
    have hrec := a_rec (n + 6) (by omega)
    simp only [show 1 ≤ n + 6 by omega, show 2 ≤ n + 6 by omega,
      show 3 ≤ n + 6 by omega, show 4 ≤ n + 6 by omega,
      show n + 6 ≠ 1 by omega, show n + 6 ≠ 2 by omega, show n + 6 ≠ 3 by omega,
      show n + 6 ≠ 4 by omega, show n + 6 ≠ 5 by omega, ↓reduceIte,
      show n + 6 - 1 = n + 5 by omega, show n + 6 - 2 = n + 4 by omega,
      show n + 6 - 3 = n + 3 by omega, show n + 6 - 4 = n + 2 by omega] at hrec ⊢
    omega

noncomputable def binet04 (n : ℕ) : ℝ :=
  ((2 : ℝ) ^ (-(n : ℤ)) *
    ((1 - Real.sqrt 5) ^ n * (-5 + 2 * Real.sqrt 5) +
     (1 + Real.sqrt 5) ^ n * (5 + 2 * Real.sqrt 5))) / Real.sqrt 5

lemma binet04_rec (n : ℕ) : binet04 (n + 2) = binet04 (n + 1) + binet04 n := by
  unfold binet04
  have hs5 : Real.sqrt 5 ≠ 0 := by positivity
  have hsq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hp1 : (2 : ℝ) ^ (-((n + 2 : ℕ) : ℤ)) = (2 : ℝ) ^ (-(n : ℤ)) / 4 := by
    rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]; ring
  have hp2 : (2 : ℝ) ^ (-((n + 1 : ℕ) : ℤ)) = (2 : ℝ) ^ (-(n : ℤ)) / 2 := by
    rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]; ring
  rw [hp1, hp2]
  have hm : (1 - Real.sqrt 5) ^ (n + 2) = (1 - Real.sqrt 5) ^ n * (6 - 2 * Real.sqrt 5) := by
    have : (1 - Real.sqrt 5) ^ 2 = 6 - 2 * Real.sqrt 5 := by nlinarith [hsq]
    rw [pow_add, this]
  have hp : (1 + Real.sqrt 5) ^ (n + 2) = (1 + Real.sqrt 5) ^ n * (6 + 2 * Real.sqrt 5) := by
    have : (1 + Real.sqrt 5) ^ 2 = 6 + 2 * Real.sqrt 5 := by nlinarith [hsq]
    rw [pow_add, this]
  rw [hm, hp, pow_succ, pow_succ]
  field_simp [hs5]
  ring

lemma binet04_2 : binet04 2 = 11 := by
  unfold binet04
  have hs5 : Real.sqrt 5 ≠ 0 := by positivity
  have hsq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h2m : (1 - Real.sqrt 5) ^ 2 = 6 - 2 * Real.sqrt 5 := by nlinarith [hsq]
  have h2p : (1 + Real.sqrt 5) ^ 2 = 6 + 2 * Real.sqrt 5 := by nlinarith [hsq]
  rw [h2m, h2p]
  have h2 : (2 : ℝ) ^ (-((2 : ℕ) : ℤ)) = 1 / 4 := by norm_num
  rw [h2]
  field_simp [hs5]
  nlinarith [hsq]

lemma binet04_3 : binet04 3 = 18 := by
  unfold binet04
  have hs5 : Real.sqrt 5 ≠ 0 := by positivity
  have hsq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h3m : (1 - Real.sqrt 5) ^ 3 = 16 - 8 * Real.sqrt 5 := by
    calc (1 - Real.sqrt 5) ^ 3 = (1 - Real.sqrt 5) ^ 2 * (1 - Real.sqrt 5) := by ring
      _ = (6 - 2 * Real.sqrt 5) * (1 - Real.sqrt 5) := by nlinarith [hsq]
      _ = 16 - 8 * Real.sqrt 5 := by nlinarith [hsq]
  have h3p : (1 + Real.sqrt 5) ^ 3 = 16 + 8 * Real.sqrt 5 := by
    calc (1 + Real.sqrt 5) ^ 3 = (1 + Real.sqrt 5) ^ 2 * (1 + Real.sqrt 5) := by ring
      _ = (6 + 2 * Real.sqrt 5) * (1 + Real.sqrt 5) := by nlinarith [hsq]
      _ = 16 + 8 * Real.sqrt 5 := by nlinarith [hsq]
  rw [h3m, h3p]
  have h2 : (2 : ℝ) ^ (-((3 : ℕ) : ℤ)) = 1 / 8 := by norm_num
  rw [h2]
  field_simp [hs5]
  nlinarith [hsq]

lemma binet04_eq_fib (n : ℕ) (hn : 2 ≤ n) :
    binet04 n = (Nat.fib (n + 4) : ℝ) + (Nat.fib (n + 2) : ℝ) := by
  have hstep : ∀ k : ℕ,
      binet04 (k + 2) = (Nat.fib (k + 6) : ℝ) + (Nat.fib (k + 4) : ℝ) ∧
      binet04 (k + 3) = (Nat.fib (k + 7) : ℝ) + (Nat.fib (k + 5) : ℝ) := by
    intro k
    induction k with
    | zero =>
      refine ⟨?_, ?_⟩
      · rw [binet04_2]; norm_num [Nat.fib]
      · rw [binet04_3]; norm_num [Nat.fib]
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      rw [binet04_rec (k + 2), ih.2, ih.1]
      have f1 : (Nat.fib (k + 8) : ℝ) = (Nat.fib (k + 6) : ℝ) + (Nat.fib (k + 7) : ℝ) := by
        exact_mod_cast (Nat.fib_add_two (n := k + 6))
      have f2 : (Nat.fib (k + 6) : ℝ) = (Nat.fib (k + 4) : ℝ) + (Nat.fib (k + 5) : ℝ) := by
        exact_mod_cast (Nat.fib_add_two (n := k + 4))
      linarith
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  exact (hstep k).1

lemma a_closed_real (n : ℕ) (hn : n > 1) :
    (a n : ℝ) =
      -4 + ((2 : ℝ) ^ (-(n : ℤ)) *
        ((1 - Real.sqrt 5) ^ n * (-5 + 2 * Real.sqrt 5) +
         (1 + Real.sqrt 5) ^ n * (5 + 2 * Real.sqrt 5))) / Real.sqrt 5 - (n : ℝ) := by
  have hZ := a_closed_fib_int (by omega : 2 ≤ n)
  have hR : (a n : ℝ) = (Nat.fib (n + 4) : ℝ) + (Nat.fib (n + 2) : ℝ) - (n : ℝ) - 4 := by
    exact_mod_cast hZ
  have hb := binet04_eq_fib n (by omega)
  unfold binet04 at hb
  linarith

theorem main_proof :
    (∀ n ≥ 6, (a n : ℤ) =
      3 * (a (n - 1) : ℤ) - 2 * (a (n - 2) : ℤ) - (a (n - 3) : ℤ) + (a (n - 4) : ℤ)) ∧
    (((1 - X) ^ 2 * (1 - X - X ^ 2) : PowerSeries ℤ) * PowerSeries.mk (fun n => (a n : ℤ)) =
      X * (1 + 2 * X - 2 * X ^ 2 - X ^ 3 + X ^ 4)) ∧
    (∀ n > 1, (a n : ℝ) =
      -4 + ((2 : ℝ) ^ (-(n : ℤ)) *
        ((1 - Real.sqrt 5) ^ n * (-5 + 2 * Real.sqrt 5) +
         (1 + Real.sqrt 5) ^ n * (5 + 2 * Real.sqrt 5))) / Real.sqrt 5 - (n : ℝ)) :=
  ⟨a_rec, a_gf, a_closed_real⟩

end OMA.P163704

theorem OMA.solution : type_of% @OMA.S_oeis_a163704.main := OMA.P163704.main_proof
