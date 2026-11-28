import OMAReductions.R_Erdos556_erdos_556_R1
import Mathlib

/-! Every 3-colouring of the edges of K_13 has a monochromatic 4-cycle, i.e. R(C_4; 3) ≤ 13. -/

-- Credit: @sntntHb
-- Sketch (Bialostocki–Schönheim style double counting, no computer search):
-- * In a C_4-free colour class two distinct vertices have at most one common neighbour, so
--   the ordered cherries (v, a, b), a ≠ b both adjacent to v, inject into ordered pairs (a, b):
--   the sum over v of d(v)(d(v) - 1) is at most 13 · 12 = 156 in each colour.
-- * At each vertex the three colour degrees sum to 12, so by convexity the three values
--   d(d - 1) sum to at least 36, with equality only when all three degrees are 4.
-- * 13 · 36 = 468 = 3 · 156 forces equality everywhere: colour 0 is 4-regular and every two
--   distinct vertices have exactly one common neighbour.
-- * Then the ordered triangles number exactly 52 (one per ordered edge), but rotating a
--   triangle is a fixed-point-free map of order 3, so their number is divisible by 3.

open SimpleGraph Finset
open scoped Classical


namespace C4R

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Ordered cherries: (centre, (a, b)) with a ≠ b both adjacent to the centre. -/
noncomputable def P (G : SimpleGraph V) : Finset (V × V × V) :=
  univ.filter (fun t => t.2.1 ≠ t.2.2 ∧ G.Adj t.1 t.2.1 ∧ G.Adj t.1 t.2.2)

noncomputable def nb (G : SimpleGraph V) (v : V) : Finset V := univ.filter (G.Adj v)

lemma c4_of (G : SimpleGraph V) {v w a b : V} (hvw : v ≠ w) (hab : a ≠ b)
    (hva : G.Adj v a) (hvb : G.Adj v b) (hwa : G.Adj w a) (hwb : G.Adj w b) :
    cycleGraph 4 ⊑ G := by
  let f : Fin 4 → V := ![v, a, w, b]
  have hinj : Function.Injective f := by
    intro i j hij
    have h1 := hva.ne; have h2 := hvb.ne; have h3 := hwa.ne; have h4 := hwb.ne
    fin_cases i <;> fin_cases j <;> simp_all [f, eq_comm]
  refine ⟨⟨⟨f, ?_⟩, hinj⟩⟩
  intro i j hij
  rw [cycleGraph_adj] at hij
  fin_cases i <;> fin_cases j <;> first | (exfalso; revert hij; decide) | simp_all [f, G.adj_comm]

lemma card_P (G : SimpleGraph V) :
    (P G).card = ∑ v, ((nb G v).card * (nb G v).card - (nb G v).card) := by
  have h : ∀ v, ((nb G v).card * (nb G v).card - (nb G v).card)
      = ∑ p : V × V, if (p.1 ≠ p.2 ∧ G.Adj v p.1 ∧ G.Adj v p.2) then 1 else 0 := by
    intro v
    rw [← offDiag_card, ← Finset.card_filter]
    congr 1
    ext p
    simp [nb, mem_offDiag]
    tauto
  rw [P, Finset.card_filter, Fintype.sum_prod_type]
  exact Finset.sum_congr rfl (fun v _ => (h v).symm)

lemma card_P_le (G : SimpleGraph V) (hG : ¬ cycleGraph 4 ⊑ G) :
    (P G).card ≤ Fintype.card V * Fintype.card V - Fintype.card V := by
  rw [← Finset.card_univ, ← offDiag_card]
  refine Finset.card_le_card_of_injOn (fun t => t.2) ?_ ?_
  · intro t ht
    simp only [P, mem_filter, mem_univ, true_and, coe_filter] at ht
    simp [mem_offDiag, ht.1]
  · intro t ht s hs hts
    simp only [P, coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at ht hs
    simp only at hts
    obtain ⟨t1, t2, t3⟩ := t
    obtain ⟨s1, s2, s3⟩ := s
    simp only [Prod.mk.injEq] at hts ⊢
    obtain ⟨rfl, rfl⟩ := hts
    refine ⟨?_, rfl, rfl⟩
    by_contra hne
    exact hG (c4_of G hne ht.1 ht.2.1 ht.2.2 hs.2.1 hs.2.2)


lemma arith (a b c : ℕ) (h : a + b + c = 12) :
    36 ≤ (a * a - a) + (b * b - b) + (c * c - c) ∧
    ((a * a - a) + (b * b - b) + (c * c - c) = 36 → a = 4 ∧ b = 4 ∧ c = 4) := by
  have ha := Nat.le_mul_self a
  have hb := Nat.le_mul_self b
  have hc := Nat.le_mul_self c
  constructor
  · zify [ha, hb, hc] at h ⊢
    nlinarith [sq_nonneg ((a : ℤ) - 4), sq_nonneg ((b : ℤ) - 4), sq_nonneg ((c : ℤ) - 4)]
  · intro he
    zify [ha, hb, hc] at h he
    have h0 : ((a : ℤ) - 4) ^ 2 + ((b : ℤ) - 4) ^ 2 + ((c : ℤ) - 4) ^ 2 = 0 := by nlinarith
    have h1 : ((a : ℤ) - 4) ^ 2 = 0 := by
      nlinarith [sq_nonneg ((a : ℤ) - 4), sq_nonneg ((b : ℤ) - 4), sq_nonneg ((c : ℤ) - 4)]
    have h2 : ((b : ℤ) - 4) ^ 2 = 0 := by
      nlinarith [sq_nonneg ((a : ℤ) - 4), sq_nonneg ((b : ℤ) - 4), sq_nonneg ((c : ℤ) - 4)]
    have h3 : ((c : ℤ) - 4) ^ 2 = 0 := by
      nlinarith [sq_nonneg ((a : ℤ) - 4), sq_nonneg ((b : ℤ) - 4), sq_nonneg ((c : ℤ) - 4)]
    simp only [pow_eq_zero_iff two_ne_zero, sub_eq_zero] at h1 h2 h3
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2, by exact_mod_cast h3⟩

lemma deg_sum {N : ℕ} (c : Fin 3 → SimpleGraph (Fin N))
    (hc : (⊤ : SimpleGraph (Fin N)).IsEdgeColouring c) (v : Fin N) :
    ∑ i, (nb (c i) v).card = N - 1 := by
  have key : ∀ w, (∑ i : Fin 3, if (c i).Adj v w then 1 else 0) = if v = w then 0 else 1 := by
    intro w
    have hcov : (⊤ : SimpleGraph (Fin N)).Adj v w ↔ ∃ i, (c i).Adj v w := by
      rw [hc.1, iSup_adj]
    have hdis : ∀ i j, i ≠ j → ¬ ((c i).Adj v w ∧ (c j).Adj v w) := by
      intro i j hij ⟨h1, h2⟩
      have := hc.2 i j hij
      rw [disjoint_iff] at this
      have h3 : (c i ⊓ c j).Adj v w := ⟨h1, h2⟩
      rw [this] at h3
      exact h3
    rw [Fin.sum_univ_three]
    by_cases hvw : v = w
    · subst hvw; simp
    · have hex := hcov.1 (by simpa using hvw)
      simp only [hvw, if_false]
      have d01 := hdis 0 1 (by decide)
      have d02 := hdis 0 2 (by decide)
      have d12 := hdis 1 2 (by decide)
      obtain ⟨i, hi⟩ := hex
      fin_cases i <;> simp_all <;> split_ifs <;> simp_all
  have : ∑ i, (nb (c i) v).card = ∑ w, if v = w then 0 else 1 := by
    simp only [nb, Finset.card_filter]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun w _ => key w)
  rw [this, Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, smul_eq_mul,
    mul_one]
  have : (univ.filter (fun x : Fin N => ¬ v = x)) = univ.erase v := by
    ext x; simp [eq_comm]
  rw [this, Finset.card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]


/-- A 4-regular graph on 13 vertices in which every two distinct vertices have exactly one
common neighbour does not exist: its edges would split into triangles, but the number of
ordered triangles is 52, not a multiple of 3. -/
lemma no_friend (G : SimpleGraph (Fin 13)) (hdeg : ∀ v, (nb G v).card = 4)
    (hex : ∀ a b, a ≠ b → ∃ v, G.Adj v a ∧ G.Adj v b)
    (huniq : ∀ a b v w, a ≠ b → G.Adj v a → G.Adj v b → G.Adj w a → G.Adj w b → v = w) :
    False := by
  let T : Finset ((Fin 13 × Fin 13) × Fin 13) :=
    univ.filter (fun t => G.Adj t.2 t.1.1 ∧ G.Adj t.1.1 t.1.2 ∧ G.Adj t.1.2 t.2)
  have hT : T.card = 52 := by
    have h1 : ∀ x : Fin 13 × Fin 13,
        (∑ v : Fin 13, if (G.Adj v x.1 ∧ G.Adj x.1 x.2 ∧ G.Adj x.2 v) then 1 else 0)
          = if G.Adj x.1 x.2 then 1 else 0 := by
      intro x
      by_cases hx : G.Adj x.1 x.2
      · obtain ⟨v, hv1, hv2⟩ := hex x.1 x.2 hx.ne
        rw [if_pos hx, Finset.sum_eq_single v]
        · rw [if_pos ⟨hv1, hx, hv2.symm⟩]
        · intro w _ hwv
          rw [if_neg]
          rintro ⟨hw1, -, hw2⟩
          exact hwv (huniq x.1 x.2 w v hx.ne hw1 hw2.symm hv1 hv2)
        · simp
      · rw [if_neg hx]
        exact Finset.sum_eq_zero (fun v _ => by rw [if_neg]; tauto)
    have h2 : ∀ a : Fin 13, (∑ b : Fin 13, if G.Adj a b then 1 else 0) = 4 := by
      intro a
      rw [← hdeg a, nb, Finset.card_filter]
    simp only [T]
    rw [Finset.card_filter, Fintype.sum_prod_type]
    simp only
    calc _ = ∑ x : Fin 13 × Fin 13, (if G.Adj x.1 x.2 then 1 else 0) :=
          Finset.sum_congr rfl (fun x _ => h1 x)
      _ = 52 := by
          rw [Fintype.sum_prod_type]
          simp only [h2]
          simp
  let α := {t : (Fin 13 × Fin 13) × Fin 13 //
    G.Adj t.2 t.1.1 ∧ G.Adj t.1.1 t.1.2 ∧ G.Adj t.1.2 t.2}
  have hα : Fintype.card α = 52 := by
    rw [← hT, Fintype.card_subtype]
  let f : Function.End α := fun t => ⟨((t.1.1.2, t.1.2), t.1.1.1), t.2.2.1, t.2.2.2, t.2.1⟩
  have hf : f ^ 3 ^ 1 = 1 := by
    funext t
    rfl
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hmod := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := 3) (n := 1) hf
  have hfix : Fintype.card (Function.fixedPoints f) = 0 := by
    rw [Fintype.card_eq_zero_iff]
    constructor
    rintro ⟨t, hfx⟩
    have h1 := congrArg (fun t : α => t.1.1.1) hfx
    simp only [f] at h1
    exact t.2.2.1.ne h1.symm
  rw [hfix, hα] at hmod
  revert hmod
  decide

theorem r13 (c : Fin 3 → SimpleGraph (Fin 13))
    (hc : (⊤ : SimpleGraph (Fin 13)).IsEdgeColouring c) : ∃ i, cycleGraph 4 ⊑ c i := by
  by_contra hno'
  have hno : ∀ i, ¬ cycleGraph 4 ⊑ c i := fun i h => hno' ⟨i, h⟩
  have hle : ∀ i, (P (c i)).card ≤ 156 := fun i => by
    simpa using card_P_le (c i) (hno i)
  let g : Fin 3 → Fin 13 → ℕ := fun i v => (nb (c i) v).card * (nb (c i) v).card - (nb (c i) v).card
  have hge : ∀ v, 36 ≤ ∑ i, g i v := by
    intro v
    have hs := deg_sum c hc v
    rw [Fin.sum_univ_three] at hs ⊢
    exact (arith _ _ _ hs).1
  have hsum : ∑ i, (P (c i)).card = ∑ v, ∑ i, g i v := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun i _ => card_P (c i))
  have htot : ∑ i, (P (c i)).card ≤ 468 := by
    rw [Fin.sum_univ_three]; have := hle 0; have := hle 1; have := hle 2; omega
  have hlow : 468 ≤ ∑ v, ∑ i, g i v := by
    calc 468 = ∑ _v : Fin 13, 36 := by simp
      _ ≤ _ := Finset.sum_le_sum (fun v _ => hge v)
  have heqv : ∀ v, ∑ i, g i v = 36 := by
    have h1 : ∑ _v : Fin 13, 36 = ∑ v, ∑ i, g i v := by simp; omega
    have := (Finset.sum_eq_sum_iff_of_le (fun v _ => hge v)).1 h1
    exact fun v => (this v (mem_univ v)).symm
  have hdeg : ∀ v, (nb (c 0) v).card = 4 := by
    intro v
    have hs := deg_sum c hc v
    have he := heqv v
    rw [Fin.sum_univ_three] at hs he
    exact ((arith _ _ _ hs).2 he).1
  have hP0 : (P (c 0)).card = 156 := by
    have := hle 0; have := hle 1; have := hle 2
    rw [Fin.sum_univ_three] at hsum
    omega
  -- every pair of distinct vertices has a common neighbour in colour 0
  have hinj : Set.InjOn (fun t : Fin 13 × Fin 13 × Fin 13 => t.2) (P (c 0)) := by
    intro t ht s hs hts
    simp only [P, coe_filter, mem_univ, true_and] at ht hs
    obtain ⟨t1, t2, t3⟩ := t
    obtain ⟨s1, s2, s3⟩ := s
    simp only [Prod.mk.injEq] at hts ⊢
    obtain ⟨rfl, rfl⟩ := hts
    refine ⟨?_, rfl, rfl⟩
    by_contra hne
    exact hno 0 (c4_of (c 0) hne ht.1 ht.2.1 ht.2.2 hs.2.1 hs.2.2)
  have himg : (P (c 0)).image (fun t => t.2) = (univ : Finset (Fin 13)).offDiag := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [mem_image, P, mem_filter, mem_univ, true_and] at hx
      obtain ⟨t, ht, rfl⟩ := hx
      simp [mem_offDiag, ht.1]
    · rw [Finset.card_image_of_injOn hinj, hP0, offDiag_card]
      simp
  apply no_friend (c 0) hdeg
  · intro a b hab
    have : (a, b) ∈ (P (c 0)).image (fun t => t.2) := by
      rw [himg]; simp [mem_offDiag, hab]
    simp only [mem_image, P, mem_filter, mem_univ, true_and] at this
    obtain ⟨⟨v, a', b'⟩, ⟨-, h1, h2⟩, he⟩ := this
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨v, h1, h2⟩
  · intro a b v w hab hva hvb hwa hwb
    by_contra hne
    exact hno 0 (c4_of (c 0) hne hab hva hvb hwa hwb)

end C4R

theorem OMA.solution : OMA.R_Erdos556_erdos_556_R1.H1 := fun c hc => C4R.r13 c hc
