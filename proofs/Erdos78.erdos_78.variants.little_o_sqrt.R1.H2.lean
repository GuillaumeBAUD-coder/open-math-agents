import OMAReductions.R_Erdos78_erdos_78_variants_little_o_sqrt_R1

/-! # Homogeneous sets in hexadecimal graph powers -/
-- Credit: @steveDOTdigital
namespace OMA.HexPowers
open Finset Erdos78

private def digit (a b : ℕ) : Bool :=
  decide (((a+17-b)%17) ∈ ([1,2,4,8,9,13,15,16] : List ℕ))

private lemma symmetric_digit : ∀ a b : Fin 16, digit a b = digit b a := by decide

-- Four increasing digits cannot have all six edges the same color.
private def fourOK (a b c d : Fin 16) : Prop :=
  a < b → b < c → c < d →
    ¬ (digit a c = digit a b ∧ digit a d = digit a b ∧ digit b c = digit a b ∧
       digit b d = digit a b ∧ digit c d = digit a b)

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1400000 in
private lemma four : ∀ a b c d, fourOK a b c d := by
  intro a
  fin_cases a <;> unfold fourOK <;> decide

private lemma digit_bound (s : Finset ℕ) (small : ∀ x ∈ s, x < 16) (b : Bool)
    (h : ∀ u ∈ s, ∀ v ∈ s, u ≠ v → digit u v = b) : s.card ≤ 3 := by
  by_contra! big
  obtain ⟨T,sub,size⟩ := exists_subset_card_eq (show 4 ≤ s.card by omega)
  let e : Fin 4 ↪o ℕ := T.orderEmbOfFin size
  have mem (i : Fin 4) : e i ∈ s := sub (T.orderEmbOfFin_mem size i)
  let p (i : Fin 4) : Fin 16 := ⟨e i,small _ (mem i)⟩
  have inc {i j : Fin 4} (lt : i < j) : p i < p j := e.strictMono lt
  have col {i j : Fin 4} (ne : i ≠ j) : digit (p i) (p j) = b :=
    h _ (mem i) _ (mem j) (e.injective.ne ne)
  have no := four (p 0) (p 1) (p 2) (p 3)
    (inc (by decide)) (inc (by decide)) (inc (by decide))
  exact no ⟨(col (by decide)).trans (col (by decide)).symm,
    (col (by decide)).trans (col (by decide)).symm,(col (by decide)).trans (col (by decide)).symm,
    (col (by decide)).trans (col (by decide)).symm,(col (by decide)).trans (col (by decide)).symm⟩

private def Rule (color : ℕ → ℕ → Bool) : Prop := ∀ u v : ℕ, color u v =
  (if u = v then false else if u%16 = v%16 then color (u/16) (v/16) else digit (u%16) (v%16))

private lemma symmetric {color : ℕ → ℕ → Bool} (rule : Rule color) (u v : ℕ) :
    color u v = color v u := by
  by_cases eq : u = v
  · subst v; rfl
  by_cases rem : u%16 = v%16
  · rw [rule u v,rule v u,if_neg eq,if_neg (Ne.symm eq),if_pos rem,if_pos rem.symm]
    exact symmetric rule (u/16) (v/16)
  · rw [rule u v,rule v u,if_neg eq,if_neg (Ne.symm eq),if_neg rem,if_neg (Ne.symm rem)]
    exact symmetric_digit ⟨_,Nat.mod_lt _ (by decide)⟩ ⟨_,Nat.mod_lt _ (by decide)⟩
termination_by u+v
decreasing_by omega

private lemma power_bound {color : ℕ → ℕ → Bool} (rule : Rule color) (d : ℕ) (s : Finset ℕ)
    (small : ∀ x ∈ s, x < 16^d) (b : Bool) (mono : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → color x y = b) :
    s.card ≤ 3^d := by
  classical
  induction d generalizing s with
  | zero =>
    have sub : s ⊆ {0} := by
      intro x hx
      have := small x hx
      have eq : x = 0 := by simpa using this
      simp [eq]
    simpa using card_le_card sub
  | succ d ih =>
    let R := s.image (fun x => x%16)
    have digits : R.card ≤ 3 := by
      apply digit_bound R (by rintro x hx; obtain ⟨v,_,rfl⟩ := mem_image.mp hx; omega) b
      intro i hi j hj ne
      obtain ⟨x,hx,rfl⟩ := mem_image.mp hi
      obtain ⟨y,hy,rfl⟩ := mem_image.mp hj
      have xy : x ≠ y := by rintro rfl; exact ne rfl
      have h := mono x hx y hy xy
      simpa only [rule x y,if_neg xy,if_neg ne] using h
    have each (r : ℕ) (_ : r ∈ R) : (s.filter (fun x => x%16=r)).card ≤ 3^d := by
      let T := s.filter fun x => x%16=r
      let Q := T.image fun x => x/16
      have inj : Set.InjOn (fun x : ℕ => x/16) (T : Set ℕ) := by
        intro x hx y hy eq
        have rx := (mem_filter.mp hx).2
        have ry := (mem_filter.mp hy).2
        change x/16 = y/16 at eq
        change x%16 = r at rx
        change y%16 = r at ry
        omega
      have card : Q.card = T.card := card_image_of_injOn inj
      change T.card ≤ _
      rw [←card]
      apply ih Q
      · intro q hq
        obtain ⟨x,hx,rfl⟩ := mem_image.mp hq
        have lt := small x (mem_filter.mp hx).1
        rw [pow_succ] at lt
        exact (Nat.div_lt_iff_lt_mul (by decide : 0 < 16)).mpr lt
      · intro q hq p hp ne
        obtain ⟨x,hx,rfl⟩ := mem_image.mp hq
        obtain ⟨y,hy,rfl⟩ := mem_image.mp hp
        have xy : x ≠ y := by rintro rfl; exact ne rfl
        have rem := (mem_filter.mp hx).2.trans (mem_filter.mp hy).2.symm
        have h := mono x (mem_filter.mp hx).1 y (mem_filter.mp hy).1 xy
        simpa only [rule x y,if_neg xy,if_pos rem] using h
    calc
      s.card = ∑ r ∈ R, (s.filter fun x => x%16=r).card :=
        card_eq_sum_card_fiberwise (f := fun x : ℕ => x%16) (fun x hx => mem_image_of_mem _ hx)
      _ ≤ ∑ _r ∈ R, 3^d := sum_le_sum each
      _ ≤ 3^(d+1) := by simpa [pow_succ,mul_comm] using Nat.mul_le_mul_right (3^d) digits

private lemma fin_bound {color : ℕ → ℕ → Bool} (rule : Rule color) (d n : ℕ) (hn : n ≤ 16^d)
    (s : Finset (Fin n)) (b : Bool)
    (h : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → color x.val y.val = b) : s.card ≤ 3^d := by
  let S := s.map Fin.valEmbedding
  have cap (i : ℕ) (hi : i ∈ S) : i < 16^d := by
    obtain ⟨x,_,rfl⟩ := mem_map.mp hi
    exact x.isLt.trans_le hn
  have homo : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → color i j = b := by
    intro i hi j hj ne
    obtain ⟨x,hx,rfl⟩ := mem_map.mp hi
    obtain ⟨y,hy,rfl⟩ := mem_map.mp hj
    exact h x hx y hy (by rintro rfl; exact ne rfl)
  simpa [S] using power_bound rule d S cap b homo

theorem powers (color : ℕ → ℕ → Bool) (rule : Rule color) (d n : ℕ) (hn : n ≤ 16^d) :
    NoHomogeneousSet (explicitGraph (fun p => color p.2.1 p.2.2) n) (3^d+1) := by
  let G := explicitGraph (fun p => color p.2.1 p.2.2) n
  have adj {x y : Fin n} (ne : x ≠ y) : G.Adj x y ↔ color x.val y.val = true := by
    change (x ≠ y ∧ (color x.val y.val = true ∨ color y.val x.val = true)) ↔ _
    rw [symmetric rule y.val x.val]
    simp [ne]
  constructor
  · intro s cl
    have h := fin_bound rule d n hn s true (fun x hx y hy ne => (adj ne).mp (cl.isClique hx hy ne))
    have card := cl.card_eq
    omega
  · intro s cl
    have h := fin_bound rule d n hn s false (by
      intro x hx y hy ne
      have a := (cl.isClique hx hy ne).2
      cases bit : color x.val y.val <;> first | rfl | exact False.elim (a ((adj ne).mpr bit)))
    have card := cl.card_eq
    omega

end OMA.HexPowers

theorem OMA.solution : OMA.R_Erdos78_erdos_78_variants_little_o_sqrt_R1.H2 := OMA.HexPowers.powers
