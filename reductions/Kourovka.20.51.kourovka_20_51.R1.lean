import FormalConjectures.Kourovka.«20_51»

/-! Direct products with cyclic groups propagate realizable odd class counts to odd multiples. -/

-- Credit: @desenyon
namespace OMA.R_Kourovka_20_51_kourovka_20_51_R1

/-- The Buckley–MacHale arithmetic construction, restricted to prime class counts. -/
def H1 : Prop := ∀ t : ℕ, t.Prime → 3 < t →
  ∃ p q : ℕ, p.Prime ∧ Odd p ∧ q.Prime ∧ Odd q ∧ p ∣ q - 1 ∧ p + (q-1)/p = t

/-- Class-count realization for the odd prime-order kernel and complement construction. -/
def H2 : Prop := ∀ p q : ℕ, p.Prime → Odd p → q.Prime → Odd q → p ∣ q - 1 →
  ∃ (G : Type) (_ : Group G), Finite G ∧ (∃ a b : G, a*b ≠ b*a) ∧
    Odd (Nat.card G) ∧ Nat.card (ConjClasses G) = p + (q-1)/p

private theorem extend {s n : ℕ} (hn : Odd n)
    (hs : ∃ (G : Type) (_ : Group G), Finite G ∧ (∃ a b : G, a*b ≠ b*a) ∧
      Odd (Nat.card G) ∧ Nat.card (ConjClasses G) = s) :
    ∃ (G : Type) (_ : Group G), Finite G ∧ (∃ a b : G, a*b ≠ b*a) ∧
      Odd (Nat.card G) ∧ Nat.card (ConjClasses G) = s*n := by
  obtain ⟨G, inst, fin, ⟨a,b,hab⟩, hodd, hclasses⟩ := hs
  let : NeZero n := ⟨by obtain ⟨k,h⟩ := hn; omega⟩
  let C := Multiplicative (ZMod n)
  have hc : Nat.card C = n := by change Nat.card (ZMod n) = n; simp [Nat.card_eq_fintype_card]
  refine ⟨G × C, inferInstance, inferInstance, ⟨(a,1),(b,1),fun e => hab (congrArg Prod.fst e)⟩,
    by rw [Nat.card_prod, hc]; exact hodd.mul hn, ?_⟩
  have he := commProb_prod G C
  have hone : commProb C = 1 := commProb_eq_one_iff.mpr inferInstance
  rw [hone, mul_one, commProb_def', commProb_def', Nat.card_prod, hc, hclasses] at he
  have hg : (Nat.card G : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt Finite.card_pos)
  have hq : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  push_cast at he
  field_simp [hg,hq] at he
  rw [Nat.mul_comm s n]
  exact_mod_cast he

theorem main : H1 → H2 → type_of% @Kourovka.«20.51».kourovka_20_51 := by
  intro harith hgroup t
  induction t using Nat.strong_induction_on with
  | h t ih =>
    intro ht ho
    by_cases hp : t.Prime
    · obtain ⟨p,q,pp,op,pq,oq,hd,rfl⟩ := harith t hp ht
      exact hgroup p q pp op pq oq hd
    obtain ⟨a,b,ha,hb,hab⟩ := (Nat.not_prime_iff_exists_mul_eq (by omega)).mp hp
    have oddab : Odd a ∧ Odd b := Nat.odd_mul.mp (hab ▸ ho)
    by_cases hA : 3 < a
    · rw [← hab]
      exact extend oddab.2 (ih a ha hA oddab.1)
    by_cases hB : 3 < b
    · rw [← hab, Nat.mul_comm]
      exact extend oddab.1 (ih b hb hB oddab.2)
    obtain ⟨i,hi⟩ := oddab.1
    obtain ⟨j,hj⟩ := oddab.2
    have ea : a = 1 ∨ a = 3 := by omega
    have eb : b = 1 ∨ b = 3 := by omega
    have a3 : a = 3 := ea.resolve_left (by intro e; rw [e, one_mul] at hab; omega)
    have b3 : b = 3 := eb.resolve_left (by intro e; rw [e, mul_one] at hab; omega)
    rw [← hab, a3, b3]
    exact hgroup 3 19 (by decide) (by decide) (by decide) (by decide) (by decide)

end OMA.R_Kourovka_20_51_kourovka_20_51_R1
