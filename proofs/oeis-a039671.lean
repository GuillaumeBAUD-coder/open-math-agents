import OMAStatements.S_oeis_a039671
import Mathlib.Tactic

open OMA.S_oeis_a039671

namespace StampCompositions

private def prepend (n k : ℕ) (p : (j : Fin (min (n+1) k)) × Bounded (n-j.val) k) :
    Bounded (n+1) k := by
  let a := p.1.val+1
  have h := p.1.isLt
  refine ⟨⟨a :: p.2.val.blocks, ?_, ?_⟩, ?_⟩
  · intro b hb
    rcases List.mem_cons.mp hb with rfl | ht
    · dsimp [a]; omega
    · exact p.2.val.blocks_pos ht
  · simp only [List.sum_cons, Composition.blocks_sum]
    dsimp [a]
    omega
  · intro b hb
    rcases List.mem_cons.mp hb with rfl | ht
    · dsimp [a]; omega
    · exact p.2.property b ht

private lemma injective (n k : ℕ) : Function.Injective (prepend n k) := by
  rintro ⟨a,u⟩ ⟨b,v⟩ h
  have lists := congrArg (fun c : Bounded (n+1) k => c.val.blocks) h
  change (a.val+1) :: u.val.blocks = (b.val+1) :: v.val.blocks at lists
  obtain ⟨heads,tails⟩ := List.cons.inj lists
  have ab : a = b := Fin.ext (by omega)
  subst b
  have uv : u = v := Subtype.ext (Composition.ext tails)
  cases uv
  rfl

private lemma surjective (n k : ℕ) : Function.Surjective (prepend n k) := by
  intro c
  cases e : c.val.blocks with
  | nil =>
    have h := c.val.blocks_sum
    simp [e] at h
  | cons a l =>
    have mem : a ∈ c.val.blocks := by simp [e]
    have pa := c.val.blocks_pos mem
    have ka := c.property a mem
    have total : a+l.sum = n+1 := by simpa only [e, List.sum_cons] using c.val.blocks_sum
    let j : Fin (min (n+1) k) := ⟨a-1, by omega⟩
    let u : Bounded (n-j.val) k :=
      ⟨⟨l, fun {b} hb => c.val.blocks_pos (by simp [e, hb]), by dsimp [j]; omega⟩,
        fun b hb => c.property b (by simp [e, hb])⟩
    refine ⟨⟨j,u⟩, Subtype.ext (Composition.ext ?_)⟩
    change (j.val+1) :: l = c.val.blocks
    rw [e, show j.val+1 = a by dsimp [j]; omega]

private lemma count (n k : ℕ) : postage k n = Nat.card (Bounded n k) := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero =>
      let empty : Bounded 0 k := ⟨⟨[], by simp, rfl⟩, by simp⟩
      let _ : Unique (Bounded 0 k) :=
        { default := empty, uniq := fun c => Subtype.ext (Composition.ext ((c.val.blocks_eq_nil).2 rfl)) }
      simp [postage]
    | succ n =>
      let e := Equiv.ofBijective (prepend n k) ⟨injective n k, surjective n k⟩
      rw [← Nat.card_congr e, Nat.card_sigma, postage]
      apply Finset.sum_congr rfl
      intro j _
      exact ih _ (by omega)

end StampCompositions

theorem OMA.solution : type_of% @OMA.S_oeis_a039671.main := by
  intro n pos
  have z : postage 0 n = 0 := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt pos)
    simp [postage]
    intro i
    have hi := i.isLt
    omega
  rw [Finset.sum_range_succ', z, add_zero]
  exact Finset.sum_congr rfl (fun j _ => StampCompositions.count n (j+1))
