import OMAReductions.R_Erdos1182_erdos_1182_variants_small_values_R1_H2_R1
 
/-! Explicit candidates for the dense triangle-good graphs in Table 2 of
Brandt, Brinkmann and Harmuth (1998). An upper-triangular bit matrix marks
the missing edges. Orders 9 through 12 use the graphs drawn on pp. 17–19.
For each order the proof checks the edge count and gives a path of length
at most two between every pair. The remaining tasks concern only whether
the prescribed edge pattern occurs in every triangle-free host complement. -/
namespace OMA.R_Erdos1182_erdos_1182_variants_small_values_R1_H2_R1_H1_R1

open SimpleGraph

/-- Complement embeddings for the specified patterns of orders 4 through 6. -/
def H1 : Prop := ∀ t : Fin 3,
  let n := t.val+4
  let m := (![2048,540672,541065248] : Fin 3 → ℕ) t
  ∀ C : SimpleGraph (Fin (2*n-1)), C.CliqueFree 3 →
    ∃ f : Fin n ↪ Fin (2*n-1), ∀ i j, i < j →
      m.testBit (i.val*n+j.val) = false → ¬ C.Adj (f i) (f j)

/-- Complement embeddings for the specified patterns of orders 7 through 8. -/
def H2 : Prop := ∀ t : Fin 2,
  let n := t.val+7
  let m := (![8757838336,36169948434793600] : Fin 2 → ℕ) t
  ∀ C : SimpleGraph (Fin (2*n-1)), C.CliqueFree 3 →
    ∃ f : Fin n ↪ Fin (2*n-1), ∀ i j, i < j →
      m.testBit (i.val*n+j.val) = false → ¬ C.Adj (f i) (f j)

/-- Complement embeddings for the specified patterns of orders 9 through 10. -/
def H3 : Prop := ∀ t : Fin 2,
  let n := t.val+9
  let m := (![2251801971660822,618970019714747783169716278] : Fin 2 → ℕ) t
  ∀ C : SimpleGraph (Fin (2*n-1)), C.CliqueFree 3 →
    ∃ f : Fin n ↪ Fin (2*n-1), ∀ i j, i < j →
      m.testBit (i.val*n+j.val) = false → ¬ C.Adj (f i) (f j)

/-- Complement embeddings for the specified patterns of orders 11 through 12. -/
def H4 : Prop := ∀ t : Fin 2,
  let n := t.val+11
  let m := (![158495020111019088292975255562,14855280693082744087392632874] : Fin 2 → ℕ) t
  ∀ C : SimpleGraph (Fin (2*n-1)), C.CliqueFree 3 →
    ∃ f : Fin n ↪ Fin (2*n-1), ∀ i j, i < j →
      m.testBit (i.val*n+j.val) = false → ¬ C.Adj (f i) (f j)

lemma sizes_and_paths : ∀ k : Fin 9,
  let n := k.val+4
  let m := (![2048,540672,541065248,8757838336,36169948434793600,2251801971660822,618970019714747783169716278,158495020111019088292975255562,14855280693082744087392632874] : Fin 9 → ℕ) k
  let G : SimpleGraph (Fin n) :=
    { Adj := fun i j => i ≠ j ∧ m.testBit ((min i j).val*n+(max i j).val) = false
      symm := ⟨fun i j h => ⟨h.1.symm,by simpa [min_comm j i,max_comm j i] using h.2⟩⟩
      loopless := ⟨by simp⟩ }
  let _ : DecidableRel G.Adj := fun i j => inferInstanceAs (Decidable (_ ∧ _))
  (∀ i j : Fin n, i=j ∨ G.Adj i j ∨ ∃ v, G.Adj i v ∧ G.Adj v j) ∧
  G.edgeFinset.card = (![5,8,12,16,20,27,33,41,49] : Fin 9 → ℕ) k := by decide

theorem main : H1 → H2 → H3 → H4 → OMA.R_Erdos1182_erdos_1182_variants_small_values_R1_H2_R1.H1 := by
  intro a b c d k
  let n := k.val+4
  let m := (![2048,540672,541065248,8757838336,36169948434793600,2251801971660822,618970019714747783169716278,158495020111019088292975255562,14855280693082744087392632874] : Fin 9 → ℕ) k
  let G : SimpleGraph (Fin n) :=
    { Adj := fun i j => i ≠ j ∧ m.testBit ((min i j).val*n+(max i j).val) = false
      symm := ⟨fun i j h => ⟨h.1.symm,by simpa [min_comm j i,max_comm j i] using h.2⟩⟩
      loopless := ⟨by simp⟩ }
  letI : DecidableRel G.Adj := fun i j => inferInstanceAs (Decidable (_ ∧ _))
  obtain ⟨paths,card⟩ := sizes_and_paths k
  have conv : G.edgeSet.ncard = G.edgeFinset.card := by
    rw [Set.ncard_eq_toFinset_card G.edgeSet]
    congr 1
    ext e
    simp [SimpleGraph.edgeFinset]
  refine ⟨G,⟨fun i j => ?_⟩,conv.trans card,?_⟩
  · rcases paths i j with h|h|⟨v,hi,hj⟩
    · subst j; exact Reachable.refl _
    · exact h.reachable
    · exact hi.reachable.trans hj.reachable
  intro C hC
  have embeds : ∃ f : Fin n ↪ Fin (2*n-1), ∀ i j, i < j →
      m.testBit (i.val*n+j.val) = false → ¬ C.Adj (f i) (f j) := by
    fin_cases k
    · exact a 0 C hC.1
    · exact a 1 C hC.1
    · exact a 2 C hC.1
    · exact b 0 C hC.1
    · exact b 1 C hC.1
    · exact c 0 C hC.1
    · exact c 1 C hC.1
    · exact d 0 C hC.1
    · exact d 1 C hC.1
  obtain ⟨f,hf⟩ := embeds
  refine ⟨⟨⟨f,?_⟩,f.injective⟩⟩
  intro i j hij
  refine ⟨f.injective.ne hij.ne,?_⟩
  rcases lt_or_gt_of_ne hij.ne with h|h
  · exact hf i j h (by simpa [min_eq_left h.le,max_eq_right h.le] using hij.2)
  · exact fun e => hf j i h (by simpa [min_eq_right h.le,max_eq_left h.le] using hij.2) e.symm

end OMA.R_Erdos1182_erdos_1182_variants_small_values_R1_H2_R1_H1_R1
