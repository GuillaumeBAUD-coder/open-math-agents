import OMAReductions.R_Erdos338_erdos_338_variants_squares_R1

-- Step Erdos338.erdos_338.variants.squares.R1.H1: hypothesis H1 of reduction Erdos338.erdos_338.variants.squares.R1
-- Credit: @gunnerhowe
-- H1 := basisOrder (Set.range fun k : ℕ ↦ k ^ 2) = 4
-- Proof: Lagrange (Nat.sum_four_squares) gives order at most 4; squares are 0, 1, 4 mod 8,
-- so no 8N + 7 is a sum of at most 3 squares, hence order not at most 3.

namespace OMA.Step338H1

open Filter Erdos338

abbrev Sq : Set ℕ := Set.range fun k : ℕ ↦ k ^ 2

lemma sq_mod8 (k : ℕ) : k ^ 2 % 8 = 0 ∨ k ^ 2 % 8 = 1 ∨ k ^ 2 % 8 = 4 := by
  have h : k % 8 < 8 := Nat.mod_lt _ (by norm_num)
  rw [Nat.pow_mod]
  interval_cases (k % 8) <;> simp

/-- minimal number of squares (mod 8) needed to reach each residue -/
def g : ℕ → ℕ
  | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 2 | 6 => 3 | _ => 4

lemma g_step (r x : ℕ) (hx : x = 0 ∨ x = 1 ∨ x = 4) (hr : r < 8) :
    g ((x + r) % 8) ≤ g r + 1 := by
  rcases hx with rfl | rfl | rfl <;> interval_cases r <;> decide

lemma card_ge (S : Multiset ℕ) (hS : ∀ x ∈ S, x ∈ Sq) : g (S.sum % 8) ≤ S.card := by
  induction S using Multiset.induction_on with
  | empty => simp [g]
  | cons a S ih =>
    have ha : a ∈ Sq := hS a (Multiset.mem_cons_self a S)
    have ih' := ih (fun x hx => hS x (Multiset.mem_cons_of_mem hx))
    obtain ⟨k, rfl⟩ := ha
    dsimp only
    rw [Multiset.sum_cons, Multiset.card_cons, Nat.add_mod]
    have hs : S.sum % 8 % 8 = S.sum % 8 := Nat.mod_mod _ _
    have := g_step (S.sum % 8) (k ^ 2 % 8) (sq_mod8 k) (Nat.mod_lt _ (by norm_num))
    omega

lemma not_hasOrder_three : ¬ HasOrder Sq 3 := by
  intro h
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp h
  obtain ⟨S, hS, hc, hsum⟩ := hN (8 * N + 7) (by omega)
  have := card_ge S hS
  rw [hsum] at this
  have h7 : (8 * N + 7) % 8 = 7 := by omega
  rw [h7] at this
  simp [g] at this
  omega

lemma hasOrder_mono {A : Set ℕ} {h h' : ℕ} (H : HasOrder A h) (hh : h ≤ h') : HasOrder A h' := by
  unfold HasOrder at *
  filter_upwards [H] with m ⟨S, hS, hc, hs⟩
  exact ⟨S, hS, hc.trans hh, hs⟩

lemma hasOrder_four : HasOrder Sq 4 := by
  refine Filter.Eventually.of_forall fun m => ?_
  obtain ⟨a, b, c, d, h⟩ := Nat.sum_four_squares m
  refine ⟨{a ^ 2, b ^ 2, c ^ 2, d ^ 2}, ?_, by simp, by simp [← h]; ring⟩
  intro x hx
  simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩

theorem H1 : basisOrder Sq = 4 := by
  apply le_antisymm
  · exact iInf₂_le 4 hasOrder_four
  · refine le_iInf₂ fun h hh => ?_
    by_contra hlt'
    have hlt := not_le.mp hlt'
    have : h ≤ 3 := by exact_mod_cast Order.le_of_lt_succ (by exact_mod_cast hlt)
    exact not_hasOrder_three (hasOrder_mono hh this)

end OMA.Step338H1

theorem OMA.solution : OMA.R_Erdos338_erdos_338_variants_squares_R1.H1 := by
  unfold OMA.R_Erdos338_erdos_338_variants_squares_R1.H1
  exact OMA.Step338H1.H1
