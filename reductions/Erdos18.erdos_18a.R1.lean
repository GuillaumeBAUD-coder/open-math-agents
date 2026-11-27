import FormalConjectures.ErdosProblems.«18»
import Mathlib.Data.ZMod.Basic

/-!
# A dyadic-representation reduction for Erdős 18(a)

Credit: @saientropy. The mathematical method is due to Howe, Huffman,
Kohlmeyer and Kruer and their credited predecessors. The three separate
tasks are dense residue support, exact integer lifting, and factorial radix.
The reduction and its glue lemmas are independently written.
-/

namespace OMA.R_Erdos18_erdos_18a_R1

open Filter

/-- A dense set of dyadic residues has short, low representatives. -/
def H1 : Prop :=
  ∀ᶠ k : ℕ in atTop, ∃ B : Finset (ZMod (2 ^ k)),
    2 ^ k < 2 * B.card ∧ ∀ y ∈ B, ∃ S : List ℕ,
      (∀ d ∈ S, d ∣ (36 * k).factorial) ∧ S.length ≤ (Nat.log 2 k + 1) ^ 5 ∧
      S.sum ≤ 2 ^ (3 * k) ∧ (S.sum : ZMod (2 ^ k)) = y

/-- Short representatives of every dyadic residue give exact representations
for bounded integers by distinct divisors of a single factorial. -/
def H2 : Prop :=
  (∀ᶠ k : ℕ in atTop, ∀ x : ZMod (2 ^ k), ∃ S : List ℕ,
    (∀ d ∈ S, d ∣ (36 * k).factorial) ∧ S.length ≤ 2 * (Nat.log 2 k + 1) ^ 5 ∧
    S.sum ≤ 2 * 2 ^ (3 * k) ∧ (S.sum : ZMod (2 ^ k)) = x) →
  ∃ C : ℕ, ∀ᶠ T : ℕ in atTop, ∀ R : ℕ, R < 2 ^ T → ∃ D : Finset ℕ,
    D ⊆ (4 * T).factorial.divisors ∧ D.sum id = R ∧ D.card ≤ C * (Nat.log 2 T + 1) ^ 6

/-- A factorial radix extends the short representations for ordinary bit
length to a uniform bound for every target up to a factorial. -/
def H3 : Prop :=
  (∃ C : ℕ, ∀ᶠ T : ℕ in atTop, ∀ R : ℕ, R < 2 ^ T → ∃ D : Finset ℕ,
    D ⊆ (4 * T).factorial.divisors ∧ D.sum id = R ∧ D.card ≤ C * (Nat.log 2 T + 1) ^ 6) →
  ∀ᶠ n : ℕ in atTop, ∃ K : ℕ,
    (K : ℝ) < (Real.log (Real.log (n.factorial : ℝ))) ^ (9 : ℝ) ∧
    ∀ R : ℕ, 1 ≤ R → R ≤ n.factorial → ∃ D : Finset ℕ,
      D ⊆ n.factorial.divisors ∧ D.sum id = R ∧ D.card ≤ K

lemma sum_of_dense {α : Type*} [AddCommGroup α] [Fintype α] (B : Finset α)
    (h : Fintype.card α < 2 * B.card) (x : α) :
    ∃ y ∈ B, ∃ z ∈ B, y + z = x := by
  classical
  let f : α → α := fun z => x - z
  have inj : Function.Injective f := by
    intro z z' he
    simpa [f] using he
  have hs : (Finset.univ : Finset α).card < B.card + (B.image f).card := by
    rw [Finset.card_univ, Finset.card_image_of_injective _ inj, ← two_mul]
    exact h
  obtain ⟨y,hy⟩ := Finset.inter_nonempty_of_card_lt_card_add_card
    (Finset.subset_univ B) (Finset.subset_univ (B.image f)) hs
  obtain ⟨hyB,hyF⟩ := Finset.mem_inter.mp hy
  obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hyF
  exact ⟨f z,hyB,z,hz,sub_add_cancel x z⟩

lemma uniform_bound {m K : ℕ}
    (h : ∀ R : ℕ, 1 ≤ R → R ≤ m → ∃ D : Finset ℕ,
      D ⊆ m.divisors ∧ D.sum id = R ∧ D.card ≤ K) :
    Erdos18.practicalH m ≤ K := by
  unfold Erdos18.practicalH
  apply Finset.sup_le
  intro R hR
  obtain ⟨lo,hi⟩ := Finset.mem_Icc.mp hR
  obtain ⟨D,hsub,hd,hcard⟩ := h R lo hi
  apply le_trans (Nat.sInf_le (m := D.card) ?_) hcard
  refine ⟨D,hsub,rfl,D,?_,?_⟩
  · exact Set.Subset.rfl
  · exact hd.symm

theorem main : H1 → H2 → H3 → type_of% @Erdos18.erdos_18a := by
  intro h1 h2 h3
  have low := h2 (by
    filter_upwards [h1] with k hk
    obtain ⟨B,hcard,hrep⟩ := hk
    intro x
    have hsize : Fintype.card (ZMod (2 ^ k)) < 2 * B.card := by
      simpa only [ZMod.card] using hcard
    obtain ⟨y,hy,z,hz,hyz⟩ := sum_of_dense B hsize x
    obtain ⟨U,hU,lU,sU,eU⟩ := hrep y hy
    obtain ⟨V,hV,lV,sV,eV⟩ := hrep z hz
    refine ⟨U ++ V, ?_, ?_, ?_, ?_⟩
    · intro d hd
      exact (List.mem_append.mp hd).elim (hU d) (hV d)
    · simpa [two_mul] using Nat.add_le_add lU lV
    · simpa [two_mul] using Nat.add_le_add sU sV
    · simpa [List.sum_append, Nat.cast_add, eU, eV] using hyz)
  obtain ⟨n₀, hall⟩ := Filter.eventually_atTop.mp (h3 low)
  refine ⟨9, by norm_num, Filter.frequently_atTop.mpr ?_⟩
  intro a
  let n := max a n₀
  obtain ⟨K,hK,hD⟩ := hall n (le_max_right a n₀)
  have hh : (Erdos18.practicalH n.factorial : ℝ) ≤ (K : ℝ) := by
    exact_mod_cast uniform_bound hD
  exact ⟨n.factorial, (le_max_left a n₀).trans (Nat.self_le_factorial n),
    Erdos18.factorial_isPractical n, hh.trans_lt hK⟩

end OMA.R_Erdos18_erdos_18a_R1
