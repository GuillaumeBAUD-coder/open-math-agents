import FormalConjectures.Wikipedia.GracefulLabeling

/-!
# A reduction of the Graceful Tree Conjecture through edge-width multiplicities

Credit goes to @ysanatomic.

The first step realizes the graceful divisibility counts along powers of six and the
two intermediate divisors at each level. The second asks for at most one missing
width while retaining those counts. With one collision, every protected divisor
divides the repeated width exactly when it divides the missing width. The third
step asks to repair this restricted collision. The root may move during both repairs.
-/

namespace OMA.R_GracefulLabeling_graceful_tree_conjecture_R2

open SimpleGraph

/-- Realize the divisibility counts at six-adic scales and their largest multiples,
with a prescribed vertex carrying the largest label. -/
def H1 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (T : SimpleGraph V) [DecidableRel T.Adj],
    T.IsTree → ∀ r : V,
    let m := T.edgeFinset.card
    let width (f : V → ℕ) : Sym2 V → ℕ :=
      Sym2.lift ⟨fun u v => Nat.dist (f u) (f v), fun u v => Nat.dist_comm (f u) (f v)⟩
    ∃ f : V → ℕ, Function.Injective f ∧ f r = m ∧ (∀ x, f x ≤ m) ∧
      ∀ j a : ℕ, a=1 ∨ a=2 ∨ a=3 ∨ a=6 ∨ a=m/6^j →
        (T.edgeFinset.filter (fun e => 6^j*a ∣ width f e)).card = m/(6^j*a)

/-- Retaining the divisibility counts, realize all widths, or realize every width
except b once with one extra copy of a. The multiset equation records all
multiplicities, including exclusion of widths outside the required interval. -/
def H2 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (T : SimpleGraph V) [DecidableRel T.Adj],
    T.IsTree →
    let m := T.edgeFinset.card
    let width (f : V → ℕ) : Sym2 V → ℕ :=
      Sym2.lift ⟨fun u v => Nat.dist (f u) (f v), fun u v => Nat.dist_comm (f u) (f v)⟩
    let counts (f : V → ℕ) := ∀ j a : ℕ, a=1 ∨ a=2 ∨ a=3 ∨ a=6 ∨ a=m/6^j →
      (T.edgeFinset.filter (fun e => 6^j*a ∣ width f e)).card = m/(6^j*a)
    (∃ f : V → ℕ, Function.Injective f ∧ (∀ x, f x ≤ m) ∧ counts f) →
    ∃ g : V → ℕ, Function.Injective g ∧ (∀ x, g x ≤ m) ∧ counts g ∧
      ((∀ d ∈ Finset.Icc 1 m, ∃ x y, T.Adj x y ∧ Nat.dist (g x) (g y) = d) ∨
        ∃ a ∈ Finset.Icc 1 m, ∃ b ∈ Finset.Icc 1 m, a ≠ b ∧
          T.edgeFinset.val.map (width g) + {b} = (Finset.Icc 1 m).val + {a})

/-- Repair a repeated width a and a missing width b with the same divisibility
pattern for every protected modulus. The new labeling may place its extrema anywhere. -/
def H3 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (T : SimpleGraph V) [DecidableRel T.Adj],
    T.IsTree →
    let m := T.edgeFinset.card
    let width (f : V → ℕ) : Sym2 V → ℕ :=
      Sym2.lift ⟨fun u v => Nat.dist (f u) (f v), fun u v => Nat.dist_comm (f u) (f v)⟩
    ∀ a ∈ Finset.Icc 1 m, ∀ b ∈ Finset.Icc 1 m, a ≠ b →
      (∀ j c : ℕ, c=1 ∨ c=2 ∨ c=3 ∨ c=6 ∨ c=m/6^j → (6^j*c ∣ a ↔ 6^j*c ∣ b)) →
      (∃ f : V → ℕ, Function.Injective f ∧ (∀ x, f x ≤ m) ∧
        T.edgeFinset.val.map (width f) + {b} = (Finset.Icc 1 m).val + {a}) →
      ∃ g : V → ℕ, Function.Injective g ∧ (∀ x, g x ≤ m) ∧
        ∀ d ∈ Finset.Icc 1 m, ∃ x y, T.Adj x y ∧ Nat.dist (g x) (g y) = d

/-- Count the multiples of d on both sides of the repaired multiset equation. -/
lemma divisibility_of_collision {E : Type*} (s : Finset E) (w : E → ℕ)
    {m a b d : ℕ} (hist : s.val.map w + {b} = (Finset.Icc 1 m).val + {a})
    (hc : (s.filter (fun e => d ∣ w e)).card = m/d) : d ∣ a ↔ d ∣ b := by
  have ref : ((Finset.Icc 1 m).filter (fun v => d ∣ v)).card = m/d := by
    rw [← Nat.card_multiples' m d]
    congr 1
    ext v
    simp only [Finset.mem_filter,Finset.mem_Icc,Finset.mem_range]
    omega
  have eq := congrArg (fun t : Multiset ℕ => (t.filter (fun v => d ∣ v)).card) hist
  simp only [Multiset.filter_add,Multiset.card_add,Multiset.filter_singleton,
    Multiset.filter_map,Multiset.card_map] at eq
  change (s.filter (fun e => d ∣ w e)).card + (if d ∣ b then ({b} : Multiset ℕ) else 0).card =
    ((Finset.Icc 1 m).filter (fun v => d ∣ v)).card + (if d ∣ a then ({a} : Multiset ℕ) else 0).card at eq
  rw [hc,ref] at eq
  by_cases ha : d ∣ a <;> by_cases hb : d ∣ b <;> simp_all

/-- A result for all finite graphs on small types applies in every universe. -/
lemma graceful_of_small_bounded
    (hsmall : ∀ {W : Type} [Fintype W] [DecidableEq W]
      (S : SimpleGraph W) [DecidableRel S.Adj], S.IsTree →
      let m := S.edgeFinset.card
      ∃ f : W → ℕ, Function.Injective f ∧ (∀ v, f v ≤ m) ∧
        ∀ d ∈ Finset.Icc 1 m, ∃ x y, S.Adj x y ∧ Nat.dist (f x) (f y) = d)
    {V : Type*} [Fintype V] [DecidableEq V] (T : SimpleGraph V)
    [DecidableRel T.Adj] (hT : T.IsTree) :
    let m := T.edgeFinset.card
    ∃ f : V → ℕ, Function.Injective f ∧ (∀ v, f v ≤ m) ∧
      T.edgeFinset.image (fun e =>
        e.lift ⟨fun u v => Int.natAbs ((f u : ℤ) - (f v : ℤ)),
                fun u v => by
                  show ((f u : ℤ) - f v).natAbs = ((f v : ℤ) - f u).natAbs
                  rw [← Int.natAbs_neg, neg_sub]⟩) = Finset.Icc 1 m := by
  intro m
  classical
  let e := Fintype.equivFin V
  let S := T.comap e.symm
  let i : S ≃g T := SimpleGraph.Iso.comap e.symm T
  have hS := i.isTree_iff.mpr hT
  have hcard : S.edgeFinset.card = m := i.card_edgeFinset_eq
  obtain ⟨f, hf, hb, hd⟩ := hsmall S hS
  refine ⟨f ∘ i.symm, hf.comp i.symm.injective, fun v => (hb _).trans_eq hcard,
    Eq.symm (Finset.eq_of_subset_of_card_le ?_ ?_)⟩
  · intro d hm
    obtain ⟨x, y, hxy, heq⟩ := hd d (by simpa [hcard] using hm)
    refine Finset.mem_image.mpr ⟨s(i x, i y), mem_edgeFinset.mpr (i.map_rel_iff.mpr hxy), ?_⟩
    change ((f (i.symm (i x)) : ℤ) - f (i.symm (i y))).natAbs = d
    simp only [RelIso.symm_apply_apply]
    dsimp [Nat.dist] at heq
    omega
  · simpa [m] using Finset.card_image_le (s := T.edgeFinset) (f := _)

theorem main : H1 → H2 → H3 → type_of% @GracefulLabeling.graceful_tree_conjecture := by
  intro h₁ h₂ h₃ V _ _ T _ hT
  apply graceful_of_small_bounded _ T hT
  intro W _ _ S _ hS
  obtain ⟨f,hi,_,hb,hc⟩ := h₁ S hS hS.connected.nonempty.some
  obtain ⟨g,gi,gb,gc,hg⟩ := h₂ S hS ⟨f,hi,hb,hc⟩
  rcases hg with hfull | ⟨a,ha,b,hb',hne,hh⟩
  · exact ⟨g,gi,gb,hfull⟩
  · refine h₃ S hS a ha b hb' hne ?_ ⟨g,gi,gb,hh⟩
    intro j c hc'
    exact divisibility_of_collision _ _ hh (gc j c hc')

end OMA.R_GracefulLabeling_graceful_tree_conjecture_R2
