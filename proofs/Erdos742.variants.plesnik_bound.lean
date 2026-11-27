import FormalConjectures.ErdosProblems.«742»

/-!
# Proof of `Erdos742.variants.plesnik_bound`

A diameter-2-critical graph on `n` vertices has fewer than `3n(n-1)/8` edges. Equivalently it has
fewer than three times as many edges as non-edges. We prove this by double counting:

1. (`critical`) For every edge `uv`, either some non-neighbour `y` of `u` has `v` as its unique
   common neighbour with `u` (`Bd G u v`), or the same with `u` and `v` swapped, or `u` and `v` have
   no common neighbour. Otherwise `G - uv` still has diameter 2.
2. A dart `(u,v)` with `Bd G u v` is determined by its witness pair `(u,y)`, a non-adjacent pair with
   exactly one common neighbour (`bd_le_w`).
3. For an edge `uv` of the third kind only (`Ap`), charge the non-adjacent pairs `(u,y)` weight
   `1 + [v ~ y]`. Both orientations together carry total charge `2(n-2)` (`ap_F`).
4. Each ordered non-adjacent pair receives total charge at most `3n-7` (`charge`), so
   `2(n-2)|E| ≤ (3n-7)(n(n-1) - 2|E|)`, which gives `8|E| < 3n(n-1)` (`plesnik`).
-/

open SimpleGraph

namespace OMA742
variable {V : Type*}

lemma diam_eq_two_of (H : SimpleGraph V)
    (h2 : ∀ x y, x ≠ y → H.Adj x y ∨ ∃ w, H.Adj x w ∧ H.Adj w y)
    (hne : ∃ x y, x ≠ y ∧ ¬ H.Adj x y) : H.diam = 2 := by
  have hle : H.ediam ≤ 2 := by
    rw [ediam_le_iff]
    intro u v
    by_cases huv : u = v
    · subst huv; simp
    rcases h2 u v huv with h | ⟨w, h1, h2⟩
    · exact (edist_le (Walk.cons h Walk.nil)).trans (by simp)
    · exact (edist_le (Walk.cons h1 (Walk.cons h2 Walk.nil))).trans (by simp)
  obtain ⟨x, y, hxy, hnadj⟩ := hne
  have hge : 2 ≤ H.ediam := by
    refine le_trans ?_ (edist_le_ediam (u := x) (v := y))
    have h0 : H.edist x y ≠ 0 := by rwa [Ne, edist_eq_zero_iff]
    have h1 : H.edist x y ≠ 1 := by rwa [Ne, edist_eq_one_iff_adj]
    generalize H.edist x y = e at h0 h1
    induction e using ENat.recTopCoe with
    | top => simp
    | coe e =>
      have : e ≠ 0 := by exact_mod_cast h0
      have : e ≠ 1 := by exact_mod_cast h1
      exact_mod_cast (show 2 ≤ e by omega)
  have he : H.ediam = 2 := le_antisymm hle hge
  have hnt : H.ediam ≠ ⊤ := by rw [he]; simp
  show H.ediam.toNat = 2
  rw [he]; rfl

lemma common_of_diam (H : SimpleGraph V) (hd : H.diam = 2) (x y : V) (hxy : x ≠ y)
    (hn : ¬ H.Adj x y) : ∃ w, H.Adj x w ∧ H.Adj w y := by
  have hnt : H.ediam ≠ ⊤ := ediam_ne_top_of_diam_ne_zero (by omega)
  have he : H.ediam = 2 := by
    have h1 : ((H.ediam.toNat : ℕ) : ℕ∞) = H.ediam := ENat.natCast_toNat hnt
    have h2 : H.ediam.toNat = 2 := hd
    rw [← h1, h2]; rfl
  have hle : H.edist x y ≤ 2 := he ▸ edist_le_ediam
  have hr : H.Reachable x y := edist_ne_top_iff_reachable.mp (ne_top_of_le_ne_top (by simp) hle)
  obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_edist
  rw [← hp] at hle
  have hl : p.length ≤ 2 := by exact_mod_cast hle
  match p, hl with
  | Walk.nil, _ => exact absurd rfl hxy
  | Walk.cons h Walk.nil, _ => exact absurd h hn
  | Walk.cons h (Walk.cons h' Walk.nil), _ => exact ⟨_, h, h'⟩
  | Walk.cons _ (Walk.cons _ (Walk.cons _ _)), hl => simp at hl

lemma exists_far (H : SimpleGraph V) (hd : H.diam = 2) : ∃ x y, x ≠ y ∧ ¬ H.Adj x y := by
  by_contra hc
  push Not at hc
  have : H.diam ≤ 1 := by
    have hle : H.ediam ≤ 1 := by
      rw [ediam_le_iff]
      intro u v
      by_cases huv : u = v
      · subst huv; simp
      exact (edist_le (Walk.cons (hc u v huv) Walk.nil)).trans (by simp)
    have hnt : H.ediam ≠ ⊤ := ne_top_of_le_ne_top (by simp) hle
    have h1 : ((H.ediam.toNat : ℕ) : ℕ∞) = H.ediam := ENat.natCast_toNat hnt
    have h3 : ((H.ediam.toNat : ℕ) : ℕ∞) ≤ 1 := h1 ▸ hle
    show H.ediam.toNat ≤ 1
    exact_mod_cast h3
  omega

/-- witness: `v` is the unique common neighbour of `u` and some non-neighbour `y`. -/
def Bd (G : SimpleGraph V) (u v : V) : Prop :=
  G.Adj u v ∧ ∃ y, y ≠ u ∧ ¬ G.Adj u y ∧ G.Adj v y ∧ ∀ w, G.Adj u w → G.Adj w y → w = v

lemma critical (G : SimpleGraph V) (hd : G.diam = 2) (u v : V) (huv : G.Adj u v)
    (hc : (G.deleteEdges {s(u, v)}).diam ≠ 2) :
    Bd G u v ∨ Bd G v u ∨ ∀ w, ¬ (G.Adj u w ∧ G.Adj w v) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hBu, hBv, ⟨w0, hw0u, hw0v⟩⟩ := hcon
  apply hc
  apply diam_eq_two_of
  · intro x y hxy
    simp only [deleteEdges_adj, Set.mem_singleton_iff]
    by_cases hA : G.Adj x y ∧ ¬ s(x, y) = s(u, v)
    · exact Or.inl hA
    right
    by_cases hadj : G.Adj x y
    · -- {x,y} = {u,v}
      have he : s(x, y) = s(u, v) := by tauto
      rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · refine ⟨w0, ⟨hw0u, ?_⟩, ⟨hw0v, ?_⟩⟩ <;> intro h <;> rcases Sym2.eq_iff.mp h with h | h <;>
          grind [SimpleGraph.irrefl]
      · refine ⟨w0, ⟨hw0v.symm, ?_⟩, ⟨hw0u.symm, ?_⟩⟩ <;> intro h <;>
          rcases Sym2.eq_iff.mp h with h | h <;> grind [SimpleGraph.irrefl]
    · obtain ⟨w1, hx1, h1y⟩ := common_of_diam G hd x y hxy hadj
      by_contra hno
      push Not at hno
      have key : ∀ w, G.Adj x w → G.Adj w y → s(x, w) = s(u, v) ∨ s(w, y) = s(u, v) := by
        intro w h1 h2
        by_contra h
        push Not at h
        exact absurd (hno w ⟨h1, h.1⟩) (by tauto)
      rcases key w1 hx1 h1y with h | h <;> rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · subst h1 h2
        apply hBu
        refine ⟨huv, y, (Ne.symm hxy), hadj, h1y, fun w hw1 hw2 => ?_⟩
        rcases key w hw1 hw2 with h | h <;> rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
          grind [SimpleGraph.irrefl]
      · subst h1 h2
        apply hBv
        refine ⟨huv.symm, y, (Ne.symm hxy), hadj, h1y, fun w hw1 hw2 => ?_⟩
        rcases key w hw1 hw2 with h | h <;> rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
          grind [SimpleGraph.irrefl]
      · subst h1 h2
        apply hBv
        refine ⟨huv.symm, x, hxy, fun h => hadj h.symm, hx1.symm, fun w hw1 hw2 => ?_⟩
        rcases key w hw2.symm hw1.symm with h | h <;>
          rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> grind [SimpleGraph.irrefl]
      · subst h1 h2
        apply hBu
        refine ⟨huv, x, hxy, fun h => hadj h.symm, hx1.symm, fun w hw1 hw2 => ?_⟩
        rcases key w hw2.symm hw1.symm with h | h <;>
          rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> grind [SimpleGraph.irrefl]
  · refine ⟨u, v, G.ne_of_adj huv, ?_⟩
    simp [deleteEdges_adj]


section count
variable [Fintype V] [DecidableEq V]

open Classical in
noncomputable def ind (p : Prop) : ℕ := if p then 1 else 0

lemma ind_le_one (p : Prop) : ind p ≤ 1 := by
  unfold ind; split_ifs <;> omega

lemma sum_ind (p : V → Prop) [DecidablePred p] :
    ∑ v, ind (p v) = (Finset.univ.filter p).card := by
  rw [Finset.card_filter]
  refine Finset.sum_congr rfl fun v _ => ?_
  by_cases h : p v <;> simp [ind, h]

lemma sum_ind_ne2 (a b : V) (hab : a ≠ b) :
    ∑ v, ind (v ≠ a ∧ v ≠ b) = Fintype.card V - 2 := by
  classical
  rw [sum_ind]
  have : Finset.univ.filter (fun v => v ≠ a ∧ v ≠ b) = (Finset.univ.erase a).erase b := by
    ext v; simp [and_comm]
  rw [this, Finset.card_erase_of_mem (by simp [Ne.symm hab]), Finset.card_erase_of_mem (by simp),
    Finset.card_univ]
  omega

lemma sum_ind_ne3 (a b c : V) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∑ v, ind (v ≠ a ∧ v ≠ b ∧ v ≠ c) = Fintype.card V - 3 := by
  classical
  rw [sum_ind]
  have : Finset.univ.filter (fun v => v ≠ a ∧ v ≠ b ∧ v ≠ c) =
      ((Finset.univ.erase a).erase b).erase c := by
    ext v; simp; tauto
  rw [this, Finset.card_erase_of_mem (by simp [Ne.symm hac, Ne.symm hbc]),
    Finset.card_erase_of_mem (by simp [Ne.symm hab]), Finset.card_erase_of_mem (by simp),
    Finset.card_univ]
  omega

variable (G : SimpleGraph V)

def P (u y : V) : Prop := y ≠ u ∧ ¬ G.Adj u y
def W (u y : V) : Prop := P G u y ∧ ∃ v, G.Adj u v ∧ G.Adj v y ∧ ∀ w, G.Adj u w → G.Adj w y → w = v
def Ap (u v : V) : Prop := G.Adj u v ∧ ¬ Bd G u v ∧ ¬ Bd G v u

noncomputable def F (u v : V) : ℕ := ∑ y, ind (P G u y) * (1 + ind (G.Adj v y))

lemma bd_le_w (u : V) : ∑ v, ind (Bd G u v) ≤ ∑ y, ind (W G u y) := by
  classical
  rw [sum_ind, sum_ind]
  have hex : ∀ v, Bd G u v → ∃ y, W G u y ∧ G.Adj v y ∧
      ∀ w, G.Adj u w → G.Adj w y → w = v := by
    rintro v ⟨huv, y, hyu, hny, hvy, huniq⟩
    exact ⟨y, ⟨⟨hyu, hny⟩, v, huv, hvy, huniq⟩, hvy, huniq⟩
  let f : V → V := fun v => if h : Bd G u v then (hex v h).choose else v
  apply Finset.card_le_card_of_injOn f
  · intro v hv
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hv ⊢
    simp only [f, dif_pos hv]
    exact (hex v hv).choose_spec.1
  · intro v hv v' hv' hff
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hv hv'
    simp only [f, dif_pos hv, dif_pos hv'] at hff
    have h1 := (hex v hv).choose_spec
    have h2 := (hex v' hv').choose_spec
    rw [← hff] at h2
    exact (h1.2.2 v' hv'.1 h2.2.1).symm


lemma ap_F (u v : V) (hap : Ap G u v) (hdisj : ∀ w, ¬ (G.Adj u w ∧ G.Adj w v)) :
    2 * (Fintype.card V - 2) ≤ F G u v + F G v u := by
  classical
  have huv := hap.1
  rw [← sum_ind_ne2 u v (G.ne_of_adj huv), Finset.mul_sum, F, F, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun y _ => ?_
  have hd := hdisj y
  have hd' : ¬ (G.Adj v y ∧ G.Adj u y) := fun h => hd ⟨h.2, h.1.symm⟩
  by_cases h1 : y = u
  · subst h1; simp [ind]
  by_cases h2 : y = v
  · subst h2; simp [ind]
  by_cases h3 : G.Adj u y <;> by_cases h4 : G.Adj v y <;>
    simp_all [ind, P, ne_comm]

lemma charge (u y : V) (hP : P G u y) (hn : 3 ≤ Fintype.card V) :
    2 * (Fintype.card V - 2) * ind (W G u y) + ∑ v, ind (Ap G u v) * (1 + ind (G.Adj v y)) ≤
      3 * Fintype.card V - 7 := by
  classical
  obtain ⟨hyu, hnadj⟩ := hP
  by_cases hW : W G u y
  · obtain ⟨_, v0, huv0, hv0y, huniq⟩ := hW
    have hle : ∑ v, ind (Ap G u v) * (1 + ind (G.Adj v y)) ≤
        ∑ v, ind (v ≠ u ∧ v ≠ y ∧ v ≠ v0) := by
      refine Finset.sum_le_sum fun v _ => ?_
      by_cases hap : Ap G u v
      · have huv := hap.1
        have hvy : ¬ G.Adj v y := by
          intro hvy
          have := huniq v huv hvy
          subst this
          exact hap.2.1 ⟨huv, y, hyu, hnadj, hvy, huniq⟩
        have h1 : v ≠ u := (G.ne_of_adj huv).symm
        have h2 : v ≠ y := fun h => hnadj (h ▸ huv)
        have h3 : v ≠ v0 := by
          rintro rfl; exact hvy hv0y
        simp [ind, hap, hvy, h1, h2, h3]
      · simp [ind, hap]
    rw [sum_ind_ne3 u y v0 hyu.symm (G.ne_of_adj huv0)
      (fun h => hnadj (h ▸ huv0))] at hle
    have : ind (W G u y) ≤ 1 := ind_le_one _
    have h2 : 2 * (Fintype.card V - 2) * ind (W G u y) ≤ 2 * (Fintype.card V - 2) := by
      calc _ ≤ 2 * (Fintype.card V - 2) * 1 := by gcongr
        _ = _ := by ring
    omega
  · have hle : ∑ v, ind (Ap G u v) * (1 + ind (G.Adj v y)) ≤ ∑ v, 2 * ind (v ≠ u ∧ v ≠ y) := by
      refine Finset.sum_le_sum fun v _ => ?_
      by_cases hap : Ap G u v
      · have huv := hap.1
        have h1 : v ≠ u := (G.ne_of_adj huv).symm
        have h2 : v ≠ y := fun h => hnadj (h ▸ huv)
        have := ind_le_one (G.Adj v y)
        simp only [ind, hap, h1, h2, if_true, ne_eq, not_false_eq_true, and_self] at this ⊢
        omega
      · simp [ind, hap]
    rw [← Finset.mul_sum, sum_ind_ne2 u y hyu.symm] at hle
    simp only [ind, hW, if_false, mul_zero, zero_add]
    simp only [ind] at hle
    omega

lemma ap_symm (u v : V) : Ap G u v ↔ Ap G v u := by
  unfold Ap; constructor <;> rintro ⟨h1, h2, h3⟩ <;> exact ⟨h1.symm, h3, h2⟩

lemma main_count (hG : G.diam = 2 ∧ ∀ e ∈ G.edgeSet, (G.deleteEdges {e}).diam ≠ 2)
    (hn : 3 ≤ Fintype.card V) :
    (Fintype.card V - 2) * ∑ u, ∑ v, ind (G.Adj u v) ≤
      (3 * Fintype.card V - 7) * ∑ u, ∑ y, ind (P G u y) := by
  classical
  set n := Fintype.card V
  have hcrit : ∀ u v, Ap G u v → ∀ w, ¬ (G.Adj u w ∧ G.Adj w v) := by
    intro u v hap
    rcases critical G hG.1 u v hap.1 (hG.2 _ hap.1) with h | h | h
    · exact absurd h hap.2.1
    · exact absurd h hap.2.2
    · exact h
  have hS2 : ∑ u, ∑ v, ind (G.Adj u v) ≤
      2 * ∑ u, ∑ v, ind (Bd G u v) + ∑ u, ∑ v, ind (Ap G u v) := by
    have hsw : ∑ u, ∑ v, ind (Bd G v u) = ∑ u, ∑ v, ind (Bd G u v) := Finset.sum_comm
    calc ∑ u, ∑ v, ind (G.Adj u v)
        ≤ ∑ u, ∑ v, (ind (Bd G u v) + ind (Bd G v u) + ind (Ap G u v)) := by
          refine Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => ?_
          by_cases h1 : Bd G u v
          · have := ind_le_one (G.Adj u v); simp only [ind, h1, if_true] at this ⊢; omega
          by_cases h2 : Bd G v u
          · have := ind_le_one (G.Adj u v); simp only [ind, h2, if_true] at this ⊢; omega
          by_cases h3 : G.Adj u v
          · have hap : Ap G u v := ⟨h3, h1, h2⟩
            have h := ind_le_one (G.Adj u v)
            have : ind (Ap G u v) = 1 := by simp [ind, hap]
            omega
          · simp [ind, h3]
      _ = _ := by
          simp only [Finset.sum_add_distrib, hsw]; ring
  have hS4 : ∑ u, ∑ v, ind (Bd G u v) ≤ ∑ u, ∑ y, ind (W G u y) :=
    Finset.sum_le_sum fun u _ => bd_le_w G u
  have hS6 : (n - 2) * ∑ u, ∑ v, ind (Ap G u v) ≤ ∑ u, ∑ v, ind (Ap G u v) * F G u v := by
    have hsym : ∑ u, ∑ v, ind (Ap G u v) * F G v u = ∑ u, ∑ v, ind (Ap G u v) * F G u v := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
      rw [ap_symm]
    have h2 : 2 * ((n - 2) * ∑ u, ∑ v, ind (Ap G u v)) ≤
        2 * ∑ u, ∑ v, ind (Ap G u v) * F G u v := by
      calc 2 * ((n - 2) * ∑ u, ∑ v, ind (Ap G u v))
          = ∑ u, ∑ v, ind (Ap G u v) * (2 * (n - 2)) := by
            simp only [Finset.mul_sum]
            refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
            ring
        _ ≤ ∑ u, ∑ v, ind (Ap G u v) * (F G u v + F G v u) := by
            refine Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => ?_
            by_cases hap : Ap G u v
            · exact Nat.mul_le_mul_left _ (ap_F G u v hap (hcrit u v hap))
            · simp [ind, hap]
        _ = 2 * ∑ u, ∑ v, ind (Ap G u v) * F G u v := by
            simp only [mul_add, Finset.sum_add_distrib, hsym]; ring
    omega
  have hS7 : ∑ u, ∑ v, ind (Ap G u v) * F G u v =
      ∑ u, ∑ y, ind (P G u y) * ∑ v, ind (Ap G u v) * (1 + ind (G.Adj v y)) := by
    refine Finset.sum_congr rfl fun u _ => ?_
    simp only [F, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun v _ => ?_
    ring
  have hWP : ∀ u y, ind (W G u y) = ind (P G u y) * ind (W G u y) := by
    intro u y
    by_cases h : W G u y
    · simp [ind, h, h.1]
    · simp [ind, h]
  calc (n - 2) * ∑ u, ∑ v, ind (G.Adj u v)
      ≤ (n - 2) * (2 * ∑ u, ∑ v, ind (Bd G u v) + ∑ u, ∑ v, ind (Ap G u v)) := by gcongr
    _ ≤ 2 * (n - 2) * ∑ u, ∑ y, ind (W G u y) + ∑ u, ∑ v, ind (Ap G u v) * F G u v := by
      have := Nat.mul_le_mul_left (2 * (n - 2)) hS4
      nlinarith
    _ = ∑ u, ∑ y, ind (P G u y) * (2 * (n - 2) * ind (W G u y) +
          ∑ v, ind (Ap G u v) * (1 + ind (G.Adj v y))) := by
      rw [hS7, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun y _ => ?_
      conv_lhs => rw [hWP u y]
      ring
    _ ≤ ∑ u, ∑ y, ind (P G u y) * (3 * n - 7) := by
      refine Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun y _ => ?_
      by_cases hP : P G u y
      · exact Nat.mul_le_mul_left _ (charge G u y hP hn)
      · simp [ind, hP]
    _ = (3 * n - 7) * ∑ u, ∑ y, ind (P G u y) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      ring


lemma sum_adj [DecidableRel G.Adj] : ∑ u, ∑ v, ind (G.Adj u v) = 2 * G.edgeFinset.card := by
  rw [← sum_degrees_eq_twice_card_edges]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [sum_ind, ← card_neighborFinset_eq_degree, neighborFinset_eq_filter]

lemma sum_P_add [DecidableRel G.Adj] :
    ∑ u, ∑ y, ind (P G u y) + 2 * G.edgeFinset.card =
      Fintype.card V * (Fintype.card V - 1) := by
  classical
  rw [← sum_adj, ← Finset.sum_add_distrib]
  have : ∀ u : V, ∑ y, ind (P G u y) + ∑ y, ind (G.Adj u y) = Fintype.card V - 1 := by
    intro u
    rw [← Finset.sum_add_distrib]
    have h1 : ∀ y, ind (P G u y) + ind (G.Adj u y) = ind (y ≠ u) := by
      intro y
      by_cases hy : y = u
      · subst hy; simp [ind, P]
      · by_cases ha : G.Adj u y <;> simp [ind, P, hy, ha]
    simp only [h1]
    rw [sum_ind]
    have : Finset.univ.filter (fun y => y ≠ u) = Finset.univ.erase u := by ext; simp
    rw [this, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
  simp only [this, Finset.sum_const, Finset.card_univ, smul_eq_mul]

lemma three_le (hd : G.diam = 2) : 3 ≤ Fintype.card V := by
  classical
  obtain ⟨x, y, hxy, hn⟩ := exists_far G hd
  obtain ⟨w, hxw, hwy⟩ := common_of_diam G hd x y hxy hn
  have hxw' := G.ne_of_adj hxw
  have hwy' := G.ne_of_adj hwy
  have : ({x, y, w} : Finset V).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hxy, hxw']),
      Finset.card_pair (Ne.symm hwy')]
  rw [← this]
  exact Finset.card_le_univ _

theorem plesnik [DecidableRel G.Adj]
    (hG : G.diam = 2 ∧ ∀ e ∈ G.edgeSet, (G.deleteEdges {e}).diam ≠ 2) :
    (G.edgeFinset.card : ℝ) < 3 * (Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1) / 8 := by
  have hn := three_le G hG.1
  have hm := main_count G hG hn
  rw [sum_adj] at hm
  have hs := sum_P_add G
  set E := G.edgeFinset.card
  set N := ∑ u, ∑ y, ind (P G u y)
  set n := Fintype.card V
  have hmR : ((n : ℝ) - 2) * (2 * E) ≤ (3 * n - 7) * N := by
    have h1 : ((n - 2 : ℕ) : ℝ) = n - 2 := by rw [Nat.cast_sub (by omega)]; push_cast; ring
    have h2 : ((3 * n - 7 : ℕ) : ℝ) = 3 * n - 7 := by rw [Nat.cast_sub (by omega)]; push_cast; ring
    have := (Nat.cast_le (α := ℝ)).mpr hm
    push_cast at this
    rw [h1, h2] at this
    exact this
  have hsR : (N : ℝ) + 2 * E = n * (n - 1) := by
    have := congrArg (fun k : ℕ => (k : ℝ)) hs
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at this
    rw [this, Nat.cast_sub (by omega)]; push_cast; ring
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hNE : (N : ℝ) = n * (n - 1) - 2 * E := by linarith
  rw [hNE] at hmR
  have hpos : (0 : ℝ) < n * (n - 1) := by nlinarith
  nlinarith

end count

end OMA742

theorem OMA.solution : type_of% @Erdos742.variants.plesnik_bound := by
  intro V _ _ G _ hG
  exact OMA742.plesnik G hG
