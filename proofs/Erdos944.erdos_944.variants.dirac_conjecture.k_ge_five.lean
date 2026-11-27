import FormalConjectures.ErdosProblems.«944»

/-!
# Vertex-critical graphs without critical edges

The two circulants are the complements of Jensen's templates in the form given by
Skottova and Steiner, [*Critical edge sets in vertex-critical graphs*]
(https://arxiv.org/abs/2508.08703), Section 4 and
Appendix A. We use the parameters `m = q = 2` and rescale the residues.

Each of the two finite checks bounds the clique number of the common neighborhood
of two distinct offsets inside the neighborhood of zero. Translating an
additional anchor vertex to zero turns this into a bound on any color class after
a single edge deletion. The explicit clique tilings give the colorings after
deleting a vertex.
-/

namespace DiracTiling

private def oddShift (i : ℕ) (j : Fin 4) : ℤ :=
  if i % 2 = 0 then ![0, 1, 4, 5] j else ![-2, -1, 2, 3] j

private def evenShift (i : ℕ) (j : Fin 8) : ℤ :=
  if i % 2 = 0 then ![-4, -2, 1, 3, 4, 6, 9, 11] j else ![-3, -1, 0, 2, 5, 7, 8, 10] j

private def adjust (N : ℕ) (x : ℤ) : ℤ :=
  if x < 0 then x + N else if (N : ℤ) ≤ x then x - N else x

private theorem adjust_cast (N : ℕ) (x : ℤ) :
    (adjust N x : ZMod N) = (x : ZMod N) := by
  by_cases h : x < 0
  · simp [adjust, h, Int.cast_add]
  · by_cases h' : (N : ℤ) ≤ x <;> simp [adjust, h, h', Int.cast_sub]

private theorem odd_bounds (s : ℕ) (hs : s % 2 = 0) (i : Fin s) (j : Fin 4) :
    0 ≤ 4 * (i.val : ℤ) + oddShift i.val j ∧
      4 * (i.val : ℤ) + oddShift i.val j < 4 * (s : ℤ) := by
  have hi := i.isLt
  unfold oddShift
  split <;> fin_cases j <;> norm_num <;> omega

set_option maxHeartbeats 0 in
private theorem odd_inj (s : ℕ) (i i' : Fin s) (j j' : Fin 4)
    (h : 4 * (i.val : ℤ) + oddShift i.val j =
      4 * (i'.val : ℤ) + oddShift i'.val j') : i = i' ∧ j = j' := by
  have hi := i.isLt
  have hi' := i'.isLt
  fin_cases j <;> fin_cases j' <;>
    unfold oddShift at h <;> split at h <;> split at h <;>
      norm_num at h <;> constructor <;> apply Fin.ext <;> norm_num <;> omega

private theorem even_bounds (s : ℕ) (hs : s % 2 = 1) (hlarge : 5 ≤ s)
    (i : Fin s) (j : Fin 8) :
    0 ≤ adjust (8 * s + 1) (8 * (i.val : ℤ) + evenShift i.val j) ∧
       adjust (8 * s + 1) (8 * (i.val : ℤ) + evenShift i.val j) < 8 * (s : ℤ) := by
  have hi := i.isLt
  unfold evenShift
  split <;> fin_cases j <;> norm_num [adjust] <;> split <;> (try split) <;> omega

private theorem adjust_eq_or (N : ℕ) (x y : ℤ)
    (hx : x - y < 2 * (N : ℤ)) (hy : y - x < 2 * (N : ℤ))
    (h : adjust N x = adjust N y) :
    x = y ∨ x = y + N ∨ y = x + N := by
  unfold adjust at h
  (repeat' split at h) <;> omega

private theorem even_shift_bounds (i : ℕ) (j : Fin 8) :
    -4 ≤ evenShift i j ∧ evenShift i j ≤ 11 := by
  unfold evenShift
  split <;> fin_cases j <;> norm_num

private theorem even_shift_no_nine (j j' : Fin 8) :
    evenShift 0 j - evenShift 0 j' ≠ 9 := by
  revert j j'
  decide +kernel

private theorem even_no_wrap (s : ℕ) (hs : s % 2 = 1) (i i' : Fin s) (j j' : Fin 8)
    (h : 8 * (i.val : ℤ) + evenShift i.val j =
      8 * (i'.val : ℤ) + evenShift i'.val j' + (8 * (s : ℤ) + 1)) : False := by
  obtain ⟨h₁, h₂⟩ := even_shift_bounds i.val j
  obtain ⟨h₃, h₄⟩ := even_shift_bounds i'.val j'
  have hi := i.isLt
  have hi' := i'.isLt
  have hi0 : i.val + 1 = s := by omega
  have hi'0 : i'.val = 0 := by omega
  have hpar : i.val % 2 = 0 := by omega
  have hshift : evenShift i.val j = evenShift 0 j := by simp [evenShift, hpar]
  rw [hshift, hi'0] at h
  exact even_shift_no_nine j j' (by omega)

private def residue (p : Fin 2 × Fin 8) : ℤ :=
  (8 * (p.1.val : ℤ) + evenShift p.1.val p.2) % 16

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem residue_injective :
    ∀ p q : Fin 2 × Fin 8, residue p = residue q → p = q := by decide +kernel

private theorem even_inj (s : ℕ) (hs : s % 2 = 1)
    (i i' : Fin s) (j j' : Fin 8)
    (h : adjust (8 * s + 1) (8 * (i.val : ℤ) + evenShift i.val j) =
      adjust (8 * s + 1) (8 * (i'.val : ℤ) + evenShift i'.val j')) :
    i = i' ∧ j = j' := by
  have hi := i.isLt
  have hi' := i'.isLt
  obtain ⟨h₁, h₂⟩ := even_shift_bounds i.val j
  obtain ⟨h₃, h₄⟩ := even_shift_bounds i'.val j'
  rcases adjust_eq_or _ _ _ (by omega) (by omega) h with hEq | hDiff | hDiff
  · let p : Fin 2 := ⟨i.val % 2, Nat.mod_lt _ (by omega)⟩
    let q : Fin 2 := ⟨i'.val % 2, Nat.mod_lt _ (by omega)⟩
    have hp : evenShift i.val j = evenShift p.val j := by simp [evenShift, p ]
    have hq : evenShift i'.val j' = evenShift q.val j' := by simp [evenShift, q ]
    have hpq : residue (p,j) = residue (q,j') := by
      simp only [residue, p, q]
      rw [← hp, ← hq]
      omega
    have heq := residue_injective _ _ hpq
    obtain ⟨hpq', hj⟩ := Prod.mk.inj heq
    subst j'
    have hs' : evenShift i.val j = evenShift i'.val j := by
      rw [hp, hq, hpq']
    exact ⟨Fin.ext (by omega), rfl⟩
  · exact (even_no_wrap s hs i i' j j' (by exact_mod_cast hDiff)).elim
  · exact (even_no_wrap s hs i' i j' j (by exact_mod_cast hDiff)).elim

end DiracTiling

namespace DiracCirculant

private def oddDistances : List ℕ := [1, 3, 4, 5]

private def evenDistances : List ℕ := [1, 2, 3, 5, 6, 7, 8, 9, 10, 11, 13, 15]

private def offsets (D : List ℕ) : List ℤ :=
  D.flatMap fun d => [-(d : ℤ), d]

private def near (D : List ℕ) (N : ℕ) (a b : ℤ) : Bool :=
  (offsets D).any fun d => (a - b - d) % (N : ℤ) == 0

private def cliqueBound (adj : ℤ → ℤ → Bool) : ℕ → List ℤ → ℕ
  | 0, _ => 0
  | _, [] => 0
  | fuel + 1, a :: l =>
    max (cliqueBound adj fuel l) (1 + cliqueBound adj fuel (l.filter (adj a)))

private theorem card_le_cliqueBound (adj : ℤ → ℤ → Bool) (fuel : ℕ) (l : List ℤ)
    (hfuel : l.length ≤ fuel) (S : Finset ℤ) (hS : ∀ x ∈ S, x ∈ l)
    (hClique : (S : Set ℤ).Pairwise (fun x y => adj x y = true)) :
    S.card ≤ cliqueBound adj fuel l := by
  induction fuel generalizing l S with
  | zero =>
    have hl : l = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hfuel)
    subst l
    have hzero : S.card = 0 := Finset.card_eq_zero.mpr
      (Finset.eq_empty_iff_forall_notMem.mpr fun x hx => List.not_mem_nil (hS x hx))
    simp [hzero]
  | succ fuel ih =>
    cases l with
    | nil =>
      have hzero : S.card = 0 := Finset.card_eq_zero.mpr
        (Finset.eq_empty_iff_forall_notMem.mpr fun x hx => List.not_mem_nil (hS x hx))
      simp [hzero]
    | cons a l =>
      rw [cliqueBound]
      have hf : l.length ≤ fuel := by simpa using hfuel
      by_cases ha : a ∈ S
      · let T := S.erase a
        have ht : T.card ≤ cliqueBound adj fuel (l.filter (adj a)) := by
          apply ih _ ((List.length_filter_le _ _).trans hf)
          · intro x hx
            have hx' := Finset.mem_erase.mp hx
            refine List.mem_filter.mpr ⟨?_, hClique ha hx'.2 hx'.1.symm⟩
            exact (List.mem_cons.mp (hS x hx'.2)).resolve_left hx'.1
          · exact hClique.mono (by
              intro x hx
              exact Finset.mem_of_mem_erase hx)
        have hc : T.card + 1 = S.card := Finset.card_erase_add_one ha
        exact le_max_of_le_right (by omega)
      · exact le_max_of_le_left (ih l hf S (by
          intro x hx
          exact (List.mem_cons.mp (hS x hx)).resolve_left (by
            intro h
            subst x
            contradiction)) hClique)

private def cert (D : List ℕ) (N lim : ℕ) : Bool :=
  let O := offsets D
  O.all fun a => O.all fun b =>
    a == b || decide (cliqueBound (near D N) O.length
      (O.filter fun x => near D N a x && near D N b x) ≤ lim)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem odd_certificate : cert oddDistances 17 1 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem even_certificate : cert evenDistances 41 5 = true := by decide +kernel

private theorem card_common_le (D : List ℕ) (N lim : ℕ) (hc : cert D N lim = true)
    (a b : ℤ) (ha : a ∈ offsets D) (hb : b ∈ offsets D) (hab : a ≠ b)
    (S : Finset ℤ)
    (hS : ∀ x ∈ S, x ∈ offsets D ∧ near D N a x = true ∧ near D N b x = true)
    (hClique : (S : Set ℤ).Pairwise (fun x y => near D N x y = true)) :
    S.card ≤ lim := by
  simp only [cert, List.all_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
  apply le_trans (card_le_cliqueBound (near D N) _ _ (List.length_filter_le _ _) S ?_ hClique) ((hc a ha b hb).resolve_left hab)
  intro x hx
  obtain ⟨h₁, h₂, h₃⟩ := hS x hx
  simpa [h₂, h₃] using h₁


private theorem offsets_neg (D : List ℕ) {d : ℤ} (hd : d ∈ offsets D) :
    -d ∈ offsets D := by
  simp only [offsets, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hd ⊢
  obtain ⟨i, hi, h | h⟩ := hd
  · exact ⟨i, hi, Or.inr (by simp [h])⟩
  · exact ⟨i, hi, Or.inl (by simp [h])⟩

private def graph (D : List ℕ) (N : ℕ) : SimpleGraph (ZMod N) where
  Adj a b := a ≠ b ∧ ∃ d ∈ offsets D, (d : ZMod N) = a - b
  symm := ⟨by
    intro a b h
    obtain ⟨hne, d, hd, he⟩ := h
    refine ⟨hne.symm, -d, offsets_neg D hd, ?_⟩
    rw [Int.cast_neg, he, neg_sub]⟩
  loopless := ⟨fun a h => h.1 rfl⟩

private theorem graph_translate (D : List ℕ) (N : ℕ) (x y c : ZMod N) :
    (graph D N).Adj (x + c) (y + c) ↔ (graph D N).Adj x y := by
  have hne : x + c ≠ y + c ↔ x ≠ y := not_congr (add_left_inj c)
  simp only [graph, hne, add_sub_add_right_eq_sub]

private theorem local_near (D : List ℕ) (N M R : ℕ)
    (hD : ∀ a ∈ offsets D, a.natAbs ≤ R) (hN : N = M ∨ 3 * R < N)
    {a b : ℤ} (ha : a ∈ offsets D) (hb : b ∈ offsets D)
    (h : ∃ d ∈ offsets D, (d : ZMod N) = (a : ZMod N) - (b : ZMod N)) :
    near D M a b = true := by
  obtain ⟨d, hd, he⟩ := h
  simp only [near, List.any_eq_true, beq_iff_eq]
  refine ⟨d, hd, ?_⟩
  have hdiv : (N : ℤ) ∣ a - b - d := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1
    rw [Int.cast_sub, Int.cast_sub, he, sub_self]
  rcases hN with rfl | hN
  · exact Int.emod_eq_zero_of_dvd hdiv
  · have ha' := hD a ha
    have hb' := hD b hb
    have hd' := hD d hd
    have hsmall : (a - b - d).natAbs < (N : ℤ).natAbs := by
      have h₁ := Int.natAbs_sub_le a b
      have h₂ := Int.natAbs_sub_le (a - b) d
      simp only [Int.natAbs_natCast]
      omega
    rw [Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdiv hsmall, Int.zero_emod]

private theorem card_shared (D : List ℕ) (N M R lim : ℕ)
    (hD : ∀ a ∈ offsets D, a.natAbs ≤ R) (hN : N = M ∨ 3 * R < N)
    (hc : cert D M lim = true) (u v w : ZMod N) (huv : u ≠ v)
    (hu : (graph D N).Adj u w) (hv : (graph D N).Adj v w) (S : Finset (ZMod N))
    (hS : ∀ x ∈ S, (graph D N).Adj x w ∧ (graph D N).Adj u x ∧ (graph D N).Adj v x)
    (hClique : (S : Set (ZMod N)).Pairwise (graph D N).Adj) :
    S.card ≤ lim := by
  classical
  obtain ⟨_, a, ha, hcasta⟩ := hu
  obtain ⟨_, b, hb, hcastb⟩ := hv
  have hab : a ≠ b := by
    intro h
    subst b
    apply huv
    exact sub_left_inj.mp (hcasta.symm.trans hcastb)
  let f (x : ZMod N) : ℤ := if hx : x ∈ S then ((hS x hx).1.2).choose else 0
  have hf (x : ZMod N) (hx : x ∈ S) : f x ∈ offsets D ∧ (f x : ZMod N) = x - w := by
    simpa [f, hx] using ((hS x hx).1.2).choose_spec
  have hfInj : Set.InjOn f ↑S := by
    intro x hx y hy h
    apply sub_left_inj.mp
    rw [← (hf x hx).2, ← (hf y hy).2, h]
  have htransfer {x y : ZMod N} {p q : ℤ}
      (hp : p ∈ offsets D) (hq : q ∈ offsets D)
      (hpc : (p : ZMod N) = x - w) (hqc : (q : ZMod N) = y - w)
      (hadj : (graph D N).Adj x y) : near D M p q = true := by
    obtain ⟨_, d, hd, he⟩ := hadj
    apply local_near D N M R hD hN hp hq
    refine ⟨d, hd, ?_⟩
    rw [hpc, hqc, he]
    abel
  rw [← Finset.card_image_of_injOn hfInj]
  apply card_common_le D M lim hc a b ha hb hab
  · intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hfx, hfxc⟩ := hf x hx
    exact ⟨hfx, htransfer ha hfx hcasta hfxc (hS x hx).2.1,
      htransfer hb hfx hcastb hfxc (hS x hx).2.2⟩
  · intro z hz z' hz' hne
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz'
    obtain ⟨hfx, hfxc⟩ := hf x hx
    obtain ⟨hfy, hfyc⟩ := hf y hy
    exact htransfer hfx hfy hfxc hfyc (hClique hx hy (ne_of_apply_ne f hne))

private theorem offsets_odd_small : ∀ a ∈ offsets oddDistances, a.natAbs ≤ 5 := by
  simp [offsets, oddDistances]

private theorem offsets_even_small : ∀ a ∈ offsets evenDistances, a.natAbs ≤ 15 := by
  simp [offsets, evenDistances]

private theorem robust (D : List ℕ) (N M R lim : ℕ)
    (hD : ∀ a ∈ offsets D, a.natAbs ≤ R) (hN : N = M ∨ 3 * R < N)
    (hc : cert D M lim = true) (e : Sym2 (ZMod N)) (S : Finset (ZMod N))
    (hClique : (S : Set (ZMod N)).Pairwise (fun x y => (graph D N).Adj x y ∨ s(x,y) = e)) :
    S.card ≤ lim + 3 := by
  classical
  by_contra! hlarge
  have ht : ∃ u ∈ S, ∃ v ∈ S, u ≠ v ∧
      ∀ (x y : ZMod N), x ∈ S → y ∈ S → x ≠ y → s(x,y) ≠ s(u,v) → (graph D N).Adj x y := by
    by_cases h : ∃ u ∈ S, ∃ v ∈ S, u ≠ v ∧ ¬(graph D N).Adj u v
    · obtain ⟨u, hu, v, hv, huv, hn⟩ := h
      have he := (hClique hu hv huv).resolve_left hn
      exact ⟨u, hu, v, hv, huv, fun x y hx hy hxy hne =>
        (hClique hx hy hxy).resolve_right (fun h => hne (h.trans he.symm))⟩
    · obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp (by omega : 1 < S.card)
      push Not at h
      exact ⟨u, hu, v, hv, huv, fun x y hx hy hxy _ => h x hx y hy hxy⟩
  obtain ⟨u, hu, v, hv, huv, hgood⟩ := ht
  let T := (S.erase u).erase v
  have hT : T.card + 2 = S.card := by
    have h₁ := Finset.card_erase_add_one hu
    have h₂ := Finset.card_erase_add_one (Finset.mem_erase.mpr ⟨huv.symm, hv⟩)
    dsimp [T]
    omega
  obtain ⟨w, hw⟩ := Finset.card_pos.mp (by omega : 0 < T.card)
  let P := T.erase w
  have hp := Finset.card_erase_add_one hw
  have memT (x : ZMod N) (hx : x ∈ T) : x ∈ S ∧ x ≠ u ∧ x ≠ v := by
    obtain ⟨hxv, h⟩ := Finset.mem_erase.mp hx
    obtain ⟨hxu, hxs⟩ := Finset.mem_erase.mp h
    exact ⟨hxs, hxu, hxv⟩
  have hadj (x y : ZMod N) (hx : x ∈ T) (hy : y ∈ S) (hne : x ≠ y) :
      (graph D N).Adj x y := by
    obtain ⟨hxs, hxu, hxv⟩ := memT x hx
    apply hgood x y hxs hy hne
    intro h
    rcases (Sym2.mk_eq_mk_iff (p := (x,y)) (q := (u,v))).mp h with h | h
    · exact hxu (congrArg Prod.fst h)
    · exact hxv (congrArg Prod.fst h)
  have hwS := (memT w hw).1
  have hbound := card_shared D N M R lim hD hN hc u v w huv
    (hadj w u hw hu (memT w hw).2.1).symm
    (hadj w v hw hv (memT w hw).2.2).symm P
    (by
      intro x hx
      obtain ⟨hxw, hxT⟩ := Finset.mem_erase.mp hx
      obtain ⟨_, hxu, hxv⟩ := memT x hxT
      exact ⟨hadj x w hxT hwS hxw, (hadj x u hxT hu hxu).symm,
        (hadj x v hxT hv hxv).symm⟩)
    (by
      intro x hx y hy hne
      exact hadj x y (Finset.mem_of_mem_erase hx) (memT y (Finset.mem_of_mem_erase hy)).1 hne)
  dsimp [P] at hbound
  omega

private theorem robust_odd (s : ℕ) (hs : 4 ≤ s) (e : Sym2 (ZMod (4 * s + 1)))
    (S : Finset (ZMod (4 * s + 1)))
    (hClique : (S : Set (ZMod (4 * s + 1))).Pairwise (fun x y =>
      (graph oddDistances (4 * s + 1)).Adj x y ∨ s(x,y) = e)) : S.card ≤ 4 :=
  robust _ _ 17 5 1 offsets_odd_small (Or.inr (by omega)) odd_certificate e S hClique

private theorem robust_even (s : ℕ) (hs : 5 ≤ s) (hparity : s % 2 = 1)
    (e : Sym2 (ZMod (8 * s + 1))) (S : Finset (ZMod (8 * s + 1)))
    (hClique : (S : Set (ZMod (8 * s + 1))).Pairwise (fun x y =>
      (graph evenDistances (8 * s + 1)).Adj x y ∨ s(x,y) = e)) : S.card ≤ 8 :=
  robust _ _ 41 15 5 offsets_even_small (by omega) even_certificate e S hClique

private theorem odd_shift_diff (i : ℕ) (j j' : Fin 4) (h : j ≠ j') :
    DiracTiling.oddShift i j - DiracTiling.oddShift i j' ∈ offsets oddDistances := by
  unfold DiracTiling.oddShift
  split <;> revert j j' <;> decide +kernel

private theorem even_shift_diff (i : ℕ) (j j' : Fin 8) (h : j ≠ j') :
    DiracTiling.evenShift i j - DiracTiling.evenShift i j' ∈ offsets evenDistances := by
  unfold DiracTiling.evenShift
  split <;> revert j j' <;> decide +kernel

private theorem base_coloring (D : List ℕ) (a s : ℕ)
    (pos : Fin s × Fin a → ℤ) (sh : ℕ → Fin a → ℤ)
    (hbound : ∀ p, 0 ≤ pos p ∧ pos p < (a * s : ℕ))
    (hinj : Function.Injective pos)
    (hcast : ∀ i : Fin s, ∀ j : Fin a, (pos (i,j) : ZMod (a*s+1)) =
      ((a : ℤ) * i.val + sh i.val j : ℤ))
    (hdiff : ∀ i j j', j ≠ j' → sh i j - sh i j' ∈ offsets D) :
    ∃ c : {x : ZMod (a*s+1) // x ≠ -1} → Fin s,
      ∀ x y, x ≠ y → c x = c y → (graph D (a*s+1)).Adj x.val y.val := by
  classical
  let I := {x : ZMod (a*s+1) // x ≠ -1}
  have hval (p : Fin s × Fin a) :
      ((pos p : ZMod (a*s+1)).val : ℤ) = pos p := by
    rw [ZMod.val_intCast, Int.emod_eq_of_lt (hbound p).1]
    exact (hbound p).2.trans (by omega)
  let f (p : Fin s × Fin a) : I := ⟨(pos p : ZMod (a*s+1)), by
    intro h
    have hneg := ZMod.val_neg_one (a*s)
    have hv := hval p
    rw [h, hneg] at hv
    exact (hbound p).2.ne hv.symm⟩
  have hf : Function.Injective f := by
    intro p q h
    apply hinj
    have h' := congrArg (fun x : I => (x.val.val : ℤ)) h
    exact (hval p).symm.trans (h'.trans (hval q))
  have hcard : Fintype.card (Fin s × Fin a) = Fintype.card I := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
    change s * a = Fintype.card {x : ZMod (a*s+1) // ¬x = -1}
    rw [Fintype.card_subtype_compl (fun x : ZMod (a*s+1) => x = -1), ZMod.card]
    simp [Nat.mul_comm]
  let e : (Fin s × Fin a) ≃ I :=
    Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hf, hcard⟩)
  refine ⟨fun x => (e.symm x).1, ?_⟩
  intro x y hxy hc
  change (e.symm x).1 = (e.symm y).1 at hc
  have hx : (pos (e.symm x) : ZMod (a*s+1)) = x.val :=
    congrArg Subtype.val (e.apply_symm_apply x)
  have hy : (pos (e.symm y) : ZMod (a*s+1)) = y.val :=
    congrArg Subtype.val (e.apply_symm_apply y)
  have hd : (e.symm x).2 ≠ (e.symm y).2 := by
    intro h
    exact hxy (e.symm.injective (Prod.ext hc h))
  refine ⟨fun h => hxy (Subtype.ext h), _, hdiff (e.symm x).1 _ _ hd, ?_⟩
  rw [← hx, ← hy]
  change _ = (pos ((e.symm x).1,(e.symm x).2) : ZMod (a*s+1)) -
    (pos ((e.symm y).1,(e.symm y).2) : ZMod (a*s+1))
  rw [hcast, hcast, ← hc, Int.cast_sub, Int.cast_add, Int.cast_add]
  abel

private theorem odd_coloring (s : ℕ) (hs : s % 2 = 0) :
    ∃ c : {x : ZMod (4*s+1) // x ≠ -1} → Fin s,
      ∀ x y, x ≠ y → c x = c y → (graph oddDistances (4*s+1)).Adj x.val y.val := by
  apply base_coloring oddDistances 4 s
    (fun p => 4 * (p.1.val : ℤ) + DiracTiling.oddShift p.1.val p.2) DiracTiling.oddShift
  · intro p
    exact_mod_cast DiracTiling.odd_bounds s hs p.1 p.2
  · intro p q h
    obtain ⟨h₁,h₂⟩ := DiracTiling.odd_inj s p.1 q.1 p.2 q.2 h
    exact Prod.ext h₁ h₂
  · intros
    rfl
  · exact odd_shift_diff

private theorem even_coloring (s : ℕ) (hs : s % 2 = 1) (hl : 5 ≤ s) :
    ∃ c : {x : ZMod (8*s+1) // x ≠ -1} → Fin s,
      ∀ x y, x ≠ y → c x = c y → (graph evenDistances (8*s+1)).Adj x.val y.val := by
  apply base_coloring evenDistances 8 s
    (fun p => DiracTiling.adjust (8*s+1) (8 * (p.1.val : ℤ) + DiracTiling.evenShift p.1.val p.2))
    DiracTiling.evenShift
  · intro p
    exact_mod_cast DiracTiling.even_bounds s hs hl p.1 p.2
  · intro p q h
    obtain ⟨h₁,h₂⟩ := DiracTiling.even_inj s hs p.1 q.1 p.2 q.2 h
    exact Prod.ext h₁ h₂
  · intro i j
    exact DiracTiling.adjust_cast _ _
  · exact even_shift_diff

open Erdos944

private theorem assemble {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (a s : ℕ) (v₀ : V) (hV : Fintype.card V = a * s + 1)
    (hdel : ∀ v : V, ∃ c : {x : V // x ≠ v} → Fin s,
      ∀ x y, G.Adj x.val y.val → c x ≠ c y)
    (hcap : ∀ (e : Sym2 V) (S : Finset V),
      (S : Set V).Pairwise (fun x y => ¬G.Adj x y ∨ s(x,y) = e) → S.card ≤ a) :
    G.IsErdos944 (s+1) 1 := by
  classical
  have hn (e : Sym2 V) : ¬ (G.deleteEdges {e}).Colorable s := by
    rintro ⟨c⟩
    have hbound (i : Fin s) : (Finset.univ.filter (fun x : V => c x = i)).card ≤ a := by
      apply hcap e
      intro x hx y hy _
      have hx' := (Finset.mem_filter.mp hx).2
      have hy' := (Finset.mem_filter.mp hy).2
      by_cases hG : G.Adj x y
      · right
        by_contra hne
        have hAdj : (G.deleteEdges {e}).Adj x y :=
          SimpleGraph.deleteEdges_adj.mpr ⟨hG, hne⟩
        exact c.valid hAdj (hx'.trans hy'.symm)
      · exact Or.inl hG
    have hsum : Fintype.card V ≤ s * a := by
      calc
        Fintype.card V = ∑ i : Fin s, (Finset.univ.filter (fun x : V => c x = i)).card :=
          Finset.card_eq_sum_card_fiberwise (f := fun x => c x) (by simp)
        _ ≤ ∑ _i : Fin s, a := Finset.sum_le_sum (fun i _ => hbound i)
        _ = s * a := by simp
    rw [hV, Nat.mul_comm a s] at hsum
    omega
  have hc : G.Colorable (s+1) := by
    obtain ⟨c, hc⟩ := hdel v₀
    let g (x : V) : Fin (s+1) :=
      if hx : x = v₀ then Fin.last s else (c ⟨x,hx⟩).castSucc
    refine ⟨SimpleGraph.Coloring.mk g ?_⟩
    intro x y hxy
    by_cases hx : x = v₀ <;> by_cases hy : y = v₀
    · exact (hxy.ne (hx.trans hy.symm)).elim
    · rw [show g x = Fin.last s from dif_pos hx,
        show g y = (c ⟨y, hy⟩).castSucc from dif_neg hy]
      exact (Fin.castSucc_ne_last _).symm
    · simp [g, hx, hy]
    · simpa [g, hx, hy] using hc ⟨x,hx⟩ ⟨y,hy⟩ hxy
  have hχ : G.chromaticNumber = (s : ℕ∞) + 1 :=
    SimpleGraph.chromaticNumber_eq_iff_colorable_not_colorable.mpr
      ⟨hc, fun h => hn s(v₀,v₀) (h.mono_left (fun _ _ hAdj => (SimpleGraph.deleteEdges_adj.mp hAdj).1))⟩
  refine ⟨⟨by simpa using hχ, ?_⟩, ?_⟩
  · intro v
    obtain ⟨c, hc⟩ := hdel v
    let H := (⊤ : G.Subgraph).deleteVerts ({v} : Set V)
    have hv (x : H.verts) : x.val ≠ v := x.property.2
    have hcol : H.coe.Colorable s :=
      ⟨SimpleGraph.Coloring.mk (fun x => c ⟨x.val,hv x⟩) (by
        intro x y hxy
        exact hc _ _ (H.coe_adj_sub x y hxy))⟩
    change H.coe.chromaticNumber < (⊤ : G.Subgraph).coe.chromaticNumber
    have htop := SimpleGraph.chromaticNumber_mono_of_hom
      (SimpleGraph.Subgraph.topIso (G := G)).symm.toHom
    apply lt_of_lt_of_le _ htop
    rw [hχ]
    exact hcol.chromaticNumber_le.trans_lt (ENat.natCast_lt_add_one_iff.mpr le_rfl)
  · intro edges hcrit
    by_contra! hncard
    let _ : Nonempty (Sym2 V) := ⟨s(v₀,v₀)⟩
    obtain ⟨e, he⟩ := (Set.ncard_le_one_iff_subset_singleton (s := edges)).mp hncard
    have hlt : (G.deleteEdges edges).chromaticNumber < (s : ℕ∞) + 1 := hχ ▸ hcrit
    have hle : (G.deleteEdges edges).chromaticNumber ≤ (s : ℕ∞) := by
      exact (ENat.lt_add_one_iff (ENat.natCast_ne_top s)).mp hlt
    exact hn e ((SimpleGraph.chromaticNumber_le_iff_colorable.mp hle).mono_left
      (SimpleGraph.deleteEdges_anti he))

universe u

private theorem realize (D : List ℕ) (a s : ℕ)
    (ht : ∃ c : {x : ZMod (a*s+1) // x ≠ -1} → Fin s,
      ∀ x y, x ≠ y → c x = c y → (graph D (a*s+1)).Adj x.val y.val)
    (hrob : ∀ (e : Sym2 (ZMod (a*s+1))) (S : Finset (ZMod (a*s+1))),
      (S : Set (ZMod (a*s+1))).Pairwise (fun x y =>
        (graph D (a*s+1)).Adj x y ∨ s(x,y) = e) → S.card ≤ a) :
    ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 (s+1) 1 := by
  classical
  let V := ULift.{u} (ZMod (a*s+1))
  let enc : V ≃ ZMod (a*s+1) := Equiv.ulift
  let G := ((graph D (a*s+1))ᶜ).comap enc
  refine ⟨V, G, assemble G a s ⟨0⟩ ?_ ?_ ?_⟩
  · rw [Fintype.card_congr enc, ZMod.card]
  · intro v
    obtain ⟨c, hc⟩ := ht
    let off := -enc v - 1
    have ht' : enc v + off = -1 := by
      dsimp [off]
      abel
    let tr (x : {x : V // x ≠ v}) : {x : ZMod (a*s+1) // x ≠ -1} :=
      ⟨enc x.val + off, fun h => x.property (enc.injective ((add_left_inj off).mp (h.trans ht'.symm)))⟩
    refine ⟨fun x => c (tr x), ?_⟩
    intro x y hxy he
    obtain ⟨hne, hn⟩ := (SimpleGraph.compl_adj _ _ _).mp hxy
    have htne : tr x ≠ tr y := by
      intro h
      exact hne ((add_left_inj off).mp (congrArg Subtype.val h))
    exact hn ((graph_translate _ _ _ _ off).mp (hc _ _ htne he))
  · intro e S hS
    have hbound := hrob (e.map enc) (S.map enc.toEmbedding) (by
      intro x hx y hy hne
      obtain ⟨p,hp,rfl⟩ := Finset.mem_map.mp hx
      obtain ⟨q,hq,rfl⟩ := Finset.mem_map.mp hy
      have hpq : p ≠ q := ne_of_apply_ne enc hne
      rcases hS hp hq hpq with hn | he
      · left
        by_contra hAdj
        exact hn ((SimpleGraph.compl_adj _ _ _).mpr ⟨hne,hAdj⟩)
      · right
        exact congrArg (Sym2.map enc) he)
    simpa using hbound

theorem solution_aux (k : ℕ) (hk : 5 ≤ k) :
    ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1 := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  by_cases hs : s % 2 = 0
  · exact realize oddDistances 4 s (odd_coloring s hs) (robust_odd s (by omega))
  · exact realize evenDistances 8 s (even_coloring s (by omega) (by omega))
      (robust_even s (by omega) (by omega))

end DiracCirculant

theorem OMA.solution : type_of% @Erdos944.erdos_944.variants.dirac_conjecture.k_ge_five :=
  DiracCirculant.solution_aux