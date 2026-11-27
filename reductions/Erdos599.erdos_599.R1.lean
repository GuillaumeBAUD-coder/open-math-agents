import FormalConjectures.ErdosProblems.«599»

/-!
Separate the maximal-wave construction from the linkability theorem. H1 uses the
essential endpoints of a maximal wave and deletes the interior of its roof.
H2 is linkability of an unhindered web, expressed with finite paths. A ray in a
wave contributes no terminal vertex, so removing rays preserves the separator
and preserves any omission from the source set. The support restrictions on
waves encode deleting incoming edges at the sources and outgoing edges at the
sinks. See Aharoni and Berger (2009), Lemmas 3.20 and 3.26 and Theorem 5.4.
-/

-- Credit: @dk8827

open SimpleGraph

namespace OMA.R_Erdos599_erdos_599_R1

def H1 : Prop :=
  ∀ (V : Type) (G : SimpleGraph V) (A B : Set V), Disjoint A B →
    ∃ (R : Set V) (S : Set R) (a : S → V) (p : ∀ s : S, G.Walk (a s) s.1.1),
      (∀ s, a s ∈ A) ∧
      (∀ (s : S) v, v ∈ (p s).support → v ∈ R → v = s.1.1) ∧
      (Pairwise fun s t => Disjoint {v | v ∈ (p s).support} {v | v ∈ (p t).support}) ∧
      (∀ u ∈ A, ∀ v ∈ B, ∀ w : G.Walk u v, w.IsPath →
        ∃ x ∈ w.support, x ∈ ((↑) : R → V) '' S) ∧
      let H := G.induce R
      let B' := ((↑) : R → V) ⁻¹' B
      ∀ (T : Set R) (b : T → R) (q : ∀ t : T, H.Walk (b t) t.1),
        (∀ t, b t ∈ S) →
        (∀ t, (q t).IsPath) →
        (∀ t, (∀ x ∈ (q t).support.tail, x ∉ S) ∧
              (∀ x ∈ (q t).support.dropLast, x ∉ B')) →
        (Pairwise fun t u => Disjoint {v | v ∈ (q t).support} {v | v ∈ (q u).support}) →
        (∀ u ∈ S, ∀ v ∈ B', ∀ w : H.Walk u v, w.IsPath →
          ∃ x ∈ w.support, x ∈ T) →
        ∀ x ∈ S, ∃ t, b t = x

def H2 : Prop :=
  ∀ (V : Type) (G : SimpleGraph V) (A B : Set V),
    (∀ (T : Set V) (b : T → V) (q : ∀ t : T, G.Walk (b t) t.1),
      (∀ t, b t ∈ A) →
      (∀ t, (q t).IsPath) →
      (∀ t, (∀ x ∈ (q t).support.tail, x ∉ A) ∧
            (∀ x ∈ (q t).support.dropLast, x ∉ B)) →
      (Pairwise fun t u => Disjoint {v | v ∈ (q t).support} {v | v ∈ (q u).support}) →
      (∀ u ∈ A, ∀ v ∈ B, ∀ w : G.Walk u v, w.IsPath →
        ∃ x ∈ w.support, x ∈ T) →
      ∀ x ∈ A, ∃ t, b t = x) →
    ∃ (b : A → V) (p : ∀ a : A, G.Walk a.1 (b a)),
      (∀ a, b a ∈ B) ∧
      (Pairwise fun s t => Disjoint {v | v ∈ (p s).support} {v | v ∈ (p t).support})

theorem main : H1 → H2 → type_of% @Erdos599.erdos_599 := by
  classical
  intro hW hL V G A B hAB _ _
  obtain ⟨R, S, a, p, ha, hpR, hp, hSep, hNo⟩ := hW V G A B hAB
  obtain ⟨b, q, hb, hq⟩ := hL R (G.induce R) S (((↑) : R → V) ⁻¹' B) hNo
  let incl : G.induce R →g G := (SimpleGraph.Embedding.induce R).toHom
  let q' (s : S) : G.Walk s.1.1 (b s).1 := (q s).map incl
  have mem_q' (s : S) (v : V) :
      v ∈ (q' s).support ↔ ∃ x : R, x ∈ (q s).support ∧ x.1 = v := by
    rw [show (q' s).support = (q s).support.map incl from Walk.support_map _ _, List.mem_map]
    rfl
  have qr (s : S) (v : V) (hv : v ∈ (q' s).support) : v ∈ R := by
    obtain ⟨x, _, rfl⟩ := (mem_q' s v).1 hv
    exact x.2
  have qDisj (s t : S) (hst : s ≠ t) :
      Disjoint {v | v ∈ (q' s).support} {v | v ∈ (q' t).support} := by
    refine Set.disjoint_left.2 (fun v hs ht => ?_)
    obtain ⟨x, hx, hxv⟩ := (mem_q' s v).1 hs
    obtain ⟨y, hy, hyv⟩ := (mem_q' t v).1 ht
    have he : x = y := Subtype.ext (hxv.trans hyv.symm)
    exact Set.disjoint_left.1 (hq hst) hx (he.symm ▸ hy)
  let K (s : S) : G.Walk (a s) (b s).1 := (p s).append (q' s)
  let P (s : S) : G.Walk (a s) (b s).1 := ((K s).toPath : G.Walk (a s) (b s).1)
  have valid (s : S) : (P s).IsPath := (K s).toPath.2
  have p_or_q (s : S) (v : V) (hv : v ∈ (P s).support) :
      v ∈ (p s).support ∨ v ∈ (q' s).support :=
    (Walk.mem_support_append_iff (p s) (q' s)).1 ((K s).support_toPath_subset_support hv)
  have mem_q_of_R (s : S) (v : V) (hv : v ∈ (P s).support) (hr : v ∈ R) :
      v ∈ (q' s).support := by
    rcases p_or_q s v hv with h | h
    · rw [hpR s v h hr]
      exact (q' s).start_mem_support
    · exact h
  let S₀ : Set V := ((↑) : R → V) '' S
  have mem_unique (s : S) (v : V) (hs : v ∈ S₀) (hv : v ∈ (P s).support) :
      v = s.1.1 := by
    obtain ⟨r, hr, rfl⟩ := hs
    let t : S := ⟨r, hr⟩
    have hvq := mem_q_of_R s r.1 hv r.2
    by_cases hst : s = t
    · rw [hst]
    · exact (Set.disjoint_left.1 (qDisj s t hst) hvq (q' t).start_mem_support).elim
  have hHit (s : S) : s.1.1 ∈ (P s).support := by
    obtain ⟨v, hv, hvS⟩ := hSep (a s) (ha s) (b s).1 (hb s) (P s) (valid s)
    exact mem_unique s v hvS hv ▸ hv
  refine ⟨S, a, fun s => (b s).1, P, S₀, ha, hb, valid, ?_, ?_, ?_, hSep⟩
  · intro s t hst
    refine Set.disjoint_left.2 (fun v hs ht => ?_)
    by_cases hr : v ∈ R
    · exact Set.disjoint_left.1 (qDisj s t hst) (mem_q_of_R s v hs hr) (mem_q_of_R t v ht hr)
    · exact Set.disjoint_left.1 (hp hst)
        ((p_or_q s v hs).resolve_right (fun hv => hr (qr s v hv)))
        ((p_or_q t v ht).resolve_right (fun hv => hr (qr t v hv)))
  · rintro v ⟨r, hr, rfl⟩
    exact ⟨⟨r, hr⟩, hHit ⟨r, hr⟩⟩
  · intro s
    exact ⟨s.1.1, ⟨⟨s.1, s.2, rfl⟩, hHit s⟩, fun v hv => mem_unique s v hv.1 hv.2⟩

end OMA.R_Erdos599_erdos_599_R1
