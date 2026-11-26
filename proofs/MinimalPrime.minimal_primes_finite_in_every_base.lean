import FormalConjectures.Wikipedia.MinimalPrime

-- Credit: @harshshah1618

open MinimalPrime

theorem OMA.solution : type_of% @MinimalPrime.minimal_primes_finite_in_every_base := by
  intro b
  classical
  by_cases hb : 2 ≤ b
  · by_contra hf
    have hi : {p : ℕ | IsMinimalPrimeInBase b p}.Infinite := hf
    let e : ℕ ↪ {p : ℕ | IsMinimalPrimeInBase b p} := hi.natEmbedding _
    have hw : {l : List ℕ | ∀ d, d ∈ l → d ∈ (↑(Finset.range b) : Set ℕ)}.PartiallyWellOrderedOn
        (List.SublistForall₂ Eq) :=
      Set.PartiallyWellOrderedOn.partiallyWellOrderedOn_sublistForall₂ Eq
        (Finset.range b).partiallyWellOrderedOn
    obtain ⟨m, n, hmn, hsub⟩ := hw.exists_lt (f := fun i => Nat.digits b (e i))
      (fun i d hd => Finset.mem_range.mpr (Nat.digits_lt_base (by omega) hd))
    obtain ⟨l, heq, hl⟩ := List.sublistForall₂_iff.mp hsub
    have heq' : Nat.digits b (e m) = l := by
      simpa only [List.forall₂_eq_eq_eq] using heq
    have hsub' : (Nat.digits b (e m)).Sublist (Nat.digits b (e n)) := heq' ▸ hl
    have hne : (e m : ℕ) ≠ e n := fun h => hmn.ne (e.injective (Subtype.ext h))
    exact (e n).2.2.2 ⟨e m, (e m).2.2.1, hne, hsub'⟩
  · exact Set.finite_empty.subset (fun p hp => (hb hp.1).elim)
