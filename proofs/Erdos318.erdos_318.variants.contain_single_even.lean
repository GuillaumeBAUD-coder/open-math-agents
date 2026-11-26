import FormalConjectures.ErdosProblems.«318»

/-!
Erdős observed that an infinite set with exactly one positive even number
cannot have property P₁, as recorded by Sattler (1982). Give the even
denominator a negative sign and every other denominator a positive sign.
A sum of reciprocals of odd integers has an odd common denominator, so it
cannot equal the reciprocal of the even element.
-/

open Set

private theorem sum_inv_odd_denom (S : Finset ℕ) (ho : ∀ n ∈ S, Odd n) :
    ∃ a b : ℕ, Odd b ∧ ∑ n ∈ S, (1 : ℝ) / n = a / (b : ℝ) := by
  induction S using Finset.induction_on with
  | empty => exact ⟨0, 1, by decide, by simp⟩
  | @insert n S hn ih =>
    have hno := ho n (Finset.mem_insert_self ..)
    obtain ⟨a, b, hb, hs⟩ := ih (fun k hk => ho k (Finset.mem_insert_of_mem hk))
    refine ⟨b + n * a, n * b, hno.mul hb, ?_⟩
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by obtain ⟨k, hk⟩ := hno; omega)
    have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast (show b ≠ 0 by obtain ⟨k, hk⟩ := hb; omega)
    rw [Finset.sum_insert hn, hs]
    push_cast
    field_simp

theorem OMA.solution : type_of% @Erdos318.erdos_318.variants.contain_single_even := by
  intro A hA hA'
  classical
  obtain ⟨e, he⟩ := Set.ncard_eq_one.mp hA'
  have he_prop : e ∈ A \ {0} ∧ Even e := by
    change e ∈ {n | n ∈ A \ {0} ∧ Even n}
    rw [he]
    rfl
  have he0 : e ≠ 0 := he_prop.1.2
  obtain ⟨o, ho, hots⟩ := hA.exists_notMem_finset ({0, e} : Finset ℕ)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hots
  let f : ℕ → ℝ := fun n => if n = e then -1 else 1
  intro hp
  obtain ⟨S, hne, hsub, hs⟩ := hp f (by
    intro h
    have hv := congrFun h ⟨e, he_prop.1⟩
    norm_num [Function.comp_apply, f] at hv) (by
    intro h
    have hv := congrFun h ⟨o, ho, hots.1⟩
    norm_num [Function.comp_apply, f, hots.2] at hv) (by
    rintro _ ⟨n, rfl⟩
    by_cases hn : n = e <;> simp [f, hn])
  by_cases hes : e ∈ S
  · have hod : ∀ n ∈ S.erase e, Odd n := by
      intro n hn
      obtain ⟨hne', hnS⟩ := Finset.mem_erase.mp hn
      by_contra h
      have hmem : n ∈ {n | n ∈ A \ {0} ∧ Even n} :=
        ⟨hsub hnS, Nat.not_odd_iff_even.mp h⟩
      rw [he] at hmem
      exact hne' hmem
    obtain ⟨a, b, hb, hab⟩ := sum_inv_odd_denom _ hod
    have he' : (e : ℝ) ≠ 0 := by exact_mod_cast he0
    have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast (show b ≠ 0 by obtain ⟨k, hk⟩ := hb; omega)
    rw [← Finset.add_sum_erase _ _ hes] at hs
    have hs' : ∑ n ∈ S.erase e, f n / n = ∑ n ∈ S.erase e, (1 : ℝ) / n := by
      apply Finset.sum_congr rfl
      intro n hn
      simp [f, (Finset.mem_erase.mp hn).1]
    rw [hs', hab] at hs
    simp only [f, if_pos rfl] at hs
    field_simp at hs
    have hba : b = e * a := by exact_mod_cast (show (b : ℝ) = e * a by linarith)
    exact (Nat.not_even_iff_odd.mpr hb) (hba ▸ he_prop.2.mul_right a)
  · have hpos : 0 < ∑ n ∈ S, f n / n := by
      apply Finset.sum_pos _ hne
      intro n hn
      have hn0 : n ≠ 0 := (hsub hn).2
      have hne' : n ≠ e := fun heq => hes (heq ▸ hn)
      simp [f, hne', Nat.pos_of_ne_zero hn0]
    linarith
