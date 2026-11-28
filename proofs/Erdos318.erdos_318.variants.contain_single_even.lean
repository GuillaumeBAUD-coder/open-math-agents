import FormalConjectures.ErdosProblems.«318»

theorem OMA.solution : type_of% @Erdos318.erdos_318.variants.contain_single_even := by
  classical
  intro A hA hA' hp
  obtain ⟨e, he⟩ := Set.ncard_eq_one.mp hA'
  have he' : e ∈ A \ {0} ∧ Even e := by change e ∈ {n | n ∈ A \ {0} ∧ Even n}; rw [he]; rfl
  obtain ⟨o, ho, hots⟩ := hA.exists_notMem_finset ({0, e} : Finset ℕ)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hots
  let f (n : ℕ) : ℝ := if n = e then -1 else 1
  obtain ⟨S, hne, hsub, hs⟩ := hp f
    (fun h => by have := congrFun h ⟨e, he'.1⟩; norm_num [f] at this)
    (fun h => by have := congrFun h ⟨o, ho, hots.1⟩; norm_num [f, hots.2] at this)
    (by rintro _ ⟨n, rfl⟩; by_cases hn : n = e <;> simp [f, hn])
  by_cases hes : e ∈ S
  · have hod : ∀ n ∈ S.erase e, Odd n := fun n hn => by
      obtain ⟨hne', hnS⟩ := Finset.mem_erase.mp hn
      by_contra h
      have hm : n ∈ {n | n ∈ A \ {0} ∧ Even n} := ⟨hsub hnS, Nat.not_odd_iff_even.mp h⟩
      rw [he] at hm; exact hne' hm
    let P := ∏ n ∈ S.erase e, n
    have hP : Odd P := Finset.prod_induction _ _ (fun _ _ => Odd.mul) odd_one hod
    have hPa : (P : ℝ) * ∑ n ∈ S.erase e, f n / n = (∑ n ∈ S.erase e, P / n : ℕ) := by
      rw [Finset.mul_sum, Nat.cast_sum]
      refine Finset.sum_congr rfl fun n hn => ?_
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (hod n hn).pos.ne'
      simp only [f, if_neg (Finset.mem_erase.mp hn).1, mul_one_div]
      rw [div_eq_iff hn0]
      exact_mod_cast (Nat.div_mul_cancel (Finset.dvd_prod_of_mem _ hn)).symm
    rw [← Finset.add_sum_erase _ _ hes, show f e = -1 from if_pos rfl, neg_div] at hs
    rw [show ∑ n ∈ S.erase e, f n / n = 1 / e by linarith, mul_one_div,
      div_eq_iff (by exact_mod_cast he'.1.2)] at hPa
    exact (Nat.not_even_iff_odd.mpr hP) ((by exact_mod_cast hPa : P = _ * e) ▸ he'.2.mul_left _)
  · have : 0 < ∑ n ∈ S, f n / n := Finset.sum_pos (fun n hn => by
      have := (hsub hn).2
      simp [f, show n ≠ e from fun h => hes (h ▸ hn), Nat.pos_of_ne_zero this]) hne
    linarith
