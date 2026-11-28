import OMAStatements.S_mse_698186

namespace OMA.Disproof_mse_698186

private def S3 : Set ℕ := {p : ℕ | p.Prime ∧ p % 4 = 3}

private lemma list_prod_mod_four_eq_one :
    ∀ l : List ℕ, (∀ p ∈ l, p % 4 = 1) → l.prod % 4 = 1
  | [], _ => rfl
  | p :: ps, h => by
      simp only [List.prod_cons]
      have hp := h p (by simp)
      have hps := list_prod_mod_four_eq_one ps (fun q hq => h q (by simp [hq]))
      rw [Nat.mul_mod, hp, hps]

private lemma list_prod_pos :
    ∀ l : List ℕ, (∀ p ∈ l, 0 < p) → 0 < l.prod
  | [], _ => by simp
  | p :: ps, h => by
      simp only [List.prod_cons]
      exact Nat.mul_pos (h p (by simp)) (list_prod_pos ps (fun q hq => h q (by simp [hq])))

private lemma list_map_prod_emod_four (f : ℕ → ℤ) :
    ∀ l : List ℕ, (∀ p ∈ l, f p % 4 = (p : ℤ) % 4) →
      (l.map f).prod % 4 = (l.prod : ℤ) % 4
  | [], _ => rfl
  | p :: ps, h => by
      simp only [List.map_cons, List.prod_cons]
      rw [Int.mul_emod, h p (by simp),
        list_map_prod_emod_four f ps (fun q hq => h q (by simp [hq])), ← Int.mul_emod]
      simp

private lemma S3_infinite : S3.Infinite := by
  intro hfin
  let F : Finset ℕ := hfin.toFinset
  let P : ℕ := F.toList.prod
  have hPpos : 0 < P := by
    apply list_prod_pos
    intro p hp
    have hpS : p ∈ S3 := (hfin.mem_toFinset).mp (Finset.mem_toList.mp hp)
    exact hpS.1.pos
  let M : ℕ := 4 * P - 1
  have hMmod : M % 4 = 3 := by omega
  have hMne : M ≠ 0 := by omega
  have hex : ∃ q ∈ M.primeFactorsList, q % 4 = 3 := by
    by_contra hall
    have hall1 : ∀ q ∈ M.primeFactorsList, q % 4 = 1 := by
      intro q hq
      have hqp : q.Prime := Nat.prime_of_mem_primeFactorsList hq
      have hqdvd : q ∣ M := Nat.dvd_of_mem_primeFactorsList hq
      have hqne2 : q ≠ 2 := by
        intro h2
        rw [h2] at hqdvd
        omega
      have hqodd : q % 2 = 1 := (hqp.eq_two_or_odd).resolve_left hqne2
      have hqne3 : q % 4 ≠ 3 := fun h3 => hall ⟨q, hq, h3⟩
      omega
    have hprod1 : M.primeFactorsList.prod % 4 = 1 := list_prod_mod_four_eq_one _ hall1
    rw [Nat.prod_primeFactorsList hMne] at hprod1
    omega
  rcases hex with ⟨q, hqmem, hqmod⟩
  have hqp : q.Prime := Nat.prime_of_mem_primeFactorsList hqmem
  have hqS : q ∈ S3 := ⟨hqp, hqmod⟩
  have hqF : q ∈ F.toList := Finset.mem_toList.mpr ((hfin.mem_toFinset).mpr hqS)
  have hqP : q ∣ P := List.dvd_prod hqF
  have hq4P : q ∣ 4 * P := dvd_mul_of_dvd_right hqP 4
  have hqM : q ∣ M := Nat.dvd_of_mem_primeFactorsList hqmem
  have hMadd : M + 1 = 4 * P := by omega
  have hq1 : q ∣ 1 := (Nat.dvd_add_right hqM).mp (hMadd ▸ hq4P)
  exact hqp.not_dvd_one hq1

private lemma generated_S3_ne_one_of_mod_four_eq_three {m : ℕ} (hm : m % 4 = 3) :
    OMA.S_mse_698186.generated S3 m ≠ 1 := by
  intro hgen
  have hmne : m ≠ 0 := by omega
  have hmod : (OMA.S_mse_698186.generated S3 m) % 4 = (m.primeFactorsList.prod : ℤ) % 4 := by
    unfold OMA.S_mse_698186.generated
    apply list_map_prod_emod_four
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactorsList hp
    have hpdvd : p ∣ m := Nat.dvd_of_mem_primeFactorsList hp
    have hpne2 : p ≠ 2 := by
      intro h2
      rw [h2] at hpdvd
      omega
    have hpodd : p % 2 = 1 := (hpp.eq_two_or_odd).resolve_left hpne2
    split_ifs with hpS
    · have hp3 : p % 4 = 3 := hpS.2
      omega
    · have hpne3 : p % 4 ≠ 3 := fun h3 => hpS ⟨hpp, h3⟩
      omega
  rw [hgen, Nat.prod_primeFactorsList hmne] at hmod
  omega

end OMA.Disproof_mse_698186

theorem OMA.disproof : ¬ (type_of% @OMA.S_mse_698186.main) := by
  intro hmain
  have hinf :=
    hmain OMA.Disproof_mse_698186.S3 (fun _ hp => hp.1) OMA.Disproof_mse_698186.S3_infinite 4
  rcases hinf.nonempty with ⟨n, _, hn⟩
  let i : ℕ := 3 - n % 4
  have hi : i < 4 := by omega
  have hmod : (n + i) % 4 = 3 := by omega
  exact OMA.Disproof_mse_698186.generated_S3_ne_one_of_mod_four_eq_three hmod (hn i hi)
