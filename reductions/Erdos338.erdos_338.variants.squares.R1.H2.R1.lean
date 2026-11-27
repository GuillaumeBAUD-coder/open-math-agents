import OMAReductions.R_Erdos338_erdos_338_variants_squares_R1

/-! For an odd integer, Jacobi’s four-square formula gives at least eight times
the integer in signed ordered representations. Taking absolute values loses a
factor of at most sixteen. Repeated coordinates contribute only a ternary
quadratic form. The reduction separates those two counts and proves the passage
from large odd integers to all large integers by adjoining one larger square. -/

namespace OMA.R_Erdos338_erdos_338_variants_squares_R1_H2_R1

open Filter Finset

def H1 : Prop := ∀ᶠ m : ℕ in atTop, Odd m → m ≤ 2 * ((univ : Finset (Fin 4 → Fin (m+1))).filter fun v => ∑ i, ((v i : ℕ)^2) = m).card

def H2 : Prop := ∀ᶠ m : ℕ in atTop, Odd m →
  2 * (((univ : Finset (Fin 4 → Fin (m+1))).filter fun v => ∑ i, ((v i : ℕ)^2) = m).filter fun v => ¬ Function.Injective v).card < m

private lemma separate (T : ℕ) : ∀ᶠ n : ℕ in atTop, ∃ k m : ℕ,
    T ≤ m ∧ Odd m ∧ n = k^2+m ∧ m < k^2 := by
  filter_upwards [eventually_ge_atTop ((8*(T+100))^2)] with n hn
  let t := n.sqrt/8
  have hq : 8*(T+100) ≤ n.sqrt := Nat.le_sqrt.mpr (by simpa [pow_two] using hn)
  have ht : T+100 ≤ t := by dsimp [t]; omega
  have h1 : 8*t ≤ n.sqrt := by dsimp [t]; omega
  have h2 : n.sqrt+1 ≤ 8*t+8 := by dsimp [t]; omega
  have lo := (Nat.mul_le_mul h1 h1).trans (Nat.sqrt_le n)
  have hi := (Nat.lt_succ_sqrt n).trans_le (Nat.mul_le_mul h2 h2)
  let k := 6*t + (n+1)%2
  have k1 : 6*t ≤ k := by dsimp [k]; omega
  have k2 : k ≤ 6*t+1 := by dsimp [k]; omega
  have hsq : 20*t ≤ t*t := by nlinarith only [Nat.mul_le_mul_right t (show 20 ≤ t by omega)]
  have hk : k^2 + T ≤ n := by nlinarith only [lo, Nat.mul_le_mul k2 k2, hsq, ht]
  have hg : n < 2*k^2 := by nlinarith only [hi, Nat.mul_le_mul k1 k1, hsq, ht]
  refine ⟨k,n-k^2,by omega,?_,by omega,by omega⟩
  rw [Nat.odd_iff]
  have hmod : k^2 % 2 = (n+1)%2 := by
    have hp : k % 2 = (n+1)%2 := by dsimp [k]; omega
    calc k^2 % 2 = (k % 2)^2 % 2 := Nat.pow_mod _ _ _
         _ = (n+1)%2 := by
           rw [hp]
           have cases : (n+1)%2 = 0 ∨ (n+1)%2 = 1 := by omega
           rcases cases with e | e <;> rw [e] <;> decide
  omega

theorem main : H1 → H2 → OMA.R_Erdos338_erdos_338_variants_squares_R1.H2 := by
  classical
  intro h1 h2
  obtain ⟨T,hT⟩ := eventually_atTop.mp (h1.and h2)
  filter_upwards [separate T] with n ⟨k,m,hm,ho,hn,hl⟩
  obtain ⟨hA,hB⟩ := hT m hm
  have ha := hA ho
  have hb := hB ho
  let reps := ((univ : Finset (Fin 4 → Fin (m+1))).filter fun v => ∑ i, ((v i : ℕ)^2) = m)
  change m ≤ 2 * reps.card at ha
  change 2 * (reps.filter fun v => ¬ Function.Injective v).card < m at hb
  have ex : ∃ v ∈ reps, Function.Injective v := by
    by_contra! h
    have he : (reps.filter fun v => ¬ Function.Injective v) = reps :=
      filter_eq_self.mpr h
    rw [he] at hb
    omega
  obtain ⟨v,hv,hinj⟩ := ex
  have hsum := (mem_filter.mp hv).2
  let f (i : Fin 4) : ℕ := (v i : ℕ)^2
  have fi : Function.Injective f := by
    intro i j h
    apply hinj
    apply Fin.ext
    dsimp [f] at h
    nlinarith only [h]
  let S := univ.image f
  have hs : ∑ x ∈ S, x = m := by
    rw [show S = univ.image f from rfl, sum_image fi.injOn]
    exact hsum
  have hk : k^2 ∉ S := by
    intro hk
    have := single_le_sum (fun x (_ : x ∈ S) => Nat.zero_le x) hk
    omega
  refine ⟨insert (k^2) S, ?_, ?_, ?_⟩
  · intro x hx
    rcases mem_insert.mp hx with rfl | hx
    · exact ⟨k,rfl⟩
    · obtain ⟨i,_,rfl⟩ := mem_image.mp hx
      exact ⟨v i,rfl⟩
  · rw [card_insert_of_notMem hk]
    simp [S, card_image_of_injective _ fi]
  · rw [sum_insert hk,hs,hn]
end OMA.R_Erdos338_erdos_338_variants_squares_R1_H2_R1
