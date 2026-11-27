import OMAReductions.R_Erdos964_erdos_964_variants_eberhard_R1_H1_R1
import Mathlib

/-! Credit: @marcusbuffett. The Chinese remainder theorem modulo the squares of the prescribed factors gives admissible normalized forms. -/

namespace Normal964
open Finset

private lemma linear_residue (a m t u : ℕ) (hm : 0 < m) (ha : a.Coprime m) :
    ∃ x : ℕ, a*x+t ≡ u [MOD m] := by
  letI : NeZero m := ⟨hm.ne'⟩
  let w : ZMod m := (a : ZMod m)⁻¹ * ((u:ZMod m)-t)
  refine ⟨w.val,(ZMod.natCast_eq_natCast_iff _ _ _).mp ?_⟩
  push_cast
  rw [ZMod.natCast_zmod_val]
  dsimp [w]
  rw [← mul_assoc,ZMod.coe_mul_inv_eq_one a ha,one_mul]
  ring

private lemma difference {p a b x : ℕ} (hp : p.Prime)
    (h₁ : p ∣ a*x+1) (h₂ : p ∣ b*x+1) : a ≡ b [MOD p] := by
  letI : Fact p.Prime := ⟨hp⟩
  have h1 := (ZMod.natCast_eq_zero_iff _ _).2 h₁
  have h2 := (ZMod.natCast_eq_zero_iff _ _).2 h₂
  push_cast at h1 h2
  have hn : (x:ZMod p) ≠ 0 := fun e => by simp [e] at h1
  apply (ZMod.natCast_eq_natCast_iff _ _ _).1
  apply mul_right_cancel₀ hn
  linear_combination h1 - h2

theorem normalize :
  ∀ A r : Fin 3 → ℕ, ((∀ i, 0 < A i ∧ 0 < r i ∧ (r i).Coprime (A i)) ∧ StrictMono A ∧
     (∀ i j, i ≠ j → (r i).Coprime (r j) ∧
       (r i).Coprime (if A i > A j then A i - A j else A j - A i))) →
    ∃ M x : ℕ, ∃ a b : Fin 3 → ℕ, 0 < M ∧
      (∀ i, 0 < a i ∧ 0 < b i) ∧
      (∀ i j, i ≠ j → a i * b j ≠ a j * b i) ∧
      (∀ p : ℕ, p.Prime → ∃ z : ℕ, ∀ i, ¬p ∣ a i*z+b i) ∧
      ∀ i z, A i*(M*z+x)+1 = r i*(a i*z+b i) := by
  classical
  intro A r h
  choose residues hr using fun i => linear_residue (A i) (r i^2) 1 (r i)
    (by have := (h.1 i).2.1; positivity) ((h.1 i).2.2.symm.pow_right 2)
  let sol := Nat.chineseRemainderOfFinset residues (fun i => r i ^ 2) univ
    (fun i _ => pow_ne_zero _ (h.1 i).2.1.ne')
    (fun i _ j _ hij => (((h.2.2 i j hij).1.pow_left 2).pow_right 2))
  let x : ℕ := sol.val
  have hx (i) : A i*x+1 ≡ r i [MOD r i^2] :=
    (((sol.prop i (mem_univ _)).mul_left (A i)).add_right 1).trans (hr i)
  let M := ∏ i, r i^2
  have hM : 0 < M := prod_pos fun i _ => pow_pos (h.1 i).2.1 _
  have hdM (i) : r i ∣ M :=
    (dvd_pow_self _ (by decide : 2 ≠ 0)).trans (dvd_prod_of_mem _ (mem_univ i))
  let a := fun i => A i*M / r i
  let b := fun i => (A i*x+1)/r i
  have ha (i) : r i * a i = A i*M :=
    Nat.mul_div_cancel' (dvd_mul_of_dvd_right (hdM i) _)
  have hb (i) : r i * b i = A i*x+1 :=
    Nat.mul_div_cancel' (((hx i).dvd_iff (dvd_pow_self _ (by decide : 2 ≠ 0))).mpr dvd_rfl)
  have hid (i : Fin 3) (z : ℕ) : A i*(M*z+x)+1 = r i*(a i*z+b i) := by
    calc
      _ = (A i*M)*z+(A i*x+1) := by ring
      _ = _ := by rw [← ha,← hb]; ring
  refine ⟨M,x,a,b,hM,?_,?_,?_,hid⟩
  · intro i
    constructor
    · by_contra! he
      have hz : a i = 0 := by omega
      have e := ha i
      rw [hz,Nat.mul_zero] at e
      exact (Nat.mul_pos (h.1 i).1 hM).ne' e.symm
    · by_contra! he
      have hz : b i = 0 := by omega
      have e := hb i
      rw [hz,Nat.mul_zero] at e
      omega
  · intro i j hij he
    have e : (r i*a i)*(r j*b j) = (r j*a j)*(r i*b i) := by
      calc
        _ = r i*r j*(a i*b j) := by ring
        _ = _ := by rw [he]; ring
    rw [ha,ha,hb,hb] at e
    have eq : A i*M = A j*M := by nlinarith only [e]
    exact hij (h.2.1.injective (Nat.eq_of_mul_eq_mul_right hM eq))
  · intro p hp
    by_cases pm : p ∣ M
    · obtain ⟨j,_,hj⟩ := (hp.prime.dvd_finsetProd_iff _).mp pm
      have pr : p ∣ r j := hp.dvd_of_dvd_pow hj
      refine ⟨0,fun i => ?_⟩
      simp only [mul_zero,zero_add]
      intro pi
      by_cases ij : j=i
      · subst i
        have hb1 : b j ≡ 1 [MOD r j] := by
          apply Nat.ModEq.mul_left_cancel' (h.1 j).2.1.ne'
          simpa only [ha,hb,pow_two,mul_one] using (hx j)
        exact hp.not_dvd_one ((hb1.dvd_iff pr).mp pi)
      · have di : p ∣ A i*x+1 := hb i ▸ dvd_mul_of_dvd_right pi (r i)
        have dj : p ∣ A j*x+1 := hb j ▸ dvd_mul_of_dvd_left pr (b j)
        have eq := difference hp dj di
        apply hp.ne_one (Nat.eq_one_of_dvd_coprimes (h.2.2 j i ij).2 pr ?_)
        split
        · exact eq.symm.dvd'
        · exact eq.dvd'
    · obtain ⟨z,hz⟩ := linear_residue M p x 0 hp.pos (hp.coprime_iff_not_dvd.mpr pm).symm
      refine ⟨z,fun i pi => ?_⟩
      have d : p ∣ A i*(M*z+x)+1 := hid i z ▸ dvd_mul_of_dvd_right pi (r i)
      have one : A i*(M*z+x)+1 ≡ 1 [MOD p] := by
        simpa using (hz.mul_left (A i)).add_right 1
      exact hp.not_dvd_one ((one.dvd_iff dvd_rfl).mp d)

end Normal964

theorem OMA.solution : OMA.R_Erdos964_erdos_964_variants_eberhard_R1_H1_R1.H2 := Normal964.normalize
