import OMAStatements.S_mo_373001

-- Problem: Can a commutator power realize a nontrivial twist of a generating pair?
-- Upstream: formal-conjectures statements/mo-373001.lean (declaration OMA.S_mo_373001.main)
-- Credit: @amtamaddon (the owner of the agent is credited as the solver)

open Equiv

namespace OMA.P373001

abbrev G : Type := alternatingGroup (Fin 7)

def pa : Perm (Fin 7) := swap 3 4 * swap 5 6

def pb : Perm (Fin 7) := swap 0 3 * swap 3 2 * swap 2 5 * swap 5 1 * swap 1 4 * swap 4 6

set_option maxRecDepth 1000000 in
def a : G := ⟨pa, Equiv.Perm.mem_alternatingGroup.2 (by decide)⟩

set_option maxRecDepth 1000000 in
def b : G := ⟨pb, Equiv.Perm.mem_alternatingGroup.2 (by decide)⟩

theorem card_G : Nat.card G = 2520 := by
  have h := nat_card_alternatingGroup (α := Fin 7)
  rw [h]
  simp [Nat.factorial]

instance simpleG : IsSimpleGroup G :=
  alternatingGroup.isSimpleGroup (by simp)

set_option maxRecDepth 1000000 in
theorem ord7 : orderOf b = 7 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact orderOf_eq_prime (by decide) (by decide)

set_option maxRecDepth 1000000 in
theorem ord5 : orderOf (a * b ^ 3) = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact orderOf_eq_prime (by decide) (by decide)

set_option maxRecDepth 1000000 in
theorem ord3 : orderOf (a * b * a * b ^ 3) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  exact orderOf_eq_prime (by decide) (by decide)

set_option maxRecDepth 1000000 in
theorem ord4 : orderOf (a * b * a * b ^ 2 * a * b ^ 4) = 4 := by
  have : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := a * b * a * b ^ 2 * a * b ^ 4)
    (by decide) (by decide)
  simpa using h

set_option maxRecDepth 1000000 in
theorem ord2 : orderOf a = 2 := by
  have : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  exact orderOf_eq_prime (by decide) (by decide)

theorem closure_top : Subgroup.closure ({a, b} : Set G) = ⊤ := by
  set H : Subgroup G := Subgroup.closure ({a, b} : Set G) with hH
  have ha : a ∈ H := Subgroup.subset_closure (by simp)
  have hb : b ∈ H := Subgroup.subset_closure (by simp)
  have h7 : 7 ∣ Nat.card H := by
    have := Subgroup.orderOf_dvd_natCard H hb
    rwa [ord7] at this
  have h5 : 5 ∣ Nat.card H := by
    have := Subgroup.orderOf_dvd_natCard H (mul_mem ha (pow_mem hb 3))
    rwa [ord5] at this
  have h3 : 3 ∣ Nat.card H := by
    have := Subgroup.orderOf_dvd_natCard H
      (mul_mem (mul_mem (mul_mem ha hb) ha) (pow_mem hb 3))
    rwa [ord3] at this
  have h4 : 4 ∣ Nat.card H := by
    have := Subgroup.orderOf_dvd_natCard H
      (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem ha hb) ha) (pow_mem hb 2)) ha) (pow_mem hb 4))
    rwa [ord4] at this
  have h420 : 420 ∣ Nat.card H := by
    have h12 : 12 ∣ Nat.card H :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 3 4) h3 h4
    have h60 : 60 ∣ Nat.card H :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 12 5) h12 h5
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 60 7) h60 h7
  have hidx : H.index * Nat.card H = 2520 := by
    rw [Subgroup.index_mul_card, card_G]
  have hidx6 : H.index ≤ 6 := by
    obtain ⟨k, hk⟩ := h420
    rw [hk] at hidx
    by_contra hcon
    rw [not_le] at hcon
    have hk0 : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h | h
      · rw [h] at hidx; simp at hidx
      · exact h
    nlinarith
  rcases (Subgroup.normalCore_normal H).eq_bot_or_eq_top with hbot | htop
  · exfalso
    have hker : (MulAction.toPermHom G (G ⧸ H)).ker = ⊥ := by
      rw [← Subgroup.normalCore_eq_ker]; exact hbot
    have hinj : Function.Injective (MulAction.toPermHom G (G ⧸ H)) :=
      (MonoidHom.ker_eq_bot_iff _).1 hker
    have hfin : Finite (G ⧸ H) := inferInstance
    have hle : Nat.card G ≤ Nat.card (Perm (G ⧸ H)) := Nat.card_le_card_of_injective _ hinj
    have hperm : Nat.card (Perm (G ⧸ H)) = (H.index).factorial := by
      rw [Nat.card_perm, Subgroup.index_eq_card]
    rw [card_G, hperm] at hle
    have : (H.index).factorial ≤ Nat.factorial 6 := Nat.factorial_le hidx6
    have h720 : Nat.factorial 6 = 720 := by decide
    omega
  · exact top_le_iff.1 (htop ▸ Subgroup.normalCore_le H)

end OMA.P373001

set_option maxRecDepth 1000000 in
open OMA.P373001 in
theorem OMA.solution : type_of% @OMA.S_mo_373001.main := by
  refine ⟨G, inferInstance, inferInstance, simpleG, a, b, 3, ?_, closure_top, ?_⟩
  · rw [ord2]; norm_num
  · constructor <;> decide
