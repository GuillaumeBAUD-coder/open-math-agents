import OMAReductions.R_oeis_a046932_R1

open Polynomial

namespace A046932H

theorem expand_dvd {R : Type*} [CommRing R] {p : ℕ} (hp : p ≠ 0) {f g : R[X]}
    (h : expand R p f ∣ expand R p g) : f ∣ g := by
  obtain ⟨c, hc⟩ := h
  refine ⟨contract p c, ?_⟩
  have := congrArg (contract p) hc
  rw [contract_expand (p := p) hp, mul_comm, contract_mul_expand hp] at this
  rw [this, mul_comm]

theorem key {S : Type*} [CommRing S] [Algebra (ZMod 2) S] [CharP S 2] (m k a : ℕ)
    (hdiv : (X ^ k + X + 1 : (ZMod 2)[X]) ∣ X ^ a + 1) (s : S)
    (hs : s ^ ((2 ^ m) ^ k) + s ^ (2 ^ m) + s = 0) : s ^ ((2 ^ m) ^ a) + s = 0 := by
  let ψ : Module.End (ZMod 2) S := (iterateFrobenius S 2 m).toAddMonoidHom.toZModLinearMap 2
  have hψ : ∀ i (t : S), (ψ ^ i) t = t ^ ((2 ^ m) ^ i) := by
    intro i
    induction i with
    | zero => intro t; simp
    | succ i ih =>
      intro t
      rw [pow_succ, Module.End.mul_apply, ih]
      show (t ^ (2 ^ m)) ^ ((2 ^ m) ^ i) = _
      rw [← pow_mul, pow_succ', mul_comm]
  obtain ⟨M, hM⟩ := hdiv
  have h1 := congrArg (fun f => aeval ψ f s) hM

  rw [mul_comm, map_mul, Module.End.mul_apply] at h1
  have h2 : aeval ψ (X ^ k + X + 1 : (ZMod 2)[X]) s = 0 := by
    have := hψ 1 s
    simp only [pow_one] at this
    simp [hψ, this, hs]
  rw [h2, map_zero] at h1
  have := hψ a s
  simpa [this] using h1

theorem period_dvd (f : (ZMod 2)[X]) (T : ℕ) (hT : 0 < T) (hf : f ∣ X ^ T + 1) :
    sInf {m : ℕ | 0 < m ∧ f ∣ X ^ m + 1} ∣ T := by
  have hne : ({m : ℕ | 0 < m ∧ f ∣ X ^ m + 1} : Set ℕ).Nonempty := ⟨T, hT, hf⟩
  have hd := Nat.sInf_mem hne
  set d := sInf {m : ℕ | 0 < m ∧ f ∣ X ^ m + 1}
  obtain ⟨hd0, hdd⟩ := hd
  have e : ∀ n : ℕ, (X ^ n + 1 : (ZMod 2)[X]) = X ^ n - 1 := fun n => by
    rw [CharTwo.sub_eq_add]
  rw [e] at hdd hf
  have h1 : f ∣ X ^ (d * (T / d)) - 1 := by
    rw [pow_mul]
    have := sub_dvd_pow_sub_pow (X ^ d : (ZMod 2)[X]) 1 (T / d)
    rw [one_pow] at this
    exact hdd.trans this
  have h2 : f ∣ X ^ (T % d) - 1 := by
    have : (X ^ T - 1 : (ZMod 2)[X]) = X ^ (T % d) * (X ^ (d * (T / d)) - 1) + (X ^ (T % d) - 1) := by
      conv_lhs => rw [← Nat.div_add_mod T d]
      ring
    rw [this] at hf
    exact (dvd_add_right (h1.mul_left _)).mp hf
  by_contra hnd
  have hr : 0 < T % d := Nat.pos_of_ne_zero (fun h => hnd (Nat.dvd_of_mod_eq_zero h))
  have : d ≤ T % d := Nat.sInf_le ⟨hr, by rw [e]; exact h2⟩
  exact absurd (Nat.mod_lt T hd0) (not_lt.mpr this)

theorem step (m k a : ℕ) (hm : 1 ≤ m)
    (hdiv : (X ^ k + X + 1 : (ZMod 2)[X]) ∣ X ^ a + 1) :
    (X ^ (((2 ^ m) ^ k - 1) / (2 ^ m - 1)) + X + 1 : (ZMod 2)[X]) ∣
      X ^ (((2 ^ m) ^ a - 1) / (2 ^ m - 1)) + 1 := by
  set q := 2 ^ m with hq
  have hq2 : 2 ≤ q := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have geo : ∀ n : ℕ, (q - 1) * ((q ^ n - 1) / (q - 1)) + 1 = q ^ n := by
    intro n
    rw [Nat.mul_div_cancel' (Nat.sub_one_dvd_pow_sub_one q n)]
    exact Nat.sub_add_cancel (Nat.one_le_pow _ _ (by omega))
  have ex : ∀ n : ℕ, (X ^ (q ^ n) : (ZMod 2)[X]) = X * (X ^ (q - 1)) ^ ((q ^ n - 1) / (q - 1)) := by
    intro n
    rw [← pow_mul (X : (ZMod 2)[X]), ← pow_succ' (X : (ZMod 2)[X]), geo n]
  have ex1 : (X ^ q : (ZMod 2)[X]) = X * X ^ (q - 1) := by
    rw [← pow_succ']; congr 1; omega
  obtain ⟨Q, hQdef⟩ : ∃ Q : (ZMod 2)[X], Q = X ^ (q ^ k) + X ^ q + X := ⟨_, rfl⟩
  have hQ : Q = X * expand (ZMod 2) (q - 1) (X ^ ((q ^ k - 1) / (q - 1)) + X + 1) := by
    simp only [hQdef, map_add, map_pow, expand_X, map_one]
    rw [ex k, ex1]
    ring
  have hR : (X ^ (q ^ a) + X : (ZMod 2)[X]) =
      X * expand (ZMod 2) (q - 1) (X ^ ((q ^ a - 1) / (q - 1)) + 1) := by
    simp only [map_add, map_pow, expand_X, map_one]
    rw [ex a]
    ring
  have hQnu : ¬ IsUnit Q := by
    intro hu
    exact not_isUnit_X (isUnit_of_dvd_unit ⟨_, hQ⟩ hu)
  have : Nontrivial (AdjoinRoot Q) := by
    unfold AdjoinRoot
    rw [Ideal.Quotient.nontrivial_iff, Ne, Ideal.span_singleton_eq_top]
    exact hQnu
  have : CharP (AdjoinRoot Q) 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) (AdjoinRoot Q)).injective 2
  have hs : (AdjoinRoot.root Q) ^ (q ^ k) + (AdjoinRoot.root Q) ^ q + AdjoinRoot.root Q = 0 := by
    have := AdjoinRoot.mk_self (f := Q)
    conv at this => lhs; arg 2; rw [hQdef]
    simpa only [map_add, map_pow, AdjoinRoot.mk_X] using this
  have h := key m k a hdiv (AdjoinRoot.root Q) hs
  have hdQ : Q ∣ X ^ (q ^ a) + X := by
    rw [← AdjoinRoot.mk_eq_zero]
    simpa only [map_add, map_pow, AdjoinRoot.mk_X] using h
  rw [hQ, hR] at hdQ
  have := (mul_dvd_mul_iff_left X_ne_zero).mp hdQ
  exact expand_dvd (by omega) this

end A046932H

theorem OMA.solution : OMA.R_oeis_a046932_R1.H1 := by
  intro k m _ hm
  by_cases h0 : OMA.S_oeis_a046932.a k = 0
  · simp [h0]
  have hne : ({n : ℕ | 0 < n ∧ (X ^ k + X + 1 : (ZMod 2)[X]) ∣ X ^ n + 1} : Set ℕ).Nonempty := by
    by_contra hc
    rw [Set.not_nonempty_iff_eq_empty] at hc
    exact h0 (Nat.sInf_eq_zero.mpr (Or.inr hc))
  obtain ⟨hpos, hdv⟩ := Nat.sInf_mem hne
  have hq2 : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hle : 2 ^ m ≤ (2 ^ m) ^ OMA.S_oeis_a046932.a k := Nat.le_self_pow h0 _
  rw [pow_mul', pow_mul' 2 (OMA.S_oeis_a046932.a k)]
  exact A046932H.period_dvd _ _ (Nat.div_pos (by omega) (by omega))
    (A046932H.step m k _ hm hdv)
