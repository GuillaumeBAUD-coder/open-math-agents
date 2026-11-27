import OMAReductions.R_Erdos20_erdos_20_R1_H2_R2
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators

-- Credit: @tongenspace

theorem OMA.solution : OMA.R_Erdos20_erdos_20_R1_H2_R2.H2 := by
  classical
  intro r n m t N hN hmN htn W hW
  let pack : (Fin t → (Fin n → Fin m)) → (Fin N → Fin N) :=
    fun f j =>
      if hj : j.val < t * n then
        have hn : 0 < n := by
          by_contra h
          have hn0 : n = 0 := by omega
          simp [hn0] at hj
        have hb : j.val / n < t := (Nat.div_lt_iff_lt_mul hn).mpr (by simpa [Nat.mul_comm] using hj)
        ⟨(f ⟨j.val / n, hb⟩ ⟨j.val % n, Nat.mod_lt j.val hn⟩).val,
          Nat.lt_of_lt_of_le (Fin.isLt _) hmN⟩
      else
        ⟨0, hN⟩
  have hpack_eval : ∀ (f : Fin t → (Fin n → Fin m)) (b : Fin t) (k : Fin n),
      have hidx : b.val * n + k.val < N := by
        have h1 : b.val * n + k.val < (b.val + 1) * n := by
          rw [Nat.add_mul, Nat.one_mul]
          exact Nat.add_lt_add_left k.isLt _
        have h2 : (b.val + 1) * n ≤ t * n := Nat.mul_le_mul_right n (Nat.succ_le_of_lt b.isLt)
        exact Nat.lt_of_lt_of_le h1 (Nat.le_trans h2 htn)
      (pack f ⟨b.val * n + k.val, hidx⟩).val = (f b k).val := by
    intro f b k hidx
    have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) k.isLt
    have hlt_tn : b.val * n + k.val < t * n := by
      have h1 : b.val * n + k.val < (b.val + 1) * n := by
        rw [Nat.add_mul, Nat.one_mul]
        exact Nat.add_lt_add_left k.isLt _
      exact Nat.lt_of_lt_of_le h1 (Nat.mul_le_mul_right n (Nat.succ_le_of_lt b.isLt))
    simp only [pack, hlt_tn, ↓reduceDIte]
    have hdiv : (b.val * n + k.val) / n = b.val := by
      rw [Nat.mul_comm b.val n, Nat.mul_add_div hn, Nat.div_eq_of_lt k.isLt, Nat.add_zero]
    have hmod : (b.val * n + k.val) % n = k.val := by
      rw [Nat.mul_comm b.val n, Nat.mul_add_mod, Nat.mod_eq_of_lt k.isLt]
    have hb_eq : (⟨(b.val * n + k.val) / n, (Nat.div_lt_iff_lt_mul hn).mpr
        (by simpa [Nat.mul_comm] using hlt_tn)⟩ : Fin t) = b := Fin.ext hdiv
    have hk_eq : (⟨(b.val * n + k.val) % n, Nat.mod_lt _ hn⟩ : Fin n) = k := Fin.ext hmod
    rw [hb_eq, hk_eq]
  have hpack_inj : Function.Injective pack := by
    intro f g hfg
    funext b k
    apply Fin.ext
    have h1 := hpack_eval f b k
    have h2 := hpack_eval g b k
    rw [hfg] at h1
    exact h1.symm.trans h2
  let P : Finset (Fin t → (Fin n → Fin m)) := Fintype.piFinset (fun _ : Fin t => W)
  refine ⟨P.image pack, ?_, ?_⟩
  · rw [Finset.card_image_of_injective P hpack_inj]
    simp [P]
  · intro v hv hsun
    have hpre : ∀ i : Fin r, ∃ f, f ∈ P ∧ pack f = v i := by
      intro i
      exact Finset.mem_image.mp (hv i)
    let f : Fin r → Fin t → (Fin n → Fin m) := fun i => Classical.choose (hpre i)
    have hfP : ∀ i : Fin r, f i ∈ P := fun i => (Classical.choose_spec (hpre i)).1
    have hfeq : ∀ i : Fin r, pack (f i) = v i := fun i => (Classical.choose_spec (hpre i)).2
    have hf_eq : ∀ a b : Fin r, f a = f b := by
      intro a b
      funext blk
      have hw : ∀ a' b' : Fin r, f a' blk = f b' blk := by
        apply hW (fun i => f i blk)
        · intro i
          exact (Fintype.mem_piFinset.mp (hfP i)) blk
        · intro k
          have hidx : blk.val * n + k.val < N := by
            have h1 : blk.val * n + k.val < (blk.val + 1) * n := by
              rw [Nat.add_mul, Nat.one_mul]
              exact Nat.add_lt_add_left k.isLt _
            have h2 : (blk.val + 1) * n ≤ t * n := Nat.mul_le_mul_right n (Nat.succ_le_of_lt blk.isLt)
            exact Nat.lt_of_lt_of_le h1 (Nat.le_trans h2 htn)
          let j : Fin N := ⟨blk.val * n + k.val, hidx⟩
          have heval : ∀ i : Fin r, (v i j).val = (f i blk k).val := by
            intro i
            rw [← hfeq i]
            exact hpack_eval (f i) blk k
          rcases hsun j with hall | hinj
          · left
            intro a' b'
            apply Fin.ext
            rw [← heval a', ← heval b', hall a' b']
          · right
            intro a' b' hab
            apply hinj
            apply Fin.ext
            rw [heval a', heval b']
            exact congrArg Fin.val hab
      exact hw a b
    intro a b
    rw [← hfeq a, ← hfeq b, hf_eq a b]
