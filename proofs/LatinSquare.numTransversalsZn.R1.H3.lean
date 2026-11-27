import OMAReductions.R_LatinSquare_numTransversalsZn_R1
import Mathlib

open Set Filter
open scoped Topology

theorem OMA.solution : OMA.R_LatinSquare_numTransversalsZn_R1.H3 := by
  intro u x lim hx hu
  obtain ⟨N,hN⟩ := eventually_atTop.mp
    (lim.eventually (Ioo_mem_nhds (show x/2 < x by linarith [hx.1])
      (show x < (1+x)/2 by linarith [hx.2])))
  have initial (M : ℕ) : ∃ a b : ℝ, 0 < a ∧ b < 1 ∧ a ≤ x/2 ∧ (1+x)/2 ≤ b ∧
      ∀ n ≥ 1, n < M → u n ∈ Icc a b := by
    induction M with
    | zero => exact ⟨_,_,by linarith [hx.1],by linarith [hx.2],le_rfl,le_rfl,by omega⟩
    | succ m ih =>
      obtain ⟨a,b,ha,hb,hax,hxb,hs⟩ := ih
      by_cases hm : 1 ≤ m
      · obtain ⟨hm₁,hm₂⟩ := hu m hm
        refine ⟨min a (u m),max b (u m),lt_min ha hm₁,max_lt hb hm₂,
          (min_le_left ..).trans hax,hxb.trans (le_max_left ..),?_⟩
        intro n hn hn'
        rcases Nat.lt_succ_iff_lt_or_eq.mp hn' with h | rfl
        · exact ⟨(min_le_left ..).trans (hs n hn h).1,(hs n hn h).2.trans (le_max_left ..)⟩
        · exact ⟨min_le_right ..,le_max_right ..⟩
      · exact ⟨a,b,ha,hb,hax,hxb,by intros; omega⟩
  obtain ⟨a,b,ha,hb,hax,hxb,hs⟩ := initial N
  refine ⟨a,b,ha,hb,by linarith,?_⟩
  intro n hn
  by_cases h : n < N
  · exact hs n hn h
  · obtain ⟨hl,hr⟩ := hN n (by omega)
    exact ⟨hax.trans hl.le,hr.le.trans hxb⟩
