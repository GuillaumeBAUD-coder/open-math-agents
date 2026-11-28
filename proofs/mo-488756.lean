import OMAStatements.S_mo_488756
import Mathlib

namespace OMA.S_mo_488756

lemma frag_erase {α β : Type*} [DecidableEq α] [LE β] (w : α → α → β) {t : Finset α}
    (h : Fragmented w t) : ∀ a, Fragmented w (t.erase a) := by
  induction h with
  | empty => intro a; simpa using Fragmented.empty
  | @delete s v hc _ ih =>
    intro a
    by_cases hva : v = a
    · subst hva; exact ‹Fragmented w (s.erase v)›
    · have h1 : Fragmented w ((s.erase v).erase a) := ih a
      have h2 : (s.erase v).erase a = (s.erase a).erase v := Finset.erase_right_comm
      rw [h2] at h1
      refine Fragmented.delete ?_ h1
      refine ⟨Finset.mem_erase.2 ⟨hva, hc.1⟩, ?_⟩
      intro x hx a' ha' b hb hne
      apply hc.2
      · simp only [Finset.mem_erase] at hx ⊢; tauto
      · simp only [Finset.mem_erase] at ha' ⊢; tauto
      · simp only [Finset.mem_erase] at hb ⊢; tauto
      · exact hne

end OMA.S_mo_488756

theorem OMA.solution : type_of% @OMA.S_mo_488756.main := by
  intro α β _ _ w _ s a hs hins
  apply hs
  by_cases ha : a ∈ s
  · rwa [Finset.insert_eq_of_mem ha] at hins
  · have := OMA.S_mo_488756.frag_erase w hins a
    rwa [Finset.erase_insert ha] at this
