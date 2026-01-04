import SocialChoice.Profile
import SocialChoice.Axioms.Participation

namespace SocialChoice


def Reinforcement (f : VotingRule) : Prop :=
  ∀ {U A : Type} [DecidableEq U] [Fintype A] [DecidableEq A]
      (V W : Finset U) (hdisj : Disjoint V W)
      (P : Profile (Electorate U V) A)
      (Q : Profile (Electorate U W) A)
      (R : Profile (Electorate U (V ∪ W)) A),
    restrictProfile R V (by intro x hx; exact Finset.mem_union.mpr (Or.inl hx)) = P →
    restrictProfile R W (by intro x hx; exact Finset.mem_union.mpr (Or.inr hx)) = Q →
    (f P ∩ f Q).Nonempty →
      f R = f P ∩ f Q

def SubsetReinforcement (f : VotingRule) : Prop :=
  ∀ {U A : Type} [DecidableEq U] [Fintype A] [DecidableEq A]
      (V W : Finset U) (hdisj : Disjoint V W)
      (P : Profile (Electorate U V) A)
      (Q : Profile (Electorate U W) A)
      (R : Profile (Electorate U (V ∪ W)) A),
    restrictProfile R V (by intro x hx; exact Finset.mem_union.mpr (Or.inl hx)) = P →
    restrictProfile R W (by intro x hx; exact Finset.mem_union.mpr (Or.inr hx)) = Q →
    f P ∩ f Q ⊆ f R

lemma reinforcement_subset {f : VotingRule} :
    Reinforcement f → SubsetReinforcement f := by
  intro h U A _ _ _ V W hdisj P Q R hRV hRW x hx
  have hnonempty : (f P ∩ f Q).Nonempty := ⟨x, hx⟩
  have hEq := h (V := V) (W := W) (hdisj := hdisj)
    (P := P) (Q := Q) (R := R) hRV hRW hnonempty
  simpa [hEq] using hx

end SocialChoice
