import SocialChoice.Profile
import SocialChoice.Axioms.Participation

namespace SocialChoice

universe u

def Reinforcement (f : VotingRule) : Prop :=
  ∀ {U A : Type u} [DecidableEq U] [Fintype A] [DecidableEq A]
      (V W : Finset U)
      (P : Profile (Electorate U V) A)
      (Q : Profile (Electorate U W) A)
      (R : Profile (Electorate U (V ∪ W)) A),
    restrictProfile R V (by intro x hx; exact Finset.mem_union.mpr (Or.inl hx)) = P →
    restrictProfile R W (by intro x hx; exact Finset.mem_union.mpr (Or.inr hx)) = Q →
    (f P ∩ f Q).Nonempty →
      f R = f P ∩ f Q

def SubsetReinforcement (f : VotingRule) : Prop :=
  ∀ {U A : Type u} [DecidableEq U] [Fintype A] [DecidableEq A]
      (V W : Finset U)
      (P : Profile (Electorate U V) A)
      (Q : Profile (Electorate U W) A)
      (R : Profile (Electorate U (V ∪ W)) A),
    restrictProfile R V (by intro x hx; exact Finset.mem_union.mpr (Or.inl hx)) = P →
    restrictProfile R W (by intro x hx; exact Finset.mem_union.mpr (Or.inr hx)) = Q →
    f P ∩ f Q ⊆ f R

lemma reinforcement_subset {f : VotingRule} :
    Reinforcement f → SubsetReinforcement f := by
  intro h U A _ _ _ V W P Q R hRV hRW x hx
  have hnonempty : (f P ∩ f Q).Nonempty := ⟨x, hx⟩
  have hEq := h (V := V) (W := W) (P := P) (Q := Q) (R := R) hRV hRW hnonempty
  simpa [hEq] using hx

end SocialChoice
