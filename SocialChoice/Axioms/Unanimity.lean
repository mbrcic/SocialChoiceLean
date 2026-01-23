import SocialChoice.Profile
import SocialChoice.Meta

namespace SocialChoice

@[scAxiom]
def Unanimity (f : VotingRule) : Prop :=
  ∀ {V A : Type} [Fintype V] [Fintype A] [Nonempty V] (P : Profile V A) (c : A),
    (∀ v : V, TopRank P v c) → f P = {c}

theorem unanimity_preservedUnderRefinement :
    PreservedUnderRefinement Unanimity := by
  intro f g hf_total _ hfg hZg V A _ _ _ P c htop
  classical
  let _ : Nonempty A := ⟨c⟩
  have hsubset : f P ⊆ ({c} : Finset A) := by
    intro x hx
    have hxg : x ∈ g P := hfg P hx
    simpa [hZg P c htop] using hxg
  have hnonempty : (f P).Nonempty := hf_total P
  rcases hnonempty with ⟨x, hx⟩
  have hx' : x = c := by
    have : x ∈ ({c} : Finset A) := hsubset hx
    simpa using this
  have hc : c ∈ f P := by
    simpa [hx'] using hx
  have hsup : ({c} : Finset A) ⊆ f P := by
    intro y hy
    have hy' : y = c := by
      simpa using hy
    subst hy'
    exact hc
  apply Finset.ext
  intro y
  constructor
  · intro hy
    exact hsubset hy
  · intro hy
    exact hsup hy

end SocialChoice
