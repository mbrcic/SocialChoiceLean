import SocialChoice.Axioms.Participation

namespace SocialChoice

@[scAxiom]
def Resolvability (f : VotingRule) : Prop :=
  ∀ {U A : Type} [DecidableEq U] [Fintype A]
      (V : Finset U) (u : U) (hu : u ∉ V)
      (P : Profile (Electorate U V) A) (x : A),
    x ∈ f P →
    ∃ (r : LinearOrder A) (Q : Profile (Electorate U (insert u V)) A),
      (∀ v : Electorate U V, Q.pref (liftVoter (u := u) v) = P.pref v) ∧
      Q.pref (newVoter (u := u) (V := V) hu) = r ∧
      f Q = {x}

end SocialChoice
