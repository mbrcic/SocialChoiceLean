import SocialChoice.Profile
import SocialChoice.Meta

namespace SocialChoice

@[scAxiom]
def MajorityCriterion (f : VotingRule) : Prop :=
  ∀ {V A : Type} [Fintype V] [Fintype A] (P : Profile V A) (c : A),
    StrictMajority (votersTop P c) → f P = {c}

@[scAxiom]
def MajorityLoserCriterion (f : VotingRule) : Prop :=
  ∀ {V A : Type} [Fintype V] [Fintype A] (P : Profile V A) (c : A),
    StrictMajority (votersBottom P c) → (∃ d, d ≠ c) → c ∉ f P

@[scAxiom]
def MutualMajorityCriterion (f : VotingRule) : Prop :=
  ∀ {V A : Type} [Fintype V] [Fintype A]
      (P : Profile V A) (S : Finset V) (T : Finset A),
    StrictMajority S →
    T.Nonempty →
    (∀ v ∈ S, ∀ a ∈ T, ∀ b ∉ T, Prefers P v a b) →
    f P ⊆ T

lemma mutualMajorityCriterion_implies_majorityCriterion (f : VotingRule)
    (hf : MutualMajorityCriterion f) (hf_total : IsVotingRule f) :
    MajorityCriterion f := by
  intro V A _ _ P c hmaj
  classical
  have hsubset : f P ⊆ ({c} : Finset A) := by
    apply hf (P := P) (S := votersTop P c) (T := {c}) hmaj
    · simp
    intro v hv a ha b hb
    have hv_top : TopRank P v c := (Finset.mem_filter.mp hv).2
    have ha' : a = c := by
      simpa using ha
    have hb' : b ≠ c := by
      simpa using hb
    simpa [ha'] using hv_top b hb'
  have hnonempty : (f P).Nonempty := hf_total P
  rcases hnonempty with ⟨x, hx⟩
  have hx' : x = c := by
    have : x ∈ ({c} : Finset A) := hsubset hx
    simpa using this
  have hc : c ∈ f P := by
    simpa [hx'] using hx
  apply Finset.ext
  intro y
  constructor
  · intro hy
    exact hsubset hy
  · intro hy
    have hy' : y = c := by
      simpa using hy
    subst hy'
    exact hc

lemma mutualMajorityCriterion_implies_majorityLoserCriterion (f : VotingRule)
    (hf : MutualMajorityCriterion f) : MajorityLoserCriterion f := by
  intro V A _ _ P c hmaj hne
  classical
  have hsubset : f P ⊆ (Finset.univ.erase c) := by
    apply hf (P := P) (S := votersBottom P c) (T := Finset.univ.erase c) hmaj
    · rcases hne with ⟨d, hd⟩
      exact ⟨d, by simp [hd]⟩
    intro v hv a ha b hb
    have hv_bottom : BottomRank P v c := (Finset.mem_filter.mp hv).2
    have ha_ne : a ≠ c := (Finset.mem_erase.mp ha).1
    have hb_eq : b = c := by
      by_contra hb_ne
      exact hb (Finset.mem_erase.mpr ⟨hb_ne, by simp⟩)
    subst hb_eq
    exact hv_bottom a ha_ne
  intro hc
  have hc' : c ∈ Finset.univ.erase c := hsubset hc
  have hc_ne : c ≠ c := (Finset.mem_erase.mp hc').1
  exact hc_ne rfl

end SocialChoice
