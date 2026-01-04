import SocialChoice.Profile
import SocialChoice.Margin
import SocialChoice.Cycles

namespace SocialChoice

def condorcet_winner {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (x : A) : Prop :=
  ∀ y, x ≠ y → margin_pos P x y

def condorcet_loser {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (x : A) : Prop :=
  (∀ y, x ≠ y → margin_pos P y x) ∧ ∃ y, x ≠ y

def condorcet_criterion (f : VotingRule) : Prop :=
  ∀ {V A : Type} [Fintype V] [Fintype A] (P : Profile V A) (x : A),
    condorcet_winner P x → f P = {x}

def condorcet_loser_criterion (f : VotingRule) : Prop :=
  ∀ {V A : Type} [Fintype V] [Fintype A] (P : Profile V A) (x : A),
    condorcet_loser P x → x ∉ f P

def CondorcetWinner {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (c : A) : Prop :=
  ∀ d : A, d ≠ c → StrictMajority (votersPreferring P c d)

def CondorcetLoser {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (c : A) : Prop :=
  ∀ d : A, d ≠ c → StrictMajority (votersPreferring P d c)

def CondorcetConsistency (f : VotingRule) : Prop :=
  ∀ {V A : Type} [Fintype V] [Fintype A] (P : Profile V A) (c : A),
    CondorcetWinner P c → f P = {c}

def CondorcetLoserAvoidance (f : VotingRule) : Prop :=
  ∀ {V A : Type} [Fintype V] [Fintype A] (P : Profile V A) (c : A),
    CondorcetLoser P c → c ∉ f P

lemma no_margin_pos_cycle_of_condorcet {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (c : A) :
    condorcet_winner P c → ¬ ∃ l, cycle (margin_pos P) l ∧ c ∈ l := by
  intro hw hcyc
  rcases hcyc with ⟨l, hcycle, hwmem⟩
  have hdom := dominate_of_cycle l (margin_pos P) hcycle c hwmem
  rcases hdom with ⟨y, _hy_mem, hyw⟩
  have hne : y ≠ c := by
    intro hEq
    subst hEq
    exact (margin_pos_irrefl (P := P) y) hyw
  have hwy : margin_pos P c y := hw y (by simpa [eq_comm] using hne)
  exact (margin_pos_asymm (P := P) c y hwy) hyw

end SocialChoice
