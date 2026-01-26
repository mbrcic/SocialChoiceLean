import SocialChoice.Profile
import SocialChoice.Meta
import SocialChoice.Axioms.Pareto
import SocialChoice.Axioms.Unanimity
import SocialChoice.Axioms.Majority
import SocialChoice.Axioms.Condorcet
import SocialChoice.Axioms.Independence
import SocialChoice.Axioms.InformationalBasis
import SocialChoice.Axioms.Anonymity
import SocialChoice.Axioms.Reinforcement
import SocialChoice.Axioms.Reversal
import SocialChoice.Axioms.Participation

namespace SocialChoice

lemma not_mem_liftWinners_of_not_pred {A : Type} {p : A → Prop} [DecidablePred p]
    {s : Finset {a : A // p a}} {c : A} (hc : ¬ p c) :
    c ∉ liftWinners s := by
  classical
  intro hc'
  rcases Finset.mem_image.mp hc' with ⟨x, hx, hxc⟩
  have : p c := by
    simpa [hxc] using x.property
  exact hc this

theorem independenceOfDominated_implies_paretoEfficiency :
    Implies IndependenceOfDominated ParetoEfficiency := by
  intro f _ hInd V A _ _ _ P c d hpref
  classical
  letI : DecidableEq A := Classical.decEq A
  have hEq := hInd (P := P) (c := c) (d := d) hpref
  have hnot :
      d ∉ liftWinners (f (restrictCandidates P (fun a => a ≠ d))) :=
    not_mem_liftWinners_of_not_pred (p := fun a => a ≠ d)
      (s := f (restrictCandidates P (fun a => a ≠ d))) (by simp)
  simpa [hEq] using hnot

theorem independenceOfDominated_implies_independenceOfUniversallyLeastPreferred :
    Implies IndependenceOfDominated IndependenceOfUniversallyLeastPreferred := by
  intro f _ hInd V A _ _ _ _ P c d hcd hbot
  exact hInd (P := P) (c := c) (d := d) (fun v => hbot v c hcd)

theorem paretoEfficiency_implies_unanimity :
    Implies ParetoEfficiency Unanimity := by
  intro f hf hPar V A _ _ _ P c htop
  classical
  let _ : Nonempty A := ⟨c⟩
  have hsubset : f P ⊆ ({c} : Finset A) := by
    intro x hx
    by_contra hxne
    have hxne' : x ≠ c := by
      simpa using hxne
    have hxnot : x ∉ f P := by
      have hpref : ∀ v : V, Prefers P v c x := by
        intro v
        exact htop v x hxne'
      exact hPar (P := P) (c := c) (d := x) hpref
    exact hxnot hx
  have hnonempty : (f P).Nonempty := hf P
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

theorem mutualMajorityCriterion_implies_majorityCriterion_Imp :
    Implies MutualMajorityCriterion MajorityCriterion := by
  intro f hf hmut
  exact mutualMajorityCriterion_implies_majorityCriterion f hmut hf

theorem mutualMajorityCriterion_implies_majorityLoserCriterion_Imp :
    Implies MutualMajorityCriterion MajorityLoserCriterion := by
  intro f _ hmut
  exact mutualMajorityCriterion_implies_majorityLoserCriterion f hmut

theorem majorityCriterion_implies_unanimity :
    Implies MajorityCriterion Unanimity := by
  intro f hf hmaj V A _ _ _ P c htop
  classical
  have htop_set : votersTop P c = Finset.univ := by
    ext v
    constructor
    · intro hv
      exact Finset.mem_univ v
    · intro hv
      exact Finset.mem_filter.mpr ⟨hv, htop v⟩
  have hmaj' : StrictMajority (votersTop P c) := by
    have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ‹Nonempty V›
    have hlt : Fintype.card V < 2 * Fintype.card V := by
      have hlt' : Fintype.card V < Fintype.card V + Fintype.card V :=
        Nat.lt_add_of_pos_right (n := Fintype.card V) (k := Fintype.card V) hpos
      simpa [Nat.two_mul] using hlt'
    simpa [StrictMajority, htop_set] using hlt
  exact hmaj P c hmaj'

theorem condorcetConsistency_implies_majorityCriterion :
    Implies CondorcetConsistency MajorityCriterion := by
  intro f _ hcond V A _ _ P c hmaj
  classical
  have hcw : CondorcetWinner P c := by
    intro d hne
    have hsubset : votersTop P c ⊆ votersPreferring P c d := by
      intro v hv
      have hv_top : TopRank P v c := (Finset.mem_filter.mp hv).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ v, hv_top d hne⟩
    have hle : (votersTop P c).card ≤ (votersPreferring P c d).card :=
      Finset.card_le_card hsubset
    have hlt : Fintype.card V < 2 * (votersTop P c).card := by
      simpa [StrictMajority] using hmaj
    have hle' : 2 * (votersTop P c).card ≤ 2 * (votersPreferring P c d).card :=
      Nat.mul_le_mul_left 2 hle
    have hlt' : Fintype.card V < 2 * (votersPreferring P c d).card :=
      Nat.lt_of_lt_of_le hlt hle'
    simpa [StrictMajority] using hlt'
  exact hcond P c hcw

theorem condorcetLoserCriterion_implies_majorityLoserCriterion :
    Implies CondorcetLoserCriterion MajorityLoserCriterion := by
  intro f _ hcond V A _ _ P c hmaj hne
  classical
  have hloser : CondorcetLoser P c := by
    refine ⟨?_, hne⟩
    intro d hdc
    have hsubset : votersBottom P c ⊆ votersPreferring P d c := by
      intro v hv
      have hv_bottom : BottomRank P v c := (Finset.mem_filter.mp hv).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ v, hv_bottom d hdc⟩
    have hle : (votersBottom P c).card ≤ (votersPreferring P d c).card :=
      Finset.card_le_card hsubset
    have hlt : Fintype.card V < 2 * (votersBottom P c).card := by
      simp [StrictMajority] at hmaj
      exact hmaj
    have hle' : 2 * (votersBottom P c).card ≤ 2 * (votersPreferring P d c).card :=
      Nat.mul_le_mul_left 2 hle
    have hlt' : Fintype.card V < 2 * (votersPreferring P d c).card :=
      Nat.lt_of_lt_of_le hlt hle'
    simpa [StrictMajority] using hlt'
  exact hcond P c hloser

theorem reversalSymmetry_implies_singletonReversalSymmetry :
    Implies ReversalSymmetry SingletonReversalSymmetry := by
  intro f _ hrev V A _ _ P x hnontriv hx
  classical
  letI : DecidableEq A := Classical.decEq A
  have hnot_univ : f P ≠ (Finset.univ : Finset A) := by
    rcases hnontriv with ⟨y, hy⟩
    intro hEq
    have hy_mem : y ∈ f P := by
      simp [hEq]
    have hy' : y = x := by
      simp [hx] at hy_mem
      exact hy_mem
    exact hy hy'.symm
  have hdisj := hrev (P := P) hnot_univ
  have hxmem : x ∈ f P := by
    simp [hx]
  intro hxrev
  have hxinter : x ∈ f P ∩ f (reverse_profile P) := by
    exact Finset.mem_inter.mpr ⟨hxmem, hxrev⟩
  have : x ∈ (∅ : Finset A) := by
    rw [hdisj] at hxinter
    exact hxinter
  simp at this

theorem reinforcement_implies_subsetReinforcement :
    Implies Reinforcement SubsetReinforcement := by
  intro f _ href
  exact reinforcement_subset (f := f) href

theorem marginBased_implies_anonymity :
    Implies MarginBased Anonymity := by
  intro f _ hmargin V A _ _ P σ
  classical
  apply hmargin (P₁ := permuteVoters P σ) (P₂ := P)
  intro x y
  simp

theorem topsOnly_implies_anonymity :
    Implies TopsOnly Anonymity := by
  intro f _ htops V A _ _ P σ
  classical
  apply htops (P₁ := permuteVoters P σ) (P₂ := P)
  intro a
  simp

theorem strongFishburnParticipation_implies_positiveInvolvement :
    Implies StrongFishburnParticipation PositiveInvolvement := by
  intro f hf hpart U A _ _ V u hu P Q c hagree hc htop
  classical
  let r := Q.pref (newVoter (u := u) (V := V) hu)
  letI : LinearOrder A := r
  have hfish : FishburnWeak r (f Q) (f P) := by
    simpa [StrongFishburnParticipation, StrongParticipation, FishburnExtension, r] using
      (hpart (V := V) (u := u) hu P Q hagree)
  by_contra hcQ
  let _ : Nonempty A := ⟨c⟩
  have hneQ : (f Q).Nonempty := hf Q
  rcases hneQ with ⟨x, hx⟩
  have hxne : x ≠ c := by
    intro hxc
    exact hcQ (by simpa [hxc] using hx)
  have hcs : c ∈ f P \ f Q := by
    exact Finset.mem_sdiff.mpr ⟨hc, hcQ⟩
  obtain ⟨h1, h2, h3⟩ := hfish
  have hle : r.le x c := by
    by_cases hxP : x ∈ f P
    · have hxst : x ∈ f Q ∩ f P := Finset.mem_inter.mpr ⟨hx, hxP⟩
      exact h2 x hxst c hcs
    · have hxst : x ∈ f Q \ f P := Finset.mem_sdiff.mpr ⟨hx, hxP⟩
      exact h3 x hxst c hcs
  have hlt : r.lt c x := htop x hxne
  exact (not_le_of_gt hlt) hle

theorem strongFishburnParticipation_implies_negativeInvolvement :
    Implies StrongFishburnParticipation NegativeInvolvement := by
  intro f hf hpart U A _ _ V u hu P Q c hagree hc hbot
  classical
  let r := Q.pref (newVoter (u := u) (V := V) hu)
  letI : LinearOrder A := r
  have hfish : FishburnWeak r (f Q) (f P) := by
    simpa [StrongFishburnParticipation, StrongParticipation, FishburnExtension, r] using
      (hpart (V := V) (u := u) hu P Q hagree)
  by_contra hcQ
  have hcQ' : c ∈ f Q := by
    simpa using hcQ
  let _ : Nonempty A := ⟨c⟩
  have hneP : (f P).Nonempty := hf P
  rcases hneP with ⟨x, hx⟩
  have hxne : x ≠ c := by
    intro hxc
    exact hc (by simpa [hxc] using hx)
  have hcs : c ∈ f Q \ f P := by
    exact Finset.mem_sdiff.mpr ⟨hcQ', hc⟩
  obtain ⟨h1, h2, h3⟩ := hfish
  have hle : r.le c x := by
    by_cases hxQ : x ∈ f Q
    · have hxst : x ∈ f Q ∩ f P := Finset.mem_inter.mpr ⟨hxQ, hx⟩
      exact h1 c hcs x hxst
    · have hxst : x ∈ f P \ f Q := Finset.mem_sdiff.mpr ⟨hx, hxQ⟩
      exact h3 c hcs x hxst
  have hlt : r.lt x c := hbot x hxne
  exact (not_le_of_gt hlt) hle

end SocialChoice
