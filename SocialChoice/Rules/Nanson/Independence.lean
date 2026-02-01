import Mathlib.Tactic
import Mathlib.Tactic.FinCases
import SocialChoice.Axioms.Independence
import SocialChoice.ListBallot
import SocialChoice.Rules.Nanson.Reversal

namespace SocialChoice

open Classical
open Finset

attribute [instance] Classical.decEq Classical.decPred

/-!
## Nanson fails independence of dominated

Counterexample with 3 candidates (0,1,2) and 2 voters:
v0: 1 > 2 > 0
v1: 2 > 0 > 1
Candidate 2 Pareto-dominates 0.
Nanson selects {2}, but after removing 0, Nanson selects {1,2}.
-/

namespace NansonIndependenceCounterexample

abbrev A3 := Fin 3
abbrev a : A3 := 0
abbrev b : A3 := 1
abbrev c : A3 := 2

def ballot120 : ListBallot 3 := ListBallot.mk' [1, 2, 0]
def ballot201 : ListBallot 3 := ListBallot.mk' [2, 0, 1]

def ballots : Fin 2 → ListBallot 3
  | ⟨0, _⟩ => ballot120
  | ⟨1, _⟩ => ballot201

noncomputable def profile : Profile (Fin 2) A3 :=
  profileOfListBallots ballots

lemma prefers_2_0 : ∀ v : Fin 2, Prefers profile v c a := by
  intro v
  fin_cases v <;>
    simp [profile, ballots, prefers_iff_prefersInList, prefersInList] <;> decide

noncomputable def profile' : Profile (Fin 2) {x : A3 // x ≠ a} :=
  restrictProfile profile a

def cand1 : {x : A3 // x ≠ a} := ⟨b, by decide⟩
def cand2 : {x : A3 // x ≠ a} := ⟨c, by decide⟩

lemma votersPreferring_profile_b_c :
    votersPreferring profile b c = ({0} : Finset (Fin 2)) := by
  classical
  ext v
  fin_cases v <;>
    simp [votersPreferring, profile, ballots, prefers_iff_prefersInList, prefersInList] <;>
    decide

lemma votersPreferring_profile_c_b :
    votersPreferring profile c b = ({1} : Finset (Fin 2)) := by
  classical
  ext v
  fin_cases v <;>
    simp [votersPreferring, profile, ballots, prefers_iff_prefersInList, prefersInList] <;>
    decide

lemma votersPreferring_profile_b_a :
    votersPreferring profile b a = ({0} : Finset (Fin 2)) := by
  classical
  ext v
  fin_cases v <;>
    simp [votersPreferring, profile, ballots, prefers_iff_prefersInList, prefersInList] <;>
    decide

lemma votersPreferring_profile_a_b :
    votersPreferring profile a b = ({1} : Finset (Fin 2)) := by
  classical
  ext v
  fin_cases v <;>
    simp [votersPreferring, profile, ballots, prefers_iff_prefersInList, prefersInList] <;>
    decide

lemma votersPreferring_profile_c_a :
    votersPreferring profile c a = ({0, 1} : Finset (Fin 2)) := by
  classical
  ext v
  fin_cases v <;>
    simp [votersPreferring, profile, ballots, prefers_iff_prefersInList, prefersInList] <;>
    decide

lemma votersPreferring_profile_a_c :
    votersPreferring profile a c = (∅ : Finset (Fin 2)) := by
  classical
  ext v
  fin_cases v <;>
    simp [votersPreferring, profile, ballots, prefers_iff_prefersInList, prefersInList] <;>
    decide

lemma margin_profile_b_c : margin profile b c = 0 := by
  have h1 :
      (Finset.univ.filter (fun v => Prefers profile v b c)) = ({0} : Finset (Fin 2)) := by
    simpa [votersPreferring] using votersPreferring_profile_b_c
  have h2 :
      (Finset.univ.filter (fun v => Prefers profile v c b)) = ({1} : Finset (Fin 2)) := by
    simpa [votersPreferring] using votersPreferring_profile_c_b
  simp [margin, h1, h2]

lemma margin_profile_b_a : margin profile b a = 0 := by
  have h1 :
      (Finset.univ.filter (fun v => Prefers profile v b a)) = ({0} : Finset (Fin 2)) := by
    simpa [votersPreferring] using votersPreferring_profile_b_a
  have h2 :
      (Finset.univ.filter (fun v => Prefers profile v a b)) = ({1} : Finset (Fin 2)) := by
    simpa [votersPreferring] using votersPreferring_profile_a_b
  simp [margin, h1, h2]

lemma margin_profile_c_a : margin profile c a = 2 := by
  have h1 :
      (Finset.univ.filter (fun v => Prefers profile v c a)) = ({0, 1} : Finset (Fin 2)) := by
    simpa [votersPreferring] using votersPreferring_profile_c_a
  have h2 :
      (Finset.univ.filter (fun v => Prefers profile v a c)) = (∅ : Finset (Fin 2)) := by
    simpa [votersPreferring] using votersPreferring_profile_a_c
  simp [margin, h1, h2]

lemma margin_profile_c_b : margin profile c b = 0 := by
  have h1 :
      (Finset.univ.filter (fun v => Prefers profile v c b)) = ({1} : Finset (Fin 2)) := by
    simpa [votersPreferring] using votersPreferring_profile_c_b
  have h2 :
      (Finset.univ.filter (fun v => Prefers profile v b c)) = ({0} : Finset (Fin 2)) := by
    simpa [votersPreferring] using votersPreferring_profile_b_c
  simp [margin, h1, h2]

lemma margin_profile_a_b : margin profile a b = 0 := by
  have h := margin_antisymmetric (P := profile) a b
  simpa [margin_profile_b_a] using h

lemma margin_profile_a_c : margin profile a c = -2 := by
  have h := margin_antisymmetric (P := profile) a c
  simpa [margin_profile_c_a] using h

lemma c2Borda_profile_a : c2BordaScore profile a = -2 := by
  simp [c2BordaScore, Fin.sum_univ_three, self_margin_zero, margin_profile_a_b,
    margin_profile_a_c]

lemma c2Borda_profile_b : c2BordaScore profile b = 0 := by
  simp [c2BordaScore, Fin.sum_univ_three, self_margin_zero, margin_profile_b_a,
    margin_profile_b_c]

lemma c2Borda_profile_c : c2BordaScore profile c = 2 := by
  simp [c2BordaScore, Fin.sum_univ_three, self_margin_zero, margin_profile_c_a,
    margin_profile_c_b]

lemma profile_pos_iff (x : A3) : 0 < c2BordaScore profile x ↔ x = c := by
  fin_cases x <;> simp [c2Borda_profile_a, c2Borda_profile_b, c2Borda_profile_c, c]

lemma nanson_profile : nanson profile = ({c} : Finset A3) := by
  classical
  have hnotall : ¬ ∀ x, c2BordaScore profile x = 0 := by
    intro hall
    have := hall c
    linarith [c2Borda_profile_c]
  have hsurv : (Finset.univ.filter (fun x => c2BordaScore profile x > 0)).Nonempty := by
    refine ⟨c, ?_⟩
    simp [c2Borda_profile_c]
  have hsubset : nanson profile ⊆ {c} := by
    intro x hx
    have hxpos : 0 < c2BordaScore profile x :=
      nanson_score_pos_of_mem (P := profile) hnotall hsurv hx
    have hx' : x = c := (profile_pos_iff x).1 hxpos
    simp [hx']
  have hnonempty : (nanson profile).Nonempty := by
    simpa using (nanson_isVotingRule (P := profile))
  rcases hnonempty with ⟨x, hx⟩
  have hx' : x = c := by
    have : x ∈ ({c} : Finset A3) := hsubset hx
    simpa using this
  have hc : c ∈ nanson profile := by
    simp [hx'] at hx
    exact hx
  apply (Finset.eq_singleton_iff_unique_mem).2
  refine ⟨hc, ?_⟩
  intro y hy
  have : y ∈ ({c} : Finset A3) := hsubset hy
  simpa using this

lemma votersPreferring_restrict_cand1 :
    votersPreferring profile' cand1 cand2 = votersPreferring profile b c := by
  classical
  ext v
  simp [profile', votersPreferring, prefers_restrictProfile_iff, cand1, cand2]

lemma votersPreferring_restrict_cand2 :
    votersPreferring profile' cand2 cand1 = votersPreferring profile c b := by
  classical
  ext v
  simp [profile', votersPreferring, prefers_restrictProfile_iff, cand1, cand2]

lemma margin_profile'_cand1_cand2 : margin profile' cand1 cand2 = 0 := by
  have h1 :
      (Finset.univ.filter (fun v => Prefers profile' v cand1 cand2)) =
        ({0} : Finset (Fin 2)) := by
    simpa [votersPreferring] using votersPreferring_restrict_cand1.trans votersPreferring_profile_b_c
  have h2 :
      (Finset.univ.filter (fun v => Prefers profile' v cand2 cand1)) =
        ({1} : Finset (Fin 2)) := by
    simpa [votersPreferring] using votersPreferring_restrict_cand2.trans votersPreferring_profile_c_b
  simp [margin, h1, h2]

lemma margin_profile'_cand2_cand1 : margin profile' cand2 cand1 = 0 := by
  have h := margin_antisymmetric (P := profile') cand2 cand1
  simpa [margin_profile'_cand1_cand2] using h

lemma univ_profile'_eq : (Finset.univ : Finset {x : A3 // x ≠ a}) = {cand1, cand2} := by
  classical
  ext x
  constructor
  · intro _
    rcases x with ⟨x, hxne⟩
    fin_cases x
    · cases hxne rfl
    · simp [cand1, cand2]
    · simp [cand1, cand2]
  · intro hx
    simp at hx
    simp

lemma c2Borda_profile'_cand1 : c2BordaScore profile' cand1 = 0 := by
  classical
  simp [c2BordaScore, univ_profile'_eq, self_margin_zero, margin_profile'_cand1_cand2]

lemma c2Borda_profile'_cand2 : c2BordaScore profile' cand2 = 0 := by
  classical
  simp [c2BordaScore, univ_profile'_eq, self_margin_zero, margin_profile'_cand2_cand1]

lemma nanson_profile' : nanson profile' = (Finset.univ : Finset {x : A3 // x ≠ a}) := by
  classical
  have hall : ∀ x, c2BordaScore profile' x = 0 := by
    intro x
    rcases x with ⟨x, hxne⟩
    fin_cases x
    · cases hxne rfl
    ·
      have hx' : (⟨b, hxne⟩ : {x : A3 // x ≠ a}) = cand1 := by
        apply Subtype.ext
        rfl
      simpa [hx'] using c2Borda_profile'_cand1
    ·
      have hx' : (⟨c, hxne⟩ : {x : A3 // x ≠ a}) = cand2 := by
        apply Subtype.ext
        rfl
      simpa [hx'] using c2Borda_profile'_cand2
  have haux : nansonAux (Fintype.card {x : A3 // x ≠ a}) {x : A3 // x ≠ a} profile' =
      (Finset.univ : Finset {x : A3 // x ≠ a}) := by
    cases hcard : Fintype.card {x : A3 // x ≠ a} with
    | zero =>
        simp [nansonAux]
    | succ n =>
        simp [nansonAux, hall]
  simpa [nanson] using haux

lemma nanson_profile'_has_1 : cand1 ∈ nanson profile' := by
  simp [nanson_profile']

lemma nanson_profile_not_1 : (b : A3) ∉ nanson profile := by
  simp [nanson_profile, b, c]

lemma lift_nanson_profile'_has_1 : (b : A3) ∈ liftWinners (nanson profile') := by
  have h : cand1 ∈ nanson profile' := nanson_profile'_has_1
  simpa [liftWinners, cand1] using h

end NansonIndependenceCounterexample

open NansonIndependenceCounterexample

theorem nanson_not_independenceOfDominated : ¬ IndependenceOfDominated nanson := by
  intro hind
  have hpref : ∀ v : Fin 2, Prefers profile v c a :=
    prefers_2_0
  have hEq := hind (P := profile) (c := c) (d := a) hpref
  have hmem :
      (b : A3) ∈
        liftWinners (nanson (restrictCandidates profile (fun x => x ≠ a))) := by
    simpa [profile', restrictProfile] using lift_nanson_profile'_has_1
  have hmem' : (b : A3) ∈ nanson profile := by
    simpa [hEq] using hmem
  exact (nanson_profile_not_1 hmem').elim

end SocialChoice
