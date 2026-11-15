import IntegrationSection5.HeadUnaryCompletion
import IntegrationSection5.GammaOrderedContraction
import Section5.GammaGraphs

/-! Complete original-Gamma certification of the constructed two-stage
program, across its internal presentation identifications. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)} {S R : Set M} {n m l : ℕ}

theorem gamma_extendPointMap {A : DefSet (M := M) S n m} {B : DefSet (M := M) S n l}
    (f : Map A B) (hSR : S ⊆ R) (hf : GammaGraphDefinable G (pointMapGraph f)) :
    GammaGraphDefinable G (pointMapGraph (extendPointMap f hSR)) := by
  apply GammaGraphDefinable.congr hf
  intro p q
  constructor
  · rintro ⟨a,ha,hq⟩
    exact ⟨⟨a.val,a.property⟩,ha,hq⟩
  · rintro ⟨a,ha,hq⟩
    exact ⟨⟨a.val,a.property⟩,ha,hq⟩

theorem gamma_headCompletionTail {A : DefSet (M := M) S 2 m} (T : HeadPreparation A)
    (hSR : S ⊆ R) {U : DefSet (M := M) R 1 (1+T.arity)} {V : DefSet (M := M) R 1 l}
    (hU : carrier U = carrier T.contractedSet) (Q : SpecialBijection U V)
    (hQ : GammaGraphDefinable G (pointMapGraph Q.toMap)) :
    GammaGraphDefinable G (pointMapGraph (headCompletionTail T hSR hU Q).toMap) := by
  apply GammaGraphDefinable.congr hQ
  intro p q
  have hEq : U = (T.extendBase hSR).contractedSet :=
    PresentedSet.eq_of_carrier_eq (hU.trans (T.extendBase_contractedSet hSR).symm)
  constructor
  · rintro ⟨a,ha,hq⟩
    have ha' : a.val ∈ carrier (T.extendBase hSR).contractedSet := by
      rw [← hEq]
      exact a.property
    refine ⟨⟨a.val,ha'⟩,ha,?_⟩
    change ((specialCastBoth Q hEq rfl).toMap ⟨a.val,ha'⟩).val = q
    rw [specialCastBoth_val]
    exact hq
  · rintro ⟨a,ha,hq⟩
    have ha' : a.val ∈ carrier U := by
      rw [hEq]
      exact a.property
    refine ⟨⟨a.val,ha'⟩,ha,?_⟩
    change ((specialCastBoth Q hEq rfl).toMap a).val = q at hq
    rw [specialCastBoth_val] at hq
    exact hq

theorem gamma_headUnaryCompletion {A : DefSet (M := M) S 2 m} (T : HeadPreparation A)
    (hSR : S ⊆ R) {U : DefSet (M := M) R 1 (1+T.arity)} {V : DefSet (M := M) R 1 l}
    (hU : carrier U = carrier T.contractedSet) (Q : SpecialBijection U V)
    (hV : IsRVPullback (carrier V))
    (hT : GammaGraphDefinable G (pointMapGraph T.map))
    (hTarget : GammaSetDefinable G (carrier T.target))
    (hQ : GammaGraphDefinable G (pointMapGraph Q.toMap))
    (hVG : GammaSetDefinable G (carrier V)) :
    GammaProgramDefinable G (headUnaryCompletion T hSR hU Q hV) :=
  ⟨gamma_extendPointMap T.map hSR hT,hTarget,
    gamma_headCompletionTail T hSR hU Q hQ,hVG,gamma_headImage V hVG⟩

end IntegrationInACVF.Section5
