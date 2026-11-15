import IntegrationSection5.RelativeSpecialRestriction
import IntegrationSection5.GammaOrderedContraction
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section5.pointSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : SpecialTransformations.Section3.GammaParameters.Base (M := M)}
variable {S : Set M} {n m l : ℕ}
variable {X : DefSet (M := M) S n m} {Y : DefSet (M := M) S n l}

theorem gamma_restrictPointMap (f : Map X Y) (A : DefSet (M := M) S n m)
    (hAX : carrier A ⊆ carrier X) (hA : GammaSetDefinable G (carrier A))
    (hf : GammaGraphDefinable G (pointMapGraph f)) :
    GammaGraphDefinable G (pointMapGraph (restrictPointMap f A hAX)) := by
  apply GammaGraphDefinable.congr ((gammaLogicInput G).restrict_graph hA hf)
  intro p q
  constructor
  · rintro ⟨hp,a,ha,hq⟩
    have he : (⟨p,hAX hp⟩ : X) = a := Subtype.ext ha.symm
    exact ⟨⟨p,hp⟩,rfl,(congrArg (fun x : X => (f x).val) he).trans hq⟩
  · rintro ⟨a,ha,hq⟩
    exact ⟨ha ▸ a.property,⟨a.val,hAX a.property⟩,ha,hq⟩

theorem gamma_restrictPointImage (f : Map X Y) (A : DefSet (M := M) S n m)
    (hAX : carrier A ⊆ carrier X) (hA : GammaSetDefinable G (carrier A))
    (hf : GammaGraphDefinable G (pointMapGraph f)) :
    GammaSetDefinable G (carrier (restrictPointImage f A hAX)) := by
  have h := (gammaLogicInput G).image_graph (gamma_restrictPointMap f A hAX hA hf)
  have he : {q | ∃ p, pointMapGraph (restrictPointMap f A hAX) p q} =
      carrier (restrictPointImage f A hAX) := by
    ext q
    constructor
    · rintro ⟨p,a,rfl,hq⟩
      exact ⟨a,hq⟩
    · rintro ⟨a,hq⟩
      exact ⟨a.val,a,rfl,hq⟩
  exact he ▸ h

theorem restrictPointMap_surjective (f : Map X Y) (A : DefSet (M := M) S n m)
    (hAX : carrier A ⊆ carrier X) : Function.Surjective (restrictPointMap f A hAX) := by
  rintro ⟨q,a,ha⟩
  exact ⟨a,Subtype.ext ha⟩

end IntegrationInACVF.Section5
