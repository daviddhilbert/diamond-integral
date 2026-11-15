import IntegrationSection5.CoordinateCanonicalFibre
import IntegrationSection5.GammaGraphOperations
import Section5.GammaLift

/-! Complete original-Gamma graphs for one-coordinate canonical maps. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)} {S : Set M} {n m : ℕ}

theorem gamma_coordinateCanonical_graph (A : DefSet (M := M) S n m)
    (hA : GammaSetDefinable G (carrier A)) (i : Fin n) :
    GammaGraphDefinable G (pointMapGraph (coordinateCanonicalBijection A i)) := by
  let U := PresentedSet.univ (pointSpace (M := M) n m) G.real
  apply GammaGraphDefinable.congr ((gammaLogicInput G).restrict_graph hA
    ((gammaLogicInput G).real_map_graph (coordinateCanonicalMap U i)))
  intro p q
  constructor
  · rintro ⟨hp,a,ha,hq⟩
    exact ⟨⟨p,hp⟩,rfl,(congrArg (coordinateCanonical i) ha).symm.trans hq⟩
  · rintro ⟨a,ha,hq⟩
    exact ⟨ha ▸ a.property,⟨a.val,Set.mem_univ _⟩,ha,hq⟩

def coordinateCanonicalGammaIso (A : DefSet (M := M) S n m)
    (hA : GammaSetDefinable G (carrier A)) (i : Fin n) :
    GammaIso G (carrier A) (carrier (coordinateCanonicalImage A i)) where
  equiv := Equiv.ofBijective (coordinateCanonicalBijection A i) (coordinateCanonicalBijection_bijective A i)
  graph := gamma_coordinateCanonical_graph A hA i

theorem gamma_coordinateCanonicalImage (A : DefSet (M := M) S n m)
    (hA : GammaSetDefinable G (carrier A)) (i : Fin n) :
    GammaSetDefinable G (carrier (coordinateCanonicalImage A i)) :=
  (coordinateCanonicalGammaIso A hA i).target_definable (gammaLogicInput G)

end IntegrationInACVF.Section5
