import IntegrationSection5.GammaRVPredicateChain
import IntegrationSection5.GammaIsoCoordinates
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
variable {S : Set M} {n m : ℕ}

theorem empty_set_definable : SetDefinable (pointSpace (M := M) n m) S ∅ :=
  @SpecialTransformations.DefinableGeometry.Space.definable_empty LRV M
    (@CanonicalStructure.normalize M sM) (pointSpace n m) S

namespace Focus
variable {H : DefSet (M := M) S n m}

def empty (i : Fin n) (k : Fin m) (hTag : Tagged (carrier H) i k) :
    SpecialTransformations.Section5.Focus H i k where
  tagged := hTag
  locus := ∅
  locus_pullback := (isRVPullback_iff _).mpr (by intro p hp; exact hp.elim)
  locus_subset := Set.empty_subset _
  center := fun _ => 0
  independent := by intro p hp; exact hp.2.elim
  center_mem := by intro p hp; exact hp.2.elim
  locus_definable := empty_set_definable
  center_graph := by
    have h := SetDefinable.left_relation (pointSpace (M := M) n m)
      (SpecialTransformations.Section4.vfSpace 1) (empty_set_definable (M := M) (S := S) (n := n) (m := m))
    apply RelationDefinable.congr _ _ h
    intro p z
    simp only [Set.mem_empty_iff_false,Set.mem_inter_iff,and_false,false_and]

theorem empty_eta (i : Fin n) (k : Fin m) (hTag : Tagged (carrier H) i k)
    (p : Point (M := M) n m) : (empty i k hTag).toFocusGeometry.eta p = p := by
  simp only [FocusGeometry.eta,empty,Set.mem_empty_iff_false,ite_false]

theorem empty_image (i : Fin n) (k : Fin m) (hTag : Tagged (carrier H) i k) :
    carrier (empty i k hTag).etaImage = carrier H := by
  ext p
  constructor
  · rintro ⟨a,ha⟩
    have he : (empty i k hTag).toFocusGeometry.eta a.val = p := ha
    rw [empty_eta] at he
    exact he ▸ a.property
  · intro hp
    exact ⟨⟨p,hp⟩,empty_eta i k hTag p⟩

theorem empty_gamma {G : SpecialTransformations.Section3.GammaParameters.Base (M := M)}
    (i : Fin n) (k : Fin m) (hTag : Tagged (carrier H) i k) :
    GammaFocusDefinable G (empty i k hTag) := by
  have hE : GammaSetDefinable G (∅ : Set (Point (M := M) n m)) :=
    (gammaLogicInput G).real_set _ empty_set_definable
  refine ⟨hE,?_⟩
  apply GammaGraphDefinable.congr (gamma_set_coordinate_scalar_graph _ hE i)
  intro p q
  constructor
  · rintro ⟨a,_,_⟩
    exact a.property.elim
  · rintro ⟨hp,_⟩
    exact hp.2.elim

end Focus
end IntegrationInACVF.Section5
