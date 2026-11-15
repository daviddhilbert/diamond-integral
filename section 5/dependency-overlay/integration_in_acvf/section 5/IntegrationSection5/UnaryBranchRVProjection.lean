import IntegrationSection5.UnaryBranchProjection
import IntegrationSection5.FixedVFRVIso
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
variable {S : Set M} {m b : ℕ}
variable {R H : DefSet (M := M) S 1 m} {B : DefSet (M := M) S 1 b}
variable {u : SpecialBijection (coordinateCanonicalImage R 0) B}
variable {E : Set (Fin m → RV (M := M))} {previous : Option Bool}
namespace CanonicalUnaryBranchExtension

def activeProjectionMap (C : CanonicalUnaryBranchExtension (G := G) u H E previous) : Map C.active_image B :=
  Map.mk C.activeProjection (Map.graph_definable (activeUnaryProjectionMap 0 C.projection C.active_image))

theorem activeProjection_sameRV_iff (C : CanonicalUnaryBranchExtension (G := G) u H E previous)
    (p q : C.active_image) : SameRV (C.activeProjectionMap p).val (C.activeProjectionMap q).val ↔ SameRV p.val q.val := by
  constructor
  · intro he
    obtain ⟨hv,hl⟩ := (sameRV_iff _ _).mp he
    apply (sameRV_iff _ _).mpr
    refine ⟨fun i => ?_,?_⟩
    · fin_cases i
      exact hv 0
    · funext j
      obtain ⟨k,rfl⟩ := C.projection_surjective j
      exact congrFun hl k
  · exact activeUnaryProjection_sameRV 0 C.projection

theorem activeProjection_inverse_contractible (C : CanonicalUnaryBranchExtension (G := G) u H E previous) :
    Contractible (Map.inverse C.activeProjectionMap C.activeProjection_bijective) := by
  intro p q he
  apply (C.activeProjection_sameRV_iff _ _).mp
  rw [Map.apply_inverse,Map.apply_inverse]
  exact he

def activeRVIso (C : CanonicalUnaryBranchExtension (G := G) u H E previous) :
    GammaRVIso G (pullbackObject C.active_image) (pullbackObject B) :=
  fixedVFRVIso C.activeProjectionMap C.activeProjection_bijective
    (fun p q h => (C.activeProjection_sameRV_iff p q).mpr h) C.activeProjection_inverse_contractible
    C.activeProjectionIso.graph (fun p i => by fin_cases i; rfl)

theorem activeRVIso_square (C : CanonicalUnaryBranchExtension (G := G) u H E previous) (p : C.active_image) :
    rvIsoHomMap C.activeRVIso.iso (Map.toImage (rawKeyMap C.active_image) p) =
      Map.toImage (rawKeyMap B) (C.activeProjectionMap p) :=
  fixedVFRVIso_square C.activeProjectionMap C.activeProjection_bijective
    (fun p q h => (C.activeProjection_sameRV_iff p q).mpr h) C.activeProjection_inverse_contractible
    C.activeProjectionIso.graph (fun p i => by fin_cases i; rfl) p

end CanonicalUnaryBranchExtension
end IntegrationInACVF.Section5
