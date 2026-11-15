import IntegrationSection5.CanonicalUnaryBranchExtension
import IntegrationSection5.GammaFiniteCoordinates
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

def activeProjection (C : CanonicalUnaryBranchExtension (G := G) u H E previous) :
    C.active_image → B := fun p => ⟨activeUnaryProjection 0 C.projection p.val,C.active_projection_mem p.val p.property⟩

theorem activeProjection_bijective (C : CanonicalUnaryBranchExtension (G := G) u H E previous) :
    Function.Bijective C.activeProjection := by
  constructor
  · intro p q he
    have hv := congrArg (fun z : B => z.val) he
    apply Subtype.ext
    apply Prod.ext
    · funext i
      fin_cases i
      exact congrArg (fun z : Point (M := M) 1 b => vfAt z 0) hv
    · funext j
      obtain ⟨k,rfl⟩ := C.projection_surjective j
      exact congrFun (congrArg (fun z : Point (M := M) 1 b => z.2) hv) k
  · intro b
    obtain ⟨p,hp⟩ := C.active_projection_surjective b
    exact ⟨p,Subtype.ext hp⟩

def activeProjectionIso (C : CanonicalUnaryBranchExtension (G := G) u H E previous) :
    GammaIso G (carrier C.active_image) (carrier B) where
  equiv := Equiv.ofBijective C.activeProjection C.activeProjection_bijective
  graph := by
    let X := PresentedSet.univ (pointSpace (M := M) 1 C.arity) G.real
    apply GammaGraphDefinable.congr ((gammaLogicInput G).restrict_graph C.active_gamma
      ((gammaLogicInput G).real_map_graph (activeUnaryProjectionMap 0 C.projection X)))
    intro p q
    constructor
    · rintro ⟨hp,a,ha,hq⟩
      exact ⟨⟨p,hp⟩,rfl,(congrArg (activeUnaryProjection 0 C.projection) ha).symm.trans hq⟩
    · rintro ⟨p,hp,hq⟩
      exact ⟨hp ▸ p.property,⟨p.val,Set.mem_univ _⟩,hp,hq⟩

theorem activeProjectionIso_vf (C : CanonicalUnaryBranchExtension (G := G) u H E previous)
    (p : C.active_image) : vfAt (C.activeProjectionIso.equiv p).val 0 = vfAt p.val 0 := rfl

end CanonicalUnaryBranchExtension
end IntegrationInACVF.Section5
