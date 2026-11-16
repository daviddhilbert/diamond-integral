import «section 6».VariableApertureReplacement
import «section 6».CentripetalFocusProjection

/-! An actual whole-label annulus in the new component image is a full
retained-RV coordinate bundle, also for a variable old aperture. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) n r) S}

structure VariableApertureReleaseData (D : CentripetalData (G := G) A)
    (U : DefSet (rawRVSpace (M := M) (n+(1+r))) S)
    (ρ : (Fin r → RVInfinity M) → Gamma M) : Prop where
  labels : ∀ a ∈ A.carrier, (regularize (D.point a)).2 ∈ U.carrier ↔
    a.2 ∈ D.activeTags.carrier ∧
      (ρ a.2).val < vfValue (a.1 D.coordinate-D.extendedFocus a) ∧ D.core a=false
  stable : ∀ a ∈ A.carrier, a.2 ∈ D.activeTags.carrier → ∀ x : VF M,
    (ρ a.2).val < vfValue (a.1 D.coordinate-x) →
      (Function.update a.1 D.coordinate x,a.2) ∈ A.carrier

namespace CentripetalData

def variableReleasedImage (D : CentripetalData (G := G) A)
    (U : DefSet (rawRVSpace (M := M) (n+(1+r))) S) :=
  focusActive (regularizeMap D.map.image).image U

theorem mem_variableReleasedImage (D : CentripetalData (G := G) A)
    (U : DefSet (rawRVSpace (M := M) (n+(1+r))) S) (q : Mixed M n (n+(1+r))) :
    q ∈ (D.variableReleasedImage U).carrier ↔
      ∃ a, a ∈ A.carrier ∧ (regularize (D.point a)).2 ∈ U.carrier ∧
        regularize (D.point a)=q := by
  constructor
  · rintro ⟨⟨p,hp⟩,hqU⟩
    obtain ⟨a,ha⟩ := p.property
    have he : regularize (D.point a.val)=q := (congrArg regularize ha).trans hp
    refine ⟨a.val,a.property,?_,he⟩
    rw [he]
    exact hqU
  · rintro ⟨a,ha,hU,rfl⟩
    exact ⟨⟨D.bijection ⟨a,ha⟩,rfl⟩,hU⟩

theorem variableReleasedImage_bundle
    {B : DefSet (rawMixedSpace (M := M) (n+1) r) S}
    (D : CentripetalData (G := G) B) (hj : D.coordinate=Fin.last n)
    (U : DefSet (rawRVSpace (M := M) ((n+1)+(1+r))) S)
    (ρ : (Fin r → RVInfinity M) → Gamma M) (H : VariableApertureReleaseData D U ρ) :
    (D.variableReleasedImage U).carrier=
      (rvCoordinateBundle (vfDropLast (D.variableReleasedImage U)).image
        (Fin.castAdd (1+r) (Fin.last n))).carrier := by
  apply coordinate_bundle_of_replacement
  · intro q hq
    obtain ⟨a,ha,hU,rfl⟩ := (D.mem_variableReleasedImage U q).mp hq
    simp only [regularize,Fin.append_left]
    rfl
  · intro q hq d hrv
    obtain ⟨a,ha,hU,he⟩ := (D.mem_variableReleasedImage U q).mp hq
    obtain ⟨hu,hOld,hNew⟩ := (H.labels a ha).mp hU
    have hrv' : rv M d=rv M ((D.point a).1 D.coordinate) := by
      rw [hj]
      exact hrv.trans (congrArg (fun p => rv M (p.1 (Fin.last n))) he.symm)
    obtain ⟨b,hb,hTags,hbU,hbOld,hbNew,hPoint⟩ :=
      D.variable_aperture_coordinate_replacement ρ H.stable a ha hu hOld hNew d hrv'
    apply (D.mem_variableReleasedImage U _).mpr
    refine ⟨b,hb,(H.labels b hb).mpr ⟨hbU,hbOld,hbNew⟩,?_⟩
    rw [hPoint,regularize_coordinate_replacement _ _ _ hrv',he,hj]

end CentripetalData
end DiamondIntegral.Section6
