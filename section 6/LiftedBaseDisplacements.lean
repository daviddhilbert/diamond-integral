import «section 6».RVCoordinateDisplacements
import «section 6».CarriedFiniteChains

/-! The exact final-label displacement certificate is inherited by
the actual unary base lifts and carried lower-dimensional lifts. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s m : ℕ} {I : Type*}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem UnaryContextLift.rv_displacement
    (h00 : M ⊨ Axioms.ACVF00)
    {A : DefSet (rawMixedSpace (M := M) 1 r) S} {B : DefSet (rawMixedSpace (M := M) 1 s) S}
    {i : Fin m} {X : UnaryPreparationContext A i} {f : Map A B}
    {P : I → DefSet (rawMixedSpace (M := M) m X.arity) S}
    (F : UnaryContextLift (G := G) X f P) (H : SpecialCovariantChain (G := G) A B f) :
    RVCoordinateDisplacement F.map i := by
  intro p z he
  have hTags : (f (X.projection p)).val.2=(f (X.projection z)).val.2 := by
    rw [← F.commutes p,← F.commutes z,F.target.projection_value,F.target.projection_value]
    exact congrArg (fun u => u ∘ F.target.labels) he
  have hp := congrArg Subtype.val (F.commutes p)
  have hz := congrArg Subtype.val (F.commutes z)
  rw [F.target.projection_value] at hp hz
  have hpVF := congrArg (fun w : Mixed M 1 s => w.1 0) hp
  have hzVF := congrArg (fun w : Mixed M 1 s => w.1 0) hz
  have h := H.unary_rv_displacement h00 0 (X.projection p) (X.projection z) hTags
  rw [← hpVF,← hzVF,X.projection_value,X.projection_value] at h
  exact h

theorem CarriedChainLift.rv_displacement
    {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
    {f : Map A B} {X : CarriedRefinementFrame A}
    (F : CarriedChainLift (G := G) X f) {i : Fin n} (h : RVCoordinateDisplacement f i) :
    RVCoordinateDisplacement F.map i.castSucc := by
  intro p z he
  have hTags : (f (X.oldPoint p)).val.2=(f (X.oldPoint z)).val.2 := by
    rw [← F.commutes p,← F.commutes z]
    exact congrArg (fun u => u ∘ F.target.labels) he
  have hpVF := congrArg (fun w : Mixed M n s => w.1 i) (F.commutes p)
  have hzVF := congrArg (fun w : Mixed M n s => w.1 i) (F.commutes z)
  have hOld := h (X.oldPoint p) (X.oldPoint z) hTags
  rw [← hpVF,← hzVF] at hOld
  exact hOld

end DiamondIntegral.Section6
