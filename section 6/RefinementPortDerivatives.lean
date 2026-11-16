import «section 6».RefinementPortHomeomorphisms
import «section 6».RetainedUnaryHomeChains

/-! Retaining additional old labels preserves actual total derivatives.
The projection of a full RV refinement has identity total derivative,
so every generic unit derivative of a base map ports to the refinement. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open Classical FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}

theorem retainedRVOutput_derivative (hc : CanonicalStructure.IsCanonical (M := M))
    (f : Map A B) (p : A) (L : (Fin n → VF M) →ₗ[VF M] (Fin n → VF M))
    (h : HasMixedVFDerivativeAt f p L) : HasMixedVFDerivativeAt (retainedRVOutput hc f) p L := by
  obtain ⟨F,⟨ρ,hρ⟩,hD⟩ := h
  refine ⟨F,⟨ρ,fun x hx => ?_⟩,hD⟩
  obtain ⟨hxA,hFx⟩ := hρ x hx
  refine ⟨hxA,?_⟩
  have hValue := congrArg (fun q : Mixed M n s => (q.1,Fin.append q.2 p.val.2)) hFx
  change (retainedRVOutput hc f ⟨(x,p.val.2),hxA⟩).val=(F x,(retainedRVOutput hc f p).val.2)
  simpa only [retainedRVOutput_value] using hValue

theorem RVRefinementFrame.oldMap_unit_derivative
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (X : RVRefinementFrame A) (p : X.base) : HasMixedUnitDerivativeAt X.oldMap p := by
  obtain ⟨ρ,hρ⟩ := exists_vfBall_subset_nhds hv p.val.1
    ((X.proper.clopen_fibres hv p.val.2).isOpen.mem_nhds p.property)
  obtain ⟨L,hL,hDet⟩ := hasUnitJacobianAt_id p.val.1
  refine ⟨L,⟨id,⟨ρ,fun x hx => ⟨hρ hx,?_⟩⟩,(hasDerivativeAt_iff_companion _ _ _).mp hL⟩,hDet⟩
  rfl

theorem retainedRVOutput_unit_derivative
    {B : DefSet (rawMixedSpace (M := M) n s) S}
    (hc : CanonicalStructure.IsCanonical (M := M)) (f : Map A B) (p : A)
    (h : HasMixedUnitDerivativeAt f p) : HasMixedUnitDerivativeAt (retainedRVOutput hc f) p := by
  obtain ⟨L,hL,hDet⟩ := h
  exact ⟨L,retainedRVOutput_derivative hc f p L hL,hDet⟩

theorem RVRefinementFrame.port_generic_unit
    {B : DefSet (rawMixedSpace (M := M) n s) S}
    (hc : CanonicalStructure.IsCanonical (M := M))
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (X : RVRefinementFrame A) (f : Map A B)
    (hUnit : ∀ p : A,AlgebraicIndependent (vfParameterField S) p.val.1 → HasMixedUnitDerivativeAt f p)
    (p : X.base) (hInd : AlgebraicIndependent (vfParameterField S) p.val.1) :
    HasMixedUnitDerivativeAt (X.portMap hc f) p := by
  have hOld : HasMixedUnitDerivativeAt X.oldMap p := X.oldMap_unit_derivative hv p
  have hInput : X.oldMap p=X.oldPoint p := Subtype.ext rfl
  have hF : HasMixedUnitDerivativeAt f (X.oldMap p) := by
    rw [hInput]
    exact hUnit (X.oldPoint p) hInd
  have hComp : HasMixedUnitDerivativeAt (f.comp X.oldMap) p := hF.comp hOld
  exact retainedRVOutput_unit_derivative hc (f.comp X.oldMap) p hComp

theorem RVRefinementFrame.port_relative
    {B : DefSet (rawMixedSpace (M := M) n s) S}
    (hc : CanonicalStructure.IsCanonical (M := M)) (X : RVRefinementFrame A) (f : Map A B) (j : Fin n)
    (hRelative : ∀ p : A,∀ i,i ≠ j → (f p).val.1 i=p.val.1 i)
    (p : X.base) (i : Fin n) (hi : i ≠ j) : (X.portMap hc f p).val.1 i=p.val.1 i :=
  hRelative (X.oldPoint p) i hi

end DiamondIntegral.Section6
