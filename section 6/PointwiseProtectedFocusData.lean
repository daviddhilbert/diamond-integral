import «section 6».PointwiseFocusCovariance
import «section 6».FullFocusRestrictions

/-! Pointwise source tests reconstruct every protected restriction of
the same component, with its actual focus, coefficient and aperture
compatibility retained. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A P : DefSet (rawMixedSpace (M := M) n r) S}

def PointwiseFocusCovariance.restrict {F : FullFocusGraphData (G := G) A}
    (C : PointwiseFocusCovariance F) (hPA : P.carrier ⊆ A.carrier) (hP : ProperInvariant S P.carrier)
    (hMove : ∀ p : focusActive P F.activeTags,∀ b : Fin n → VF M,
      (∀ i,(if i=F.coordinate then vfValue (C.coefficient*(F.map ⟨p.val,hPA p.property.1,p.property.2⟩).val 0)
        else C.radius.val)<vfValue (p.val.1 i-b i)) → (b,p.val.2) ∈ P.carrier) :
    PointwiseFocusCovariance (F.restrict hPA hP) where
  coefficient := C.coefficient
  nonzero := C.nonzero
  nonnegative := C.nonnegative
  coefficient_named := C.coefficient_named
  radius := C.radius
  radius_named := C.radius_named
  source := hMove
  focus p q hu hab := C.focus ⟨p.val,hPA p.property.1,p.property.2⟩
    ⟨q.val,hPA q.property.1,q.property.2⟩ hu hab

theorem PointwiseFocusCovariance.restrict_compatible
    (hc : CanonicalStructure.IsCanonical (M := M)) {F : FullFocusGraphData (G := G) A}
    (C : PointwiseFocusCovariance F) (hPA : P.carrier ⊆ A.carrier) (hP : ProperInvariant S P.carrier)
    (hMove : ∀ p : focusActive P F.activeTags,∀ b : Fin n → VF M,
      (∀ i,(if i=F.coordinate then vfValue (C.coefficient*(F.map ⟨p.val,hPA p.property.1,p.property.2⟩).val 0)
        else C.radius.val)<vfValue (p.val.1 i-b i)) → (b,p.val.2) ∈ P.carrier) :
    ApertureRestrictionData (C.fullData hc).component ((C.restrict hPA hP hMove).fullData hc).component := by
  refine ⟨hPA,rfl,rfl,fun p hp => ?_⟩
  by_cases hu : p.2 ∈ F.activeTags.carrier
  · rw [((C.restrict hPA hP hMove).fullData hc).component.extendedFocus_active hp hu,
      (C.fullData hc).component.extendedFocus_active (hPA hp) hu]
    exact ((F.restrict hPA hP).focus_at ⟨p,hp,hu⟩).trans (F.focus_at ⟨p,hPA hp,hu⟩).symm
  · rw [((C.restrict hPA hP hMove).fullData hc).component.extendedFocus_inactive hu,
      (C.fullData hc).component.extendedFocus_inactive hu]

end DiamondIntegral.Section6
