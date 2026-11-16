import «section 6».FullFocusCovarianceData

/-! Complete focus graphs restrict to protected proper pieces. Once
their common canonical radius preserves a piece, every other component
condition is inherited from the ambient graph. -/

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

def FullFocusGraphData.restrict (F : FullFocusGraphData (G := G) A)
    (hPA : P.carrier ⊆ A.carrier) (hP : ProperInvariant S P.carrier) :
    FullFocusGraphData (G := G) P where
  coordinate := F.coordinate
  activeTags := F.activeTags
  map := F.map.restrict (fun _ hp => ⟨hPA hp.1,hp.2⟩)
  independent p q hu ho := F.independent ⟨p.val,hPA p.property.1,p.property.2⟩
    ⟨q.val,hPA q.property.1,q.property.2⟩ hu ho
  proper := hP
  doublyBounded := by
    obtain ⟨γ,hγ⟩ := F.doublyBounded
    exact ⟨γ,fun p hp i => hγ p (hPA hp) i⟩
  tagged p hp q hq hu := F.tagged p (hPA hp) q (hPA hq) hu
  continuous u := by
    let g : vfFibre (focusActive P F.activeTags).carrier u →
        vfFibre (focusActive A F.activeTags).carrier u :=
      fun p => ⟨p.val,hPA p.property.1,p.property.2⟩
    have hg : Continuous g := continuous_subtype_val.subtype_mk
      (fun p => ⟨hPA p.property.1,p.property.2⟩)
    exact (F.continuous u).comp hg
  leadingTerm p := F.leadingTerm ⟨p.val,hPA p.property.1,p.property.2⟩

def FullFocusCovarianceData.restrict {F : FullFocusGraphData (G := G) A}
    (C : FullFocusCovarianceData F) (hPA : P.carrier ⊆ A.carrier)
    (hP : ProperInvariant S P.carrier)
    (hInv : ∀ u ∈ F.activeTags.carrier,
      AlphaInvariant (fun i => if i=F.coordinate then C.activeRadius u else C.complementaryRadius)
        (vfFibre P.carrier u)) : FullFocusCovarianceData (F.restrict hPA hP) where
  coefficient := C.coefficient
  coefficient_nonzero := C.coefficient_nonzero
  coefficient_nonnegative := C.coefficient_nonnegative
  coefficient_definable := C.coefficient_definable
  activeRadius := C.activeRadius
  activeNamed := C.activeNamed
  complementaryRadius := C.complementaryRadius
  complementaryNamed := C.complementaryNamed
  invariant := hInv
  covariance u hu a ha b hb hab := C.covariance u hu a (hPA ha) b (hPA hb) hab
  aperture u hu a ha := C.aperture u hu a (hPA ha)

theorem FullFocusCovarianceData.restrict_compatible {F : FullFocusGraphData (G := G) A}
    (C : FullFocusCovarianceData F) (hPA : P.carrier ⊆ A.carrier)
    (hP : ProperInvariant S P.carrier)
    (hInv : ∀ u ∈ F.activeTags.carrier,
      AlphaInvariant (fun i => if i=F.coordinate then C.activeRadius u else C.complementaryRadius)
        (vfFibre P.carrier u)) :
    ApertureRestrictionData C.component (C.restrict hPA hP hInv).component := by
  refine ⟨hPA,rfl,rfl,fun p hp => ?_⟩
  by_cases hu : p.2 ∈ F.activeTags.carrier
  · rw [(C.restrict hPA hP hInv).component.extendedFocus_active hp hu,
      C.component.extendedFocus_active (hPA hp) hu]
    exact ((F.restrict hPA hP).focus_at ⟨p,hp,hu⟩).trans
      (F.focus_at ⟨p,hPA hp,hu⟩).symm
  · rw [(C.restrict hPA hP hInv).component.extendedFocus_inactive hu,
      C.component.extendedFocus_inactive hu]

end DiamondIntegral.Section6
