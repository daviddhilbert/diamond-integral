import «section 6».FullFocusGraphData

/-! Reconstruct permitted components from complete focus graphs and
canonical covariance data. The reconstruction retains the actual
original-base focus map, so its point map agrees exactly with the old
component when the data came from that component. -/

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
variable {A : DefSet (rawMixedSpace (M := M) n r) S}

structure FullFocusCovarianceData (F : FullFocusGraphData (G := G) A) where
  coefficient : VF M
  coefficient_nonzero : coefficient ≠ 0
  coefficient_nonnegative : (1 : GammaInfinity M) ≤ vfValue coefficient
  coefficient_definable : S.Definable₁ LRV {coefficient.val}
  activeRadius : (Fin r → RVInfinity M) → Gamma M
  activeNamed : ∀ u ∈ F.activeTags.carrier,(S ∪ Set.range (rvValues u)).Definable LRV
    {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {activeRadius u}}
  complementaryRadius : Gamma M
  complementaryNamed : S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {complementaryRadius}}
  invariant : ∀ u ∈ F.activeTags.carrier,
    AlphaInvariant (fun i => if i=F.coordinate then activeRadius u else complementaryRadius) (vfFibre A.carrier u)
  covariance : ∀ (u) (hu : u ∈ F.activeTags.carrier) (a) (ha : a ∈ vfFibre A.carrier u) (b) (hb : b ∈ vfFibre A.carrier u),
    Congruent (fun _ => complementaryRadius) (Function.update a F.coordinate 0) (Function.update b F.coordinate 0) →
      (activeRadius u).val < vfValue ((F.map ⟨(a,u),ha,hu⟩).val 0-
        (F.map ⟨(b,u),hb,hu⟩).val 0)
  aperture : ∀ (u) (hu : u ∈ F.activeTags.carrier) (a) (ha : a ∈ vfFibre A.carrier u),
    (activeRadius u).val ≤ vfValue (coefficient*(F.map ⟨(a,u),ha,hu⟩).val 0)

def FullFocusCovarianceData.component {F : FullFocusGraphData (G := G) A}
    (C : FullFocusCovarianceData F) : CentripetalData (G := G) A where
  coordinate := F.coordinate
  activeTags := F.activeTags
  focus := F.focus
  focusMap := F.map
  focusMap_eq p := (F.focus_at p).symm
  sourceProper := F.proper
  sourceDoublyBounded := F.doublyBounded
  tagged := F.tagged
  continuous := F.focus_continuousOn
  focusRV p hp hu := by
    rw [F.focus_at ⟨p,hp,hu⟩]
    exact F.leadingTerm ⟨p,hp,hu⟩
  coefficient := C.coefficient
  coefficient_nonzero := C.coefficient_nonzero
  coefficient_nonnegative := C.coefficient_nonnegative
  coefficient_definable := C.coefficient_definable
  covariance u hu := by
    refine ⟨C.activeRadius u,(fun _ => C.complementaryRadius),C.activeNamed u hu,
      (fun _ => C.complementaryNamed.mono Set.subset_union_left),C.invariant u hu,?_,?_⟩
    · intro a ha b hb hab
      rw [F.focus_at ⟨(a,u),ha,hu⟩,F.focus_at ⟨(b,u),hb,hu⟩]
      exact C.covariance u hu a ha b hb hab
    · intro a ha
      rw [F.focus_at ⟨(a,u),ha,hu⟩]
      exact C.aperture u hu a ha

theorem CentripetalData.exists_normalized_full_focus_data
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (D : CentripetalData (G := G) A) (hARV : IsRVPullback A.carrier) (j : Fin r)
    (hTag : ∀ p ∈ A.carrier,rv M (p.1 D.coordinate)=p.2 j) :
    ∃ C : FullFocusCovarianceData D.fullFocusGraph,C.coefficient=D.coefficient ∧
      ∀ p : Mixed M n r,C.component.point p=D.point p := by
  obtain ⟨β,hβ,hβ1,hCov⟩ := D.exists_uniform_tagged_covariance h00 hc linear hκ hs hv hsmall hΓ hARV j hTag
  let C : FullFocusCovarianceData D.fullFocusGraph := {
    coefficient := D.coefficient
    coefficient_nonzero := D.coefficient_nonzero
    coefficient_nonnegative := D.coefficient_nonnegative
    coefficient_definable := D.coefficient_definable
    activeRadius := fun u => taggedApertureRadius D.coefficient D.coefficient_nonzero u j
    activeNamed := fun u hu => (hCov u hu).1
    complementaryRadius := β
    complementaryNamed := hβ
    invariant := fun u hu => (hCov u hu).2.2.1
    covariance := ?_
    aperture := ?_ }
  · exact ⟨C,rfl,fun _ => rfl⟩
  · intro u hu a ha b hb hab
    change _ < vfValue ((D.focusMap ⟨(a,u),ha,hu⟩).val 0-(D.focusMap ⟨(b,u),hb,hu⟩).val 0)
    rw [D.focusMap_eq ⟨(a,u),ha,hu⟩,D.focusMap_eq ⟨(b,u),hb,hu⟩]
    exact (hCov u hu).2.2.2.1 a ha b hb hab
  · intro u hu a ha
    change _ ≤ vfValue (D.coefficient*(D.focusMap ⟨(a,u),ha,hu⟩).val 0)
    rw [D.focusMap_eq ⟨(a,u),ha,hu⟩]
    exact (hCov u hu).2.2.2.2 a ha

end DiamondIntegral.Section6
