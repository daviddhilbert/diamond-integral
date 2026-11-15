import IntegrationSection5.FiniteStandardContractionData
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section5.pointSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)} {S : Set M} {n m : ℕ}
variable {A : DefSet (M := M) S n m} {σ : Equiv.Perm (Fin n)}

namespace StandardContraction

def nativeToNormalizedLiftIso (hGS : G.real ⊆ S) (C : StandardContraction A σ)
    (hA : GammaSetDefinable G (carrier A)) (hC : GammaProgramDefinable G C.program) :
    GammaIso G (carrier (rawLift C.contractionObject)) (carrier (rawLift C.normalizedObject)) :=
  ((C.gammaNaturalLiftIso hGS hA hC).symm (gammaLogicInput G)).trans (gammaLogicInput G)
    (C.gammaNormalizedLiftIso hGS hA hC)

theorem nativeToNormalizedLiftIso_natural (hGS : G.real ⊆ S) (C : StandardContraction A σ)
    (hA : GammaSetDefinable G (carrier A)) (hC : GammaProgramDefinable G C.program) (a : A) :
    (C.nativeToNormalizedLiftIso hGS hA hC).equiv (C.naturalLiftMap a) = C.normalizedNaturalLiftMap a := by
  change C.normalizedNaturalLiftMap ((Equiv.ofBijective C.naturalLiftMap C.naturalLiftMap_bijective).symm (C.naturalLiftMap a)) = _
  exact congrArg C.normalizedNaturalLiftMap ((Equiv.ofBijective C.naturalLiftMap C.naturalLiftMap_bijective).symm_apply_apply a)

theorem nativeToNormalizedLiftIso_apply (hGS : G.real ⊆ S) (C : StandardContraction A σ)
    (hA : GammaSetDefinable G (carrier A)) (hC : GammaProgramDefinable G C.program)
    (p : {q : Point (M := M) n C.arity // q ∈ carrier (rawLift C.contractionObject)}) :
    ((C.nativeToNormalizedLiftIso hGS hA hC).equiv p).val = canonical p.val := by
  obtain ⟨a,rfl⟩ := C.naturalLiftMap_bijective.2 p
  rw [nativeToNormalizedLiftIso_natural]
  rfl

theorem nativeLift_rv_index (C : StandardContraction A σ)
    (p : {q : Point (M := M) n C.arity // q ∈ carrier (rawLift C.contractionObject)}) (i : Fin n) :
    rv (vfAt p.val i) = p.val.2 (C.volumeIndex i) := by
  obtain ⟨u,hu,hvol⟩ := p.property
  have hi := congrFun hvol i
  change u.val (C.volumeIndex i) =
    @SpecialTransformations.Section4.tupleRV M (@CanonicalStructure.normalize M sM)
      (CanonicalStructure.normalized_model hM) n p.val.1 i at hi
  rw [normalized_tupleRV] at hi
  exact hi.symm.trans (congrFun hu (C.volumeIndex i))

end StandardContraction

structure NormalizedStandardSpecialPresentation (G : GammaParameters.Base (M := M)) (C : StandardContraction A σ)
    extends StandardSpecialPresentation G C where
  normalizedTargetChart : GammaIso G (carrier target) (carrier (rawLift C.normalizedObject))
  normalized_target_projection : ∀ p : target, (normalizedTargetChart.equiv p).val =
    fullRVProjection (targetProjection ∘ prependVolumeIndex C.volumeIndex) p.val
  normalized_square : ∀ p : source, normalizedTargetChart.equiv (special.toMap p) =
    C.normalizedNaturalLiftMap (sourceChart.equiv p)

def StandardSpecialPresentation.normalized (hGS : G.real ⊆ S) (C : StandardContraction A σ)
    (hA : GammaSetDefinable G (carrier A)) (hC : GammaProgramDefinable G C.program)
    (P : StandardSpecialPresentation G C) : NormalizedStandardSpecialPresentation G C where
  toStandardSpecialPresentation := P
  normalizedTargetChart := P.targetChart.trans (gammaLogicInput G) (C.nativeToNormalizedLiftIso hGS hA hC)
  normalized_target_projection p := by
    let x := P.targetChart.equiv p
    have hv : x.val.1 = p.val.1 := congrArg Prod.fst (P.target_chart_projection p)
    have hr : x.val.2 = p.val.2 ∘ P.targetProjection := congrArg Prod.snd (P.target_chart_projection p)
    change ((C.nativeToNormalizedLiftIso hGS hA hC).equiv x).val = _
    rw [C.nativeToNormalizedLiftIso_apply hGS hA hC x]
    refine Prod.ext hv ?_
    funext j
    cases j using Fin.addCases with
    | left i =>
      simpa only [canonical_new,fullRVProjection,Function.comp_apply,prependVolumeIndex,Fin.addCases_left,vfAt] using
        (C.nativeLift_rv_index x i).trans (congrFun hr (C.volumeIndex i))
    | right j =>
      simpa only [canonical_old,fullRVProjection,Function.comp_apply,prependVolumeIndex,Fin.addCases_right,id_eq] using congrFun hr j
  normalized_square p :=
    (congrArg (C.nativeToNormalizedLiftIso hGS hA hC).equiv (P.square p)).trans
      (C.nativeToNormalizedLiftIso_natural hGS hA hC (P.sourceChart.equiv p))

def FiniteStandardContractionData.normalizedSpecialPresentation
    {G : GammaParameters.Base (M := M)} {n m : ℕ} {A : Set (Point (M := M) n m)}
    {σ : Equiv.Perm (Fin n)} (D : FiniteStandardContractionData G A σ) :
    NormalizedStandardSpecialPresentation G D.contraction :=
  StandardSpecialPresentation.normalized D.real_contains D.contraction D.source_gamma D.program_gamma D.special_presentation

end IntegrationInACVF.Section5
