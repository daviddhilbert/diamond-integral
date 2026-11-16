import «section 6».AmbientCoreMatching
import «section 6».NamedCenterCorePreparation

/-! Actual paired ambient core preparations for separated source and
target center labels. The core map is the literal original bijection;
the whole ambient preparations and both complementary branches remain. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r s : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S} {B : DefSet (rawMixedSpace (M := M) 1 s) S}

structure PairedAmbientCorePreparation (f : Map A B)
    (E : DefSet (rawMixedSpace (M := M) 1 r) S) (hEA : E.carrier ⊆ A.carrier) where
  sourceFocus : UnaryFocusData A
  targetFocus : UnaryFocusData B
  sourceOffset : Map (focusActive A sourceFocus.activeTags) (DefSet.univ (rawVFSpace (M := M) 1) S)
  targetOffset : Map (focusActive B targetFocus.activeTags) (DefSet.univ (rawVFSpace (M := M) 1) S)
  sourcePrep : AmbientCorePreparation (G := G) sourceFocus sourceOffset
  targetPrep : AmbientCorePreparation (G := G) targetFocus targetOffset
  coreMap : Map (sourceFocus.offsetCoreDomain sourceOffset) (targetFocus.offsetCoreDomain targetOffset)
  coreBijective : Function.Bijective coreMap
  wholeCoreFibres : MapsWholeTagFibres coreMap
  coreCommutes : ∀ p : sourceFocus.offsetCoreDomain sourceOffset,
    (coreMap p).val=(f ⟨p.val,sourceFocus.offsetCoreDomain_subset sourceOffset p.property⟩).val
  paired : ∀ p : A,p.val ∈ (sourceFocus.offsetCoreDomain sourceOffset).carrier ↔
    (f p).val ∈ (targetFocus.offsetCoreDomain targetOffset).carrier
  centers : ∀ p : E,p.val ∈ (sourceFocus.offsetCoreDomain sourceOffset).carrier ∧
    (f ⟨p.val,hEA p.property⟩).val ∈ (targetFocus.offsetCoreDomain targetOffset).carrier

theorem paired_ambient_core_preparation_of_small_offsets
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V,iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V,x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (f : Map A B) (hf : Function.Bijective f)
    (hA : ProperInvariant S A.carrier) (hAD : VFDoublyBounded A.carrier) (hARV : IsRVPullback A.carrier)
    (hATag : ∀ p ∈ A.carrier,∀ q ∈ A.carrier,p.2=q.2 → tupleRV M p.1=tupleRV M q.1)
    (hB : ProperInvariant S B.carrier) (hBD : VFDoublyBounded B.carrier) (hBRV : IsRVPullback B.carrier)
    (hBTag : ∀ p ∈ B.carrier,∀ q ∈ B.carrier,p.2=q.2 → tupleRV M p.1=tupleRV M q.1)
    (E : DefSet (rawMixedSpace (M := M) 1 r) S) (hEA : E.carrier ⊆ A.carrier)
    (hUS : ∀ p q : E,p.val.2=q.val.2 → p=q)
    (hUT : ∀ p q : E,(f ⟨p.val,hEA p.property⟩).val.2=(f ⟨q.val,hEA q.property⟩).val.2 → p=q)
    (α β : Gamma M) (D : UniformFinitePairedCores f E hEA α β)
    (hSmallS : ∀ p : E,vfValue (p.val.1 0) < vfValue ((D.sourceOffset p).val 0))
    (hSmallT : ∀ p : E,vfValue ((f ⟨p.val,hEA p.property⟩).val.1 0) < vfValue ((D.targetOffset p).val 0)) :
    Nonempty (PairedAmbientCorePreparation (G := G) f E hEA) := by
  let E' := matchedCenterImage f E hEA
  let eMap := matchedTargetOffsetMap f E hEA hf.injective D.targetOffset
  have hE'B : E'.carrier ⊆ B.carrier := matchedCenterImage_subset f E hEA
  have hU' : ∀ p q : E',p.val.2=q.val.2 → p=q := by
    intro p q he
    obtain ⟨a,ha⟩ := (matchedCenterMap_bijective f E hEA hf.injective).surjective p
    obtain ⟨b,hb⟩ := (matchedCenterMap_bijective f E hEA hf.injective).surjective q
    subst p
    subst q
    exact congrArg (matchedCenterMap f E hEA) (hUT a b he)
  let F := unaryLabelCenterFocusData E hUS hEA hA hAD hATag
  let H := unaryLabelCenterFocusData E' hU' hE'B hB hBD hBTag
  let d := unaryLabelScalar E hUS D.sourceOffset
  let e := unaryLabelScalar E' hU' eMap
  let ds := unaryAmbientScalarMap E hUS D.sourceOffset (A := A)
  let et := unaryAmbientScalarMap E' hU' eMap (A := B)
  have hSmallT' (p : E') : vfValue (p.val.1 0) < vfValue ((eMap p).val 0) := by
    obtain ⟨a,ha⟩ := (matchedCenterMap_bijective f E hEA hf.injective).surjective p
    subst p
    simpa only [eMap,matchedTargetOffsetMap_at,matchedCenterMap_value] using hSmallT a
  obtain ⟨FS⟩ := F.exists_ambient_core_preparation d ds (unaryAmbientScalarMap_value E hUS D.sourceOffset)
    hARV (unaryLabelCenterFocusData_centers E hUS hEA hA hAD hATag)
    (unaryLabelScalar_nonzero E hUS D.sourceOffset D.sourceNonzero)
    (unaryLabelScalar_small E hUS D.sourceOffset hSmallS)
    h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt
  obtain ⟨HT⟩ := H.exists_ambient_core_preparation e et (unaryAmbientScalarMap_value E' hU' eMap)
    hBRV (unaryLabelCenterFocusData_centers E' hU' hE'B hB hBD hBTag)
    (unaryLabelScalar_nonzero E' hU' eMap (matchedTargetOffsetMap_nonzero f E hEA hf.injective D.targetOffset D.targetNonzero))
    (unaryLabelScalar_small E' hU' eMap hSmallT')
    h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt
  have hCS : (F.offsetCoreDomain ds).carrier=D.sourceCoreSet :=
    (D.sourceCoreSet_eq_labelled hUS hA hAD hATag).symm
  have hCT : (H.offsetCoreDomain et).carrier=D.targetCoreSet :=
    (D.targetCoreSet_eq_labelled hf.injective hU' hB hBD hBTag).symm
  obtain ⟨g,hg,hWhole,hCommutes⟩ := exists_paired_core_matching hf D hCS hCT hUS hUT
  have hPaired (p : A) : p.val ∈ (F.offsetCoreDomain ds).carrier ↔ (f p).val ∈ (H.offsetCoreDomain et).carrier := by
    rw [hCS,hCT]
    exact D.source_core_iff_target hf.injective p
  refine ⟨{
    sourceFocus := F
    targetFocus := H
    sourceOffset := ds
    targetOffset := et
    sourcePrep := FS
    targetPrep := HT
    coreMap := g
    coreBijective := hg
    wholeCoreFibres := hWhole
    coreCommutes := fun p => (hCommutes p).choose_spec
    paired := hPaired
    centers := ?_ }⟩
  intro p
  have hCenter : p.val ∈ (F.offsetCoreDomain ds).carrier := by
    rw [hCS]
    refine ⟨hEA p.property,p,rfl,?_⟩
    rw [sub_self]
    exact gamma_lt_value_zero (finiteValue ((D.sourceOffset p).val 0) (D.sourceNonzero p))
  exact ⟨hCenter,(hPaired ⟨p.val,hEA p.property⟩).mp hCenter⟩

end DiamondIntegral.Section6
