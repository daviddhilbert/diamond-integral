import «section 6».RowBinaryMeasuredRootTermination
import «section 6».RowCarriedFormRootControl
import «section 6».RowCarriedGammaForms
import «section 6».RowCoordinateCoreFormConstancy
import «section 6».RowCoordinateFormRootControl
import «section 6».RowCoordinateGammaDescent
import «section 6».RowCoordinateGammaLevelProjection
import «section 6».RowCoordinateGammaObstacles
import «section 6».RowCoordinateMeasuredObstacles
import «section 6».RowCoreFormCompatibility
import «section 6».RowCoreGammaForms
import «section 6».RowExactGammaTransport
import «section 6».RowFormCompatibleFocusSteps
import «section 6».RowFormCompatibleSynchronizedChains
import «section 6».RowForms
import «section 6».RowFrozenFormRootControl
import «section 6».RowGammaCodeLocus
import «section 6».RowGammaFormBounds
import «section 6».RowGammaFormFreezing
import «section 6».RowGammaFormUniformFibres
import «section 6».RowGammaTransitionParameterLoci
import «section 6».RowGammaTransitionSemantics
import «section 6».RowMeasuredCentripetalProgramTemplates
import «section 6».RowMeasuredContinuousCoordinateRootStep
import «section 6».RowMeasuredContinuousFocusRealization
import «section 6».RowMeasuredCoordinatePreparationData
import «section 6».RowMeasuredProgramSubstitution
import «section 6».RowMeasuredProjectedFreezing
import «section 6».RowMeasuredProtectedUnaryDataFreezing
import «section 6».RowMeasuredUnaryContextSteps
import «section 6».RowMeasuredUnaryValueContextPreparation
import «section 6».RowMeasuredUnaryValueContextStep
import «section 6».RowReleasedGammaForms
import «section 6».RowReleasedGammaLevelGeometry
import «section 6».RowSpecialGammaTransport
import «section 6».RowTransportedGammaLevels
import «section 6».RowUnaryCoreFormConstancy
import «section 6».RowUnaryFormControlStep
import «section 6».RowUnaryFormRootControl
import «section 6».RowUnaryGammaObstacles
import «section 6».RowUnaryMeasuredCompatibleExistence
import «section 6».RowUnaryMeasuredCompatiblePreparation
import «section 6».RowUnaryMeasuredFocusStep
import «section 6».RowUnaryMeasuredObstacles
import «section 6».RowUnaryMeasuredPreparationData
import «section 6».RowUnaryMeasuredRootIteration
import «section 6».FrozenUnaryRVTemplatePreparation
import «section 6».RowMeasuredFrozenUnaryRVDataPreparation

/-! (Row-form version for Remark 6.20, translated from `MeasuredFrozenUnaryRVTemplatePreparation`.)
 Actual finite freezing and unary preparation of a complete RV
family, with its ambient lift and every protected product check. Its
exact row constancy is expressed in the original template parameters. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 13000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {qR : ℕ} [NeZero qR]
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r q m k l : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

structure MeasuredUnaryRVTemplateFreezeCertificateRow
    (A : DefSet (rawMixedSpace (M := M) 1 r) S)
    (C : Fin k → DefSet (rawMixedSpace (M := M) 1 r) S) (hCA : ∀ i,(C i).carrier ⊆ A.carrier)
    {j : Fin m} (X : UnaryPreparationContext A j)
    (P : Fin l → DefSet (rawMixedSpace (M := M) m X.arity) S)
    (V : RVSetParameterTemplate (M := M) S 1 q)
    (θ : RowFormOn X.source qR) where
  freezing : FMT.FocusFreezingData A
  arity : ℕ
  target : DefSet (rawMixedSpace (M := M) 1 arity) S
  map : Map A target
  chain : SynchronizedCentripetalChain (G := G) (Fin k) A target map C
  proper : ProperInvariant S target.carrier
  doublyBounded : VFDoublyBounded target.carrier
  pullback : IsRVPullback target.carrier
  tagged : ∀ p ∈ target.carrier,∀ z ∈ target.carrier,p.2=z.2 → tupleRV M p.1=tupleRV M z.1
  pieces : ∀ i,SpecialCovariantChain (G := G) (C i) (map.restrict (hCA i)).image (map.restrict (hCA i)).toImage ∧
    IsRVPullback (map.restrict (hCA i)).image.carrier
  lift : UnaryContextLift (G := G) X map P
  formCompatible : FormCompatibleSynchronizedChainRow (G := G) (Fin l) X.source lift.target.source lift.map P θ
  formProducts : ∀ γ,∀ E : freezing.balls,FMT.CoordinateProductDomain
    {p | p ∈ X.source.carrier ∧ rowFormExtension θ p=γ} (FMT.vfOpenBall E.val) (freezing.centers E) j
  ambientProduct : ∀ E : freezing.balls,FMT.CoordinateProductDomain X.source.carrier
    (FMT.vfOpenBall E.val) (freezing.centers E) j
  protectedProducts : ∀ i,∀ E : freezing.balls,FMT.CoordinateProductDomain (P i).carrier
    (FMT.vfOpenBall E.val) (freezing.centers E) j
  unaryProducts : ∀ i,∀ E : freezing.balls,FMT.CoordinateProductDomain (C i).carrier
    (FMT.vfOpenBall E.val) (freezing.centers E) 0
  data : ∀ p z : A,(map p).val.2=(map z).val.2 →
    (V.fibre (fun _ => (FMT.vfFamilyFreeze freezing.balls freezing.centers (p.val.1 0)).val)).carrier=
      (V.fibre (fun _ => (FMT.vfFamilyFreeze freezing.balls freezing.centers (z.val.1 0)).val)).carrier

def MeasuredUnaryRVTemplateFreezeCertificateRow.forget
    {A : DefSet (rawMixedSpace (M := M) 1 r) S}
    {C : Fin k → DefSet (rawMixedSpace (M := M) 1 r) S} {hCA : ∀ i,(C i).carrier ⊆ A.carrier}
    {j : Fin m} {X : UnaryPreparationContext A j}
    {P : Fin l → DefSet (rawMixedSpace (M := M) m X.arity) S}
    {V : RVSetParameterTemplate (M := M) S 1 q}
    {θ : RowFormOn X.source qR}
    (F : MeasuredUnaryRVTemplateFreezeCertificateRow (G := G) A C hCA X P V θ) :
    UnaryRVTemplateFreezeCertificate (G := G) A C hCA X P V := {
  freezing := F.freezing
  arity := F.arity
  target := F.target
  map := F.map
  chain := F.chain
  proper := F.proper
  doublyBounded := F.doublyBounded
  pullback := F.pullback
  tagged := F.tagged
  pieces := F.pieces
  lift := ⟨F.lift⟩
  ambientProduct := F.ambientProduct
  protectedProducts := F.protectedProducts
  unaryProducts := F.unaryProducts
  data := F.data }

theorem measured_frozen_unary_rv_template_preparation_row
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (W : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hW : ∀ a ∈ W,iVF a) (hWS : W ⊆ S) (hSW : S ⊆ algebraicClosureSet W)
    (hnt : ∃ x : vfAlgebraicClosureField W,x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A : DefSet (rawMixedSpace (M := M) 1 r) S)
    (hA : ProperInvariant S A.carrier) (hAD : VFDoublyBounded A.carrier) (hARV : IsRVPullback A.carrier)
    (hTag : ∀ p ∈ A.carrier,∀ z ∈ A.carrier,p.2=z.2 → tupleRV M p.1=tupleRV M z.1)
    (C : Fin k → DefSet (rawMixedSpace (M := M) 1 r) S)
    (hCA : ∀ i,(C i).carrier ⊆ A.carrier) (hC : ∀ i,ProperInvariant S (C i).carrier)
    {j : Fin m} (X : UnaryPreparationContext A j)
    (P : Fin l → DefSet (rawMixedSpace (M := M) m X.arity) S)
    (hPX : ∀ i,(P i).carrier ⊆ X.source.carrier) (hP : ∀ i,ProperInvariant S (P i).carrier)
    (V : RVSetParameterTemplate (M := M) S 1 q)
    (θ : RowFormOn X.source qR)
    (hLevels : ∀ u γ,IsOpen {x : Fin m → VF M | (x,u) ∈ X.source.carrier ∧ rowFormExtension θ (x,u)=γ}) :
    Nonempty (MeasuredUnaryRVTemplateFreezeCertificateRow (G := G) A C hCA X P V θ) := by
  obtain ⟨F,s,B,f,hChain,hB,hBD,hBRV,hBTag,hPieces,H,hPhi,hProdX,hProdP,hProdC,hProdLevels,hData⟩ :=
    measured_frozen_unary_rv_data_preparation_row h00 hc linear hκ hs hv W hsmall hΓ hW hWS hSW hnt
      A hA hAD hARV hTag C hCA hC X P hPX hP θ hLevels (unaryRVTemplateRelation V r)
  refine ⟨⟨F,s,B,f,hChain,hB,hBD,hBRV,hBTag,hPieces,H,hPhi,hProdLevels,hProdX,hProdP,hProdC,?_⟩⟩
  intro p z he
  have h := hData p z he
  rwa [frozenUnaryRVTemplateRelation_row,frozenUnaryRVTemplateRelation_row] at h

end DiamondIntegral.Section6
