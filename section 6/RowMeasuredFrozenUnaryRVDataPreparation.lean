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
import «section 6».RowMeasuredUnaryContextSteps
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
import «section 6».RowMeasuredProtectedUnaryDataFreezing
import «section 6».RowMeasuredUnaryValueContextPreparation

/-! (Row-form version for Remark 6.20, translated from `MeasuredFrozenUnaryRVDataPreparation`.)
 The complete RV-data preparation used before fibrewise fusion.
The relation may have unbounded RV output. Finite freezing is constructed
over the original base, with the current ambient and every protected
piece's product condition; its unary preparation has an actual ambient
lift fixing all other VF coordinates. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {qR : ℕ} [NeZero qR]
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r q m k l : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem measured_frozen_unary_rv_data_preparation_row
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V,iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V,x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A : DefSet (rawMixedSpace (M := M) 1 r) S)
    (hA : ProperInvariant S A.carrier) (hAD : VFDoublyBounded A.carrier) (hARV : IsRVPullback A.carrier)
    (hTag : ∀ p ∈ A.carrier,∀ z ∈ A.carrier,p.2=z.2 → tupleRV M p.1=tupleRV M z.1)
    (C : Fin k → DefSet (rawMixedSpace (M := M) 1 r) S)
    (hCA : ∀ i,(C i).carrier ⊆ A.carrier) (hC : ∀ i,ProperInvariant S (C i).carrier)
    {j : Fin m} (X : UnaryPreparationContext A j)
    (P : Fin l → DefSet (rawMixedSpace (M := M) m X.arity) S)
    (hPX : ∀ i,(P i).carrier ⊆ X.source.carrier) (hP : ∀ i,ProperInvariant S (P i).carrier)
    (θ : RowFormOn X.source qR)
    (hLevels : ∀ u γ,IsOpen {x : Fin m → VF M | (x,u) ∈ X.source.carrier ∧ rowFormExtension θ (x,u)=γ})
    (D : DefSet (rawMixedSpace (M := M) 1 (r+q)) S) :
    ∃ F : FMT.FocusFreezingData A,∃ s : ℕ,∃ B : DefSet (rawMixedSpace (M := M) 1 s) S,∃ f : Map A B,
      SynchronizedCentripetalChain (G := G) (Fin k) A B f C ∧
      ProperInvariant S B.carrier ∧ VFDoublyBounded B.carrier ∧ IsRVPullback B.carrier ∧
      (∀ p ∈ B.carrier,∀ z ∈ B.carrier,p.2=z.2 → tupleRV M p.1=tupleRV M z.1) ∧
      (∀ i,SpecialCovariantChain (G := G) (C i) (f.restrict (hCA i)).image (f.restrict (hCA i)).toImage ∧
        IsRVPullback (f.restrict (hCA i)).image.carrier) ∧
      ∃ U : UnaryContextLift (G := G) X f P,
      FormCompatibleSynchronizedChainRow (G := G) (Fin l) X.source U.target.source U.map P θ ∧
      (∀ E : F.balls,FMT.CoordinateProductDomain X.source.carrier (FMT.vfOpenBall E.val) (F.centers E) j) ∧
      (∀ i,∀ E : F.balls,FMT.CoordinateProductDomain (P i).carrier (FMT.vfOpenBall E.val) (F.centers E) j) ∧
      (∀ i,∀ E : F.balls,FMT.CoordinateProductDomain (C i).carrier (FMT.vfOpenBall E.val) (F.centers E) 0) ∧
      (∀ γ,∀ E : F.balls,FMT.CoordinateProductDomain
        {p | p ∈ X.source.carrier ∧ rowFormExtension θ p=γ} (FMT.vfOpenBall E.val) (F.centers E) j) ∧
      (∀ p z : A,(f p).val.2=(f z).val.2 →
        FMT.frozenUnaryValue F.balls F.centers (unaryRVDataRow D) p.val=
          FMT.frozenUnaryValue F.balls F.centers (unaryRVDataRow D) z.val) := by
  obtain ⟨Q,hQ,hQControl⟩ := exists_unary_obstacles hc hv D
  obtain ⟨R,hR,hRControl⟩ := exists_finite_unary_obstacles hc hv C
  let U := Q ∪ R
  have hU : S.Definable₁ LRV (Subtype.val '' (U : Set (VF M))) := by
    change S.Definable₁ LRV (Subtype.val '' ((Q ∪ R : Finset (VF M)) : Set (VF M)))
    rw [Finset.coe_union,Set.image_union]
    exact hQ.union hR
  have hUC (i : Fin k) : UnaryObstacleControl (G := G) U (C i).carrier := by
    intro a ρ hAvoid x hx y hy u
    exact hRControl i a ρ (fun z hz => hAvoid z (Finset.mem_union_right Q hz)) x hx y hy u
  have hValue : ∀ a ρ,(∀ z ∈ U,z ∉ Balls.openDisc Valued.v a ρ) →
      ∀ x ∈ Balls.openDisc Valued.v a ρ,∀ y ∈ Balls.openDisc Valued.v a ρ,
      ∀ u,unaryRVDataRow D ((fun _ : Fin 1 => x),u)=unaryRVDataRow D ((fun _ : Fin 1 => y),u) := by
    intro a ρ hAvoid x hx y hy u
    apply Set.ext
    intro t
    exact hQControl a ρ (fun z hz => hAvoid z (Finset.mem_union_left R hz)) x hx y hy (Fin.append u t)
  let PP : Fin (l+1) → DefSet (rawMixedSpace (M := M) m X.arity) S := Fin.cons X.source P
  have hPP : ∀ i,ProperInvariant S (PP i).carrier := Fin.cases X.proper hP
  obtain ⟨F,ρ,hρ,hProdC,hProdP,hProdLevels,hConst,hControlValue⟩ := exists_measured_protected_unary_data_freezing_row
    h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt A hA C hC PP hPP j U hU X.source X.proper θ hLevels (unaryRVDataRow D) hValue
  let roots := UnaryRootFamily.fromObstacles A U hU
  have hBound (u) : (roots.fibre u).card ≤ U.card := by
    apply Finset.card_le_card
    intro x hx
    exact ((roots.mem_fibre u x).mp hx).2
  have hControl (i) : UnaryRootControl (G := G) roots (C i).carrier :=
    UnaryRootFamily.fromObstacles_control U hU _ (hUC i)
  obtain ⟨s,B,f,η,hChain,hB,hBD,hBRV,hBTag,hPieces,H,hPhi,hTransport,hConstant⟩ :=
    UnaryRootFamily.exists_value_prepared_form_compatible_context_process_of_bound_row
      h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt U.card A roots hA hAD hARV hTag hBound
      ρ hρ (FMT.frozenUnaryValue F.balls F.centers (unaryRVDataRow D)) ∅ hConst hControlValue
      C hCA hC hControl X P hPX hP θ hLevels
  refine ⟨F,s,B,f,hChain,hB,hBD,hBRV,hBTag,hPieces,H,hPhi,hProdP 0,
    (fun i => hProdP i.succ),hProdC,hProdLevels,?_⟩
  intro p z he
  exact (hTransport p).symm.trans
    ((hConstant (f p).val (f p).property (f z).val (f z).property he).trans (hTransport z))

end DiamondIntegral.Section6
