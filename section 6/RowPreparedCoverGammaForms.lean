import «section 6».RowArbitraryCoordinateBranches
import «section 6».RowBinaryMeasuredRootTermination
import «section 6».RowCarriedFormRootControl
import «section 6».RowCarriedGammaForms
import «section 6».RowCoordinateCoreFormConstancy
import «section 6».RowCoordinateFormRootControl
import «section 6».RowCoordinateGammaDescent
import «section 6».RowCoordinateGammaLevelProjection
import «section 6».RowCoordinateGammaObstacles
import «section 6».RowCoordinateMeasuredObstacles
import «section 6».RowExactGammaTransport
import «section 6».RowForms
import «section 6».RowFrozenFormRootControl
import «section 6».RowGammaCodeLocus
import «section 6».RowGammaFormBounds
import «section 6».RowGammaFormUniformFibres
import «section 6».RowMeasuredContinuousCoordinateRootStep
import «section 6».RowMeasuredContinuousFocusRealization
import «section 6».RowMeasuredProjectedFreezing
import «section 6».RowPreparedVariableRelease
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
import «section 6».ArbitraryProperPreparation
import «section 6».RowMeasuredCoordinatePreparationData
import «section 6».TaggedPreparedFamilies

/-! (Row-form version for Remark 6.20, translated from `PreparedCoverGammaForms`.)
 In every VF dimension, preparation of a proper cover makes a Gamma
form contractible when it was already constant on each piece's old-label
fibres. Both the form and all literal protected restrictions are retained. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {qR : ℕ} [NeZero qR]
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem SpecialCovariantChain.transported_gamma_constant_of_prepared_cover_row
    {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
    {f : Map A B} (h : SpecialCovariantChain (G := G) A B f) (h00 : M ⊨ Axioms.ACVF00)
    (C : Fin k → DefSet (rawMixedSpace (M := M) n r) S) (hCA : ∀ i,(C i).carrier ⊆ A.carrier)
    (hCover : ∀ p ∈ A.carrier,∃ i,p ∈ (C i).carrier)
    (hPrepared : ∀ i,IsRVPullback (f.restrict (hCA i)).image.carrier)
    (hTag : ∀ p ∈ B.carrier,∀ q ∈ B.carrier,p.2=q.2 → tupleRV M p.1=tupleRV M q.1)
    (ω : RowFormOn A qR)
    (hConst : ∀ i (p q : C i),p.val.2=q.val.2 →
      ω ⟨p.val,hCA i p.property⟩=ω ⟨q.val,hCA i q.property⟩) :
    ∀ p q : B,p.val.2=q.val.2 →
      (ω.comp (f.inverse (h.bijective h00))) p=(ω.comp (f.inverse (h.bijective h00))) q := by
  obtain ⟨hrs,hRV⟩ := h.retainsRV
  intro p q hpq
  let x := f.inverse (h.bijective h00) p
  let y := f.inverse (h.bijective h00) q
  have hfx : f x=p := Map.apply_inverse f _ p
  have hfy : f y=q := Map.apply_inverse f _ q
  obtain ⟨i,hxi⟩ := hCover x.val x.property
  have hpImage : p.val ∈ (f.restrict (hCA i)).image.carrier := ⟨⟨x.val,hxi⟩,congrArg Subtype.val hfx⟩
  have hqImage := rvPullback_mem_of_sameRV (hPrepared i) hpImage (hTag p.val p.property q.val q.property hpq) hpq
  obtain ⟨z,hz⟩ := hqImage
  have hzy : (⟨z.val,hCA i z.property⟩ : A)=y :=
    (h.bijective h00).injective (Subtype.ext (hz.trans (congrArg Subtype.val hfy).symm))
  have hyi : y.val ∈ (C i).carrier := (congrArg Subtype.val hzy) ▸ z.property
  have hOld : x.val.2=y.val.2 := by
    funext j
    have hx := hRV x j
    have hy := hRV y j
    rw [hfx] at hx
    rw [hfy] at hy
    exact hx.symm.trans ((congrFun hpq (rvTailIndex hrs j)).trans hy)
  exact hConst i ⟨x.val,hxi⟩ ⟨y.val,hyi⟩ hOld

theorem measured_preparation_of_piecewise_old_labels_row
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ x ∈ V,iVF x) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V,x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A : DefSet (rawMixedSpace (M := M) (n+1) r) S)
    (hA : ProperInvariant S A.carrier) (hAD : VFDoublyBounded A.carrier) (hARV : IsRVPullback A.carrier)
    (C : Fin k → DefSet (rawMixedSpace (M := M) (n+1) r) S) (hCA : ∀ i,(C i).carrier ⊆ A.carrier)
    (hC : ∀ i,ProperInvariant S (C i).carrier) (hCover : ∀ p ∈ A.carrier,∃ i,p ∈ (C i).carrier)
    (ω : RowFormOn A qR)
    (hConst : ∀ i (p q : C i),p.val.2=q.val.2 →
      ω ⟨p.val,hCA i p.property⟩=ω ⟨q.val,hCA i q.property⟩) :
    Nonempty (MeasuredCoordinatePreparationRow (G := G) A C hCA ω) := by
  obtain ⟨F⟩ := synchronized_preparation_all_dimensions h00 hc linear hκ hs hv (n+1)
    S V hsmall hΓ hV hVS hSV hnt k r A hA hAD hARV C hCA hC
  let T := F.taggedTarget h00 hc hκ hs hv
  have hTag := F.taggedTarget_tagged h00 hc hκ hs hv
  have hSpecial := T.chain.toChain.toSpecial
  let η := ω.comp (T.map.inverse (hSpecial.bijective h00))
  have hSame := hSpecial.transported_gamma_constant_of_prepared_cover_row h00 C hCA hCover T.prepared hTag ω hConst
  refine ⟨{
    arity := T.arity
    target := T.target
    map := T.map
    special := hSpecial
    proper := T.proper
    doublyBounded := T.doublyBounded
    prepared := T.pullback
    tagged := hTag
    form := η
    transportRow := ?_
    constant := ?_
    pieces := fun i => ⟨(T.chain.atPiece i).literal_restriction h00 (hCA i),T.prepared i⟩ }⟩
  · intro p
    change (ω (T.map.inverse _ (T.map p))).val=(ω p).val
    rw [Map.inverse_apply]
  · intro p hp q hq he
    rw [rowFormExtension_at η ⟨p,hp⟩,rowFormExtension_at η ⟨q,hq⟩]
    exact congrArg Subtype.val (hSame ⟨p,hp⟩ ⟨q,hq⟩ he)

end DiamondIntegral.Section6
