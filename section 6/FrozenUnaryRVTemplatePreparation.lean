import «section 6».UnaryRVTemplateRelations

/-! Actual finite freezing and unary preparation of a complete RV
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
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r q m k l : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

structure UnaryRVTemplateFreezeCertificate
    (A : DefSet (rawMixedSpace (M := M) 1 r) S)
    (C : Fin k → DefSet (rawMixedSpace (M := M) 1 r) S) (hCA : ∀ i,(C i).carrier ⊆ A.carrier)
    {j : Fin m} (X : UnaryPreparationContext A j)
    (P : Fin l → DefSet (rawMixedSpace (M := M) m X.arity) S)
    (V : RVSetParameterTemplate (M := M) S 1 q) where
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
  lift : Nonempty (UnaryContextLift (G := G) X map P)
  ambientProduct : ∀ E : freezing.balls,FMT.CoordinateProductDomain X.source.carrier
    (FMT.vfOpenBall E.val) (freezing.centers E) j
  protectedProducts : ∀ i,∀ E : freezing.balls,FMT.CoordinateProductDomain (P i).carrier
    (FMT.vfOpenBall E.val) (freezing.centers E) j
  unaryProducts : ∀ i,∀ E : freezing.balls,FMT.CoordinateProductDomain (C i).carrier
    (FMT.vfOpenBall E.val) (freezing.centers E) 0
  data : ∀ p z : A,(map p).val.2=(map z).val.2 →
    (V.fibre (fun _ => (FMT.vfFamilyFreeze freezing.balls freezing.centers (p.val.1 0)).val)).carrier=
      (V.fibre (fun _ => (FMT.vfFamilyFreeze freezing.balls freezing.centers (z.val.1 0)).val)).carrier

theorem frozen_unary_rv_template_preparation
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
    (V : RVSetParameterTemplate (M := M) S 1 q) :
    Nonempty (UnaryRVTemplateFreezeCertificate (G := G) A C hCA X P V) := by
  obtain ⟨F,s,B,f,hChain,hB,hBD,hBRV,hBTag,hPieces,hLift,hProdX,hProdP,hProdC,hData⟩ :=
    frozen_unary_rv_data_preparation h00 hc linear hκ hs hv W hsmall hΓ hW hWS hSW hnt
      A hA hAD hARV hTag C hCA hC X P hPX hP (unaryRVTemplateRelation V r)
  refine ⟨⟨F,s,B,f,hChain,hB,hBD,hBRV,hBTag,hPieces,hLift,hProdX,hProdP,hProdC,?_⟩⟩
  intro p z he
  have h := hData p z he
  rwa [frozenUnaryRVTemplateRelation_row,frozenUnaryRVTemplateRelation_row] at h

end DiamondIntegral.Section6
