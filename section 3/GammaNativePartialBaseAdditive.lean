import «section 3».GammaNativeSpecialVFAdditive
import «section 3».GammaVFProjectionChains

/-! Preparing any VF subtuple and fixing its complement preserves every additive elementary invariant, by the existing lifted special chain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {W : Type*} [AddCommMonoid W]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n p r : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

def gammaNativeAdditiveSourcePoint (U : GammaObjectAt B Set.univ (n+1))
    (q : (gammaNativeUnitLift (hc := hc) U.toGamma).domain) : typedLift U.object.obj :=
  ⟨((gammaNativeTypedLiftBijection U).symm.map q).val,((gammaNativeTypedLiftBijection U).symm.map q).property⟩

theorem gammaNativePartialBase_full_measured_additive_comparison
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ) (hg : Cardinal.mk B.gamma < κ)
    (χ : GammaGroundMeasuredRVKPlus hc B (n+1) →+ W)
    (hχ : GammaNativeElementaryInvariant hκ hs h00 hr χ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (C : BaseContext M) (hBC : B.real ⊆ (C.base : Set M))
    (U V : GammaObjectAt B Set.univ (n+1))
    (ω : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain U))
    (η : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain V))
    {X : DefSet (M := M) Set.univ p 0} {Z : DefSet (M := M) Set.univ p r}
    (T : SpecialBijection X Z) (hT : GammaChainDefinable B T.chain)
    (ι : Fin p → Fin (n+1)) (hι : Function.Injective ι)
    (hInput : ∀ q : typedLift U.object.obj, (q.val.1 ∘ ι,Fin.elim0) ∈ carrier X)
    (f : GammaFullMeasuredBijection (gammaNativeMeasuredLift U ω) (gammaNativeMeasuredLift V η))
    (hBase : ∀ q, (f.map.map q).val.1 ∘ ι =
      (T.toMap ⟨((gammaNativeAdditiveSourcePoint U q).val.1 ∘ ι,Fin.elim0),hInput (gammaNativeAdditiveSourcePoint U q)⟩).val.1)
    (hOther : ∀ q, ∀ j : Fin (n+1), j ∉ Set.range ι →
      (f.map.map q).val.1 j = (gammaNativeAdditiveSourcePoint U q).val.1 j) :
    gammaNativeAdditiveValue χ U ω = gammaNativeAdditiveValue χ V η := by
  have hSub : ∀ q ∈ carrier (typedLift U.object.obj), vfRVProjection ι (Fin.elim0 : Fin 0 → Fin (rvObjectArity U.object.obj)) q ∈ carrier X := by
    intro q hq
    have he : vfRVProjection ι (Fin.elim0 : Fin 0 → Fin (rvObjectArity U.object.obj)) q =
        (q.1 ∘ ι,Fin.elim0) := Prod.ext rfl (by funext i; exact Fin.elim0 i)
    exact he.symm ▸ hInput ⟨q,hq⟩
  obtain ⟨l,K,σ,W,hAlt,hWG,hSquare,_,hWOther⟩ := gammaVFProjection_chain_lift T.chain hT ι hι
    (typedLift U.object.obj) (gammaNativeTypedLift_definable U) Fin.elim0 hSub none T.alternating
  let S : SpecialBijection (typedLift U.object.obj) K := ⟨W,hAlt⟩
  have hVF : ∀ q, (f.map.map q).val.1 = (S.toMap (gammaNativeAdditiveSourcePoint U q)).val.1 := by
    intro q
    let a := gammaNativeAdditiveSourcePoint U q
    have hArg : (⟨vfRVProjection ι (Fin.elim0 : Fin 0 → Fin (rvObjectArity U.object.obj)) a.val,hSub _ a.property⟩ : X) =
        ⟨(a.val.1 ∘ ι,Fin.elim0),hInput a⟩ := Subtype.ext (Prod.ext rfl (by funext i; exact Fin.elim0 i))
    have hWBase : (W.toMap a).val.1 ∘ ι = (T.toMap ⟨(a.val.1 ∘ ι,Fin.elim0),hInput a⟩).val.1 :=
      (congrArg Prod.fst (hSquare a)).trans (congrArg (fun z => (T.toMap z).val.1) hArg)
    funext j
    by_cases hj : j ∈ Set.range ι
    · obtain ⟨i,rfl⟩ := hj
      exact (congrFun (hBase q) i).trans (congrFun hWBase i).symm
    · exact (hOther q j hj).trans (hWOther a j hj).symm
  exact gammaNativeSpecialVF_full_measured_additive_comparison (hκ := hκ) (hs := hs) (hr := hr) (hv := hv)
    (U := U) (T := S) (hT := hWG) (ω := ω) h00 hg χ hχ C hBC V η f hVF

end DiamondIntegral.Section3
