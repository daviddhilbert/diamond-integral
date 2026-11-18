import «section 3».GammaNativePartialBaseAdditive
import Section5.ParameterExtension

/-! The additive partial-base comparison keeps the original Gamma graph under a change of real presentation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {W : Type*} [AddCommMonoid W]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n p r : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

theorem gammaNativePartialBase_presented_additive_comparison
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ) (hg : Cardinal.mk B.gamma < κ)
    (χ : GammaGroundMeasuredRVKPlus hc B (n+1) →+ W)
    (hχ : GammaNativeElementaryInvariant hκ hs h00 hr χ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (C : BaseContext M) (hBC : B.real ⊆ (C.base : Set M))
    (U V : GammaObjectAt B Set.univ (n+1))
    (ω : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain U))
    (η : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain V))
    {X : DefSet (M := M) S p 0} {Z : DefSet (M := M) S p r}
    (T : SpecialBijection X Z) (hT : GammaChainDefinable B T.chain)
    (ι : Fin p → Fin (n+1)) (hι : Function.Injective ι)
    (hInput : ∀ q : typedLift U.object.obj, (q.val.1 ∘ ι,Fin.elim0) ∈ carrier X)
    (f : GammaFullMeasuredBijection (gammaNativeMeasuredLift U ω) (gammaNativeMeasuredLift V η))
    (hBase : ∀ q, (f.map.map q).val.1 ∘ ι =
      (T.toMap ⟨((gammaNativeAdditiveSourcePoint U q).val.1 ∘ ι,Fin.elim0),hInput (gammaNativeAdditiveSourcePoint U q)⟩).val.1)
    (hOther : ∀ q, ∀ j : Fin (n+1), j ∉ Set.range ι →
      (f.map.map q).val.1 j = (gammaNativeAdditiveSourcePoint U q).val.1 j) :
    gammaNativeAdditiveValue χ U ω = gammaNativeAdditiveValue χ V η := by
  let hSU : S ⊆ (Set.univ : Set M) := Set.subset_univ _
  let W := T.extendBase hSU
  have hW : GammaChainDefinable B W.chain := GammaChainDefinable.extendBase B T.chain hSU hT
  have hFollow : ∀ q, (f.map.map q).val.1 ∘ ι =
      (W.toMap ⟨((gammaNativeAdditiveSourcePoint U q).val.1 ∘ ι,Fin.elim0),hInput (gammaNativeAdditiveSourcePoint U q)⟩).val.1 := by
    intro q
    have h := T.chain.extendBase_apply hSU
      ⟨((gammaNativeAdditiveSourcePoint U q).val.1 ∘ ι,Fin.elim0),hInput (gammaNativeAdditiveSourcePoint U q)⟩
    exact (hBase q).trans (congrArg Prod.fst h).symm
  exact gammaNativePartialBase_full_measured_additive_comparison hκ hs h00 hr hg χ hχ hv C hBC U V ω η W hW ι hι hInput f hFollow hOther

end DiamondIntegral.Section3
