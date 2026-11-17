import «section 3».GammaPreparedIndexedFullMeasured
import «section 3».GammaPartialBasePresentationAdditive
import «section 3».GammaMeasuredIndexedAdditive

/-! A measured native lift transported by an actual partial-base special
preparation has the principal class of its prepared indexed family.
Only literal prepared rows and their complete Gamma density are used. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {W : Type*} [AddCommMonoid W]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p l a k : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

theorem gammaNativePartialBase_indexed_family_additive_comparison
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ) (hg : Cardinal.mk B.gamma < κ)
    (χ : GammaGroundMeasuredRVKPlus hc B (p+(k+1)) →+ W)
    (hχ : GammaNativeElementaryInvariant hκ hs h00 hr χ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (C₀ : BaseContext M) (hBC₀ : B.real ⊆ (C₀.base : Set M))
    (U : GammaObjectAt B Set.univ (p+(k+1)))
    (ω : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain U))
    {X : DefSet (M := M) S p 0} {C : DefSet (M := M) S p l}
    (T : SpecialBijection X C) (hT : GammaChainDefinable B T.chain) (hC : IsRVPullback (carrier C))
    (hInput : ∀ q : typedLift U.object.obj, (q.val.1 ∘ Fin.castAdd (k+1),Fin.elim0) ∈ carrier X)
    (BP : PreparedIndexPresentation B C)
    (F : GammaMeasuredRVSchema hc B (p+l) a (k+1) (fun _ => .rv))
    (hF : ∀ t ∈ preparedKeyDomain C, F.valid (rvValues t)) (P : F.object.IndexedPresentation BP)
    (Y : GammaGroundDefSet hc B (rawMixedSpace (M := M) (p+(k+1)) (l+a)))
    (hBase : ∀ q : Y, (q.val.1 ∘ Fin.castAdd (k+1),q.val.2 ∘ Fin.castAdd a) ∈ carrier C)
    (hRows : ∀ (c : C) (y : Fin (k+1) → Section2.VF M) (r : Fin a → RV (M := M)),
      (Fin.append c.val.1 y,Fin.append c.val.2 r) ∈ Y.carrier ↔
        F.object.rowVolume (rawPreparedKey c.val) r (Section2.tupleRV M y))
    (hfin : ∀ x, {r | (x,r) ∈ Y.carrier}.Finite) (η : GammaGroundVolumeForm hc B Y)
    (hDensity : ∀ (q : Y) (c : (volumeGammaSpace hc).domain),
      (volumeGammaSpace hc).decode c = (η q).val →
        F.rowDensity (rvValues (indexedLeft (gammaPreparedIndexAttachment Y q).val.2))
          (indexedRight (gammaPreparedIndexAttachment Y q).val.2) c)
    (f : GammaFullMeasuredBijection (gammaNativeMeasuredLift U ω) (⟨l+a,Y,hfin,η⟩ : GammaGroundMeasuredVFData hc B (p+(k+1))))
    (hFollow : ∀ q, (f.map.map q).val.1 ∘ Fin.castAdd (k+1) =
      (T.toMap ⟨((gammaNativeAdditiveSourcePoint U q).val.1 ∘ Fin.castAdd (k+1),Fin.elim0),hInput (gammaNativeAdditiveSourcePoint U q)⟩).val.1)
    (hOther : ∀ q, ∀ j : Fin (p+(k+1)), j ∉ Set.range (Fin.castAdd (k+1) : Fin p → Fin (p+(k+1))) →
      (f.map.map q).val.1 j = (gammaNativeAdditiveSourcePoint U q).val.1 j) :
    gammaNativeAdditiveValue χ U ω = gammaMeasuredAdditiveValue χ (F.indexedObject BP hF P) := by
  let g := gammaPreparedIndexedFullMeasured hκ hs hr hv C hC BP F hF P Y hBase hRows hfin η hDensity
  let H := f.comp hκ hs hr hv g
  exact gammaNativePartialBase_presented_additive_comparison hκ hs h00 hr hg χ hχ hv C₀ hBC₀
    U (gammaUniversalObject P.toGamma) ω (F.indexedForm BP hF P) T hT (Fin.castAdd (k+1))
    (by intro i j h; apply Fin.ext; exact congrArg (fun z : Fin (p+(k+1)) => z.val) h)
    hInput H hFollow hOther

end DiamondIntegral.Section3
