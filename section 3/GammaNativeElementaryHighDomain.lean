import «section 3».GammaElementaryHighPair
import «section 3».GammaNativeMeasuredNormalization
import «section 3».GammaNativeMeasuredLifts
import «section 3».GammaGroundRVPackPairs

/-! A native elementary object has precisely its full-weight source
labels and a nonzero cone parameter on its full-weight part. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.Section4.rawRVSpace
  SpecialTransformations.Section4.realSpace SpecialTransformations.DefinableGeometry.Space.ofEmbedding
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)
set_option quotPrecheck false in
local notation "zeroN" => (letI : LRV.Structure M := N; letI : M ⊨ Axioms.ACVF := hN; (0 : CanonicalRV.RVSort M))

theorem gammaNativeElementary_high_product_domain
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ)
    (U : GammaObjectAt B Set.univ (n+1)) (i : Fin (n+1))
    (hAd : GammaAdmissible U.toGamma.toGammaRVObject i) :
    (Section5.nativeRVGroundDomain (hc := hc)
      (gammaHighRestrictionAt (gammaElementaryAt hκ hs h00 hr U i hAd))).carrier =
      (gammaGroundRVProductDomain (Section5.nativeRVGroundDomain (hc := hc) (gammaHighRestrictionAt U)) (gammaGroundMeasuredRVPositive hc B).underlying.domain).carrier := by
  let A := U
  let E := gammaElementaryAt hκ hs h00 hr A i hAd
  have hn (u : rvObjectDomain A.object.obj) (s : @positiveRV M N Set.univ) :
      ¬ (@rvPackPair M N Set.univ _ _ (rvObjectDomain A.object.obj) (@positiveRV M N Set.univ) u s).val ∈
        (@DefSet.carrier LRV M N _ Set.univ (@rvLowDomain M N Set.univ n E.object.obj)) ↔
        u.val ∉ (@DefSet.carrier LRV M N _ Set.univ (@rvLowDomain M N Set.univ n A.object.obj)) ∧ s.val 0 ≠ zeroN :=
    @elementary_high_pair_iff M N hN Set.univ n A.object.obj i u s
  rw [Section5.nativeRVGroundDomain_carrier]
  ext x
  change (x ∈ (@DefSet.carrier LRV M N _ Set.univ (rvObjectDomain E.object.obj)) ∧
    x ∉ (@DefSet.carrier LRV M N _ Set.univ (@rvLowDomain M N Set.univ n E.object.obj))) ↔ _
  rw [mem_gammaGroundRVProductDomain]
  constructor
  · rintro ⟨hx,hxN⟩
    obtain ⟨u,s,he⟩ := @exists_rvPackPair M N Set.univ _ _
      (rvObjectDomain A.object.obj) (@positiveRV M N Set.univ) ⟨x,hx⟩
    have he' := congrArg Subtype.val he
    obtain ⟨huN,hsN⟩ := (hn u s).mp (by simpa only [he'] using hxN)
    have hs0 : (s.val 0).val ≠ @iRVZero M sM := by
      intro hz
      apply hsN
      exact Subtype.ext (hz.trans (CanonicalStructure.sortZero_normalize .rv).symm |>.trans
        (@RVOperations.zero_val M N hN).symm)
    have hpos := (gammaBasicPositive_nonzero_labels (hc := hc) (B := B) s.val).mp ⟨s.property,hs0⟩
    exact ⟨u.val,(Section5.nativeRVGroundDomain_carrier (gammaHighRestrictionAt U)).ge ⟨u.property,huN⟩,s.val,hpos,he'⟩
  · rintro ⟨u,hu,s,hsP,he⟩
    have huH := (Section5.nativeRVGroundDomain_carrier (gammaHighRestrictionAt U)).le hu
    let u' : rvObjectDomain A.object.obj := ⟨u,huH.1⟩
    have hpos := (gammaBasicPositive_nonzero_labels (hc := hc) (B := B) s).mpr hsP
    let s' : @positiveRV M N Set.univ := ⟨s,hpos.1⟩
    let a : rvObjectDomain E.object.obj := @rvPackPair M N Set.univ _ _
      (rvObjectDomain A.object.obj) (@positiveRV M N Set.univ) u' s'
    have ha : a.val = x := he
    refine ⟨ha ▸ a.property,?_⟩
    have hsN : s'.val 0 ≠ zeroN := by
      intro hz
      apply hpos.2
      exact (congrArg Subtype.val hz).trans ((@RVOperations.zero_val M N hN).trans
        (CanonicalStructure.sortZero_normalize .rv))
    have hn' := (hn u' s').mpr ⟨huH.2,hsN⟩
    change a.val ∉ (@DefSet.carrier LRV M N _ Set.univ (@rvLowDomain M N Set.univ n E.object.obj)) at hn'
    simpa only [ha] using hn'

end DiamondIntegral.Section3
