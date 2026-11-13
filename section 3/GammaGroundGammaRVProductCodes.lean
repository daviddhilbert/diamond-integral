import «section 3».GammaGroundGammaProducts
import «section 3».GammaGroundGammaCodeRestrictions
import «section 3».GammaGroundRVProducts
import «section 3».GammaRVProductCodes
/-! Full Gamma code preimages commute with coordinate products. -/
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)} {k l : ℕ}

theorem gammaGroundGammaRVCodeLift_product (A : GammaGroundGammaPiece hc ground k) (B : GammaGroundGammaPiece hc ground l) :
    (gammaGroundGammaRVCodeLift (gammaGroundGammaAppendMap A B).image).domain.carrier =
      (gammaGroundRVProductDomain (gammaGroundGammaRVCodeLift A).domain (gammaGroundGammaRVCodeLift B).domain).carrier := by
  ext t
  constructor
  · rintro ⟨c, rfl⟩
    obtain ⟨p, hp⟩ := c.property
    have ha : ((volumeGammaSpace hc).power (Fin k)).decode (gammaCodeLeft c.val) ∈ A.carrier := by
      have he : ((volumeGammaSpace hc).power (Fin k)).decode (gammaCodeLeft c.val) = p.val.1 := by
        funext i
        have h := congrFun hp (Fin.castAdd l i)
        change Fin.append p.val.1 p.val.2 (Fin.castAdd l i) = _ at h
        exact (Fin.append_left _ _ _).symm.trans h |>.symm
      exact he.symm ▸ p.property.1
    have hb : ((volumeGammaSpace hc).power (Fin l)).decode (gammaCodeRight c.val) ∈ B.carrier := by
      have he : ((volumeGammaSpace hc).power (Fin l)).decode (gammaCodeRight c.val) = p.val.2 := by
        funext i
        have h := congrFun hp (Fin.natAdd k i)
        change Fin.append p.val.1 p.val.2 (Fin.natAdd k i) = _ at h
        exact (Fin.append_right _ _ _).symm.trans h |>.symm
      exact he.symm ▸ p.property.2
    refine ⟨⟨(gammaCodeTuple (gammaCodeLeft c.val), gammaCodeTuple (gammaCodeRight c.val)),
      ⟨⟨gammaCodeLeft c.val, ha⟩, rfl⟩, ⟨⟨gammaCodeRight c.val, hb⟩, rfl⟩⟩, ?_⟩
    funext i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · exact Fin.append_left _ _ _
    · exact Fin.append_right _ _ _
  · rintro ⟨p, rfl⟩
    obtain ⟨a, ha⟩ := p.property.1
    obtain ⟨b, hb⟩ := p.property.2
    let c := gammaCodeAppend a.val b.val
    have hc' : ((volumeGammaSpace hc).power (Fin (k + l))).decode c ∈ (gammaGroundGammaAppendMap A B).image.carrier := by
      refine ⟨⟨((((volumeGammaSpace hc).power (Fin k)).decode a.val),
        (((volumeGammaSpace hc).power (Fin l)).decode b.val)), a.property, b.property⟩, ?_⟩
      exact (gammaCodeAppend_decode a.val b.val).symm
    refine ⟨⟨c, hc'⟩, ?_⟩
    change gammaCodeTuple c = rvAppend p.val.1 p.val.2
    rw [← ha, ← hb]
    funext i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · change gammaCodeTuple c (Fin.castAdd l i) = rvAppend (gammaCodeTuple a.val) (gammaCodeTuple b.val) (Fin.castAdd l i)
      simp only [rvAppend, Fin.append_left]
      apply Subtype.ext
      change Fin.append (fun i => a.val.val (i, (0 : Fin 1))) (fun j => b.val.val (j, (0 : Fin 1))) (Fin.castAdd l i) = _
      exact Fin.append_left _ _ _
    · change gammaCodeTuple c (Fin.natAdd k j) = rvAppend (gammaCodeTuple a.val) (gammaCodeTuple b.val) (Fin.natAdd k j)
      simp only [rvAppend, Fin.append_right]
      apply Subtype.ext
      change Fin.append (fun i => a.val.val (i, (0 : Fin 1))) (fun j => b.val.val (j, (0 : Fin 1))) (Fin.natAdd k j) = _
      exact Fin.append_right _ _ _

end DiamondIntegral.Section3
