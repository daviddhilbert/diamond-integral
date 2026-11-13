import «section 3».GammaGroundGammaProducts
import «section 3».GammaGroundRVUnitProducts
import «section 3».RVUnitTupleProducts
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)} {n m : ℕ}

theorem rvUnitTupleValues_append (u : Fin n → (CanonicalRV.RVSort M)ˣ) (v : Fin m → (CanonicalRV.RVSort M)ˣ) :
    rvUnitTupleValues (Fin.append u v) = Fin.append (rvUnitTupleValues u) (rvUnitTupleValues v) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [rvUnitTupleValues,Fin.append_left]
  · simp only [rvUnitTupleValues,Fin.append_right]

/-- Full RV preimages commute with concatenated Gamma products by an
actual same-ground bijection, without choosing any RV representatives. -/
def gammaGroundUnitPreimageProductBijection
    (I : GammaGroundGammaPiece hc B n) (J : GammaGroundGammaPiece hc B m) :
    GammaGroundBijection ((gammaGroundRVUnitGammaPreimage I).prod (gammaGroundRVUnitGammaPreimage J))
      (gammaGroundRVUnitGammaPreimage (gammaGroundGammaAppendMap I J).image) := by
  let A := (gammaGroundRVUnitGammaPreimage I).prod (gammaGroundRVUnitGammaPreimage J)
  let F := gammaGroundRVUnitTupleProductMap A
  have hin (u : A) : (F u).val ∈ (gammaGroundRVUnitGammaPreimage (gammaGroundGammaAppendMap I J).image).carrier := by
    change rvUnitTupleValues (Fin.append u.val.1 u.val.2) ∈ (gammaGroundGammaAppendMap I J).image.carrier
    exact ⟨⟨(rvUnitTupleValues u.val.1,rvUnitTupleValues u.val.2),u.property.1,u.property.2⟩,
      (rvUnitTupleValues_append u.val.1 u.val.2).symm⟩
  let f := F.corestrict hin
  refine ⟨f,?_,?_⟩
  · intro u v huv
    exact Subtype.ext ((Fin.appendEquiv n m).injective (congrArg Subtype.val huv))
  · intro w
    obtain ⟨γ,hγ⟩ := w.property
    change Fin.append γ.val.1 γ.val.2 = rvUnitTupleValues w.val at hγ
    let u : Fin n → (CanonicalRV.RVSort M)ˣ := fun i => w.val (Fin.castAdd m i)
    let v : Fin m → (CanonicalRV.RVSort M)ˣ := fun j => w.val (Fin.natAdd n j)
    have huval : rvUnitTupleValues u = γ.val.1 := by
      funext i
      simpa only [rvUnitTupleValues,u,Fin.append_left] using (congrFun hγ (Fin.castAdd m i)).symm
    have hvval : rvUnitTupleValues v = γ.val.2 := by
      funext j
      simpa only [rvUnitTupleValues,v,Fin.append_right] using (congrFun hγ (Fin.natAdd n j)).symm
    have hu : u ∈ (gammaGroundRVUnitGammaPreimage I).carrier := by
      change rvUnitTupleValues u ∈ I.carrier
      exact huval.symm ▸ γ.property.1
    have hv : v ∈ (gammaGroundRVUnitGammaPreimage J).carrier := by
      change rvUnitTupleValues v ∈ J.carrier
      exact hvval.symm ▸ γ.property.2
    refine ⟨⟨(u,v),hu,hv⟩,Subtype.ext ?_⟩
    change Fin.append u v = w.val
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [Fin.append_left,u]
    · simp only [Fin.append_right,v]

@[simp] theorem gammaGroundUnitPreimageProductBijection_formula
    (I : GammaGroundGammaPiece hc B n) (J : GammaGroundGammaPiece hc B m)
    (u : (gammaGroundRVUnitGammaPreimage I).prod (gammaGroundRVUnitGammaPreimage J)) :
    ((gammaGroundUnitPreimageProductBijection I J).map u).val = Fin.append u.val.1 u.val.2 := rfl

end DiamondIntegral.Section3
