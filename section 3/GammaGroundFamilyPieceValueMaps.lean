import «section 3».GammaGroundFamilyPieceMaps
import «section 3».GammaGroundUnitFamilyGenericTags
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)}
variable {P Q : Space LRV M}

/-- Maps on the individual pieces preserve their finite tags and retain
each complete branch graph, without any bijectivity hypothesis. -/
def GammaGroundFamilyMap.pieces (A : GammaGroundFiniteFamily hc B P)
    (D : Fin A.tags → GammaGroundDefSet hc B Q) (f : ∀ i, GammaGroundMap (A.piece i) (D i)) :
    GammaGroundFamilyMap A ⟨A.tags,D⟩ where
  toFun a := ⟨a.1,f a.1 a.2⟩
  definable := by
    intro i j
    by_cases he : i = j
    · subst j
      apply (f i).relation_definable.congr
      intro x y
      constructor
      · rintro ⟨a,ha,hf⟩
        exact ⟨a,f i a,ha,hf,rfl⟩
      · rintro ⟨a,b,ha,hb,hab⟩
        have hab' : f i a = b := by
          change (⟨i,f i a⟩ : Σ i, D i) = ⟨i,b⟩ at hab
          simpa only [Sigma.mk.inj_iff,heq_eq_eq,true_and] using hab
        exact ⟨a,ha,(congrArg Subtype.val hab').trans hb⟩
    · have hd : GammaGroundRelationDefinable hc B P Q (fun _ _ => False) :=
        (GammaGroundDefSet.empty hc B (P.prod Q)).definable
      apply hd.congr
      intro x y
      constructor
      · exact False.elim
      · rintro ⟨a,b,_,_,hab⟩
        exact he (congrArg Sigma.fst hab)

/-- Actual valuation is a definable map of the full tagged RV preimages,
with every original tag retained. -/
def GammaGroundGammaObject.unitValueFamilyMap {n : ℕ} (A : GammaGroundGammaObject hc B n) :
    GammaGroundFamilyMap A.unitFamily A :=
  GammaGroundFamilyMap.pieces A.unitFamily A.piece (fun i => gammaGroundFullPreimageValueMap (A.piece i))

end DiamondIntegral.Section3
