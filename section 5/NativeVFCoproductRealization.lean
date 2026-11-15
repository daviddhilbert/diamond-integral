import «section 3».GammaGroundFiniteVFCoproducts
import «section 3».GammaGroundMapFiniteGluing

/-! The genuine native VF coproduct realizes an actual disjoint sum of
its domains, with all tagged inclusion maps over the original ground. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}

def nativeVFCoproductLeft (U V : GammaGroundFiniteVFObject hc B) :
    GammaGroundMap U.domain (U.coprod V).domain :=
  (gammaGroundMixedLeftTag U.domain V.vfArity V.rvArity).corestrict (fun a => Or.inl ⟨a,rfl⟩)

def nativeVFCoproductRight (U V : GammaGroundFiniteVFObject hc B) :
    GammaGroundMap V.domain (U.coprod V).domain :=
  (gammaGroundMixedRightTag V.domain U.vfArity U.rvArity).corestrict (fun a => Or.inr ⟨a,rfl⟩)

def nativeVFCoproductSum (U V : GammaGroundFiniteVFObject hc B) : U.domain ⊕ V.domain → (U.coprod V).domain :=
  Sum.elim (nativeVFCoproductLeft U V) (nativeVFCoproductRight U V)

theorem nativeVFCoproductSum_bijective (U V : GammaGroundFiniteVFObject hc B) :
    Function.Bijective (nativeVFCoproductSum U V) := by
  constructor
  · rintro (a|a) (b|b) he
    · have hv := congrArg (fun z : (U.coprod V).domain => z.val) he
      exact congrArg Sum.inl ((gammaGroundMixedLeftTag_injective U.domain V.vfArity V.rvArity) (Subtype.ext hv))
    · have hv := congrArg (fun z : (U.coprod V).domain => z.val) he
      exact False.elim (Set.disjoint_left.mp (gammaGroundMixedTaggedImages_disjoint U.domain V.domain)
        ⟨a,hv⟩ ⟨b,rfl⟩)
    · have hv := congrArg (fun z : (U.coprod V).domain => z.val) he
      exact False.elim (Set.disjoint_left.mp (gammaGroundMixedTaggedImages_disjoint U.domain V.domain)
        ⟨b,rfl⟩ ⟨a,hv⟩)
    · have hv := congrArg (fun z : (U.coprod V).domain => z.val) he
      exact congrArg Sum.inr ((gammaGroundMixedRightTag_injective V.domain U.vfArity U.rvArity) (Subtype.ext hv))
  · rintro ⟨z,hz⟩
    rcases hz with ⟨a,ha⟩ | ⟨b,hb⟩
    · exact ⟨Sum.inl a,Subtype.ext ha⟩
    · exact ⟨Sum.inr b,Subtype.ext hb⟩

def nativeVFCoproductEquiv (U V : GammaGroundFiniteVFObject hc B) : U.domain ⊕ V.domain ≃ (U.coprod V).domain :=
  Equiv.ofBijective (nativeVFCoproductSum U V) (nativeVFCoproductSum_bijective U V)

end DiamondIntegral.Section5
