import «section 5».OriginalRVRowObjects
import «section 5».NativeTaggedDomains

/-! Original tagged Gamma-domain rows are actual native RV coproducts.
No finite-value restriction is needed, and empty summands can be removed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
open DiamondIntegral.Section3 DiamondIntegral.Section4 Section3RVCodeBridge
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {p a b : ℕ} {sp : Fin p → SortTag}

def originalEmptyDomain (B : Base (M := M)) (p a : ℕ) (sp : Fin p → SortTag) :
    GammaDomainFormula B p a sp := ⟨∅,DefinableOverBase.empty B _⟩

theorem originalRVEmptyRow (z : Fin p → M) :
    (originalRVRowDomain hc (originalEmptyDomain B p a sp) z).carrier = ∅ := rfl

def originalRVRowTaggedBijection (D : GammaDomainFormula B p a sp)
    (E : GammaDomainFormula B p b sp) (z : Fin p → M) :
    GammaGroundBijection (originalRVRowDomain hc (nativeRVTaggedDomain D E) z)
      (gammaGroundRVTaggedUnion (originalRVRowDomain hc D z) (originalRVRowDomain hc E z)) := by
  apply gammaGroundBijectionOfRawDomainEq
  ext w
  rw [originalRVRowDomain_raw,rawDomain_native_tagged_union,originalRVRowDomain_raw,originalRVRowDomain_raw]
  exact nativeRVTaggedDomain_row D E z w

def gammaGroundTaggedEmptyRightBijection
    (A : GammaGroundDefSet hc B (rawRVSpace (M := M) a))
    (C : GammaGroundDefSet hc B (rawRVSpace (M := M) b)) (hC : C.carrier = ∅) :
    GammaGroundBijection (gammaGroundRVTaggedUnion A C) A := by
  have he : (gammaGroundRVTaggedUnion A C).carrier = (gammaGroundRVLeftTag A b).image.carrier := by
    ext u
    constructor
    · rintro (h | ⟨c,_⟩)
      · exact h
      · exact ((Set.eq_empty_iff_forall_notMem.mp hC) c.val c.property).elim
    · exact Or.inl
  exact (gammaGroundRVLeftTagBijection A b).symm.comp (gammaGroundBijectionOfCarrierEq _ _ he)

def gammaGroundTaggedEmptyLeftBijection
    (A : GammaGroundDefSet hc B (rawRVSpace (M := M) a))
    (C : GammaGroundDefSet hc B (rawRVSpace (M := M) b)) (hA : A.carrier = ∅) :
    GammaGroundBijection (gammaGroundRVTaggedUnion A C) C := by
  have he : (gammaGroundRVTaggedUnion A C).carrier = (gammaGroundRVRightTag C a).image.carrier := by
    ext u
    constructor
    · rintro (⟨c,_⟩ | h)
      · exact ((Set.eq_empty_iff_forall_notMem.mp hA) c.val c.property).elim
      · exact h
    · exact Or.inr
  exact (gammaGroundRVRightTagBijection C a).symm.comp (gammaGroundBijectionOfCarrierEq _ _ he)

def originalRVLeftTagRowBijection (D : GammaDomainFormula B p a sp) (b : ℕ) (z : Fin p → M) :
    GammaGroundBijection
      (originalRVRowDomain hc (nativeRVTaggedDomain D (originalEmptyDomain B p b sp)) z)
      (originalRVRowDomain hc D z) :=
  (gammaGroundTaggedEmptyRightBijection _ _ (originalRVEmptyRow z)).comp
    (originalRVRowTaggedBijection D (originalEmptyDomain B p b sp) z)

def originalRVRightTagRowBijection (E : GammaDomainFormula B p b sp) (a : ℕ) (z : Fin p → M) :
    GammaGroundBijection
      (originalRVRowDomain hc (nativeRVTaggedDomain (originalEmptyDomain B p a sp) E) z)
      (originalRVRowDomain hc E z) :=
  (gammaGroundTaggedEmptyLeftBijection _ _ (originalRVEmptyRow z)).comp
    (originalRVRowTaggedBijection (originalEmptyDomain B p a sp) E z)

end DiamondIntegral.Section5
