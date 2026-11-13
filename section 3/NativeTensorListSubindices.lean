import «section 3».NativeTensorListAtlas
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)} {k N : ℕ}

/-- Present a known chart in its actual finite coproduct slot. -/
def gammaGroundNativeTensorListInjectionOfEq (l : List (GammaGroundNativeTensorChart hc B k))
    (i : Fin l.length) (Z : GammaGroundNativeTensorChart hc B k) (he : l.get i = Z) :
    GammaGroundMap Z.source (gammaGroundNativeTensorListObject l).domain := he ▸ gammaGroundNativeTensorListInjection l i

theorem gammaGroundNativeTensorListInjectionOfEq_injective (l : List (GammaGroundNativeTensorChart hc B k))
    (i : Fin l.length) (Z : GammaGroundNativeTensorChart hc B k) (he : l.get i = Z) :
    Function.Injective (gammaGroundNativeTensorListInjectionOfEq l i Z he) := by
  cases he
  exact gammaGroundNativeTensorListInjection_injective l i

theorem gammaGroundNativeTensorListInjectionOfEq_image (l : List (GammaGroundNativeTensorChart hc B k))
    (i : Fin l.length) (Z : GammaGroundNativeTensorChart hc B k) (he : l.get i = Z) :
    (gammaGroundNativeTensorListInjectionOfEq l i Z he).image.carrier =
      (gammaGroundNativeTensorListInjection l i).image.carrier := by
  cases he
  rfl

def gammaGroundNativeTensorListPrefixIndex (l q : List (GammaGroundNativeTensorChart hc B k)) (i : Fin l.length) :
    Fin (l++q).length := ⟨i.val,by rw [List.length_append]; have := i.isLt; omega⟩

theorem gammaGroundNativeTensorListPrefix_get (l q : List (GammaGroundNativeTensorChart hc B k)) (i : Fin l.length) :
    (l++q).get (gammaGroundNativeTensorListPrefixIndex l q i) = l.get i := by
  simp [gammaGroundNativeTensorListPrefixIndex,List.get_eq_getElem,i.isLt]

def gammaGroundNativeTensorListSuffixIndex (l q : List (GammaGroundNativeTensorChart hc B k)) (i : Fin q.length) :
    Fin (l++q).length := ⟨l.length+i.val,by rw [List.length_append]; have := i.isLt; omega⟩

theorem gammaGroundNativeTensorListSuffix_get (l q : List (GammaGroundNativeTensorChart hc B k)) (i : Fin q.length) :
    (l++q).get (gammaGroundNativeTensorListSuffixIndex l q i) = q.get i := by
  simp [gammaGroundNativeTensorListSuffixIndex,List.get_eq_getElem]

def gammaGroundNativeTensorOfFnIndex (f : Fin N → GammaGroundNativeTensorChart hc B k) (i : Fin N) :
    Fin (List.ofFn f).length := ⟨i.val,by simpa only [List.length_ofFn] using i.isLt⟩

theorem gammaGroundNativeTensorOfFn_get (f : Fin N → GammaGroundNativeTensorChart hc B k) (i : Fin N) :
    (List.ofFn f).get (gammaGroundNativeTensorOfFnIndex f i) = f i := by
  simp [gammaGroundNativeTensorOfFnIndex,List.get_eq_getElem]
end DiamondIntegral.Section3
