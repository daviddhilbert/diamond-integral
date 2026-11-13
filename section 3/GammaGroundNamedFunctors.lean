import «section 3».GammaGroundMeasuredRVSupport
import «section 3».GammaGroundVFCategories
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)}
variable {P : Space LRV M} {p : P.Carrier} {k : ℕ}

/-- Eliminating an already definable imaginary name retains the exact
RV objects and maps over the complete original ground. -/
def namedRVToGammaGround (hp : GammaGroundDefinable hc B P {p}) :
    NamedRVObject P p B.real k ⥤ GammaGroundRVObject hc B k where
  obj U := GammaGroundRVObject.ofNamed U hp
  map f := GammaGroundBijection.ofNamed f hp
  map_id U := by apply GammaGroundBijection.ext; apply GammaGroundMap.ext; intro a; rfl
  map_comp f g := by apply GammaGroundBijection.ext; apply GammaGroundMap.ext; intro a; rfl

instance namedRVToGammaGroundFaithful (hp : GammaGroundDefinable hc B P {p}) :
    (namedRVToGammaGround (k := k) hp).Faithful where
  map_injective := by
    intro U V f g h
    apply NamedBijection.ext
    apply NamedMap.ext
    intro a
    exact congrArg (fun q : GammaGroundRVObject.ofNamed U hp ⟶ GammaGroundRVObject.ofNamed V hp => q.map a) h

def GammaGroundMeasuredRVHom.ofNamed
    {U V : NamedMeasuredRVObject P p hc B.real k} (f : NamedMeasuredRVHom U V)
    (hp : GammaGroundDefinable hc B P {p}) :
    GammaGroundMeasuredRVHom (GammaGroundMeasuredRVObject.ofNamed U hp) (GammaGroundMeasuredRVObject.ofNamed V hp) :=
  ⟨GammaGroundBijection.ofNamed f.bijection hp,f.preserves⟩

/-- Both objects and their full pointwise combined-weight equations are
retained when eliminating the imaginary name. -/
def namedMeasuredRVToGammaGround (hp : GammaGroundDefinable hc B P {p}) :
    NamedMeasuredRVObject P p hc B.real k ⥤ GammaGroundMeasuredRVObject hc B k where
  obj U := GammaGroundMeasuredRVObject.ofNamed U hp
  map f := GammaGroundMeasuredRVHom.ofNamed f hp
  map_id U := by apply GammaGroundMeasuredRVHom.ext; apply GammaGroundBijection.ext; apply GammaGroundMap.ext; intro a; rfl
  map_comp f g := by apply GammaGroundMeasuredRVHom.ext; apply GammaGroundBijection.ext; apply GammaGroundMap.ext; intro a; rfl

instance namedMeasuredRVToGammaGroundFaithful (hp : GammaGroundDefinable hc B P {p}) :
    (namedMeasuredRVToGammaGround (k := k) hp).Faithful where
  map_injective := by
    intro U V f g h
    apply NamedMeasuredRVHom.ext
    apply NamedBijection.ext
    apply NamedMap.ext
    intro a
    exact congrArg (fun q : GammaGroundMeasuredRVObject.ofNamed U hp ⟶ GammaGroundMeasuredRVObject.ofNamed V hp => q.bijection.map a) h

variable [TopologicalSpace (Section2.VF M)]
def namedVFToGammaGround (hp : GammaGroundDefinable hc B P {p}) :
    NamedVFObject P p B.real k ⥤ GammaGroundVFObject hc B k where
  obj U := GammaGroundVFObject.ofNamed U hp
  map f := GammaGroundBijection.ofNamed f hp
  map_id U := by apply GammaGroundBijection.ext; apply GammaGroundMap.ext; intro a; rfl
  map_comp f g := by apply GammaGroundBijection.ext; apply GammaGroundMap.ext; intro a; rfl

instance namedVFToGammaGroundFaithful (hp : GammaGroundDefinable hc B P {p}) :
    (namedVFToGammaGround (k := k) hp).Faithful where
  map_injective := by
    intro U V f g h
    apply NamedBijection.ext
    apply NamedMap.ext
    intro a
    exact congrArg (fun q : GammaGroundVFObject.ofNamed U hp ⟶ GammaGroundVFObject.ofNamed V hp => q.map a) h
end DiamondIntegral.Section3
