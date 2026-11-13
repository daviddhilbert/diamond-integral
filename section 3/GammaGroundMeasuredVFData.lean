import «section 3».GammaGroundLifting
import «section 3».GammaGroundVolumeForms

/-! Measured VF object data over the entire Gamma ground, including
all degree-zero forms. The object lift pulls back the original RV form. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

structure GammaGroundMeasuredVFData (hc : CanonicalStructure.IsCanonical (M := M))
    (ground : GammaParameters.Base (M := M)) (k : ℕ) where
  arity : ℕ
  domain : GammaGroundDefSet hc ground (rawMixedSpace (M := M) k arity)
  finite : ∀ a, {t | (a, t) ∈ domain.carrier}.Finite
  form : GammaGroundVolumeForm hc ground domain

variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)} {k : ℕ}

def gammaGroundObjectLiftLabel (U : GammaGroundRVObject hc ground k) :
    GammaGroundMap (gammaGroundObjectLift U) U.domain :=
  GammaGroundMap.ofGlobal (gammaGroundObjectLift U) U.domain
    (universalProductSnd (rawVFSpace k) (rawRVSpace U.arity) ground.real)
    (fun q => by
      obtain ⟨u, hu, _⟩ := q.property
      change q.val.2 ∈ U.domain.carrier
      exact hu ▸ u.property)

@[simp] theorem gammaGroundObjectLiftLabel_value (U : GammaGroundRVObject hc ground k) (q : gammaGroundObjectLift U) :
    (gammaGroundObjectLiftLabel U q).val = q.val.2 := rfl

def gammaGroundMeasuredObjectLift (U : GammaGroundMeasuredRVObject hc ground k) : GammaGroundMeasuredVFData hc ground k where
  arity := U.underlying.arity
  domain := gammaGroundObjectLift U.underlying
  finite := gammaGroundObjectLift_finite_rv_fibres U.underlying
  form := U.form.comp (gammaGroundObjectLiftLabel U.underlying)

@[simp] theorem gammaGroundMeasuredObjectLift_form (U : GammaGroundMeasuredRVObject hc ground k)
    (q : gammaGroundObjectLift U.underlying) :
    gammaGroundFormValue (gammaGroundMeasuredObjectLift U).form q =
      gammaGroundFormValue U.form (gammaGroundObjectLiftLabel U.underlying q) := rfl

def GammaGroundMeasuredVFData.restrict (U : GammaGroundMeasuredVFData hc ground k)
    (X : GammaGroundDefSet hc ground (rawMixedSpace (M := M) k U.arity))
    (hX : X.carrier ⊆ U.domain.carrier) : GammaGroundMeasuredVFData hc ground k :=
  ⟨U.arity, X, fun a => (U.finite a).subset (fun _ hx => hX hx), U.form.comp (GammaGroundMap.inclusion hX)⟩

def GammaGroundMeasuredVFData.empty (hc : CanonicalStructure.IsCanonical (M := M))
    (ground : GammaParameters.Base (M := M)) (k : ℕ) : GammaGroundMeasuredVFData hc ground k where
  arity := 0
  domain := GammaGroundDefSet.empty hc ground (rawMixedSpace k 0)
  finite _ := Set.finite_empty
  form := gammaGroundOneForm _

def GammaGroundMeasuredVFData.unit (hc : CanonicalStructure.IsCanonical (M := M))
    (ground : GammaParameters.Base (M := M)) : GammaGroundMeasuredVFData hc ground 0 where
  arity := 0
  domain := GammaGroundDefSet.univ hc ground (rawMixedSpace 0 0)
  finite _ := Set.Subsingleton.finite (fun x _ y _ => funext (fun i => i.elim0))
  form := gammaGroundOneForm _

end DiamondIntegral.Section3
