import «section 3».MeasuredVFData
import «section 3».GammaFormOperations
import Section4.VFProducts

/-! Measured VF object products use genuine mixed products and the
product of the two pulled-back Gamma forms, uniformly including degree zero. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4

noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {C : BaseContext M} {hc : CanonicalStructure.IsCanonical (M := M)} {k l : ℕ}

def measuredVFProductLeft (U : MeasuredVFData C hc k) (V : MeasuredVFData C hc l) :
    Map (mixedProductDomain U.domain V.domain) U.domain :=
  (Map.prodFst U.domain V.domain).comp (mixedUnpack U.domain V.domain)

def measuredVFProductRight (U : MeasuredVFData C hc k) (V : MeasuredVFData C hc l) :
    Map (mixedProductDomain U.domain V.domain) V.domain :=
  (Map.prodSnd U.domain V.domain).comp (mixedUnpack U.domain V.domain)

def MeasuredVFData.product (U : MeasuredVFData C hc k) (V : MeasuredVFData C hc l) :
    MeasuredVFData C hc (k + l) where
  arity := U.arity + V.arity
  domain := mixedProductDomain U.domain V.domain
  finite := finiteRVFibres_product (U := ⟨(k, U.arity), U.domain⟩)
    (V := ⟨(l, V.arity), V.domain⟩) U.finite V.finite
  form := GammaVolumeForm.mul (U.form.comp (measuredVFProductLeft U V))
    (V.form.comp (measuredVFProductRight U V))

@[simp] theorem MeasuredVFData.product_form (U : MeasuredVFData C hc k)
    (V : MeasuredVFData C hc l) (a : (U.product V).domain) :
    gammaFormValue (U.product V).form a =
      gammaFormValue U.form (measuredVFProductLeft U V a) *
        gammaFormValue V.form (measuredVFProductRight U V a) := rfl

def MeasuredVFData.unit (C : BaseContext M) (hc : CanonicalStructure.IsCanonical (M := M)) :
    MeasuredVFData C hc 0 where
  arity := 0
  domain := DefSet.univ (rawMixedSpace 0 0) (C.base : Set M)
  finite a := by
    change Set.Finite {t : Fin 0 → CanonicalRV.RVSort M |
      (a, t) ∈ (DefSet.univ (rawMixedSpace 0 0) (C.base : Set M)).carrier}
    exact Set.Subsingleton.finite (fun x _ y _ => funext (fun i => i.elim0))
  form := gammaOneForm hc _

end DiamondIntegral.Section3
