import «section 5».RESSetSchemata
import IntegrationSection6.GammaRecodingAgreements

/-! Exact original-base row recoding preserves actual native RES validity
and its fixed support bound. The row domain itself is unchanged. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p q a : ℕ} {sp : Fin p → SortTag} {sq : Fin q → SortTag}

def RESSetSchema.recode (R : GammaParameterRecode B p q sp sq) (F : RESSetSchema B p a sp) :
    RESSetSchema B q a sq := ⟨R.domain F.domain, F.valueBound⟩

theorem RESSetSchema.recode_valueBound (R : GammaParameterRecode B p q sp sq) (F : RESSetSchema B p a sp) :
    (F.recode R).valueBound = F.valueBound := rfl

theorem RESSetSchema.recode_rowDomain (R : GammaParameterRecode B p q sp sq)
    (F : RESSetSchema B p a sp) (z : Fin p → M) (t : Fin q → M)
    (h : R.DomainAgreement F.domain z t) : F.rowDomain z = (F.recode R).rowDomain t := by
  ext x
  exact h x

theorem RESSetSchema.recode_valid_iff (hc : CanonicalStructure.IsCanonical (M := M))
    (R : GammaParameterRecode B p q sp sq) (F : RESSetSchema B p a sp)
    (z : Fin p → M) (t : Fin q → M)
    (hz : ∀ i, sortEval (sp i) (z i)) (ht : ∀ i, sortEval (sq i) (t i))
    (h : R.DomainAgreement F.domain z t) : F.Valid hc z ↔ (F.recode R).Valid hc t := by
  rw [F.valid_iff_finite_values hc z, (F.recode R).valid_iff_finite_values hc t,
    F.recode_rowDomain R z t h, F.recode_valueBound R]
  exact and_congr (iff_of_true hz ht) Iff.rfl

end DiamondIntegral.Section5
