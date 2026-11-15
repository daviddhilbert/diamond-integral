import «section 5».OriginalEulerCertificateExistence
import «section 5».OriginalGammaTreeRecoding
import «section 5».EulerCertificateCongruence

/-! Recoding a finite original Euler package retains every tree and source
row, so its validity and both fixed integer values descend together. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
open DiamondIntegral.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p q n : ℕ} {sp : Fin p → SortTag} {sq : Fin q → SortTag}

def OriginalEulerCertificate.recode (R : GammaParameterRecode B p q sp sq)
    (C : OriginalEulerCertificate B sp n) : OriginalEulerCertificate B sq n :=
  ⟨C.size, fun i => (C.cells i).recode R⟩

def OriginalEulerCertificate.RowAgreement (R : GammaParameterRecode B p q sp sq)
    (C : OriginalEulerCertificate B sp n) (z : Fin p → M) (t : Fin q → M) : Prop :=
  ∀ i, (C.cells i).RowAgreement R z t

theorem OriginalEulerCertificate.recode_validity_iff (hc : CanonicalStructure.IsCanonical (M := M))
    (R : GammaParameterRecode B p q sp sq) (C : OriginalEulerCertificate B sp n)
    (D : GammaDomainFormula B p n sp) (z : Fin p → M) (t : Fin q → M)
    (hC : C.RowAgreement R z t) (hD : R.DomainAgreement D z t)
    (U : LRV.Formula (Fin 1)) (E T : LRV.Formula (Fin 2)) :
    ((C.syntax hc).validity U E T (gammaDomainSyntax hc B D)).Realize (predicateParameterValues B z) ↔
      (((C.recode R).syntax hc).validity U E T (gammaDomainSyntax hc B (R.domain D))).Realize
        (predicateParameterValues B t) := by
  exact (C.syntax hc).validity_congr (fun i => ((C.cells i).recode R).syntax hc) U E T
    _ _ _ _ (fun i => (C.cells i).syntax_recode_related hc R z t (hC i)) (by
      intro x
      rw [gammaDomainSyntax_realize, gammaDomainSyntax_realize]
      exact hD x)

theorem OriginalEulerCertificate.recode_eulerValue (hc : CanonicalStructure.IsCanonical (M := M))
    (R : GammaParameterRecode B p q sp sq) (C : OriginalEulerCertificate B sp n) (k : EulerKind) :
    ((C.recode R).syntax hc).eulerValue k = (C.syntax hc).eulerValue k := by
  exact Finset.sum_congr rfl (fun i _ =>
    congrArg (fun s => s.eulerValue k) ((C.cells i).recode_shape hc R))

end DiamondIntegral.Section5
