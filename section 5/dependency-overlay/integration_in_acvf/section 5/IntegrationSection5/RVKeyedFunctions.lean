import IntegrationSection5.RVRecodeInjection
import IntegrationSection5.GammaScalarUpdate

/-! Transport a scalar function through an actual RV recoding, retaining its full original-base graph. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section3ACVF
open IntegrationInACVF.Section4
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)} {m d : ℕ} {A : Set (Point (M := M) 1 m)}

def rvKeyedFunction (Q : GammaRVMap G A d)
    (hQ : ∀ a b, Q.toFun a = Q.toFun b → a.val.2 = b.val.2)
    (g : A → VF (M := M)) (u : rvRecodeTarget Q) : VF (M := M) :=
  g ((rvRecodeIso Q hQ).equiv.symm u)

theorem rvKeyedFunction_graph (Q : GammaRVMap G A d)
    (hQ : ∀ a b, Q.toFun a = Q.toFun b → a.val.2 = b.val.2)
    (g : A → VF (M := M))
    (hg : GammaScalarGraphDefinable G (fun p y => ∃ a : A, a.val = p ∧ g a = y)) :
    GammaScalarGraphDefinable G (fun p y => ∃ u : rvRecodeTarget Q, u.val = p ∧ rvKeyedFunction Q hQ g u = y) :=
  gamma_iso_precomp_scalar (GammaIso.symm (gammaLogicInput G) (rvRecodeIso Q hQ)) g hg

theorem rvKeyedFunction_apply (Q : GammaRVMap G A d)
    (hQ : ∀ a b, Q.toFun a = Q.toFun b → a.val.2 = b.val.2)
    (g : A → VF (M := M)) (a : A) :
    rvKeyedFunction Q hQ g ((rvRecodeIso Q hQ).equiv a) = g a := by
  exact congrArg g ((rvRecodeIso Q hQ).equiv.symm_apply_apply a)

theorem rvKeyedFunction_original (Q : GammaRVMap G A d)
    (hQ : ∀ a b, Q.toFun a = Q.toFun b → a.val.2 = b.val.2)
    (u : rvRecodeTarget Q) :
    rvRecodePoint Q ((rvRecodeIso Q hQ).equiv.symm u) = u.val :=
  congrArg Subtype.val ((rvRecodeIso Q hQ).equiv.apply_symm_apply u)

end IntegrationInACVF.Section5

