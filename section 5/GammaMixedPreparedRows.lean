import «section 5».GammaMixedParameterCurrying
import «section 5».FiniteFormulaPreparation

/-! Prepared VF keys retain the original RV parameter block. Exact
full-domain and graph rows descend without naming any Gamma representative. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {p q l a b n : ℕ}

theorem append_rv_sort (p q : ℕ) :
    Fin.append (fun _ : Fin p => SortTag.rv) (fun _ : Fin q => SortTag.rv) = (fun _ => .rv) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp only [Fin.append_left, Fin.append_right]

def restoreRVParameters (D : GammaDomainFormula B n (q+a) (fun _ => .rv)) :
    GammaDomainFormula B (n+q) a (fun _ => .rv) := by
  let E := uncarryRVParameterDomain D
  refine ⟨E.val, ?_⟩
  simpa only [append_rv_sort] using E.property

theorem restoreRVParameters_row (D : GammaDomainFormula B n (q+a) (fun _ => .rv))
    (u : Fin n → M) (v : Fin q → M) (x : Fin a → M) :
    Fin.append (Fin.append u v) x ∈ (restoreRVParameters D).val ↔
      Fin.append u (Fin.append v x) ∈ D.val :=
  uncarryRVParameterDomain_row D u v x

variable {A : DefSet (M := M) S p 0} {F : DefSet (M := M) S p l}

def mixedPreparedParameterRecode (T : SpecialBijection A F)
    (hT : GammaChainDefinable B T.chain) (q : ℕ) :
    GammaParameterRecode B (p+q) ((p+l)+q)
      (Fin.append (fun _ : Fin p => .vf) (fun _ : Fin q => .rv)) (fun _ => .rv) where
  domain D := restoreRVParameters ((carryRVParameterDomain D).preparedDescend T hT)
  relation H := unflattenGammaRelation
    (restoreRVParameters ((carryRVParameterDomain (flattenGammaRelation H)).preparedDescend T hT))

theorem mixedPreparedParameterRecode_domain_agreement (T : SpecialBijection A F)
    (hT : GammaChainDefinable B T.chain)
    (D : GammaDomainFormula B (p+q) a
      (Fin.append (fun _ : Fin p => .vf) (fun _ : Fin q => .rv))) (x : F)
    (hrow : (GammaParameterRecode.prepared T hT).DomainAgreement (carryRVParameterDomain D)
      (rawVFParameter (T.inverseMap x).val) (rawPreparedKey x.val)) (v : Fin q → M) :
    (mixedPreparedParameterRecode T hT q).DomainAgreement D
      (Fin.append (rawVFParameter (T.inverseMap x).val) v) (Fin.append (rawPreparedKey x.val) v) := by
  intro w
  exact (carryRVParameterDomain_row D _ v w).symm.trans
    ((hrow (Fin.append v w)).trans (restoreRVParameters_row _ _ v w).symm)

theorem mixedPreparedParameterRecode_relation_agreement (T : SpecialBijection A F)
    (hT : GammaChainDefinable B T.chain)
    (H : GammaRelationFormula B (p+q) a b
      (Fin.append (fun _ : Fin p => .vf) (fun _ : Fin q => .rv))) (x : F)
    (hrow : (GammaParameterRecode.prepared T hT).DomainAgreement
      (carryRVParameterDomain (flattenGammaRelation H))
      (rawVFParameter (T.inverseMap x).val) (rawPreparedKey x.val)) (v : Fin q → M) :
    (mixedPreparedParameterRecode T hT q).RelationAgreement H
      (Fin.append (rawVFParameter (T.inverseMap x).val) v) (Fin.append (rawPreparedKey x.val) v) := by
  intro u w
  exact (flattenGammaRelation_row H _ u w).symm.trans
    ((mixedPreparedParameterRecode_domain_agreement T hT (flattenGammaRelation H) x hrow v
      (Fin.append u w)).trans (unflattenGammaRelation_row _ _ u w).symm)

end DiamondIntegral.Section5
