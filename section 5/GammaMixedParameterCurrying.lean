import «section 5».OriginalPredicateSyntax
import IntegrationSection6.GammaSortedRelationPromotion

/-! Original RV base coordinates can be carried as free RV columns during
VF preparation, then restored to the parameter block by exact currying. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p q a b : ℕ} {sp : Fin p → SortTag}

def carryRVParameterDomain (D : GammaDomainFormula B (p+q) a
    (Fin.append sp (fun _ : Fin q => .rv))) : GammaDomainFormula B p (q+a) sp :=
  ⟨{w | w ∘ Fin.cast (Nat.add_assoc p q a) ∈ D.val ∧
      w ∈ sortedUniverse (Fin.append sp (fun _ : Fin (q+a) => .rv))},
    D.property.preimage_real _ (Fin.cast (Nat.add_assoc p q a))⟩

theorem carryRVParameterDomain_row (D : GammaDomainFormula B (p+q) a
    (Fin.append sp (fun _ : Fin q => .rv))) (u : Fin p → M) (v : Fin q → M) (x : Fin a → M) :
    Fin.append u (Fin.append v x) ∈ (carryRVParameterDomain D).val ↔ Fin.append (Fin.append u v) x ∈ D.val := by
  change (_ ∈ D.val ∧ _) ↔ _
  rw [← Fin.append_assoc]
  constructor
  · exact And.left
  · intro h
    refine ⟨h, ?_⟩
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [Fin.append_left] using D.property.proper _ h (Fin.castAdd a (Fin.castAdd q j))
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · simpa only [Fin.append_left, Fin.append_right] using D.property.proper _ h (Fin.castAdd a (Fin.natAdd p j))
      · simpa only [Fin.append_right] using D.property.proper _ h (Fin.natAdd (p+q) j)

def uncarryRVParameterDomain (D : GammaDomainFormula B p (q+a) sp) :
    GammaDomainFormula B (p+q) a (Fin.append sp (fun _ : Fin q => .rv)) :=
  ⟨{w | w ∘ Fin.cast (Nat.add_assoc p q a).symm ∈ D.val ∧
      w ∈ sortedUniverse (Fin.append (Fin.append sp (fun _ : Fin q => .rv)) (fun _ : Fin a => .rv))},
    D.property.preimage_real _ (Fin.cast (Nat.add_assoc p q a).symm)⟩

theorem uncarryRVParameterDomain_row (D : GammaDomainFormula B p (q+a) sp)
    (u : Fin p → M) (v : Fin q → M) (x : Fin a → M) :
    Fin.append (Fin.append u v) x ∈ (uncarryRVParameterDomain D).val ↔ Fin.append u (Fin.append v x) ∈ D.val := by
  change (_ ∈ D.val ∧ _) ↔ _
  rw [append_assoc_cast_symm]
  constructor
  · exact And.left
  · intro h
    refine ⟨h, ?_⟩
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · simpa only [Fin.append_left] using D.property.proper _ h (Fin.castAdd (q+a) j)
      · simpa only [Fin.append_left, Fin.append_right] using D.property.proper _ h (Fin.natAdd p (Fin.castAdd a j))
    · simpa only [Fin.append_right] using D.property.proper _ h (Fin.natAdd p (Fin.natAdd q j))

def flattenGammaRelation (R : GammaRelationFormula B p a b sp) : GammaDomainFormula B p (a+b) sp :=
  carryRVParameterDomain (⟨R.val, R.property⟩ : GammaDomainFormula B (p+a) b (Fin.append sp (fun _ => .rv)))

theorem flattenGammaRelation_row (R : GammaRelationFormula B p a b sp)
    (z : Fin p → M) (x : Fin a → M) (y : Fin b → M) :
    Fin.append z (Fin.append x y) ∈ (flattenGammaRelation R).val ↔ Fin.append (Fin.append z x) y ∈ R.val :=
  carryRVParameterDomain_row _ z x y

def unflattenGammaRelation (D : GammaDomainFormula B p (a+b) sp) : GammaRelationFormula B p a b sp :=
  ⟨(uncarryRVParameterDomain D).val, (uncarryRVParameterDomain D).property⟩

theorem unflattenGammaRelation_row (D : GammaDomainFormula B p (a+b) sp)
    (z : Fin p → M) (x : Fin a → M) (y : Fin b → M) :
    Fin.append (Fin.append z x) y ∈ (unflattenGammaRelation D).val ↔ Fin.append z (Fin.append x y) ∈ D.val :=
  uncarryRVParameterDomain_row D z x y

end DiamondIntegral.Section5
