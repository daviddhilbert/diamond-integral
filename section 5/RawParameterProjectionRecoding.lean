import «section 5».OriginalEulerRecoding
import «section 5».OriginalEulerRowValues
import «section 5».OriginalSortedPredicates

/-! Pulling original schemata back along arbitrary raw RV parameter
coordinate maps retains all domain, graph and whole Euler rows. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p q n : ℕ}

def rawParameterDomainIndex (f : Fin p → Fin q) (a : ℕ) : Fin (p+a) → Fin (q+a) :=
  Fin.append (Fin.castAdd a ∘ f) (Fin.natAdd q)

def rawParameterRelationIndex (f : Fin p → Fin q) (a b : ℕ) : Fin ((p+a)+b) → Fin ((q+a)+b) :=
  Fin.append (Fin.castAdd b ∘ rawParameterDomainIndex f a) (Fin.natAdd (q+a))

def rawParameterProjectionRecode (B : Base (M := M)) (f : Fin p → Fin q) :
    GammaParameterRecode B p q (fun _ => .rv) (fun _ => .rv) where
  domain := fun {a} D => ⟨{w | w ∈ sortedUniverse (Fin.append (fun _ : Fin q => .rv) (fun _ : Fin a => .rv)) ∧
      w ∘ rawParameterDomainIndex f a ∈ D.val},
    (OriginalSortedPredicate.of_definable D.property).pullback _ (by
      intro i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
        simp only [rawParameterDomainIndex,Function.comp_def,Fin.append_left,Fin.append_right])⟩
  relation := fun {a b} H => ⟨{w | w ∈ sortedUniverse
      (Fin.append (Fin.append (fun _ : Fin q => .rv) (fun _ : Fin a => .rv)) (fun _ : Fin b => .rv)) ∧
      w ∘ rawParameterRelationIndex f a b ∈ H.val},
    (OriginalSortedPredicate.of_definable H.property).pullback _ (by
      intro i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
          simp only [rawParameterRelationIndex,rawParameterDomainIndex,Function.comp_def,
            Fin.append_left,Fin.append_right]
      · simp only [rawParameterRelationIndex,Function.comp_def,Fin.append_right])⟩

theorem rawParameterProjectionRecode_domain_agreement (f : Fin p → Fin q)
    {a : ℕ} (D : GammaDomainFormula B p a (fun _ => .rv)) (t : Fin q → M)
    (ht : ∀ i, iRV (t i)) :
    (rawParameterProjectionRecode B f).DomainAgreement D (t ∘ f) t := by
  intro v
  have he : Fin.append t v ∘ rawParameterDomainIndex f a = Fin.append (t ∘ f) v := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp only [rawParameterDomainIndex,Function.comp_def,Fin.append_left,Fin.append_right]
  change _ ↔ (_ ∧ _)
  rw [he]
  constructor
  · intro hv
    refine ⟨?_,hv⟩
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [Fin.append_left,sortEval,iRV] using ht j
    · simpa only [Fin.append_right] using D.property.proper _ hv (Fin.natAdd p j)
  · exact And.right

theorem rawParameterProjectionRecode_relation_agreement (f : Fin p → Fin q)
    {a b : ℕ} (H : GammaRelationFormula B p a b (fun _ => .rv)) (t : Fin q → M)
    (ht : ∀ i, iRV (t i)) :
    (rawParameterProjectionRecode B f).RelationAgreement H (t ∘ f) t := by
  intro x y
  have he : Fin.append (Fin.append t x) y ∘ rawParameterRelationIndex f a b =
      Fin.append (Fin.append (t ∘ f) x) y := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
        simp only [rawParameterRelationIndex,rawParameterDomainIndex,Function.comp_def,
          Fin.append_left,Fin.append_right]
    · simp only [rawParameterRelationIndex,Function.comp_def,Fin.append_right]
  change _ ↔ (_ ∧ _)
  rw [he]
  constructor
  · intro hv
    refine ⟨?_,hv⟩
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · simpa only [Fin.append_left,sortEval,iRV] using ht j
      · simpa only [Fin.append_left,Fin.append_right] using
          H.property.proper _ hv (Fin.castAdd b (Fin.natAdd p j))
    · simpa only [Fin.append_right] using H.property.proper _ hv (Fin.natAdd (p+a) j)
  · exact And.right

theorem rawParameterProjectionRecode_euler_agreement (f : Fin p → Fin q)
    (C : OriginalEulerCertificate B (fun _ : Fin p => .rv) n) (t : Fin q → M)
    (ht : ∀ i, iRV (t i)) : C.RowAgreement (rawParameterProjectionRecode B f) (t ∘ f) t := by
  intro i
  apply ((C.cells i).rowAgreement_iff_predicates _ _ _).mpr
  intro D _
  exact rawParameterProjectionRecode_domain_agreement f D.2 t ht

theorem rawParameterProjectionRecode_euler_valid_iff
    (hc : CanonicalStructure.IsCanonical (M := M)) (f : Fin p → Fin q)
    (C : OriginalEulerCertificate B (fun _ : Fin p => .rv) n)
    (D : GammaDomainFormula B p n (fun _ => .rv)) (t : Fin q → M) (ht : ∀ i, iRV (t i)) :
    C.ValidFor hc D (t ∘ f) ↔ (C.recode (rawParameterProjectionRecode B f)).ValidFor hc
      ((rawParameterProjectionRecode B f).domain D) t :=
  C.recode_validity_iff hc _ D (t ∘ f) t (rawParameterProjectionRecode_euler_agreement f C t ht)
    (rawParameterProjectionRecode_domain_agreement f D t ht) (nativeGammaRelationSyntax hc).proper
    (nativeGammaRelationSyntax hc).equal (nativeGammaRelationSyntax hc).less

end DiamondIntegral.Section5
