import «section 3».GammaMeasuredIndexedBaseEssential
import «section 3».GammaMeasuredIndexedAgreements
import «section 3».GammaMeasuredIndexedGeometry

/-! Comparing a raw indexed family with an exact presentation of its
normalized rows commutes with removing zero-volume indices. This uses
literal measured isomorphisms before taking the principal quotient. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p a d k : ℕ}
variable {T : Set (Fin p → RV (M := M))}
variable {R : (Fin p → RV (M := M)) → (Fin d → RV (M := M)) → Prop}

theorem gammaMeasuredIndexed_normalized_comparison
    (F G : GammaMeasuredRVSchema hc B p a (k+1) (fun _ => .rv))
    (BP : GammaFiniteGraphPresentation B p d T R)
    (hF : ∀ t ∈ T, F.valid (rvValues t)) (hG : ∀ t ∈ T, G.valid (rvValues t))
    (hEq : ∀ t ∈ T, F.essential.toRVTemplate.sameRow G.toRVTemplate (rvValues t))
    (P : F.object.IndexedPresentation BP) (Q : G.object.IndexedPresentation (essentialIndexPresentation BP)) :
    gammaMeasuredPrincipalValue (F.indexedObject BP hF P) =
      gammaMeasuredPrincipalValue (G.indexedObject (essentialIndexPresentation BP) (fun t ht => hG t ht.1) Q) := by
  let hE : ∀ t ∈ T, F.essential.valid (rvValues t) := fun t ht => F.essential_valid _ (hF t ht)
  let PR := F.essential.object.indexedPresentation_finiteRows BP (fun t ht => F.essential.object.finiteRow_of_valid _ (hE t ht).1)
  let PS := G.object.indexedPresentation_finiteRows BP (fun t ht => G.object.finiteRow_of_valid _ (hG t ht).1)
  obtain ⟨eF⟩ := F.indexedEssential BP hF P PR
  obtain ⟨eG⟩ := F.essential.indexedAgreement G BP hE hG hEq PR PS
  obtain ⟨eB⟩ := G.indexedBaseEssential BP hG PS Q
  exact (gammaMeasuredPrincipalValue_iso eF).trans
    ((gammaMeasuredPrincipalValue_iso eG).trans (gammaMeasuredPrincipalValue_iso eB))

end DiamondIntegral.Section3
