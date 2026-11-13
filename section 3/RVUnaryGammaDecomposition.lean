import «section 3».RVUnaryValuePartition
import «section 3».GammaGroundGammaRVCodeMembership
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)}

def unaryGammaTopMap (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) :
    Map (DefSet.univ ((volumeGammaSpace hc).power (Fin 1)) S) (DefSet.univ gammaTopSpace S) := by
  let F : (Fin 1 × Fin 1 → M) → (Fin 1 → M) := fun z _ => z (0,0)
  refine Map.ofCodes _ (fun γ : Fin 1 → Values.Gamma (M := M) => (γ 0).val) F
    (fun _ => Set.DefinableFun.proj LRV) (fun c => (c.property (0 : Fin 1)).1) ?_
  intro c
  rfl

def unaryRVGammaPiece (A : GammaGroundDefSet hc ground (rawRVSpace (M := M) 1)) :
    GammaGroundGammaPiece hc ground 1 :=
  ⟨{γ | (γ 0).val ∈ (unaryRVFullValues A).carrier},
    (unaryRVFullValues A).definable.preimage (unaryGammaTopMap hc ground.real)⟩

theorem unaryRVCompletePart_eq_gammaLift (A : GammaGroundDefSet hc ground (rawRVSpace (M := M) 1)) :
    (unaryRVCompletePart A).carrier = (gammaGroundGammaRVCodeLift (unaryRVGammaPiece A)).domain.carrier := by
  ext t
  rw [gammaGroundGammaRVCodeLift_mem]
  constructor
  · intro ht
    let γ : Values.Gamma (M := M) := ⟨unaryRVValue t,ht.2⟩
    refine ⟨fun _ => γ,ht.1,?_⟩
    intro i
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    subst i
    rfl
  · rintro ⟨γ,hγ,he⟩
    change unaryRVValue t ∈ (unaryRVFullValues A).carrier ∧ unaryRVValue t ≠ Values.infinity
    have hγ' : (γ 0).val ∈ (unaryRVFullValues A).carrier := hγ
    have hval : unaryRVValue t = (γ 0).val := (he 0).symm
    exact ⟨hval.symm ▸ hγ',fun hz => (γ 0).property (hval.symm.trans hz)⟩

/-- Unary ACVF decomposition over the original full Gamma ground. The
residue part has finite complete-domain value support; the other part is
literally the full nonzero RV preimage of a definable Gamma piece. -/
theorem unaryRV_residue_gamma_decomposition
    (A : GammaGroundDefSet hc ground (rawRVSpace (M := M) 1)) :
    ∃ R : GammaGroundDefSet hc ground (rawRVSpace (M := M) 1),
      ∃ I : GammaGroundGammaPiece hc ground 1,
        ((fun t i => Values.vrv (t i)) '' R.carrier).Finite ∧
        Disjoint R.carrier (gammaGroundGammaRVCodeLift I).domain.carrier ∧
        R.carrier ∪ (gammaGroundGammaRVCodeLift I).domain.carrier = A.carrier := by
  refine ⟨unaryRVResiduePart A,unaryRVGammaPiece A,unaryRVResiduePart_finite_values A,?_,?_⟩
  · rw [← unaryRVCompletePart_eq_gammaLift A]
    exact unaryRVValuePartition_disjoint A
  · rw [← unaryRVCompletePart_eq_gammaLift A]
    exact unaryRVValuePartition A
end DiamondIntegral.Section3
