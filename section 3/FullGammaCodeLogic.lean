import «section 3».FullRawLogic
import IntegrationSection3ACVF.FullGammaSyntax
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem fullRaw_sameScalar {ι : Type} [Finite ι] (B : FullBaseAtomicity.Base (M := M)) (i j : ι) :
    FullRawDefinable B (fun z => SameScalar (z i) (z j)) := by
  let R : M → M → Prop := SameScalar
  let S := B.real
  have hR : @Set.Definable M S LRV (CanonicalStructure.normalize (M := M)) (Fin 2)
      {z | R (z 0) (z 1)} := same_scalar_normalized_definable S
  have hd : @Set.Definable M S LRV (CanonicalStructure.normalize (M := M)) ι {z | R (z i) (z j)} := by
    letI := CanonicalStructure.normalize (M := M)
    exact hR.preimage_comp (![i,j] : Fin 2 → ι)
  exact FullBaseAtomicity.OverBase.of_real hd

theorem gammaCode_same_iff {ι : Type} (c u : ι → M) (hu : GammaSyntax.Proper u) :
    (∀ i, SameScalar (c i) (u i)) ↔ GammaSyntax.Proper c ∧ GammaSyntax.decode c = GammaSyntax.decode u := by
  constructor
  · intro h
    refine ⟨fun i => (h i).1,?_⟩
    funext i
    let a : Code (M := M) := ⟨⟨c i,(h i).1.1⟩,(h i).1.2⟩
    let b : Code (M := M) := ⟨⟨u i,(hu i).1⟩,(hu i).2⟩
    exact (codeValue_raw a).trans (((value_eq_iff a b).mpr (h i).2.2).trans (codeValue_raw b).symm)
  · rintro ⟨hc,he⟩ i
    let a : Code (M := M) := ⟨⟨c i,(hc i).1⟩,(hc i).2⟩
    let b : Code (M := M) := ⟨⟨u i,(hu i).1⟩,(hu i).2⟩
    have hv : value a = value b := (codeValue_raw a).symm.trans ((congrFun he i).trans (codeValue_raw b))
    exact ⟨hc i,hu i,(value_eq_iff a b).mp hv⟩

theorem gammaTuple_has_full_code {ι : Type} (γ : ι → Values.Gamma (M := M)) :
    ∃ c : ι → M, GammaSyntax.Proper c ∧ GammaSyntax.decode c = γ := by
  choose c hc hval using fun i => EndpointLogic.codeValue_surjective (γ i)
  exact ⟨c,hc,funext hval⟩
end DiamondIntegral.Section3
