import «section 6».InvariantValueBounds

/-! Products of named Gamma values retain all proper RV representatives
over the original base. No representative is adjoined. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}

theorem gamma_mul_named (hc : CanonicalStructure.IsCanonical (M := M)) (a b : Gamma M)
    (ha : S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {a}})
    (hb : S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {b}}) :
    S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {a*b}} := by
  have hMul := gammaMultiplyNamedCodeRelation_definable hc b hb
  change S.Definable LRV {z : Fin 2 → M | GammaParameters.NonzeroRV (z 0) ∧ GammaParameters.NonzeroRV (z 1) ∧
    GammaParameters.codeValue (z 1)=GammaParameters.codeValue (z 0)*b} at hMul
  let e : Fin 2 → Fin 1 ⊕ Fin 1 := ![.inr 0,.inl 0]
  have h := ((ha.preimage_comp (Sum.inr : Fin 1 → Fin 1 ⊕ Fin 1)).inter (hMul.preimage_comp e)).exists_of_finite
  convert h using 1
  ext z
  change (z 0 ∈ Values.gammaPullback {a*b}) ↔
    ∃ w : Fin 1 → M,w 0 ∈ Values.gammaPullback {a} ∧
      GammaParameters.NonzeroRV (w 0) ∧ GammaParameters.NonzeroRV (z 0) ∧
        GammaParameters.codeValue (z 0)=GammaParameters.codeValue (w 0)*b
  constructor
  · intro hz
    have hzNZ : GammaParameters.NonzeroRV (z 0) := ⟨hz.1,hz.2.1⟩
    obtain ⟨t,ht,hta⟩ := GammaParameters.EndpointLogic.codeValue_surjective a
    refine ⟨fun _ => t,(GammaParameters.gammaPullback_mem_codeValue_iff _ _ ht).mpr hta,ht,hzNZ,?_⟩
    exact ((GammaParameters.gammaPullback_mem_codeValue_iff _ _ hzNZ).mp hz).trans (by rw [hta])
  · rintro ⟨w,hw,hwnz,hznz,he⟩
    have hwa := (GammaParameters.gammaPullback_mem_codeValue_iff _ _ hwnz).mp hw
    apply (GammaParameters.gammaPullback_mem_codeValue_iff _ _ hznz).mpr
    exact he.trans (congrArg (fun x : Gamma M => x*b) hwa)

end DiamondIntegral.Section6
