import «section 5».RVRectangleUniformity
import «section 5».RVRectangleCatalogPreparation

/-! Actual RV product decompositions, all Euler certificates and their
entire map graphs descend from mixed VF/RV parameters to one prepared RV
key, by finite original-base uniformization followed by one special map. -/
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

theorem rv_rectangle_families_descend (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : DiamondIntegral.Section2.NontrivialDefinableGamma B)
    {S : Set M} {p q a : ℕ} (A : DefSet (M := M) S p 0)
    (hA : GammaSetDefinable B (carrier A))
    (D : GammaDomainFormula B (p+q) a (Fin.append (fun _ : Fin p => .vf) (fun _ : Fin q => .rv))) :
    ∃ J : Finset (RVRectangleDecompositionSchema D),
      ∃ R : Set M, ∃ hSR : S ⊆ R, ∃ hBR : B.real ⊆ R,
      ∃ l : ℕ, ∃ C : DefSet (M := M) R p l,
      ∃ T : SpecialBijection (SpecialTransformations.Section5.extendBase A hSR) C,
      ∃ hT : GammaChainDefinable B T.chain,
      IsRVPullback (carrier C) ∧
      ∀ (x : C) (v : Fin q → M), (∀ i, iRV (v i)) →
        ∃ W ∈ J, (W.recode (mixedPreparedParameterRecode T hT q)).Valid hc
          (Fin.append (rawPreparedKey x.val) v) := by
  let sp := Fin.append (fun _ : Fin p => SortTag.vf) (fun _ : Fin q => SortTag.rv)
  have hsp : DefinableOverBase B sp (sortedUniverse sp) :=
    real_definableOverBase B sp (sortedUniverse sp) (sortedUniverse_definable B.real sp)
  obtain ⟨J,hJ⟩ := rv_rectangle_finite_catalog hc h00 (le_of_lt hκ) hs hr hγ hΓ (sortedUniverse sp) hsp D
  obtain ⟨R,hSR,hBR,l,C,T,hT,hC,hvalid⟩ := prepare_rv_rectangle_catalog hc hκ hs h00 B hr A hA D J
  refine ⟨J,R,hSR,hBR,l,C,T,hT,hC,?_⟩
  intro x v hv
  have hz : Fin.append (rawVFParameter (T.inverseMap x).val) v ∈ sortedUniverse sp := by
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [sp,Fin.append_left,rawVFParameter] using ((T.inverseMap x).val.1 j).property
    · simpa only [sp,Fin.append_right,sortEval,iRV] using hv j
  obtain ⟨W,hW,hWV⟩ := hJ _ hz
  exact ⟨W,hW,(hvalid W hW x v hv).mp hWV⟩

end DiamondIntegral.Section5
