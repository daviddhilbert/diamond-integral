import «section 5».NativeAllVFBaseNormalForm
import «section 5».FiniteFormulaPreparation
import «section 5».NativeVFLiftFamilies

/-! Every actual original-ground mixed VF domain admits an actual
original-ground bijection to an RV-pullback. One genuine special
bijection prepares its full domain predicate with every old RV payload. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
open IntegrationInACVF.Section6
open DiamondIntegral.Section3 DiamondIntegral.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n r : ℕ}

theorem native_arbitrary_vf_pullback_preparation
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ)
    (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)) :
    ∃ l : ℕ,∃ Y : GammaGroundDefSet hc B (rawMixedSpace (M := M) n (l+r)),
      Nonempty (GammaGroundBijection A Y) ∧ IsRVPullback Y.carrier := by
  let D : GammaDomainFormula B n r (fun _ => .vf) := ⟨nativeMixedDomain A,nativeMixedDomain_definable A⟩
  let A0 : DefSet (M := M) B.real n 0 := PresentedSet.univ (pointSpace n 0) B.real
  have hA0 : GammaSetDefinable B (carrier A0) := (gammaLogicInput B).real_set _ (setDefinable A0)
  obtain ⟨R,hSR,hBR,l,C,T,hT,hC,hrows⟩ := prepare_finite_original_base_RV_predicates
    hκ hs h00 B hr A0 hA0 (fun _ : Unit => r) (fun _ => D)
  let TΓ := nativeSpecialBaseBijection (hc := hc) T hT
  have hP : ∀ a : A,((nativeMixedCoordinateMap A (Fin.castAdd 0) (Fin.elim0 : Fin 0 → Fin r)) a).val ∈
      (nativeGammaPointDomain (hc := hc) (carrier (SpecialTransformations.Section5.extendBase A0 hSR))
        (GammaChainDefinable.source B T.chain hT)).carrier := fun _ => Set.mem_univ _
  let Y := (nativeVFPrepareBaseMap (k := 0) A TΓ hP).image
  refine ⟨l,Y,⟨nativeVFPrepareBaseBijection (k := 0) A TΓ hP⟩,?_⟩
  apply nativeVFPrepareAll_pullback A TΓ hP hC
    (fun t u => Fin.append (rvValues t) (rvValues u) ∈ ((GammaParameterRecode.prepared T hT).domain D).val)
  intro c u
  have hcode := nativeSpecialBaseBijection_parameter T hT c u
  have hmem := (nativeMixedCode_mem_domain_iff A ((TΓ.symm.map c).val.1,u)).symm
  have hh : nativeMixedCode ((TΓ.symm.map c).val.1,u) ∈ D.val ↔
      Fin.append (rawVFParameter (T.inverseMap ⟨c.val,c.property⟩).val) (rvValues u) ∈ D.val :=
    (congrArg (fun w => w ∈ D.val) hcode).to_iff
  exact hmem.trans (hh.trans (hrows () ⟨c.val,c.property⟩ (rvValues u)))

end DiamondIntegral.Section5
