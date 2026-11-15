import «section 5».NativePreparedLiftGeometricComparison
import «section 5».NativePreparedGeometricRVValues
import «section 5».NativeSpecialBaseBridge

/-! A complete fixed geometric witness proves equality of the actual VF
lift-family geometric values. The denominator degree is chosen before one
genuine preparation; each base zero stratum is normalized in its common
total degree, with every old RV coordinate retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section6
open DiamondIntegral.Section3 DiamondIntegral.Section4 Section3RVCodeBridge
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {G : GammaGroundContext M}
variable {p q n r m s : ℕ}

theorem native_vf_fixed_geometric_whole_witness_fubini
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    (H : YinGammaGroundUnmeasuredLiftInput G hc)
    (Z : GammaGroundDefSet hc G.base (rawMixedSpace (M := M) p q))
    {D : Set (Fin ((p+q)+(n+r)) → M)} {E : Set (Fin ((p+q)+(m+s)) → M)}
    (W : NativeGeometricVFLiftEqualitySchema (B := G.base)
      (sp := Fin.append (fun _ : Fin p => .vf) (fun _ : Fin q => .rv)) hc D E)
    (hW : ∀ b : Z,W.Valid (nativeMixedCode b.val))
    (hf : ∀ x : Fin (p+W.leftDegree) → Section2.VF M,
      {t | (x,t) ∈ (nativeVFLiftFamily Z W.leftRV).carrier}.Finite)
    (hf' : ∀ x : Fin (p+W.rightDegree) → Section2.VF M,
      {t | (x,t) ∈ (nativeVFLiftFamily Z W.rightRV).carrier}.Finite) :
    nativeVFGeometricValue linear H (nativeVFClass
        (⟨p+W.leftDegree,q+W.leftArity,nativeVFLiftFamily Z W.leftRV,hf⟩ : GammaGroundFiniteVFObject hc G.base)) =
      nativeVFGeometricValue linear H (nativeVFClass
        (⟨p+W.rightDegree,q+W.rightArity,nativeVFLiftFamily Z W.rightRV,hf'⟩ : GammaGroundFiniteVFObject hc G.base)) := by
  let Z0 := nativePreparedLiftBaseDomain Z
  have hWraw : ∀ z,Fin.append z (Fin.elim0 : Fin 0 → M) ∈ Z0.val → W.Valid z := by
    intro z hz
    have hz' : z ∈ nativeMixedDomain Z :=
      (originalParameterDomain_row (nativeMixedDomain Z) (nativeMixedDomain_definable Z) z).mp hz
    obtain ⟨b,hb,he⟩ := hz'
    exact he ▸ hW ⟨b,hb⟩
  let A0 : DefSet (M := M) G.base.real p 0 := PresentedSet.univ (pointSpace p 0) G.base.real
  have hA : GammaSetDefinable G.base (carrier A0) :=
    (gammaLogicInput G.base).real_set _ (setDefinable A0)
  obtain ⟨R,hSR,hBR,l,C,T,hT,hpull,hprep⟩ := prepare_native_geometric_vf_lift_RV_data
    G.uncountable G.saturated G.model00 G.base G.small_real A0 hA D E W Z0
  let hC := GammaChainDefinable.target G.base T.chain hT
  let Rcode := mixedPreparedParameterRecode T hT q
  let TΓ := nativeSpecialBaseBijection (hc := hc) T hT
  have hP : ∀ x : nativeVFLiftFamily Z W.leftRV,
      ((nativeMixedCoordinateMap (nativeVFLiftFamily Z W.leftRV) (Fin.castAdd W.leftDegree)
        (Fin.elim0 : Fin 0 → Fin (q+W.leftArity))) x).val ∈
        (nativeGammaPointDomain (hc := hc) (carrier (SpecialTransformations.Section5.extendBase A0 hSR))
          (GammaChainDefinable.source G.base T.chain hT)).carrier := fun _ => Set.mem_univ _
  have hP' : ∀ x : nativeVFLiftFamily Z W.rightRV,
      ((nativeMixedCoordinateMap (nativeVFLiftFamily Z W.rightRV) (Fin.castAdd W.rightDegree)
        (Fin.elim0 : Fin 0 → Fin (q+W.rightArity))) x).val ∈
        (nativeGammaPointDomain (hc := hc) (carrier (SpecialTransformations.Section5.extendBase A0 hSR))
          (GammaChainDefinable.source G.base T.chain hT)).carrier := fun _ => Set.mem_univ _
  have hZ : ∀ (c : nativeGammaPointDomain (hc := hc) (carrier C) hC) (v : Fin q → CanonicalRV.RVSort M),
      Rcode.DomainAgreement Z0 (nativeMixedCode ((TΓ.symm.map c).val.1,v))
        (Fin.append (rawPreparedKey c.val) (rvValues v)) := by
    intro c v
    rw [nativeSpecialBaseBijection_parameter]
    exact (hprep ⟨c.val,c.property⟩ (rvValues v) (fun i => (v i).property)).2
  have hVL : ∀ (c : nativeGammaPointDomain (hc := hc) (carrier C) hC) (v : Fin q → CanonicalRV.RVSort M),
      Rcode.RelationAgreement (finiteRVSchemaLabels W.leftRV) (nativeMixedCode ((TΓ.symm.map c).val.1,v))
        (Fin.append (rawPreparedKey c.val) (rvValues v)) := by
    intro c v
    rw [nativeSpecialBaseBijection_parameter]
    exact (hprep ⟨c.val,c.property⟩ (rvValues v) (fun i => (v i).property)).1.2.2.2.1
  have hVR : ∀ (c : nativeGammaPointDomain (hc := hc) (carrier C) hC) (v : Fin q → CanonicalRV.RVSort M),
      Rcode.RelationAgreement (finiteRVSchemaLabels W.rightRV) (nativeMixedCode ((TΓ.symm.map c).val.1,v))
        (Fin.append (rawPreparedKey c.val) (rvValues v)) := by
    intro c v
    rw [nativeSpecialBaseBijection_parameter]
    exact (hprep ⟨c.val,c.property⟩ (rvValues v) (fun i => (v i).property)).1.2.2.2.2
  have hWO : ∀ z ∈ nativeMixedDomain Z,W.Valid z := by
    rintro z ⟨b,hb,he⟩
    exact he ▸ hW ⟨b,hb⟩
  have hvals := nativePreparedGeometricVFLift_row_values G.model00 linear G.uncountable.le G.saturated
    G.small_real G.small_gamma G.nontrivial_definable_gamma W Z0 hWraw T hT hprep
  have hL := nativePreparedLift_geometric_value linear H Z W.leftRV C hC TΓ hP Rcode hZ hVL hf hpull
    (fun z hz => (hWO z hz).1) (fun z hz => (hvals z hz).1)
  have hR := nativePreparedLift_geometric_value linear H Z W.rightRV C hC TΓ hP' Rcode hZ hVR hf' hpull
    (fun z hz => (hWO z hz).2.1) (fun z hz => (hvals z hz).2.1)
  let X := nativePreparedParameterBase (hc := hc) C hC (Rcode.domain Z0)
  refine hL.trans ((Finset.sum_congr rfl (fun I _ => ?_)).trans hR.symm)
  exact nativePreparedGeometricVFLift_subbase_total_values G.model00 linear G.uncountable.le G.saturated
    G.small_real G.small_gamma G.nontrivial_definable_gamma W Z0 hWraw T hT hprep
    (nativeRVZeroPatternBase X (Fin.castAdd q ∘ Fin.castAdd l) I)
    (fun z hz => ((nativeRVZeroPatternBase_mem X _ I z).mp hz).1) (Fintype.card I)

end DiamondIntegral.Section5
