import «section 5».NativePreparedLiftRows
import «section 5».NativePreparedKeyRealizations
import «section 5».NativeVFPullbackValues

/-! The bounded value of the actual original mixed VF lift family equals
the raw RV value of its literal prepared RV total. All coordinate maps,
full rows, finite labels, and original parameter bases are retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
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
variable {S : Set M} {p q a k l : ℕ}
variable (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
variable (H : YinGammaGroundUnmeasuredLiftInput G hc)
variable (Z : GammaGroundDefSet hc G.base (rawMixedSpace (M := M) p q))
variable (F : GammaFiniteRVSchema G.base (p+q) a k (Fin.append (fun _ : Fin p => .vf) (fun _ : Fin q => .rv)))
variable {P : GammaGroundDefSet hc G.base (rawMixedSpace (M := M) p 0)}
variable (C : DefSet (M := M) S p l) (hC : GammaSetDefinable G.base (carrier C))
variable (T : GammaGroundBijection P (nativeGammaPointDomain (hc := hc) (carrier C) hC))
variable (hP : ∀ x : nativeVFLiftFamily Z F,
  ((nativeMixedCoordinateMap (nativeVFLiftFamily Z F) (Fin.castAdd k) (Fin.elim0 : Fin 0 → Fin (q+a))) x).val ∈ P.carrier)
variable (R : GammaParameterRecode G.base (p+q) ((p+l)+q)
  (Fin.append (fun _ : Fin p => .vf) (fun _ : Fin q => .rv)) (fun _ => .rv))
variable (hZ : ∀ (c : nativeGammaPointDomain (hc := hc) (carrier C) hC) (v : Fin q → CanonicalRV.RVSort M),
  R.DomainAgreement (nativePreparedLiftBaseDomain Z)
    (nativeMixedCode ((T.symm.map c).val.1,v)) (Fin.append (rawPreparedKey c.val) (rvValues v)))
variable (hV : ∀ (c : nativeGammaPointDomain (hc := hc) (carrier C) hC) (v : Fin q → CanonicalRV.RVSort M),
  R.RelationAgreement (finiteRVSchemaLabels F)
    (nativeMixedCode ((T.symm.map c).val.1,v)) (Fin.append (rawPreparedKey c.val) (rvValues v)))

include hZ hV hP in
theorem nativePreparedLift_bounded_value
    (hf : ∀ x : Fin (p+k) → Section2.VF M,{t | (x,t) ∈ (nativeVFLiftFamily Z F).carrier}.Finite)
    (hpull : IsRVPullback (carrier C))
    (hv : ∀ z ∈ rawDomain (nativePreparedParameterBase (hc := hc) C hC
      (R.domain (nativePreparedLiftBaseDomain Z))),nativeFiniteRVSchemaValid (nativeFiniteRVSchemaRecode R F) z) :
    nativeVFBoundedValue linear H (nativeVFClass (⟨p+k,q+a,nativeVFLiftFamily Z F,hf⟩ : GammaGroundFiniteVFObject hc G.base)) =
      nativeRVSetValue G.model00 linear G.uncountable.le G.saturated hc G.base
        G.small_real G.small_gamma G.nontrivial_definable_gamma .bounded
        (originalRVTotalFamily (nativePreparedParameterBase (hc := hc) C hC
          (R.domain (nativePreparedLiftBaseDomain Z))) (finiteRVSchemaDomain (nativeFiniteRVSchemaRecode R F))) := by
  let Y := (nativeVFPrepareBaseMap (nativeVFLiftFamily Z F) T hP).image
  let A : GammaGroundFiniteVFObject hc G.base := ⟨p+k,q+a,nativeVFLiftFamily Z F,hf⟩
  let Anew : GammaGroundFiniteVFObject hc G.base := ⟨p+k,l+(q+a),Y,
    nativeVFPrepareBaseMap_finite G.uncountable.le G.saturated G.model00 G.small_real _ T hP hf⟩
  have hrows := nativePreparedLiftRows_mem Z F C hC T hP R hZ hV
  have hbase := nativePreparedLiftRows_base Z F C hC T hP
  have hg := nativePreparedLiftKey_graphs C hC (R.domain (nativePreparedLiftBaseDomain Z))
    (nativeFiniteRVSchemaRecode R F) Y hv hbase hrows
  have ho := nativePreparedLiftKey_onto C hC (R.domain (nativePreparedLiftBaseDomain Z))
    (nativeFiniteRVSchemaRecode R F) Y hv hrows
  calc
    nativeVFBoundedValue linear H (nativeVFClass A) = nativeVFBoundedValue linear H (nativeVFClass Anew) :=
      congrArg (nativeVFBoundedValue linear H) (nativeVFClass_bijection A Anew
        (nativeVFPrepareBaseBijection (nativeVFLiftFamily Z F) T hP))
    _ = nativeRVSetValue G.model00 linear G.uncountable.le G.saturated hc G.base
        G.small_real G.small_gamma G.nontrivial_definable_gamma .bounded (nativeMixedFullKeyMap Y).image :=
      nativeVFBoundedValue_pullback linear H Anew (nativePreparedLift_pullback Z F T hP R hZ hV hpull)
    _ = _ := nativePreparedRVKey_value Y _ _ hv hg.1 hg.2 G.model00 linear G.uncountable.le G.saturated
      G.small_real G.small_gamma G.nontrivial_definable_gamma .bounded ho

end DiamondIntegral.Section5
