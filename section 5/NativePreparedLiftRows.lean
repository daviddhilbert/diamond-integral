import «section 5».NativePreparedLiftPullbacks
import «section 5».NativePreparedKeyDomains
import «section 5».NativeGammaPointBridge

/-! The concrete transported VF lift has precisely the packed rows used
by the prepared RV key comparison. Its RV base is the actual retained-key
base, and its membership is the recoded full label graph. -/
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
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {S : Set M} {p q a k l : ℕ}

theorem nativePreparedParameterBase_at_point (C : DefSet (M := M) S p l)
    (hC : GammaSetDefinable B (carrier C)) (Z : GammaDomainFormula B ((p+l)+q) 0 (fun _ => .rv))
    (c : C) (v : Fin q → CanonicalRV.RVSort M) :
    Fin.append (rawPreparedKey c.val) (rvValues v) ∈ rawDomain (nativePreparedParameterBase (hc := hc) C hC Z) ↔
      Fin.append (Fin.append (rawPreparedKey c.val) (rvValues v)) (Fin.elim0 : Fin 0 → M) ∈ Z.val := by
  rw [nativePreparedParameterBase_raw]
  constructor
  · exact And.left
  · intro hz
    refine ⟨hz,c,?_⟩
    exact funext (fun i => (Fin.append_left _ _ i).symm)

section Prepared
variable (Z : GammaGroundDefSet hc B (rawMixedSpace (M := M) p q))
variable (F : GammaFiniteRVSchema B (p+q) a k (Fin.append (fun _ : Fin p => .vf) (fun _ : Fin q => .rv)))
variable {P : GammaGroundDefSet hc B (rawMixedSpace (M := M) p 0)}
variable (C : DefSet (M := M) S p l) (hC : GammaSetDefinable B (carrier C))
variable (T : GammaGroundBijection P (nativeGammaPointDomain (hc := hc) (carrier C) hC))
variable (hP : ∀ x : nativeVFLiftFamily Z F,
  ((nativeMixedCoordinateMap (nativeVFLiftFamily Z F) (Fin.castAdd k) (Fin.elim0 : Fin 0 → Fin (q+a))) x).val ∈ P.carrier)
variable (R : GammaParameterRecode B (p+q) ((p+l)+q)
  (Fin.append (fun _ : Fin p => .vf) (fun _ : Fin q => .rv)) (fun _ => .rv))
variable (hZ : ∀ (c : nativeGammaPointDomain (hc := hc) (carrier C) hC) (v : Fin q → CanonicalRV.RVSort M),
  R.DomainAgreement (nativePreparedLiftBaseDomain Z)
    (nativeMixedCode ((T.symm.map c).val.1,v)) (Fin.append (rawPreparedKey c.val) (rvValues v)))
variable (hV : ∀ (c : nativeGammaPointDomain (hc := hc) (carrier C) hC) (v : Fin q → CanonicalRV.RVSort M),
  R.RelationAgreement (finiteRVSchemaLabels F)
    (nativeMixedCode ((T.symm.map c).val.1,v)) (Fin.append (rawPreparedKey c.val) (rvValues v)))

include hZ hV in
theorem nativePreparedLiftRows_mem (c : C) (v : Fin q → CanonicalRV.RVSort M)
    (y : Fin k → Section2.VF M) (u : Fin a → CanonicalRV.RVSort M) :
    (Fin.append c.val.1 y,Fin.append c.val.2 (Fin.append v u)) ∈
        (nativeVFPrepareBaseMap (nativeVFLiftFamily Z F) T hP).image.carrier ↔
      Fin.append (rawPreparedKey c.val) (rvValues v) ∈ rawDomain (nativePreparedParameterBase (hc := hc) C hC
        (R.domain (nativePreparedLiftBaseDomain Z))) ∧
      Fin.append (Fin.append (Fin.append (rawPreparedKey c.val) (rvValues v)) (rvValues u))
        (rvValues (Section2.tupleRV M y)) ∈ (nativeFiniteRVSchemaRecode R F).volume := by
  let cN : nativeGammaPointDomain (hc := hc) (carrier C) hC := ⟨c.val,c.property⟩
  have he := nativePreparedLift_packed_recode Z F T hP R hZ hV cN v y u
  change _ ↔
    (Fin.append (Fin.append (rawPreparedKey c.val) (rvValues v)) (Fin.elim0 : Fin 0 → M) ∈
      (R.domain (nativePreparedLiftBaseDomain Z)).val ∧ _) at he
  exact he.trans (and_congr (nativePreparedParameterBase_at_point C hC _ c v).symm Iff.rfl)

theorem nativePreparedLiftRows_base
    (w : (nativeVFPrepareBaseMap (nativeVFLiftFamily Z F) T hP).image) :
    preparedFamilyBase w.val ∈ carrier C :=
  nativePreparedLift_base_mem Z F T hP w.val w.property
end Prepared

end DiamondIntegral.Section5
