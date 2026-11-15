import «section 5».NativePreparedLiftNormalForm
import «section 5».PreparedMixedCoordinates
import «section 5».OriginalParameterDomains
import «section 5».NativeFiniteRVSchemaRecoding

/-! Complete original-base row agreement identifies the actual prepared
VF lift image with a predicate of its full RV data. The prepared image
is therefore an actual RV-pullback over the original Gamma ground. -/
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
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p q a k l : ℕ}

def nativePreparedLiftBaseDomain (Z : GammaGroundDefSet hc B (rawMixedSpace (M := M) p q)) :
    GammaDomainFormula B (p+q) 0 (Fin.append (fun _ : Fin p => .vf) (fun _ : Fin q => .rv)) :=
  originalParameterDomain (nativeMixedDomain Z) (nativeMixedDomain_definable Z)

def nativePreparedLiftRVPredicate
    (Z : GammaGroundDefSet hc B (rawMixedSpace (M := M) p q))
    (F : GammaFiniteRVSchema B (p+q) a k (Fin.append (fun _ : Fin p => .vf) (fun _ : Fin q => .rv)))
    (R : GammaParameterRecode B (p+q) ((p+l)+q)
      (Fin.append (fun _ : Fin p => .vf) (fun _ : Fin q => .rv)) (fun _ => .rv))
    (d : PreparedFamilyRVData M p k l q a) : Prop :=
  Fin.append (Fin.append (rvValues d.1) (rvValues d.2.1)) (Fin.elim0 : Fin 0 → M) ∈
      (R.domain (nativePreparedLiftBaseDomain Z)).val ∧
    Fin.append (Fin.append (Fin.append (rvValues d.1) (rvValues d.2.1)) (rvValues d.2.2.1))
      (rvValues d.2.2.2) ∈ (nativeFiniteRVSchemaRecode R F).volume

section Prepared
variable (Z : GammaGroundDefSet hc B (rawMixedSpace (M := M) p q))
variable (F : GammaFiniteRVSchema B (p+q) a k (Fin.append (fun _ : Fin p => .vf) (fun _ : Fin q => .rv)))
variable {P : GammaGroundDefSet hc B (rawMixedSpace (M := M) p 0)}
variable {C : GammaGroundDefSet hc B (rawMixedSpace (M := M) p l)} (T : GammaGroundBijection P C)
variable (hP : ∀ x : nativeVFLiftFamily Z F,
  ((nativeMixedCoordinateMap (nativeVFLiftFamily Z F) (Fin.castAdd k) (Fin.elim0 : Fin 0 → Fin (q+a))) x).val ∈ P.carrier)
variable (R : GammaParameterRecode B (p+q) ((p+l)+q)
  (Fin.append (fun _ : Fin p => .vf) (fun _ : Fin q => .rv)) (fun _ => .rv))
variable (hZ : ∀ (c : C) (v : Fin q → CanonicalRV.RVSort M),R.DomainAgreement (nativePreparedLiftBaseDomain Z)
  (nativeMixedCode ((T.symm.map c).val.1,v)) (Fin.append (rawPreparedKey c.val) (rvValues v)))
variable (hV : ∀ (c : C) (v : Fin q → CanonicalRV.RVSort M),R.RelationAgreement (finiteRVSchemaLabels F)
  (nativeMixedCode ((T.symm.map c).val.1,v)) (Fin.append (rawPreparedKey c.val) (rvValues v)))

include hZ hV in
theorem nativePreparedLift_packed_recode (c : C) (v : Fin q → CanonicalRV.RVSort M)
    (y : Fin k → Section2.VF M) (u : Fin a → CanonicalRV.RVSort M) :
    (Fin.append c.val.1 y,Fin.append c.val.2 (Fin.append v u)) ∈
      (nativeVFPrepareBaseMap (nativeVFLiftFamily Z F) T hP).image.carrier ↔
      nativePreparedLiftRVPredicate Z F R ((flatKey c.val).2,v,u,Section2.tupleRV M y) := by
  refine (nativePreparedLiftNormalForm Z F T hP c v y u).trans (and_congr ?_ ?_)
  · exact (nativeMixedCode_mem_domain_iff Z ((T.symm.map c).val.1,v)).symm.trans
      ((originalParameterDomain_row (nativeMixedDomain Z) (nativeMixedDomain_definable Z)
        (nativeMixedCode ((T.symm.map c).val.1,v))).symm.trans (hZ c v (Fin.elim0 : Fin 0 → M)))
  · exact hV c v (rvValues u) (rvValues (Section2.tupleRV M y))

theorem nativePreparedLift_base_mem (w : Point (M := M) (p+k) (l+(q+a)))
    (hw : w ∈ (nativeVFPrepareBaseMap (nativeVFLiftFamily Z F) T hP).image.carrier) :
    preparedFamilyBase (p := p) (k := k) (l := l) (q := q) (a := a) w ∈ C.carrier := by
  obtain ⟨x,hx⟩ := hw
  let c := T.map ((nativeVFBaseParameterMap (nativeVFLiftFamily Z F) P hP) x)
  have hval : ((nativeVFPrepareBaseMap (nativeVFLiftFamily Z F) T hP) x).val = w := hx
  have hb : preparedFamilyBase (p := p) (k := k) (l := l) (q := q) (a := a)
      (((nativeVFPrepareBaseMap (nativeVFLiftFamily Z F) T hP) x).val) = c.val := by
    rw [nativeVFPrepareBaseMap_value]
    apply Prod.ext
    · exact funext (fun i => Fin.append_left _ _ i)
    · exact funext (fun i => Fin.append_left _ _ i)
  have he : preparedFamilyBase (p := p) (k := k) (l := l) (q := q) (a := a) w = c.val :=
    (congrArg (preparedFamilyBase (p := p) (k := k) (l := l) (q := q) (a := a)) hval).symm.trans hb
  exact he.symm ▸ c.property

include hZ hV in
theorem nativePreparedLift_carrier_recode :
    (nativeVFPrepareBaseMap (nativeVFLiftFamily Z F) T hP).image.carrier =
      {w : Point (M := M) (p+k) (l+(q+a)) | preparedFamilyBase w ∈ C.carrier ∧
        nativePreparedLiftRVPredicate Z F R (preparedFamilyRVData w)} := by
  ext w
  have hrow (hb : preparedFamilyBase (p := p) (k := k) (l := l) (q := q) (a := a) w ∈ C.carrier) :
      w ∈ (nativeVFPrepareBaseMap (nativeVFLiftFamily Z F) T hP).image.carrier ↔
        nativePreparedLiftRVPredicate Z F R (preparedFamilyRVData w) := by
    let c : C := ⟨preparedFamilyBase w,hb⟩
    have h := nativePreparedLift_packed_recode Z F T hP R hZ hV c
      (preparedFamilyOldRV (p := p) (k := k) (l := l) (q := q) (a := a) w)
      (preparedFamilyFibreVF (p := p) (k := k) (l := l) (q := q) (a := a) w)
      (preparedFamilyFibreRV (p := p) (k := k) (l := l) (q := q) (a := a) w)
    change (Fin.append (preparedFamilyBase w).1 (preparedFamilyFibreVF w),
      Fin.append (preparedFamilyBase w).2 (Fin.append (preparedFamilyOldRV w) (preparedFamilyFibreRV w))) ∈
        (nativeVFPrepareBaseMap (nativeVFLiftFamily Z F) T hP).image.carrier ↔
      nativePreparedLiftRVPredicate Z F R (preparedFamilyRVData w) at h
    rw [preparedFamily_reconstruct] at h
    exact h
  constructor
  · intro hw
    have hb := nativePreparedLift_base_mem Z F T hP w hw
    exact ⟨hb,(hrow hb).mp hw⟩
  · rintro ⟨hb,hp⟩
    exact (hrow hb).mpr hp

include hZ hV in
theorem nativePreparedLift_pullback (hpull : IsRVPullback C.carrier) :
    IsRVPullback (nativeVFPrepareBaseMap (nativeVFLiftFamily Z F) T hP).image.carrier := by
  rw [nativePreparedLift_carrier_recode Z F T hP R hZ hV]
  exact preparedFamilyRVData_pullback C.carrier hpull (nativePreparedLiftRVPredicate Z F R)
end Prepared

end DiamondIntegral.Section5
