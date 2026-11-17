import «section 3».GammaPreparedIndexedLiftBijections
import «section 3».GammaFullMeasuredFixedMaps

/-! The literal prepared-family bijection is measured for an arbitrary
Gamma form whose complete code relation is the prepared density row.
Every VF coordinate and the original base are retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {S : Set M} {p l a k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hr : Cardinal.mk B.real < κ)
variable (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
variable (C : DefSet (M := M) S p l) (hC : IsRVPullback (carrier C))
variable (BP : PreparedIndexPresentation B C)
variable (F : GammaMeasuredRVSchema hc B (p+l) a (k+1) (fun _ => .rv))
variable (hF : ∀ t ∈ preparedKeyDomain C, F.valid (rvValues t)) (P : F.object.IndexedPresentation BP)
variable (Y : GammaGroundDefSet hc B (rawMixedSpace (M := M) (p+(k+1)) (l+a)))
variable (hBase : ∀ q : Y, (q.val.1 ∘ Fin.castAdd (k+1),q.val.2 ∘ Fin.castAdd a) ∈ carrier C)
variable (hRows : ∀ (c : C) (y : Fin (k+1) → Section2.VF M) (r : Fin a → RV (M := M)),
  (Fin.append c.val.1 y,Fin.append c.val.2 r) ∈ Y.carrier ↔
    F.object.rowVolume (rawPreparedKey c.val) r (Section2.tupleRV M y))
variable (hfin : ∀ x, {r | (x,r) ∈ Y.carrier}.Finite)
variable (ω : GammaGroundVolumeForm hc B Y)
variable (hDensity : ∀ (q : Y) (c : (volumeGammaSpace hc).domain),
  (volumeGammaSpace hc).decode c = (ω q).val →
    F.rowDensity (rvValues (indexedLeft (gammaPreparedIndexAttachment Y q).val.2))
      (indexedRight (gammaPreparedIndexAttachment Y q).val.2) c)

def gammaPreparedIndexedFullMeasured :
    GammaFullMeasuredBijection (⟨l+a,Y,hfin,ω⟩ : GammaGroundMeasuredVFData hc B (p+(k+1)))
      (gammaNativeMeasuredLift (gammaUniversalObject P.toGamma) (F.indexedForm BP hF P)) := by
  let E := gammaPreparedIndexedLiftBijection C hC BP F hF P Y hBase hRows
  apply gammaFullMeasuredFixedVF hκ hs hr hv E (fun _ => rfl)
  intro q
  let u := gammaNativeLiftLabel (gammaUniversalObject P.toGamma) (E.map q)
  obtain ⟨c,hcValue⟩ := (volumeGammaSpace hc).onto (ω q).val
  have hCode := hDensity q c hcValue
  have hLabel : u.val = (gammaPreparedIndexAttachment Y q).val.2 := rfl
  have hCodeU : F.rowDensity (rvValues (indexedLeft u.val)) (indexedRight u.val) c := hLabel.symm ▸ hCode
  have hValue : (volumeGammaSpace hc).decode c = (F.indexedForm BP hF P u).val :=
    (F.rowGammaValue_graph _ (hF _ (F.indexed_mem BP P u).1)
      ⟨indexedRight u.val,(F.indexed_mem BP P u).2⟩ c).mp hCodeU
  exact congrArg (fun z => (cast (gammaCarrier hc) z).val) (hcValue.symm.trans hValue)

theorem gammaPreparedIndexedFullMeasured_vf (q : Y) :
    ((gammaPreparedIndexedFullMeasured hκ hs hr hv C hC BP F hF P Y hBase hRows hfin ω hDensity).map.map q).val.1 = q.val.1 := rfl

end DiamondIntegral.Section3
