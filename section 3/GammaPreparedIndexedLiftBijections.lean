import «section 3».GammaPreparedIndexedLiftDomains
import «section 3».GammaPreparedIndexAttachments

/-! The actual prepared VF family and the full lift of its indexed RV
presentation are bijective by attaching the base's RV key. The map
fixes every VF coordinate and retains all original fibre labels. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.DefinableGeometry.Space.ofEmbedding
  SpecialTransformations.Section4.rawMixedSpace SpecialTransformations.Section4.rawVFSpace SpecialTransformations.Section4.rawRVSpace
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section5.pointSpace
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {S : Set M} {p l a k : ℕ}
variable (C : DefSet (M := M) S p l) (hC : IsRVPullback (carrier C))
variable (BP : PreparedIndexPresentation B C)
variable (F : GammaMeasuredRVSchema hc B (p+l) a (k+1) (fun _ => .rv))
variable (hF : ∀ t ∈ preparedKeyDomain C, F.valid (rvValues t)) (P : F.object.IndexedPresentation BP)
variable (Y : GammaGroundDefSet hc B (rawMixedSpace (M := M) (p+(k+1)) (l+a)))
variable (hBase : ∀ q : Y, (q.val.1 ∘ Fin.castAdd (k+1),q.val.2 ∘ Fin.castAdd a) ∈ carrier C)
variable (hRows : ∀ (c : C) (y : Fin (k+1) → Section2.VF M) (r : Fin a → RV (M := M)),
  (Fin.append c.val.1 y,Fin.append c.val.2 r) ∈ Y.carrier ↔
    F.object.rowVolume (rawPreparedKey c.val) r (Section2.tupleRV M y))

include hC hF hBase hRows in
theorem gammaPreparedIndexedLift_image :
    (gammaPreparedIndexAttachment Y).image.carrier =
      (gammaNativeUnitLift (hc := hc) (gammaUniversalObject P.toGamma).toGamma).domain.carrier := by
  ext q
  constructor
  · rintro ⟨w,hw⟩
    apply (gammaPreparedIndexedLift_membership C hC BP F hF P q).mpr
    change (gammaPreparedIndexAttachment Y w).val = q at hw
    rw [← hw,gammaPreparedIndexAttachment_value]
    let c : C := ⟨(w.val.1 ∘ Fin.castAdd (k+1),w.val.2 ∘ Fin.castAdd a),hBase w⟩
    have hPacked : (Fin.append c.val.1 (w.val.1 ∘ Fin.natAdd p),
        Fin.append c.val.2 (w.val.2 ∘ Fin.natAdd l)) ∈ Y.carrier := by
      have he : (Fin.append c.val.1 (w.val.1 ∘ Fin.natAdd p),
          Fin.append c.val.2 (w.val.2 ∘ Fin.natAdd l)) = w.val :=
        Prod.ext Fin.append_castAdd_natAdd Fin.append_castAdd_natAdd
      exact he.symm ▸ w.property
    have hRow := (hRows c (w.val.1 ∘ Fin.natAdd p) (w.val.2 ∘ Fin.natAdd l)).mp hPacked
    refine ⟨?_,?_,?_⟩
    · simpa only [indexedLeft,Function.comp_def,Fin.append_left,Fin.append_right] using hBase w
    · funext j
      simp only [indexedLeft,Function.comp_apply,Fin.append_left]
    · simp only [indexedLeft,indexedRight,Function.comp_def,Fin.append_left,Fin.append_right]
      exact hRow
  · intro hq
    obtain ⟨hb,hkey,hrow⟩ := (gammaPreparedIndexedLift_membership C hC BP F hF P q).mp hq
    let t := indexedLeft q.2
    let r := indexedRight q.2
    let c : C := ⟨(q.1 ∘ Fin.castAdd (k+1),t ∘ Fin.natAdd p),hb⟩
    have hKey : (flatKey c.val).2 = t := by
      change Fin.append (Section2.tupleRV M (q.1 ∘ Fin.castAdd (k+1))) (t ∘ Fin.natAdd p) = t
      rw [← hkey]
      exact Fin.append_castAdd_natAdd
    have hRow : F.object.rowVolume (rawPreparedKey c.val) r (Section2.tupleRV M (q.1 ∘ Fin.natAdd p)) := by
      have he : rawPreparedKey c.val = rvValues t := congrArg rvValues hKey
      exact he.symm ▸ hrow
    have hPacked := (hRows c (q.1 ∘ Fin.natAdd p) r).mpr hRow
    let w : Y := ⟨(q.1,Fin.append c.val.2 r),by
      have he : (Fin.append c.val.1 (q.1 ∘ Fin.natAdd p),Fin.append c.val.2 r) =
          (q.1,Fin.append c.val.2 r) := Prod.ext Fin.append_castAdd_natAdd rfl
      exact he ▸ hPacked⟩
    refine ⟨w,?_⟩
    change (gammaPreparedIndexAttachment Y w).val = q
    rw [gammaPreparedIndexAttachment_value]
    refine Prod.ext rfl ?_
    change Fin.append (Fin.append (Section2.tupleRV M (q.1 ∘ Fin.castAdd (k+1)))
      (Fin.append c.val.2 r ∘ Fin.castAdd a)) (Fin.append c.val.2 r ∘ Fin.natAdd l) = q.2
    have hl : Fin.append c.val.2 r ∘ Fin.castAdd a = c.val.2 := funext (Fin.append_left _ _)
    have hr : Fin.append c.val.2 r ∘ Fin.natAdd l = r := funext (Fin.append_right _ _)
    rw [hl,hr]
    exact (congrArg (fun z => Fin.append z r) hKey).trans Fin.append_castAdd_natAdd

def gammaPreparedIndexedLiftBijection :
    GammaGroundBijection Y (gammaNativeUnitLift (hc := hc) (gammaUniversalObject P.toGamma).toGamma).domain :=
  (GammaGroundBijection.ofCarrierEq (gammaPreparedIndexedLift_image C hC BP F hF P Y hBase hRows)).comp
    (gammaPreparedIndexAttachmentBijection Y)

end DiamondIntegral.Section3
