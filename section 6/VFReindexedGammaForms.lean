import «section 6».RVRefinementGammaForms
import «section 6».VFReindexedSynchronizedChains

/-! Actual Gamma maps through VF coordinate permutations and retained
RV labels, including semantic core constancy on every ported component. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s : ℕ} {I : Type*}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) n r) S}

def reindexVFInverseMap (A : DefSet (rawMixedSpace (M := M) n r) S) (e : Fin n ≃ Fin n) :
    Map (reindexedVFSet A e) A :=
  (reindexVFMap (reindexedVFSet A e) e.symm).corestrict
    (fun p => (mem_reindexedVFSet A e p.val).mp p.property)

def reindexedGammaForm (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)) (e : Fin n ≃ Fin n) :
    Map (reindexedVFSet A e) (DefSet.univ (rawGammaPresentation (M := M)) S) :=
  ω.comp (reindexVFInverseMap A e)

theorem reindexedGammaForm_constant
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)) (e : Fin n ≃ Fin n)
    (hConst : ∀ p ∈ A.carrier,∀ q ∈ A.carrier,p.2=q.2 → gammaFormExtension ω p=gammaFormExtension ω q) :
    ∀ p ∈ (reindexedVFSet A e).carrier,∀ q ∈ (reindexedVFSet A e).carrier,p.2=q.2 →
      gammaFormExtension (reindexedGammaForm ω e) p=gammaFormExtension (reindexedGammaForm ω e) q := by
  intro p hp q hq he
  rw [gammaFormExtension_at _ ⟨p,hp⟩,gammaFormExtension_at _ ⟨q,hq⟩]
  have h := hConst _ (reindexVFInverseMap A e ⟨p,hp⟩).property
    _ (reindexVFInverseMap A e ⟨q,hq⟩).property he
  rw [gammaFormExtension_at,gammaFormExtension_at] at h
  exact h

theorem CentripetalData.reindexVF_core_form_constant (D : CentripetalData (G := G) A)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)) (h : D.CoreFormConstant ω)
    (e : Fin n ≃ Fin n) : (D.reindexVF e).CoreFormConstant (reindexedGammaForm ω e) := by
  have hCore (p : reindexedVFSet A e) : (D.reindexVF e).core p.val=
      D.core (reindexVFInverseMap A e p).val := by
    have hPoint : reindexVFPoint e (reindexVFInverseMap A e p).val=p.val :=
      reindexVFPoint_inverse e.symm p.val
    rw [← hPoint]
    exact D.reindexVF_core e _ (reindexVFInverseMap A e p).property
  intro p q hp hq hOther hTags
  apply h (reindexVFInverseMap A e p) (reindexVFInverseMap A e q) ((hCore p) ▸ hp) ((hCore q) ▸ hq) _ hTags
  intro i hi
  exact hOther (e.symm i) (fun he => hi (e.symm.injective he))

def VFReindexRefinementFrame.oldMap {e : Fin n ≃ Fin n} (X : VFReindexRefinementFrame A e) : Map X.data.base A :=
  (reindexVFInverseMap A e).comp X.data.oldMap

theorem VFReindexRefinementFrame.portComponent_core_form_constant {e : Fin n ≃ Fin n}
    (X : VFReindexRefinementFrame A e) (D : CentripetalData (G := G) A)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)) (h : D.CoreFormConstant ω) :
    (X.portComponent D).CoreFormConstant (ω.comp X.oldMap) :=
  X.data.portComponent_core_form_constant (D.reindexVF e) (reindexedGammaForm ω e) (D.reindexVF_core_form_constant ω h e)

theorem VFReindexRefinementFrame.gamma_form_constant {e : Fin n ≃ Fin n}
    (X : VFReindexRefinementFrame A e)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hConst : ∀ p ∈ A.carrier,∀ q ∈ A.carrier,p.2=q.2 → gammaFormExtension ω p=gammaFormExtension ω q) :
    ∀ p ∈ X.data.base.carrier,∀ q ∈ X.data.base.carrier,p.2=q.2 →
      gammaFormExtension (ω.comp X.oldMap) p=gammaFormExtension (ω.comp X.oldMap) q :=
  X.data.gamma_form_constant (reindexedGammaForm ω e) (reindexedGammaForm_constant ω e hConst)

theorem VFReindexedChainLift.gamma_form_transport {e : Fin n ≃ Fin n}
    {B : DefSet (rawMixedSpace (M := M) n s) S} {f : Map A B} {X : VFReindexRefinementFrame A e}
    {P : I → DefSet (rawMixedSpace (M := M) n r) S}
    (F : VFReindexedChainLift (G := G) X f P)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (η : Map B (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hη : ∀ p : A,(η (f p)).val=(ω p).val) (p : X.data.base) :
    ((η.comp F.target.oldMap) (F.map p)).val=((ω.comp X.oldMap) p).val := by
  have he : F.target.oldPoint (F.map p)=f (X.oldPoint p) := Subtype.ext (F.commutes p)
  change (η (F.target.oldPoint (F.map p))).val=(ω (X.oldPoint p)).val
  rw [he]
  exact hη _

end DiamondIntegral.Section6
