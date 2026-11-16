import «section 6».RVRefinementCoveredBases
import «section 6».RVRefinementSynchronizedChains
import «section 6».FormCompatibleChainTransport

/-! Exact Gamma maps and semantic core constancy survive retention of
additional RV labels, with every VF coordinate unchanged by projection. -/

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

namespace RVRefinementFrame

theorem gamma_form_constant (X : RVRefinementFrame A)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hConst : ∀ p ∈ A.carrier,∀ q ∈ A.carrier,p.2=q.2 → gammaFormExtension ω p=gammaFormExtension ω q) :
    ∀ p ∈ X.base.carrier,∀ q ∈ X.base.carrier,p.2=q.2 →
      gammaFormExtension (ω.comp X.oldMap) p=gammaFormExtension (ω.comp X.oldMap) q := by
  intro p hp q hq hTags
  have h := hConst (X.oldPoint ⟨p,hp⟩).val (X.oldPoint ⟨p,hp⟩).property
    (X.oldPoint ⟨q,hq⟩).val (X.oldPoint ⟨q,hq⟩).property (congrArg (fun u => u ∘ X.labels) hTags)
  rw [gammaFormExtension_at,gammaFormExtension_at] at h
  rw [gammaFormExtension_at _ ⟨p,hp⟩,gammaFormExtension_at _ ⟨q,hq⟩]
  exact h

theorem portComponent_core_form_constant (X : RVRefinementFrame A) (D : CentripetalData (G := G) A)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)) (h : D.CoreFormConstant ω) :
    (X.portComponent D).CoreFormConstant (ω.comp X.oldMap) := by
  have hCore (p : X.base) : (X.portComponent D).core p.val=D.core (X.oldPoint p).val :=
    D.refineLabels_core X.labels X.proper X.doublyBounded
      (labelRefinement_tagged A X.base X.labels X.fibres D.tagged) X.fibres p.val p.property
  intro p q hp hq hOther hTags
  exact h (X.oldPoint p) (X.oldPoint q) ((hCore p) ▸ hp) ((hCore q) ▸ hq)
    hOther (congrArg (fun u => u ∘ X.labels) hTags)

end RVRefinementFrame

theorem RVRefinementChainLift.gamma_form_transport
    {B : DefSet (rawMixedSpace (M := M) n s) S} {f : Map A B} {X : RVRefinementFrame A}
    {P : I → DefSet (rawMixedSpace (M := M) n r) S}
    (F : RVRefinementChainLift (G := G) X f P)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (η : Map B (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hη : ∀ p : A,(η (f p)).val=(ω p).val) (p : X.base) :
    ((η.comp F.target.oldMap) (F.map p)).val=((ω.comp X.oldMap) p).val := by
  have he : F.target.oldPoint (F.map p)=f (X.oldPoint p) := Subtype.ext (F.commutes p)
  change (η (F.target.oldPoint (F.map p))).val=(ω (X.oldPoint p)).val
  rw [he]
  exact hη _

end DiamondIntegral.Section6
