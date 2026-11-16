import «section 6».CoordinateGammaLevelProjection
import «section 6».UnaryMeasuredCompatiblePreparation

/-! Gamma forms on a prepared lower-dimensional base pull back to its
actual carried bundle. Retained labels preserve both form constancy and
the complete tuple of leading terms. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r s : ℕ} {S : Set M}
variable {A : DefSet (rawMixedSpace (M := M) n r) S}

theorem CarriedRefinementFrame.bundle_tagged (X : CarriedRefinementFrame A)
    (hTag : ∀ p ∈ A.carrier, ∀ q ∈ A.carrier, p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1) :
    ∀ p ∈ X.bundle.carrier, ∀ q ∈ X.bundle.carrier, p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1 := by
  intro p hp q hq hTags
  have hBase := labelRefinement_tagged A X.base X.labels X.fibres hTag
    (Fin.init p.1,p.2) hp.1 (Fin.init q.1,q.2) hq.1 hTags
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · exact hp.2.trans ((congrArg (fun u => u X.freeLabel) hTags).trans hq.2.symm)
  · exact congrFun hBase j

theorem CarriedRefinementFrame.gamma_form_constant (X : CarriedRefinementFrame A)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hConst : ∀ p ∈ A.carrier, ∀ q ∈ A.carrier, p.2 = q.2 →
      gammaFormExtension ω p = gammaFormExtension ω q) :
    ∀ p ∈ X.bundle.carrier, ∀ q ∈ X.bundle.carrier, p.2 = q.2 →
      gammaFormExtension (ω.comp X.oldMap) p = gammaFormExtension (ω.comp X.oldMap) q := by
  intro p hp q hq hTags
  have h := hConst (X.oldPoint ⟨p,hp⟩).val (X.oldPoint ⟨p,hp⟩).property
    (X.oldPoint ⟨q,hq⟩).val (X.oldPoint ⟨q,hq⟩).property (congrArg (fun u => u ∘ X.labels) hTags)
  rw [gammaFormExtension_at,gammaFormExtension_at] at h
  exact (gammaFormExtension_at (ω.comp X.oldMap) (⟨p,hp⟩ : X.bundle)).trans
    (h.trans (gammaFormExtension_at (ω.comp X.oldMap) (⟨q,hq⟩ : X.bundle)).symm)

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {B : DefSet (rawMixedSpace (M := M) n s) S} {f : Map A B} {X : CarriedRefinementFrame A}

theorem CarriedChainLift.gamma_form_transport (F : CarriedChainLift (G := G) X f)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (η : Map B (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hη : ∀ p : A, (η (f p)).val = (ω p).val) (p : X.bundle) :
    ((η.comp F.target.oldMap) (F.map p)).val = (ω (X.oldPoint p)).val := by
  have he : F.target.oldPoint (F.map p) = f (X.oldPoint p) := Subtype.ext (F.commutes p)
  change (η (F.target.oldPoint (F.map p))).val = _
  rw [he]
  exact hη _

end DiamondIntegral.Section6
