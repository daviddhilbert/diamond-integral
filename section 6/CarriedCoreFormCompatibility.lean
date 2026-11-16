import «section 6».CarriedApertureCompatibility
import «section 6».FormCompatibleChainTransport
import «section 6».CarriedGammaForms

/-! Carrying a permitted component preserves semantic core constancy
for the actual pullback form. Both old labels and every complementary
VF coordinate are recovered from the full carried point. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem CarriedRefinementFrame.carriedComponent_core
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A : DefSet (rawMixedSpace (M := M) n r) S} (X : CarriedRefinementFrame A)
    (D : CentripetalData (G := G) A) (p : X.bundle) :
    (X.carriedComponent h00 hc hκ hs hv D).core p.val=D.core (X.oldPoint p).val := by
  apply branchTag_injective h00
  have h := congrArg (fun z : Mixed M (n+1) (1+X.arity) => z.2 (Fin.castAdd X.arity (0 : Fin 1)))
    (X.carriedComponent_point h00 hc hκ hs hv D p.val p.property)
  simpa only [CentripetalData.point,Fin.append_left,CarriedRefinementFrame.oldPoint] using h

theorem CarriedRefinementFrame.carriedComponent_core_form_constant
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A : DefSet (rawMixedSpace (M := M) n r) S} (X : CarriedRefinementFrame A)
    (D : CentripetalData (G := G) A)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)) (h : D.CoreFormConstant ω) :
    (X.carriedComponent h00 hc hκ hs hv D).CoreFormConstant (ω.comp X.oldMap) := by
  intro p q hp hq hOther hTags
  apply h (X.oldPoint p) (X.oldPoint q)
  · exact (X.carriedComponent_core h00 hc hκ hs hv D p) ▸ hp
  · exact (X.carriedComponent_core h00 hc hκ hs hv D q) ▸ hq
  · intro i hi
    exact hOther i.castSucc (by
      change i.castSucc ≠ D.coordinate.castSucc
      exact fun he => hi (Fin.castSucc_injective n he))
  · exact congrArg (fun u => u ∘ X.labels) hTags

end DiamondIntegral.Section6
