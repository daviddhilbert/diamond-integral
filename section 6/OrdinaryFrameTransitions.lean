import «section 6».OrdinaryCanonicalFrames

/-! Exact commutation and preservation of the remaining exceptional-set
avoidance for the actual permitted primitive frames. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.OrdinaryUnaryFocusFrame
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S R : Set M} {r q t : ℕ}
variable {hc : CanonicalStructure.IsCanonical (M := M)}
variable {A : SpecialTransformations.Section5.DefSet (M := M) R 1 r}
variable {hA : SpecialTransformations.Section5.GammaSetDefinable (ordinaryNamedGammaBase S)
  (SpecialTransformations.Section5.carrier A)}
variable (X : OrdinaryUnaryFocusFrame hc A hA q)
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
variable (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)

theorem afterCanonical_at_step (p : X.source) :
    ((X.afterCanonical h00 hκ hs hv).oldMap (regularization X.source p)).val=
      SpecialTransformations.Section5.canonical (X.oldMap p).val := by
  change SpecialTransformations.Section5.canonical
    (X.oldMap ((regularization X.source).inverse (regularization_bijective X.source)
      (regularization X.source p))).val=_
  rw [Map.inverse_apply]

theorem afterCanonical_no_zero_sources
    {B : SpecialTransformations.Section5.DefSet (M := M) R 1 t}
    (T : SpecialTransformations.Section5.Chain R 1 (SpecialTransformations.Section5.canonicalImage A) B)
    (hNo : ∀ p : X.source,(X.oldMap p).val ∉ ordinaryChainZeroSources (.cons (.canonical A) T))
    (w : (X.afterCanonical h00 hκ hs hv).source) :
    ((X.afterCanonical h00 hκ hs hv).oldMap w).val ∉ ordinaryChainZeroSources T := by
  obtain ⟨p,rfl⟩ := (regularization_bijective X.source).surjective w
  rw [X.afterCanonical_at_step h00 hκ hs hv p]
  intro he
  exact hNo p (Or.inr ⟨X.oldMap p,rfl,he⟩)

variable {j : Fin r} (D : SpecialTransformations.Section5.Focus A 0 j)
variable (hD : SpecialTransformations.Section5.GammaFocusDefinable (ordinaryNamedGammaBase S) D)
variable (E : CentripetalData (G := G) X.source)
variable (hCoord : E.coordinate=0) (hActive : E.activeTags=X.activeTags D hD)
variable (hFocus : ∀ x u,E.focus x u=(X.focusData D hD).focus u)
variable (hCore : ∀ p ∈ X.source.carrier,E.core p=false)

theorem afterCentripetal_at_step (p : X.source) :
    ((X.afterCentripetal D hD h00 hκ hs hv E hCoord hActive hFocus hCore).oldMap
      (centripetalStepMap E p)).val=D.toFocusGeometry.eta (X.oldMap p).val := by
  change D.toFocusGeometry.eta
    (X.oldMap ((centripetalStepMap E).inverse (centripetalStepMap_bijective E h00)
      (centripetalStepMap E p))).val=_
  rw [Map.inverse_apply]

theorem afterCentripetal_no_zero_sources
    {B : SpecialTransformations.Section5.DefSet (M := M) R 1 t}
    (T : SpecialTransformations.Section5.Chain R 1 D.etaImage B)
    (hNo : ∀ p : X.source,(X.oldMap p).val ∉ ordinaryChainZeroSources (.cons (.centripetal D) T))
    (w : (X.afterCentripetal D hD h00 hκ hs hv E hCoord hActive hFocus hCore).source) :
    ((X.afterCentripetal D hD h00 hκ hs hv E hCoord hActive hFocus hCore).oldMap w).val ∉
      ordinaryChainZeroSources T := by
  obtain ⟨p,rfl⟩ := (centripetalStepMap_bijective E h00).surjective w
  rw [X.afterCentripetal_at_step h00 hκ hs hv D hD E hCoord hActive hFocus hCore p]
  intro he
  exact hNo p (Or.inr ⟨X.oldMap p,rfl,he⟩)

end DiamondIntegral.Section6.OrdinaryUnaryFocusFrame
