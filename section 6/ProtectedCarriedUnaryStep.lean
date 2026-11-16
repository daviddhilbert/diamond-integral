import «section 6».ProtectedCarriedLifts

/-! One unary mean step can prepare lower-dimensional pieces while
its actual carried lift protects arbitrary proper full-dimensional
pieces. The synchronized coefficient is constructed over S. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {r k l : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem UnaryFocusData.exists_protected_carried_step
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V, iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    {A : DefSet (rawMixedSpace (M := M) 1 r) S} (D : UnaryFocusData A)
    (X : CarriedRefinementFrame A)
    (C : Fin k → DefSet (rawMixedSpace (M := M) 1 r) S)
    (hCA : ∀ i, (C i).carrier ⊆ A.carrier) (hC : ∀ i, ProperInvariant S (C i).carrier)
    (P : Fin l → DefSet (rawMixedSpace (M := M) 2 X.arity) S)
    (hPX : ∀ i, (P i).carrier ⊆ X.bundle.carrier) (hP : ∀ i, ProperInvariant S (P i).carrier) :
    ∃ E : CentripetalData (G := G) A, E.coordinate = 0 ∧ E.activeTags = D.activeTags ∧
      (∀ x u, E.focus x u = D.focus u) ∧
      (∀ i, ∃ J : CentripetalData (G := G) (C i), ApertureRestrictionData E J) ∧
      Nonempty (ProtectedCarriedLift (G := G) X E.bijection P hPX) := by
  obtain ⟨F,H,hCoeff,hLower,hFull⟩ := RVFocusData.exists_paired_protected_components
    h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt D.toRVFocusData
    (D.carriedFocusData h00 hc hκ hs hv X) (D.carried_focusImage_subset h00 hc hκ hs hv X)
    C hCA hC P hPX hP
  let J (i) := (hFull i).choose
  have hJ (i) := (hFull i).choose_spec
  have hPoint (i) (p) (hp : p ∈ (P i).carrier) :
      (J i).point p = (X.carriedComponent h00 hc hκ hs hv F.component).point p :=
    ((hJ i).point p hp).trans (RVFocusRealization.carried_point h00 hc hκ hs hv D X F H hCoeff p (hPX i hp))
  exact ⟨F.component,F.coordinate,F.activeTags,F.focus,hLower,
    ⟨ProtectedCarriedLift.centripetal h00 hc hκ hs hv X F.component P hPX J hPoint⟩⟩

theorem ProtectedCarriedLift.image_proper
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    {n r s : ℕ} {I : Type*}
    {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
    {f : Map A B} {X : CarriedRefinementFrame A}
    {P : I → DefSet (rawMixedSpace (M := M) (n+1) X.arity) S}
    {hPX : ∀ i, (P i).carrier ⊆ X.bundle.carrier}
    (F : ProtectedCarriedLift (G := G) X f P hPX) (i : I) :
    ProperInvariant S (F.lift.map.restrict (hPX i)).image.carrier := by
  have h := (F.restrictions i).properHomeomorphism h00 hc linear hκ hs hv hsmall hΓ
  exact h.covariant.target_properInvariant h00 hc linear hκ hs hv hsmall hΓ h.bijective.surjective

end DiamondIntegral.Section6
