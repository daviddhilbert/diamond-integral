import «section 6».PreparedCoverGammaForms
import «section 6».FormCompatibleChainTransport

/-! An actual synchronized prepared map with Gamma constancy can
finish by regularization, retaining form compatibility, its common chain and every protected
restriction while giving the full tagged measured-preparation witness. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem PreparedSynchronizedFamily.taggedTarget_form_compatible
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A : DefSet (rawMixedSpace (M := M) (n+1) r) S}
    {P : Fin k → DefSet (rawMixedSpace (M := M) (n+1) r) S} {hPA : ∀ i,(P i).carrier ⊆ A.carrier}
    (F : PreparedSynchronizedFamily (G := G) A P hPA)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hF : FormCompatibleSynchronizedChain (G := G) (Fin k) A F.target F.map P ω) :
    FormCompatibleSynchronizedChain (G := G) (Fin k) A (F.taggedTarget h00 hc hκ hs hv).target
      (F.taggedTarget h00 hc hκ hs hv).map P ω := by
  let Q (i) := (F.map.restrict (hPA i)).image
  have hQsub (i) : (Q i).carrier ⊆ F.target.carrier := by
    rintro q ⟨p,hp⟩
    exact hp ▸ (F.map ⟨p.val,hPA i p.property⟩).property
  have hQ (i) : ProperInvariant S (Q i).carrier :=
    ((F.chain.atPiece i).literal_restriction h00 (hPA i)).target_properInvariant h00 hc hκ hs hv
  let η := ω.comp (F.map.inverse (F.chain.toChain.toSpecial.bijective h00))
  have hTransport (p : A) : (η (F.map p)).val=(ω p).val := by
    change (ω (F.map.inverse _ (F.map p))).val=(ω p).val
    rw [Map.inverse_apply]
  exact .comp P hPA hF η hTransport (.regularize F.target F.proper F.doublyBounded Q hQsub hQ
    (fun i => F.doublyBounded.mono (hQsub i)) η)

theorem PreparedSynchronizedFamily.measured_form_compatible_target
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A : DefSet (rawMixedSpace (M := M) (n+1) r) S}
    {P : Fin k → DefSet (rawMixedSpace (M := M) (n+1) r) S} {hPA : ∀ i,(P i).carrier ⊆ A.carrier}
    (F : PreparedSynchronizedFamily (G := G) A P hPA)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hF : FormCompatibleSynchronizedChain (G := G) (Fin k) A F.target F.map P ω)
    (hConst : ∀ p q : A,(F.map p).val.2=(F.map q).val.2 → (ω p).val=(ω q).val) :
    ∃ T : MeasuredCoordinatePreparation (G := G) A P hPA ω,
      FormCompatibleSynchronizedChain (G := G) (Fin k) A T.target T.map P ω := by
  let U := F.taggedTarget h00 hc hκ hs hv
  have hSpecial := U.chain.toChain.toSpecial
  let η := ω.comp (U.map.inverse (hSpecial.bijective h00))
  have hConstU (p q : A) (hpq : (U.map p).val.2=(U.map q).val.2) : (ω p).val=(ω q).val := by
    apply hConst p q
    funext j
    apply Subtype.ext
    have h := congrArg (fun v => (v (Fin.natAdd (n+1) j)).val) hpq
    change ((regularize (F.map p).val).2 (Fin.natAdd (n+1) j)).val=
      ((regularize (F.map q).val).2 (Fin.natAdd (n+1) j)).val at h
    simpa only [regularize,Fin.append_right] using h
  refine ⟨{
    arity := U.arity
    target := U.target
    map := U.map
    special := hSpecial
    proper := U.proper
    doublyBounded := U.doublyBounded
    prepared := U.pullback
    tagged := F.taggedTarget_tagged h00 hc hκ hs hv
    form := η
    transport := ?_
    constant := ?_
    pieces := fun i => ⟨(U.chain.atPiece i).literal_restriction h00 (hPA i),U.prepared i⟩ },F.taggedTarget_form_compatible h00 hc hκ hs hv ω hF⟩
  · intro p
    change (ω (U.map.inverse _ (U.map p))).val=(ω p).val
    rw [Map.inverse_apply]
  · intro x hx y hy hxy
    rw [gammaFormExtension_at η ⟨x,hx⟩,gammaFormExtension_at η ⟨y,hy⟩]
    apply hConstU (U.map.inverse _ ⟨x,hx⟩) (U.map.inverse _ ⟨y,hy⟩)
    rw [Map.apply_inverse,Map.apply_inverse]
    exact hxy

end DiamondIntegral.Section6
