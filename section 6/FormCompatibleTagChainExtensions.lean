import «section 6».FormCompatibleTagBranchAssembly

/-! A whole finite form-compatible chain extends to the actual ambient
set. Exact intermediate forms are obtained from the actual inverse map,
and on the selected branch agree with the given local intermediate form. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem FormCompatibleSynchronizedChain.tag_branch_extension
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {C : DefSet (rawMixedSpace (M := M) n r) S}
    {B : DefSet (rawMixedSpace (M := M) n s) S} {f : Map C B}
    {Q : Fin k → DefSet (rawMixedSpace (M := M) n r) S}
    {θ : Map C (DefSet.univ (rawGammaPresentation (M := M)) S)}
    (h : FormCompatibleSynchronizedChain (G := G) (Fin k) C B f Q θ) :
    ∀ X : SynchronizedTagBranchFrame C Q,
      ∀ ω : Map X.ambient (DefSet.univ (rawGammaPresentation (M := M)) S),
      (∀ p : C,(θ p).val=(ω ⟨p.val,X.subset p.property⟩).val) →
      ∃ F : SynchronizedTagBranchExtension (G := G) X f (fun i => (h.toSynchronized.atPiece i).source_subset),
        FormCompatibleSynchronizedChain (G := G) (Fin k) X.ambient F.output.ambient F.map X.pieces ω := by
  induction h with
  | identity C hC Q hQC hQ θ =>
    intro X ω hForm
    exact SynchronizedTagBranchExtension.ofMap_form_compatible h00 hc hκ hs hv X (Map.id C)
      Function.surjective_id hQC (Map.id X.ambient) ω
      (.identity _ X.proper X.pieces X.pieces_subset X.pieces_proper ω) (fun _ => rfl) (fun _ _ => rfl)
  | regularize C hC hCD Q hQC hQ hQD θ =>
    intro X ω hForm
    exact SynchronizedTagBranchExtension.ofMap_form_compatible h00 hc hκ hs hv X (regularization C)
      (regularization_bijective C).surjective hQC (regularization X.ambient) ω
      (.regularize _ X.proper X.doublyBounded X.pieces X.pieces_subset X.pieces_proper
        (fun i => X.doublyBounded.mono (X.pieces_subset i)) ω) (fun _ => rfl) (fun _ _ => rfl)
  | centripetal C D Q hQC E hData θ hSafe =>
    intro X ω hForm
    obtain ⟨F,H,hj,hCoeff,hRestr,hPoint,hOutside,hChain⟩ := exists_form_compatible_tag_component_extension
      D X.tags X.source_eq X.proper X.doublyBounded (X.tagged_of_local D.tagged)
      X.pieces Q X.pieces_subset X.pieces_proper X.pieces_eq E hData θ hSafe ω hForm
    exact SynchronizedTagBranchExtension.ofMap_form_compatible h00 hc hκ hs hv X D.bijection
      (D.bijective h00).surjective hQC F.bijection ω hChain
      (fun p => hPoint p.val p.property) (fun p hp => hOutside p.val p.property hp)
  | @comp r s t C B Z f g Q hQC θ hf η hTransport hg ihf ihg =>
    intro X ω hForm
    obtain ⟨F,hF⟩ := ihf X ω hForm
    have hBij := hF.toSynchronized.toChain.toSpecial.bijective h00
    let Ω := ω.comp (F.map.inverse hBij)
    have hGlobalTransport (p : X.ambient) : (Ω (F.map p)).val=(ω p).val := by
      change (ω (F.map.inverse _ (F.map p))).val=(ω p).val
      rw [Map.inverse_apply]
    have hFormNext (b) : (η b).val=(Ω ⟨b.val,F.output.subset b.property⟩).val := by
      obtain ⟨a,rfl⟩ := (hf.toSynchronized.toChain.toSpecial.bijective h00).surjective b
      have he : F.map ⟨a.val,X.subset a.property⟩=
          ⟨(f a).val,F.output.subset (f a).property⟩ := Subtype.ext (F.branch a)
      exact (hTransport a).trans ((hForm a).trans (by rw [← he]; exact (hGlobalTransport _).symm))
    obtain ⟨H,hH⟩ := ihg F.output Ω hFormNext
    have hGlobal : FormCompatibleSynchronizedChain (G := G) (Fin k) X.ambient H.output.ambient
        (H.map.comp F.map) X.pieces ω :=
      .comp X.pieces X.pieces_subset hF Ω hGlobalTransport (hH.changePieces (fun i => F.piece_images i))
    apply SynchronizedTagBranchExtension.ofMap_form_compatible h00 hc hκ hs hv X _
      ((hg.toSynchronized.toChain.toSpecial.bijective h00).surjective.comp
        (hf.toSynchronized.toChain.toSpecial.bijective h00).surjective)
      hQC (H.map.comp F.map) ω hGlobal
    · intro x
      have he : F.map ⟨x.val,X.subset x.property⟩=
          ⟨(f x).val,F.output.subset (f x).property⟩ := Subtype.ext (F.branch x)
      change (H.map (F.map ⟨x.val,X.subset x.property⟩)).val=_
      rw [he]
      exact H.branch _
    · intro x hx
      exact (H.outside (F.map x) (fun h => hx ((F.selected x).mp h))).trans (F.outside x hx)

end DiamondIntegral.Section6
