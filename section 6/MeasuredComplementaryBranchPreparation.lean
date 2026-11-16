import «section 6».MeasuredBranchFormConstancy

/-! Actual measured preparations on complementary whole-label branches
glue into one measured form-compatible ambient preparation. The second
branch uses the exact form pulled back through the first ambient map. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem measured_form_compatible_preparation_glue_complementary_tags
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (A : DefSet (rawMixedSpace (M := M) (n+1) r) S)
    (hA : ProperInvariant S A.carrier) (hD : VFDoublyBounded A.carrier) (hRP : IsRVPullback A.carrier)
    (hTag : ∀ p ∈ A.carrier,∀ z ∈ A.carrier,p.2=z.2 → tupleRV M p.1=tupleRV M z.1)
    (P : Fin k → DefSet (rawMixedSpace (M := M) (n+1) r) S)
    (hPA : ∀ i,(P i).carrier ⊆ A.carrier) (hP : ∀ i,ProperInvariant S (P i).carrier)
    (U : DefSet (rawRVSpace (M := M) r) S)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (F : MeasuredCoordinatePreparation (G := G) (focusActive A U) (fun i => focusActive (P i) U)
      (fun i _ hp => ⟨hPA i hp.1,hp.2⟩) (ω.comp (Map.inclusion (fun _ hp => hp.1))))
    (hF : FormCompatibleSynchronizedChain (G := G) (Fin k) (focusActive A U) F.target F.map
      (fun i => focusActive (P i) U) (ω.comp (Map.inclusion (fun _ hp => hp.1))))
    (G' : MeasuredCoordinatePreparation (G := G) (focusActive A (rvTagComplement U))
      (fun i => focusActive (P i) (rvTagComplement U)) (fun i _ hp => ⟨hPA i hp.1,hp.2⟩)
      (ω.comp (Map.inclusion (fun _ hp => hp.1))))
    (hG : FormCompatibleSynchronizedChain (G := G) (Fin k) (focusActive A (rvTagComplement U)) G'.target G'.map
      (fun i => focusActive (P i) (rvTagComplement U)) (ω.comp (Map.inclusion (fun _ hp => hp.1)))) :
    ∃ T : MeasuredCoordinatePreparation (G := G) A P hPA ω,
      FormCompatibleSynchronizedChain (G := G) (Fin k) A T.target T.map P ω := by
  let X := SynchronizedTagBranchFrame.of_slice A P hPA hA hD hP hTag U
  obtain ⟨E,hE⟩ := hF.tag_branch_extension h00 hc hκ hs hv X ω (fun _ => rfl)
  have hBRP := E.chain.toChain.target_rvPullback h00 hRP
  have hBTag := E.output.tagged_of_local F.tagged
  have hBij := E.chain.toChain.toSpecial.bijective h00
  let Ω := ω.comp (E.map.inverse hBij)
  have hTransport (p : A) : (Ω (E.map p)).val=(ω p).val := by
    change (ω (E.map.inverse _ (E.map p))).val=(ω p).val
    rw [Map.inverse_apply]
  let Z := E.outsideFrame h00 hRP hTag
  obtain ⟨G₀,hG₀⟩ := G'.refine_rv_labels_form_compatible h00 hc hκ hs hv hG Z
  let ι : Map (focusActive A (rvTagComplement U)) A := Map.inclusion (fun _ hp => hp.1)
  let Ωout := Ω.comp (Map.inclusion (fun p (hp : p ∈ Z.base.carrier) => hp.1))
  have hFormOut (p : Z.base) : (((ω.comp ι).comp Z.oldMap) p).val=(Ωout p).val := by
    obtain ⟨a,ha,hOld,hOut⟩ := E.outside_recover h00 ⟨p.val,p.property.1⟩ p.property.2
    have hInput : ι (Z.oldMap p)=a := Subtype.ext hOld
    have hImage : E.map a=⟨p.val,p.property.1⟩ := Subtype.ext ha
    change (ω (ι (Z.oldMap p))).val=(Ω ⟨p.val,p.property.1⟩).val
    rw [hInput,← hImage]
    exact (hTransport a).symm
  let G₁ : MeasuredCoordinatePreparation (G := G) (focusActive E.output.ambient (rvTagComplement E.output.tags))
      (fun i => focusActive (E.output.pieces i) (rvTagComplement E.output.tags))
      (fun i _ hp => ⟨E.output.pieces_subset i hp.1,hp.2⟩) Ωout :=
    (G₀.changeForm hFormOut).changePieces (fun i => E.outsideFrame_piece h00 hRP hTag i)
  have hG₁ : FormCompatibleSynchronizedChain (G := G) (Fin k)
      (focusActive E.output.ambient (rvTagComplement E.output.tags)) G₁.target G₁.map
      (fun i => focusActive (E.output.pieces i) (rvTagComplement E.output.tags)) Ωout :=
    (hG₀.changeForm hFormOut).changePieces (fun i => E.outsideFrame_piece h00 hRP hTag i)
  let Y := SynchronizedTagBranchFrame.of_slice E.output.ambient E.output.pieces E.output.pieces_subset
    E.output.proper E.output.doublyBounded E.output.pieces_proper hBTag (rvTagComplement E.output.tags)
  obtain ⟨H,hH⟩ := hG₁.tag_branch_extension h00 hc hκ hs hv Y Ω (fun _ => rfl)
  have hComplement (i) : IsRVPullback
      ((Y.pieces i).sdiff (focusActive (Y.pieces i) Y.tags)).carrier := by
    have he : ((Y.pieces i).sdiff (focusActive (Y.pieces i) Y.tags)).carrier=
        (focusActive (E.output.pieces i) E.output.tags).carrier := by
      ext z
      change (z ∈ (E.output.pieces i).carrier ∧
        ¬ (z ∈ (E.output.pieces i).carrier ∧ z.2 ∉ E.output.tags.carrier)) ↔
          (z ∈ (E.output.pieces i).carrier ∧ z.2 ∈ E.output.tags.carrier)
      tauto
    rw [he]
    exact (E.output.pieces_eq i) ▸ (F.pieces i).2
  let J := H.preparedFamily h00 hBRP (fun i => (G₁.pieces i).2) hComplement
  have hConst : ∀ p q : E.output.ambient,(H.map p).val.2=(H.map q).val.2 → (Ω p).val=(Ω q).val := by
    apply H.source_form_constant G₁ Ω (fun _ => rfl)
    intro p q he hp
    exact E.image_branch_form_constant F h00 ω (fun _ => rfl) Ω hTransport p q he (by
      change ¬ p.val.2 ∉ E.output.tags.carrier at hp
      exact not_not.mp hp)
  obtain ⟨T,hT⟩ := J.measured_form_compatible_target h00 hc hκ hs hv Ω hH hConst
  have hQA (i) : (E.map.restrict (hPA i)).image.carrier ⊆ E.output.ambient.carrier := by
    rintro y ⟨p,hp⟩
    exact hp ▸ (E.map.restrict (hPA i) p).property
  let T' : MeasuredCoordinatePreparation (G := G) E.output.ambient
      (fun i => (E.map.restrict (hPA i)).image) hQA Ω := T.changePieces (fun i => E.piece_images i)
  have hT' := hT.changePieces (fun i => E.piece_images i)
  refine ⟨MeasuredCoordinatePreparation.precompose h00 P hPA E.map E.chain.toChain.toSpecial
    (fun i => (E.chain.atPiece i).literal_restriction h00 (hPA i))
    hQA
    ω Ω hTransport T',?_⟩
  exact .comp P hPA hE Ω hTransport hT'

end DiamondIntegral.Section6
