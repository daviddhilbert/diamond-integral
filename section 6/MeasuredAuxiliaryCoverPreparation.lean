import «section 6».FiniteGammaFormLevels

/-! A separate finite proper cover can control the form while all
original protected sets are prepared by the same actual map. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r k l : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem measured_preparation_of_label_constant_cover
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ x ∈ V,iVF x) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V,x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A : DefSet (rawMixedSpace (M := M) (n+1) r) S)
    (hA : ProperInvariant S A.carrier) (hAD : VFDoublyBounded A.carrier) (hARV : IsRVPullback A.carrier)
    (C : Fin k → DefSet (rawMixedSpace (M := M) (n+1) r) S) (hCA : ∀ i,(C i).carrier ⊆ A.carrier)
    (hC : ∀ i,ProperInvariant S (C i).carrier)
    (Q : Fin l → DefSet (rawMixedSpace (M := M) (n+1) r) S) (hQA : ∀ i,(Q i).carrier ⊆ A.carrier)
    (hQ : ∀ i,ProperInvariant S (Q i).carrier) (hCover : ∀ p ∈ A.carrier,∃ i,p ∈ (Q i).carrier)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hConst : ∀ i (p q : Q i),p.val.2=q.val.2 →
      ω ⟨p.val,hQA i p.property⟩=ω ⟨q.val,hQA i q.property⟩) :
    Nonempty (MeasuredCoordinatePreparation (G := G) A C hCA ω) := by
  let D : Fin (k+l) → DefSet (rawMixedSpace (M := M) (n+1) r) S := Fin.append C Q
  have hDA : ∀ i,(D i).carrier ⊆ A.carrier := by
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [D,Fin.append_left] using hCA j
    · simpa only [D,Fin.append_right] using hQA j
  have hD : ∀ i,ProperInvariant S (D i).carrier := by
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [D,Fin.append_left] using hC j
    · simpa only [D,Fin.append_right] using hQ j
  obtain ⟨F⟩ := synchronized_preparation_all_dimensions h00 hc linear hκ hs hv (n+1)
    S V hsmall hΓ hV hVS hSV hnt (k+l) r A hA hAD hARV D hDA hD
  let T := F.taggedTarget h00 hc hκ hs hv
  have hTag := F.taggedTarget_tagged h00 hc hκ hs hv
  have hSpecial := T.chain.toChain.toSpecial
  let η := ω.comp (T.map.inverse (hSpecial.bijective h00))
  have hQPrepared (i : Fin l) : IsRVPullback (T.map.restrict (hQA i)).image.carrier := by
    have he : (D (Fin.natAdd k i)).carrier=(Q i).carrier := by simp only [D,Fin.append_right]
    have hImage := map_image_carrier_eq_of_source_eq
      (T.map.restrict (hDA (Fin.natAdd k i))) (T.map.restrict (hQA i)) he (fun _ => rfl)
    exact hImage ▸ T.prepared (Fin.natAdd k i)
  have hSame := hSpecial.transported_gamma_constant_of_prepared_cover h00 Q hQA hCover hQPrepared hTag ω hConst
  refine ⟨{
    arity := T.arity
    target := T.target
    map := T.map
    special := hSpecial
    proper := T.proper
    doublyBounded := T.doublyBounded
    prepared := T.pullback
    tagged := hTag
    form := η
    transport := ?_
    constant := ?_
    pieces := ?_ }⟩
  · intro p
    change (ω (T.map.inverse _ (T.map p))).val=(ω p).val
    rw [Map.inverse_apply]
  · intro p hp q hq he
    rw [gammaFormExtension_at η ⟨p,hp⟩,gammaFormExtension_at η ⟨q,hq⟩]
    exact congrArg Subtype.val (hSame ⟨p,hp⟩ ⟨q,hq⟩ he)
  · intro i
    have he : (D (Fin.castAdd l i)).carrier=(C i).carrier := by simp only [D,Fin.append_left]
    have hPiece := (T.chain.atPiece (Fin.castAdd l i)).literal_restriction h00 (hDA (Fin.castAdd l i))
    have hImage := map_image_carrier_eq_of_source_eq
      (T.map.restrict (hDA (Fin.castAdd l i))) (T.map.restrict (hCA i)) he (fun _ => rfl)
    exact ⟨hPiece.rebaseSource h00 he (fun _ => rfl),hImage ▸ T.prepared (Fin.castAdd l i)⟩

end DiamondIntegral.Section6
