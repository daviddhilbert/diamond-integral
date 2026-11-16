import «section 6».ArbitraryProperPreparation
import «section 6».MeasuredCoordinatePreparationData
import «section 6».TaggedPreparedFamilies

/-! In every VF dimension, preparation of a proper cover makes a Gamma
form contractible when it was already constant on each piece's old-label
fibres. Both the form and all literal protected restrictions are retained. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem SpecialCovariantChain.transported_gamma_constant_of_prepared_cover
    {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
    {f : Map A B} (h : SpecialCovariantChain (G := G) A B f) (h00 : M ⊨ Axioms.ACVF00)
    (C : Fin k → DefSet (rawMixedSpace (M := M) n r) S) (hCA : ∀ i,(C i).carrier ⊆ A.carrier)
    (hCover : ∀ p ∈ A.carrier,∃ i,p ∈ (C i).carrier)
    (hPrepared : ∀ i,IsRVPullback (f.restrict (hCA i)).image.carrier)
    (hTag : ∀ p ∈ B.carrier,∀ q ∈ B.carrier,p.2=q.2 → tupleRV M p.1=tupleRV M q.1)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hConst : ∀ i (p q : C i),p.val.2=q.val.2 →
      ω ⟨p.val,hCA i p.property⟩=ω ⟨q.val,hCA i q.property⟩) :
    ∀ p q : B,p.val.2=q.val.2 →
      (ω.comp (f.inverse (h.bijective h00))) p=(ω.comp (f.inverse (h.bijective h00))) q := by
  obtain ⟨hrs,hRV⟩ := h.retainsRV
  intro p q hpq
  let x := f.inverse (h.bijective h00) p
  let y := f.inverse (h.bijective h00) q
  have hfx : f x=p := Map.apply_inverse f _ p
  have hfy : f y=q := Map.apply_inverse f _ q
  obtain ⟨i,hxi⟩ := hCover x.val x.property
  have hpImage : p.val ∈ (f.restrict (hCA i)).image.carrier := ⟨⟨x.val,hxi⟩,congrArg Subtype.val hfx⟩
  have hqImage := rvPullback_mem_of_sameRV (hPrepared i) hpImage (hTag p.val p.property q.val q.property hpq) hpq
  obtain ⟨z,hz⟩ := hqImage
  have hzy : (⟨z.val,hCA i z.property⟩ : A)=y :=
    (h.bijective h00).injective (Subtype.ext (hz.trans (congrArg Subtype.val hfy).symm))
  have hyi : y.val ∈ (C i).carrier := (congrArg Subtype.val hzy) ▸ z.property
  have hOld : x.val.2=y.val.2 := by
    funext j
    have hx := hRV x j
    have hy := hRV y j
    rw [hfx] at hx
    rw [hfy] at hy
    exact hx.symm.trans ((congrFun hpq (rvTailIndex hrs j)).trans hy)
  exact hConst i ⟨x.val,hxi⟩ ⟨y.val,hyi⟩ hOld

theorem measured_preparation_of_piecewise_old_labels
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
    (hC : ∀ i,ProperInvariant S (C i).carrier) (hCover : ∀ p ∈ A.carrier,∃ i,p ∈ (C i).carrier)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hConst : ∀ i (p q : C i),p.val.2=q.val.2 →
      ω ⟨p.val,hCA i p.property⟩=ω ⟨q.val,hCA i q.property⟩) :
    Nonempty (MeasuredCoordinatePreparation (G := G) A C hCA ω) := by
  obtain ⟨F⟩ := synchronized_preparation_all_dimensions h00 hc linear hκ hs hv (n+1)
    S V hsmall hΓ hV hVS hSV hnt k r A hA hAD hARV C hCA hC
  let T := F.taggedTarget h00 hc hκ hs hv
  have hTag := F.taggedTarget_tagged h00 hc hκ hs hv
  have hSpecial := T.chain.toChain.toSpecial
  let η := ω.comp (T.map.inverse (hSpecial.bijective h00))
  have hSame := hSpecial.transported_gamma_constant_of_prepared_cover h00 C hCA hCover T.prepared hTag ω hConst
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
    pieces := fun i => ⟨(T.chain.atPiece i).literal_restriction h00 (hCA i),T.prepared i⟩ }⟩
  · intro p
    change (ω (T.map.inverse _ (T.map p))).val=(ω p).val
    rw [Map.inverse_apply]
  · intro p hp q hq he
    rw [gammaFormExtension_at η ⟨p,hp⟩,gammaFormExtension_at η ⟨q,hq⟩]
    exact congrArg Subtype.val (hSame ⟨p,hp⟩ ⟨q,hq⟩ he)

end DiamondIntegral.Section6
