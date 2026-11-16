import «section 6».OrdinaryChainCovariantRealization
import «section 6».OrdinaryLocalTranslations

/-! Complete finite-chain realization away from the actual ordinary
exceptional set. Every new map is a finite special-covariant chain and
retains an explicit selector for the old complete endpoint. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S R : Set M} {r s q : ℕ}
variable {hc : CanonicalStructure.IsCanonical (M := M)}
variable {A : SpecialTransformations.Section5.DefSet (M := M) R 1 r}
variable {B : SpecialTransformations.Section5.DefSet (M := M) R 1 s}
variable {hA : SpecialTransformations.Section5.GammaSetDefinable (ordinaryNamedGammaBase S)
  (SpecialTransformations.Section5.carrier A)}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

structure OrdinaryChainLabelledRealization (X : OrdinaryUnaryFocusFrame hc A hA q)
    (T : SpecialTransformations.Section5.Chain R 1 A B)
    (hT : SpecialTransformations.Section5.GammaChainDefinable (ordinaryNamedGammaBase S) T)
    extends OrdinaryChainCovariantRealization (G := G) X T hT where
  labelControl : ∀ p q : X.source,p.val.2=q.val.2 →
    SpecialTransformations.Section5.SameRV (T.toMap (X.oldMap p)).val (T.toMap (X.oldMap q)).val →
    (map p).val.2=(map q).val.2

theorem exists_labelled_covariant_realization_off_ordinary_exceptions
    (h00 : M ⊨ Axioms.ACVF00) (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V,iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V,x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (T : SpecialTransformations.Section5.Chain R 1 A B)
    (hT : SpecialTransformations.Section5.GammaChainDefinable (ordinaryNamedGammaBase S) T) :
    ∀ q,(X : OrdinaryUnaryFocusFrame hc A
      (SpecialTransformations.Section5.GammaChainDefinable.source (ordinaryNamedGammaBase S) T hT) q) →
      (∀ p : X.source,(X.oldMap p).val ∉ ordinaryChainZeroSources T) →
      Nonempty (OrdinaryChainLabelledRealization (G := G) X T hT) := by
  induction T with
  | nil A =>
    intro q X hNo
    exact ⟨{
      arity := q
      targetFrame := X
      map := Map.id X.source
      special := .identity X.source X.proper
      commutes := fun _ => rfl
      labelControl := fun p q hTags _ => hTags }⟩
  | @cons a b c A B C p tail ih =>
    intro q X hNo
    cases p with
    | canonical A =>
      let Y := X.afterCanonical h00 hκ hs hv
      obtain ⟨F⟩ := ih hT.2 (1+q) Y (X.afterCanonical_no_zero_sources h00 hκ hs hv tail hNo)
      refine ⟨{
        arity := F.arity
        targetFrame := F.targetFrame
        map := F.map.comp (regularization X.source)
        special := .comp (.regularize X.source X.proper X.doublyBounded) F.special
        commutes := ?_
        labelControl := ?_ }⟩
      · intro p
        have hArg : Y.oldMap (regularization X.source p)=
            (SpecialTransformations.Section5.Primitive.canonical A).toMap (X.oldMap p) :=
          Subtype.ext (X.afterCanonical_at_step h00 hκ hs hv p)
        exact (F.commutes (regularization X.source p)).trans
          (congrArg (fun a => (tail.toMap a).val) hArg)
      · intro p q hTags hSame
        let step := SpecialTransformations.Section5.Primitive.canonical A
        have hOldStepSame := tail.sameRV_of (step.toMap (X.oldMap p)) (step.toMap (X.oldMap q)) hSame
        have hOldInputSame := step.sameRV_of (X.oldMap p) (X.oldMap q) hOldStepSame
        have hVF := ((ordinary_sameRV_iff _ _).mp hOldInputSame).1
        rw [X.point p,X.point q] at hVF
        have hNewTags : (regularization X.source p).val.2=(regularization X.source q).val.2 := by
          change Fin.append (tupleRV M p.val.1) p.val.2=Fin.append (tupleRV M q.val.1) q.val.2
          rw [hVF,hTags]
        have hArg (a : X.source) : Y.oldMap (regularization X.source a)=step.toMap (X.oldMap a) :=
          Subtype.ext (X.afterCanonical_at_step h00 hκ hs hv a)
        have hEndSame : SpecialTransformations.Section5.SameRV
            (tail.toMap (Y.oldMap (regularization X.source p))).val
            (tail.toMap (Y.oldMap (regularization X.source q))).val := by
          rw [hArg p,hArg q]
          exact hSame
        exact F.labelControl (regularization X.source p) (regularization X.source q) hNewTags hEndSame
    | @centripetal a i j D =>
      have hi : i=0 := Subsingleton.elim _ _
      subst i
      obtain ⟨E,hCoord,hActive,hFocus,hCore⟩ := X.exists_component_of_no_zero_sources D hT.1.2 tail
        h00 linear hκ hs hv V hsmall hΓ hV hVS hSV hnt hNo
      let Y := X.afterCentripetal D hT.1.2 h00 hκ hs hv E hCoord hActive hFocus hCore
      obtain ⟨F⟩ := ih hT.2 (1+(1+q)) Y
        (X.afterCentripetal_no_zero_sources h00 hκ hs hv D hT.1.2 E hCoord hActive hFocus hCore tail hNo)
      have hStep : SpecialCovariantChain (G := G) X.source (regularizeMap E.map.image).image (centripetalStepMap E) :=
        .comp (.centripetal X.source E) (.regularize E.map.image
          (E.image_properInvariant h00 hc hκ hs hv) E.image_vfDoublyBounded)
      refine ⟨{
        arity := F.arity
        targetFrame := F.targetFrame
        map := F.map.comp (centripetalStepMap E)
        special := .comp hStep F.special
        commutes := ?_
        labelControl := ?_ }⟩
      · intro p
        have hArg : Y.oldMap (centripetalStepMap E p)=
            (SpecialTransformations.Section5.Primitive.centripetal D).toMap (X.oldMap p) :=
          Subtype.ext (X.afterCentripetal_at_step h00 hκ hs hv D hT.1.2 E hCoord hActive hFocus hCore p)
        exact (F.commutes (centripetalStepMap E p)).trans (congrArg (fun a => (tail.toMap a).val) hArg)
      · intro p q hTags hSame
        let step := SpecialTransformations.Section5.Primitive.centripetal D
        have hOldStepSame := tail.sameRV_of (step.toMap (X.oldMap p)) (step.toMap (X.oldMap q)) hSame
        have hOldLeading := ((ordinary_sameRV_iff _ _).mp hOldStepSame).1
        have hField (a : X.source) : (E.point a.val).1=(step.toMap (X.oldMap a)).val.1 :=
          X.component_field_matches_ordinary D hT.1.2 E hCoord hActive hFocus hCore a
        have hLeading : tupleRV M (E.point p.val).1=tupleRV M (E.point q.val).1 := by
          rw [hField p,hField q]
          exact hOldLeading
        have hComponentTags : (E.point p.val).2=(E.point q.val).2 := by
          simp only [CentripetalData.point,hCore p.val p.property,hCore q.val q.property,hTags]
        have hNewTags : (centripetalStepMap E p).val.2=(centripetalStepMap E q).val.2 := by
          change Fin.append (tupleRV M (E.point p.val).1) (E.point p.val).2=
            Fin.append (tupleRV M (E.point q.val).1) (E.point q.val).2
          rw [hLeading,hComponentTags]
        have hArg (a : X.source) : Y.oldMap (centripetalStepMap E a)=step.toMap (X.oldMap a) :=
          Subtype.ext (X.afterCentripetal_at_step h00 hκ hs hv D hT.1.2 E hCoord hActive hFocus hCore a)
        have hEndSame : SpecialTransformations.Section5.SameRV
            (tail.toMap (Y.oldMap (centripetalStepMap E p))).val
            (tail.toMap (Y.oldMap (centripetalStepMap E q))).val := by
          rw [hArg p,hArg q]
          exact hSame
        exact F.labelControl (centripetalStepMap E p) (centripetalStepMap E q) hNewTags hEndSame

end DiamondIntegral.Section6
