import «section 6».UnaryMeasuredCompatibleExistence

/-! Completion of actual binary measured preparation when the common
coordinate-root family is empty. The form descends to the unary base,
whose actual permitted preparation is lifted through the full disc
coordinate. All pieces use the same ambient map. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {r k : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem binary_measured_preparation_of_empty_coordinate_roots
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V, iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A : DefSet (rawMixedSpace (M := M) 2 r) S) (hA : ProperInvariant S A.carrier)
    (hAD : VFDoublyBounded A.carrier) (hARV : IsRVPullback A.carrier)
    (hTag : ∀ p ∈ A.carrier, ∀ q ∈ A.carrier, p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1)
    (j : Fin r) (hHeadTag : ∀ p ∈ A.carrier, rv M (p.1 (Fin.last 1)) = p.2 j)
    (R : CoordinateRootFamily A) (hEmpty : R.roots.carrier = ∅)
    (P : Fin k → DefSet (rawMixedSpace (M := M) 2 r) S)
    (hPA : ∀ i, (P i).carrier ⊆ A.carrier) (hP : ∀ i, ProperInvariant S (P i).carrier)
    (hControl : ∀ i, CoordinateRootControl (G := G) R (P i).carrier)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hLevels : ∀ u γ, IsOpen {a : Fin 2 → VF M | (a,u) ∈ A.carrier ∧ gammaFormExtension ω (a,u) = γ})
    (hForm : CoordinateFormRootControl (G := G) R (gammaFormExtension ω)) :
    Nonempty (MeasuredCoordinatePreparation (G := G) A P hPA ω) := by
  let B := (vfDropLast A).image
  let C (i) := (vfDropLast (P i)).image
  have hB := vfDropLast_image_properInvariant hA
  have hBD := vfDropLast_image_doublyBounded hAD
  have hCsub (i) : (C i).carrier ⊆ B.carrier := by
    rintro q ⟨p,hp⟩
    exact ⟨⟨p.val,hPA i p.property⟩,hp⟩
  obtain ⟨η,hη⟩ := empty_coordinate_roots_gamma_descent R ω hForm hv hEmpty hARV hAD hTag
  have hLevelsη := descended_gamma_levels_open h00 hc linear hκ hs hv hsmall hΓ hA ω hLevels η hη
  obtain ⟨T,hT⟩ := unary_measured_compatible_preparation_of_doublyBounded_tagged
    h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt B hB hBD
    (vfDropLast_image_rvPullback hARV) (vfDropLast_image_tagged hTag) C hCsub
    (fun i => vfDropLast_image_properInvariant (hP i)) η hLevelsη
  let X := CarriedRefinementFrame.identity B j hB hBD
  obtain ⟨F,hPrepared⟩ := hT.carried_preparation_exists h00 hc hκ hs hv hCsub (fun i => (T.pieces i).2) X
  have hABundle : A.carrier = X.bundle.carrier := rvPullback_coordinate_bundle A hARV j hHeadTag
  have hPBundle (i) : (P i).carrier = (rvCoordinateBundle (C i) j).carrier :=
    (hControl i).empty_roots_bundle hv (P i) hEmpty hARV hAD (hPA i) j
      (fun p hp => hHeadTag p (hPA i hp))
  have hSelected (i) : X.selectedPiece (C i) = C i := by
    apply defSet_eq_of_carrier_eq
    ext p
    rw [X.mem_selectedPiece]
    change (p ∈ B.carrier ∧ (p.1,p.2 ∘ id) ∈ (C i).carrier) ↔ p ∈ (C i).carrier
    simpa only [Function.comp_id,Prod.mk.eta] using
      (show (p ∈ B.carrier ∧ p ∈ (C i).carrier) ↔ p ∈ (C i).carrier from
        ⟨fun h => h.2,fun hp => ⟨hCsub i hp,hp⟩⟩)
  have hPFrame (i) : (P i).carrier = (rvCoordinateBundle (X.selectedPiece (C i)) X.freeLabel).carrier := by
    rw [hSelected i]
    exact hPBundle i
  let g := F.lift.map.comp (Map.inclusion (fun _ hp => hABundle ▸ hp))
  have hg : SpecialCovariantChain (G := G) A F.lift.target.bundle g :=
    SpecialCovariantChain.changeSource (defSet_eq_of_carrier_eq hABundle.symm) (fun _ => rfl) F.lift.special
  let θ := T.form.comp F.lift.target.oldMap
  refine ⟨{
    arity := F.lift.target.arity
    target := F.lift.target.bundle
    map := g
    special := hg
    proper := rvCoordinateBundle_properInvariant h00 hc hκ hs hv F.lift.target.base
      F.lift.target.freeLabel F.lift.target.proper
    doublyBounded := rvCoordinateBundle_doublyBounded F.lift.target.base F.lift.target.freeLabel
      F.lift.target.doublyBounded F.lift.target.proper.rvBounded
    prepared := F.lift.target.pullback T.prepared
    tagged := F.lift.target.bundle_tagged T.tagged
    form := θ
    transport := ?_
    constant := F.lift.target.gamma_form_constant T.form T.constant
    pieces := ?_
  }⟩
  · intro p
    have ht := F.lift.gamma_form_transport η T.form T.transport ⟨p.val,hABundle ▸ p.property⟩
    exact ht.trans (congrArg Subtype.val (hη p))
  · intro i
    have hPiece : SpecialCovariantChain (G := G) (P i) (g.restrict (hPA i)).image
        (g.restrict (hPA i)).toImage :=
      (F.restrictions i).rebaseSource h00 (hPFrame i).symm (fun _ => rfl)
    have hImage := map_image_carrier_eq_of_source_eq
      (F.lift.map.restrict (X.selectedPiece_bundle_subset (C i)))
      (g.restrict (hPA i)) (hPFrame i).symm (fun _ => rfl)
    exact ⟨hPiece,hImage ▸ hPrepared i⟩

end DiamondIntegral.Section6
