import «section 6».BinaryBasePreparedRoots
import «section 6».ExactGammaTransport
import «section 6».BinaryMeasuredActiveRootFreezing

/-! Actual binary active-root preparation with pointwise Gamma
transport and complete form root control. The finite lower preparation
carries the second coordinate and all original protected pieces. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {r k : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

structure BinaryMeasuredBasePreparedRoots (A : DefSet (rawMixedSpace (M := M) 2 r) S)
    (P : Fin k → DefSet (rawMixedSpace (M := M) 2 r) S)
    (hPA : ∀ i, (P i).carrier ⊆ A.carrier) (N : ℕ)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    extends BinaryBasePreparedRoots (G := G) A P hPA N where
  form : Map target (DefSet.univ (rawGammaPresentation (M := M)) S)
  transport : ∀ p : A, (form (map p)).val = (ω p).val
  formControl : CoordinateFormRootControl (G := G) roots (gammaFormExtension form)

theorem binary_measured_active_roots_with_base_displacement
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
    (htag : ∀ p ∈ A.carrier, ∀ q ∈ A.carrier, p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1)
    (j : Fin r) (hHead : ∀ p ∈ A.carrier, rv M (p.1 (Fin.last 1)) = p.2 j)
    (R : CoordinateRootFamily A) (N : ℕ) (hN : R.Bound N)
    (P : Fin k → DefSet (rawMixedSpace (M := M) 2 r) S)
    (hPA : ∀ i, (P i).carrier ⊆ A.carrier) (hP : ∀ i, ProperInvariant S (P i).carrier)
    (hControl : ∀ i, CoordinateRootControl (G := G) R (P i).carrier)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hLevels : ∀ u γ, IsOpen {a : Fin 2 → VF M | (a,u) ∈ A.carrier ∧ gammaFormExtension ω (a,u) = γ})
    (hForm : CoordinateFormRootControl (G := G) R (gammaFormExtension ω)) :
    Nonempty (BinaryMeasuredBasePreparedRoots (G := G) A P hPA N ω) := by
  obtain ⟨R₀,hN₀,hControl₀,hForm₀,hActive₀⟩ := binary_measured_active_roots_proper_after_freezing
    h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt A hA R N hN P hP hControl ω hLevels hForm
  let B := (vfDropLast A).image
  have hB := vfDropLast_image_properInvariant hA
  have hBD := vfDropLast_image_doublyBounded hAD
  let X := CarriedRefinementFrame.identity B j hB hBD
  have hAX : A.carrier = X.bundle.carrier := rvPullback_coordinate_bundle A hARV j hHead
  let RX : CoordinateRootFamily X.bundle :=
    ⟨R₀.roots,fun p hp => hAX ▸ R₀.subset hp,R₀.finite⟩
  let C : Fin 1 → DefSet (rawMixedSpace (M := M) 1 r) S := fun _ => RX.activeBase
  have hCB (i) : (C i).carrier ⊆ B.carrier := R₀.activeBase_subset
  have hC (i) : ProperInvariant S (C i).carrier := hActive₀
  have hPX (i) : (P i).carrier ⊆ X.bundle.carrier := fun p hp => hAX ▸ hPA i hp
  obtain ⟨s,Z,f,hChain,hZ,hZD,hZRV,hZtag,hPieces,⟨H⟩⟩ := unary_preparation_protecting_carried_pieces
    h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt B hB hBD
    (vfDropLast_image_rvPullback hARV) (vfDropLast_image_tagged htag) C hCB hC X P hPX hP
  let F := H.lift
  have hinj := (hChain.toChain.toSpecial.bijective h00).injective
  have hSource (p : X.bundle) :
      (Fin.init p.val.1,p.val.2) ∈ RX.activeBase.carrier ↔ (X.oldPoint p).val ∈ (C 0).carrier := by
    change _ ↔ (Fin.init p.val.1,p.val.2 ∘ id) ∈ RX.activeBase.carrier
    simp only [Function.comp_id]
  obtain ⟨U,hU⟩ := F.active_root_tags_after_preparation h00 hinj RX (C 0) (hCB 0) hSource (hPieces 0).2 hZtag
  let g := F.map.comp (Map.inclusion (fun _ hp => hAX ▸ hp))
  have hg : SpecialCovariantChain (G := G) A F.target.bundle g :=
    F.special.changeSource (defSet_eq_of_carrier_eq hAX.symm) (fun _ => rfl)
  have hMap (i) : F.map.restrict (hPX i) = g.restrict (hPA i) := Map.ext (fun _ => rfl)
  have hControlX (i) : CoordinateRootControl (G := G) RX (P i).carrier := by
    intro b u a ρ hAmbient hAvoid x hx y hy
    exact hControl₀ i b u a ρ (fun z hz => hAX.symm ▸ hAmbient z hz) hAvoid x hx y hy
  let ωX := ω.comp (Map.inclusion (fun _ hp => hAX.symm ▸ hp))
  have hFormX : CoordinateFormRootControl (G := G) RX (gammaFormExtension ωX) := by
    intro b u a ρ hAmbient hAvoid x hx y hy
    have hxA : (Fin.snoc b x,u) ∈ A.carrier := hAX.symm ▸ hAmbient x hx
    have hyA : (Fin.snoc b y,u) ∈ A.carrier := hAX.symm ▸ hAmbient y hy
    have hOld := hForm₀ b u a ρ (fun z hz => hAX.symm ▸ hAmbient z hz) hAvoid x hx y hy
    have hX := gammaFormExtension_at ωX (⟨_,hAmbient x hx⟩ : X.bundle)
    have hY := gammaFormExtension_at ωX (⟨_,hAmbient y hy⟩ : X.bundle)
    rw [gammaFormExtension_at ω ⟨_,hxA⟩,gammaFormExtension_at ω ⟨_,hyA⟩] at hOld
    exact hX.trans (hOld.trans hY.symm)
  let η := ωX.comp (F.map.inverse (F.special.bijective h00))
  refine ⟨{
    arity := F.target.arity
    target := F.target.bundle
    map := g
    special := hg
    baseDisplacement := by
      have hD := F.rv_displacement (hChain.toChain.toSpecial.unary_rv_displacement h00 (0 : Fin 1))
      intro p z he
      exact hD (⟨p.val,hAX ▸ p.property⟩ : X.bundle) (⟨z.val,hAX ▸ z.property⟩ : X.bundle) he
    proper := rvCoordinateBundle_properInvariant h00 hc hκ hs hv F.target.base F.target.freeLabel F.target.proper
    doublyBounded := rvCoordinateBundle_doublyBounded F.target.base F.target.freeLabel F.target.doublyBounded F.target.proper.rvBounded
    pullback := F.target.pullback hZRV
    tagged := rvCoordinateBundle_tagged F.target.base F.target.freeLabel
      (labelRefinement_tagged Z F.target.base F.target.labels F.target.fibres hZtag)
    headTag := F.target.freeLabel
    head_tag := fun _ hp => hp.2
    carried := fun p => F.carried ⟨p.val,hAX ▸ p.property⟩
    roots := F.pushCoordinateRoots hinj RX
    bound := F.pushCoordinateRoots_bound hinj RX N hN₀
    control := ?_
    restrictions := ?_
    active := U
    active_iff := hU
    form := η
    transport := ?_
    formControl := F.pushCoordinateRoots_form_control h00 hinj RX ωX hFormX
  }⟩
  · intro i
    have h := F.pushCoordinateRoots_control h00 hinj RX (P i) (hPX i) (hControlX i)
    rwa [hMap i] at h
  · intro i
    have h := H.restrictions i
    rwa [hMap i] at h
  · intro p
    change (ωX (F.map.inverse (F.special.bijective h00)
      (F.map ⟨p.val,hAX ▸ p.property⟩))).val = (ω p).val
    rw [Map.inverse_apply]
    rfl

end DiamondIntegral.Section6
