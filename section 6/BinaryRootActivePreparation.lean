import «section 6».SourceEqualityTransport

/-! Construct a binary active-root preparation from the actual unary
algorithm. The arbitrary full-dimensional protected pieces remain
literal special restrictions, with exact root control and bound. -/

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

structure BinaryActiveRootPreparation (A : DefSet (rawMixedSpace (M := M) 2 r) S)
    (P : Fin k → DefSet (rawMixedSpace (M := M) 2 r) S)
    (hPA : ∀ i, (P i).carrier ⊆ A.carrier) (N : ℕ) where
  arity : ℕ
  target : DefSet (rawMixedSpace (M := M) 2 arity) S
  map : Map A target
  special : SpecialCovariantChain (G := G) A target map
  proper : ProperInvariant S target.carrier
  doublyBounded : VFDoublyBounded target.carrier
  pullback : IsRVPullback target.carrier
  tagged : ∀ p ∈ target.carrier, ∀ q ∈ target.carrier, p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1
  headTag : Fin arity
  head_tag : ∀ p ∈ target.carrier, rv M (p.1 (Fin.last 1)) = p.2 headTag
  carried : ∀ p : A, (map p).val.1 (Fin.last 1) = p.val.1 (Fin.last 1)
  roots : CoordinateRootFamily target
  bound : roots.Bound N
  control : ∀ i, CoordinateRootControl (G := G) roots (map.restrict (hPA i)).image.carrier
  restrictions : ∀ i, SpecialCovariantChain (G := G) (P i)
    (map.restrict (hPA i)).image (map.restrict (hPA i)).toImage
  active : DefSet (rawRVSpace (M := M) arity) S
  active_iff : ∀ p ∈ target.carrier, p.2 ∈ active.carrier ↔ (roots.fibre (Fin.init p.1) p.2).Nonempty

theorem binary_active_root_preparation_exists
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
    (hControl : ∀ i, CoordinateRootControl (G := G) R (P i).carrier) :
    Nonempty (BinaryActiveRootPreparation (G := G) A P hPA N) := by
  obtain ⟨R₀,hN₀,hControl₀,hActive₀⟩ := binary_active_roots_proper_after_freezing
    h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt A hA R N hN P hP hControl
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
  refine ⟨{
    arity := F.target.arity
    target := F.target.bundle
    map := g
    special := hg
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
  }⟩
  · intro i
    have h := F.pushCoordinateRoots_control h00 hinj RX (P i) (hPX i) (hControlX i)
    rwa [hMap i] at h
  · intro i
    have h := H.restrictions i
    rwa [hMap i] at h

end DiamondIntegral.Section6
