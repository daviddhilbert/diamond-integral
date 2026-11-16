import «section 6».BinaryRootActivePreparation

/-! Construct a strict binary root-count reduction, including active
locus preparation, continuity repair, actual mean compatibility and
all literal protected special restrictions. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {r k : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

structure BinaryRootReduction (A : DefSet (rawMixedSpace (M := M) 2 r) S)
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
  roots : CoordinateRootFamily target
  bound : roots.Bound N
  control : ∀ i, CoordinateRootControl (G := G) roots (map.restrict (hPA i)).image.carrier
  restrictions : ∀ i, SpecialCovariantChain (G := G) (P i)
    (map.restrict (hPA i)).image (map.restrict (hPA i)).toImage

theorem binary_root_reduction_exists
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
    (R : CoordinateRootFamily A) (N : ℕ) (hN : R.Bound (N+1))
    (P : Fin k → DefSet (rawMixedSpace (M := M) 2 r) S)
    (hPA : ∀ i, (P i).carrier ⊆ A.carrier) (hP : ∀ i, ProperInvariant S (P i).carrier)
    (hControl : ∀ i, CoordinateRootControl (G := G) R (P i).carrier) :
    Nonempty (BinaryRootReduction (G := G) A P hPA N) := by
  obtain ⟨F⟩ := binary_active_root_preparation_exists h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt
    A hA hAD hARV htag j hHead R (N+1) hN P hPA hP hControl
  let C (i) := (F.map.restrict (hPA i)).image
  have hCsub (i) : (C i).carrier ⊆ F.target.carrier := by
    rintro q ⟨p,hp⟩
    exact hp ▸ (F.map ⟨p.val,hPA i p.property⟩).property
  have hC (i) : ProperInvariant S (C i).carrier := by
    have h := (F.restrictions i).properHomeomorphism h00 hc linear hκ hs hv hsmall hΓ
    exact h.covariant.target_properInvariant h00 hc linear hκ hs hv hsmall hΓ h.bijective.surjective
  obtain ⟨Q,D,hQN,hTags,hControlQ,hCoord,hActive,hMean,hProtected,hStep⟩ :=
    exists_continuous_coordinate_root_step h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt
      F.target F.proper F.doublyBounded F.tagged F.roots (N+1) F.bound F.active
      (fun p hp hu => (F.active_iff p hp).mp hu)
      (unary_focus_tail_continuous _) C hCsub hC F.control
  have hOldActive (p) (hp : p ∈ F.roots.roots.carrier) : p.2 ∈ F.active.carrier := by
    apply (F.active_iff p (F.roots.subset hp)).mpr
    apply (F.roots.mem_activeBase (Fin.init p.1) p.2).mp
    exact ⟨⟨p,hp⟩,rfl⟩
  have hAllActive (p) (hp : p ∈ Q.roots.carrier) : p.2 ∈ D.activeTags.carrier := by
    rw [hActive]
    obtain ⟨q,hq,he⟩ := hTags ⟨p,hp,rfl⟩
    exact he ▸ hOldActive q hq
  have hAllMean (p) (hp : p ∈ Q.roots.carrier) :
      D.extendedFocus p = Barycentre.mean (Q.fibre (Fin.init p.1) p.2) :=
    hMean p (Q.subset hp) (hActive ▸ hAllActive p hp)
  let E (i) := (hProtected i).choose
  have hE (i) := (hProtected i).choose_spec
  let R' := Q.stepFamily D h00 hCoord hAllActive hAllMean
  let f := centripetalStepMap D
  let g := f.comp F.map
  have hNarrow (i) := (hStep.atPiece i).literal_restriction h00 (hCsub i)
  have hComposite (i) := SpecialCovariantChain.comp (F.restrictions i) (hNarrow i)
  have hImage (i) : (f.restrict (hCsub i)).image = (g.restrict (hPA i)).image :=
    image_eq_of_surjective_liesOver g ((f.restrict (hCsub i)).toImage.comp (F.map.restrict (hPA i)).toImage)
      ((hComposite i).bijective h00).surjective (hPA i) (fun _ => rfl)
  refine ⟨{
    arity := 2+(1+F.arity)
    target := (regularizeMap D.map.image).image
    map := g
    special := .comp F.special hStep.toChain.toSpecial
    proper := regularization_properInvariant h00 hc hκ hs hv _
      (D.image_properInvariant h00 hc hκ hs hv) D.image_vfDoublyBounded
    doublyBounded := regularized_vfDoublyBounded D.image_vfDoublyBounded
    pullback := D.regularized_image_rvPullback h00 F.pullback
    tagged := ?_
    headTag := Fin.castAdd (1+F.arity) (Fin.last 1)
    head_tag := fun p hp => centripetal_step_leading_term D p hp (Fin.last 1)
    roots := R'
    bound := Q.stepFamily_bound D h00 hCoord hAllActive hAllMean N hQN
    control := ?_
    restrictions := fun i => (hComposite i).restriction_of_liesOver h00 g (hPA i) (fun _ => rfl)
  }⟩
  · rw [show (regularizeMap D.map.image).image.carrier = regularize '' D.map.image.carrier from regularization_carrier _]
    exact regularized_tagged _
  · intro i
    have h := Q.root_control_step D (E i) (hE i) h00 hCoord hAllActive hAllMean (hControlQ i)
    change CoordinateRootControl (G := G) R' (f.restrict (hCsub i)).image.carrier at h
    rwa [hImage i] at h

end DiamondIntegral.Section6
