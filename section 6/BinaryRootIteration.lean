import «section 6».BinaryRootReduction

/-! Terminating actual binary root iteration. Each successor constructs
a common protected reduction and decreases the uniform root bound;
the zero case uses the actual unary projected terminal preparation. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem CoordinateRootFamily.roots_empty_of_bound_zero {n r : ℕ}
    {A : DefSet (rawMixedSpace (M := M) (n+1) r) S} (R : CoordinateRootFamily A)
    (hN : R.Bound 0) : R.roots.carrier = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro p hp
  have hx : p.1 (Fin.last n) ∈ R.fibre (Fin.init p.1) p.2 := by
    rw [R.mem_fibre,Fin.snoc_init_self]
    exact hp
  have hzero := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero (hN (Fin.init p.1) p.2))
  exact Finset.notMem_empty _ (hzero ▸ hx)

theorem binary_preparation_of_root_bound {k : ℕ}
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V, iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (N : ℕ) : ∀ {r : ℕ} (A : DefSet (rawMixedSpace (M := M) 2 r) S),
      ProperInvariant S A.carrier → VFDoublyBounded A.carrier → IsRVPullback A.carrier →
      (∀ p ∈ A.carrier, ∀ q ∈ A.carrier, p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1) →
      ∀ (j : Fin r), (∀ p ∈ A.carrier, rv M (p.1 (Fin.last 1)) = p.2 j) →
      ∀ R : CoordinateRootFamily A, R.Bound N →
      ∀ (P : Fin k → DefSet (rawMixedSpace (M := M) 2 r) S) (hPA : ∀ i, (P i).carrier ⊆ A.carrier),
      (∀ i, ProperInvariant S (P i).carrier) → (∀ i, CoordinateRootControl (G := G) R (P i).carrier) →
      ∃ t : ℕ, ∃ Z : DefSet (rawMixedSpace (M := M) 2 t) S, ∃ g : Map A Z,
        SpecialCovariantChain (G := G) A Z g ∧ ProperInvariant S Z.carrier ∧
        VFDoublyBounded Z.carrier ∧ IsRVPullback Z.carrier ∧
        ∀ i, SpecialCovariantChain (G := G) (P i) (g.restrict (hPA i)).image
          (g.restrict (hPA i)).toImage ∧ IsRVPullback (g.restrict (hPA i)).image.carrier := by
  induction N with
  | zero =>
    intro r A hA hAD hARV htag j hHead R hN P hPA hP hControl
    obtain ⟨t,Z,g,hg,hZ,hZD,hZRV,hFixed,hPieces⟩ := binary_preparation_of_empty_coordinate_roots
      h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt A hA hAD hARV htag j hHead R
      (R.roots_empty_of_bound_zero hN) P hPA hP hControl
    exact ⟨t,Z,g,hg,hZ,hZD,hZRV,hPieces⟩
  | succ N ih =>
    intro r A hA hAD hARV htag j hHead R hN P hPA hP hControl
    obtain ⟨F⟩ := binary_root_reduction_exists h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt
      A hA hAD hARV htag j hHead R N hN P hPA hP hControl
    let C (i) := (F.map.restrict (hPA i)).image
    have hCsub (i) : (C i).carrier ⊆ F.target.carrier := by
      rintro q ⟨p,hp⟩
      exact hp ▸ (F.map ⟨p.val,hPA i p.property⟩).property
    have hC (i) : ProperInvariant S (C i).carrier := by
      have h := (F.restrictions i).properHomeomorphism h00 hc linear hκ hs hv hsmall hΓ
      exact h.covariant.target_properInvariant h00 hc linear hκ hs hv hsmall hΓ h.bijective.surjective
    obtain ⟨t,Z,g,hg,hZ,hZD,hZRV,hPieces⟩ := ih F.target F.proper F.doublyBounded F.pullback F.tagged
      F.headTag F.head_tag F.roots F.bound C hCsub hC F.control
    refine ⟨t,Z,g.comp F.map,.comp F.special hg,hZ,hZD,hZRV,fun i => ?_⟩
    have hComp := SpecialCovariantChain.comp (F.restrictions i) (hPieces i).1
    have hImage : (g.restrict (hCsub i)).image = ((g.comp F.map).restrict (hPA i)).image :=
      image_eq_of_surjective_liesOver (g.comp F.map)
        ((g.restrict (hCsub i)).toImage.comp (F.map.restrict (hPA i)).toImage)
        (hComp.bijective h00).surjective (hPA i) (fun _ => rfl)
    exact ⟨hComp.restriction_of_liesOver h00 (g.comp F.map) (hPA i) (fun _ => rfl),
      hImage ▸ (hPieces i).2⟩

end DiamondIntegral.Section6
