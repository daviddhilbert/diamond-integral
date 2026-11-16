import «section 6».HeadDimensionPreparation
import «section 6».ZeroArityPreparation

/-! Simultaneous proper preparation in every VF dimension. The outer
induction is uniform in the original base and its VF support, so its
fibre instances use exactly the base with the actual head adjoined. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem synchronized_preparation_all_dimensions
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (n : ℕ) :
    ∀ (S V : Set M), Cardinal.mk S < κ →
      NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M) →
      (∀ x ∈ V,iVF x) → V ⊆ S → S ⊆ algebraicClosureSet V →
      (∃ x : vfAlgebraicClosureField V,x ≠ 0 ∧ Valued.v x.val ≠ 1) →
      ∀ k,SynchronizedPreparationInDimension (G := G) S n k := by
  induction n with
  | zero =>
    intro S V hsmall hΓ hV hVS hSV hnt k r H hH hD hRP P hPA hP
    exact ⟨PreparedSynchronizedFamily.identity hH hD hRP P hPA hP
      (fun i => zero_arity_rvPullback (P i).carrier)⟩
  | succ n ih =>
    intro S V hsmall hΓ hV hVS hSV hnt k r H hH hD hRP P hPA hP
    let H' := (regularizeMap H).image
    let f := regularization H
    let P' (i : Fin k) := (f.restrict (hPA i)).image
    have hP'H' (i : Fin k) : (P' i).carrier ⊆ H'.carrier := by
      rintro p ⟨a,ha⟩
      exact ha ▸ (f ⟨a.val,hPA i a.property⟩).property
    have hPre : SynchronizedCentripetalChain (G := G) (Fin k) H H' f P :=
      .regularize H hH hD P hPA hP (fun i => hD.mono (hPA i))
    have hH' : ProperInvariant S H'.carrier := regularization_properInvariant h00 hc hκ hs hv H hH hD
    have hD' : VFDoublyBounded H'.carrier := regularized_vfDoublyBounded hD
    have hRP' : IsRVPullback H'.carrier := regularization_rvPullback H hRP
    have hP' (i : Fin k) : ProperInvariant S (P' i).carrier :=
      ((hPre.atPiece i).literal_restriction h00 (hPA i)).target_properInvariant h00 hc hκ hs hv
    have hTag : ∀ p ∈ H'.carrier,∀ z ∈ H'.carrier,p.2=z.2 → tupleRV M p.1=tupleRV M z.1 := by
      rw [show H'.carrier=regularize '' H.carrier from regularization_carrier H]
      exact regularized_tagged H.carrier
    have hLocal (a : VF M) : Nonempty (PreparedSynchronizedFamily (G := G)
        ((headFibreTemplate H').fibre (fun _ => a.val))
        (fun i => (headFibreTemplate (P' i)).fibre (fun _ => a.val))
        (fun i => headFibreTemplate_subset (hP'H' i) a)) := by
      let z : Fin 1 → M := fun _ => a.val
      obtain ⟨hV',hVS',hSV',hnt',hsmall',hΓ'⟩ := vf_preparation_support_adjoin_tuple
        hV hVS hSV hnt (le_of_lt hκ) hsmall hΓ z (fun _ => a.property)
      exact ih (S ∪ Set.range z) (V ∪ Set.range z) hsmall' hΓ' hV' hVS' hSV' hnt' k
        _ ((headFibreTemplate H').fibre z)
        (headFibreTemplate_properInvariant H' hH' a)
        (headFibreTemplate_doublyBounded H' hD' a)
        (headFibreTemplate_rvPullback H' hRP' a)
        (fun i => (headFibreTemplate (P' i)).fibre z)
        (fun i => headFibreTemplate_subset (hP'H' i) a)
        (fun i => headFibreTemplate_properInvariant (P' i) (hP' i) a)
    obtain ⟨F⟩ := synchronized_preparation_of_tagged_head_inputs h00 hc linear hκ hs hv V hsmall hΓ
      hV hVS hSV hnt (ih S V hsmall hΓ hV hVS hSV hnt k)
      H' hH' hD' hRP' hTag P' hP'H' hP' hLocal
    exact ⟨F.precompose hPA hPre⟩

end DiamondIntegral.Section6
