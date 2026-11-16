import «section 6».BinaryMeasuredBasePreparation
import «section 6».BinaryDisplacementPreparation

/-! Binary measured preparation for arbitrary doubly bounded proper
sources, retaining the proved final-label base displacement. The full
Gamma image is transported exactly through the actual preliminary maps. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem binary_measured_displacement_preparation
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V,iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V,x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A : DefSet (rawMixedSpace (M := M) 2 r) S) (hA : ProperInvariant S A.carrier)
    (hAD : VFDoublyBounded A.carrier)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hLevels : ∀ u γ,IsOpen {a : Fin 2 → VF M | (a,u) ∈ A.carrier ∧ gammaFormExtension ω (a,u)=γ}) :
    ∃ T : MeasuredCoordinatePreparation (G := G) A (fun i : Fin 0 => i.elim0) (fun i => i.elim0) ω,
      RVCoordinateDisplacement T.map 0 := by
  obtain ⟨s,B,f,H,hB,hBD,hBRP,hDisp,_⟩ := binary_displacement_preparation
    h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt A hA hAD
  let η := ω.comp (f.inverse (H.bijective h00))
  have hTransport (p : A) : (η (f p)).val=(ω p).val := by
    change (ω (f.inverse (H.bijective h00) (f p))).val=_
    rw [Map.inverse_apply]
  have hLevelsη := H.exact_gamma_levels_open h00 hc linear hκ hs hv hsmall hΓ ω hLevels η hTransport
  let B₁ := (regularizeMap B).image
  let b := regularization B
  have hb : SpecialCovariantChain (G := G) B B₁ b := .regularize B hB hBD
  let θ := η.comp (b.inverse (hb.bijective h00))
  have hTransport₁ (p : B) : (θ (b p)).val=(η p).val := by
    change (η (b.inverse (hb.bijective h00) (b p))).val=_
    rw [Map.inverse_apply]
  have hLevelsθ := hb.exact_gamma_levels_open h00 hc linear hκ hs hv hsmall hΓ η hLevelsη θ hTransport₁
  have hB₁ := regularization_properInvariant h00 hc hκ hs hv B hB hBD
  have hTag : ∀ p ∈ B₁.carrier,∀ z ∈ B₁.carrier,p.2=z.2 → tupleRV M p.1=tupleRV M z.1 := by
    rw [show B₁.carrier=regularize '' B.carrier from regularization_carrier B]
    exact regularized_tagged _
  let j : Fin (2+s) := Fin.castAdd s (Fin.last 1)
  have hLeading : ∀ p ∈ B₁.carrier,rv M (p.1 (Fin.last 1))=p.2 j := by
    rintro p ⟨q,hq⟩
    rw [← hq]
    change rv M ((regularize q.val).1 (Fin.last 1))=(regularize q.val).2 j
    simp only [j,regularize,Fin.append_left]
    rfl
  let preMap := b.comp f
  have hPrefix : SpecialCovariantChain (G := G) A B₁ preMap := .comp H hb
  let C : Fin 0 → DefSet (rawMixedSpace (M := M) 2 r) S := Fin.elim0
  have hCA : ∀ i,(C i).carrier ⊆ A.carrier := fun i => i.elim0
  let P (i : Fin 0) := (preMap.restrict (hCA i)).image
  have hPA : ∀ i,(P i).carrier ⊆ B₁.carrier := fun i => i.elim0
  obtain ⟨T,hTDisp⟩ := binary_measured_tagged_preparation_with_base_displacement
    h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt B₁ hB₁ (regularized_vfDoublyBounded hBD)
    (regularization_rvPullback B hBRP) hTag j hLeading P hPA (fun i => i.elim0) θ hLevelsθ
  have hAllTransport (p : A) : (θ (preMap p)).val=(ω p).val :=
    (hTransport₁ (f p)).trans (hTransport p)
  have hDispB : RVCoordinateDisplacement b (0 : Fin 2) := .of_fixed 0 (fun _ => rfl)
  obtain ⟨hArityB,hRetainB⟩ := hb.retainsRV
  have hPrefixDisp := hDisp.comp hDispB (rvTailIndex hArityB) hRetainB
  obtain ⟨hArityT,hRetainT⟩ := T.special.retainsRV
  exact ⟨T.precompose h00 C hCA preMap hPrefix (fun i => i.elim0) hPA ω θ hAllTransport,
    hPrefixDisp.comp hTDisp (rvTailIndex hArityT) hRetainT⟩

end DiamondIntegral.Section6
