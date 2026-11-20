import «section 6».DiamondSurjectivity
import «section 6».RelativeApertureChains

/-! Remark 6.15 (`spec:is:iso`): a special covariant bijection between objects
of `μVF^◇[n]` whose forms agree outside a definable set of VF-dimension `< n`
is a morphism of `μVF^◇[n]`.

This holds for the revised bounded variable-aperture class of Definition 6.11
(`RelativeApertureChain`, which contains the original special covariant
chains): such chains factor into relatively unary proper covariant
homeomorphisms, and have unit derivative at VF-generic points (Lemma 6.14), so
the measure identity reduces to the agreement of the forms; generic points
avoid the exceptional set. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6.DiamondSpecialIsomorphisms
open DiamondIntegral.Section6 DiamondIntegral.Section6.DiamondCategory
open DiamondIntegral.Section6.DiamondGroupoid DiamondIntegral.Section6.DiamondSurjectivity
open DiamondIntegral.Section6.DiamondTransport

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

/-- Chains in the revised class of Definition 6.11 factor into relatively
unary proper covariant homeomorphisms. -/
theorem relative_factor (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S, ∅⟩ : ParameterBase M))
    {r s : ℕ} {A : DefSet (rawMixedSpace (M := M) n r) S}
    {B : DefSet (rawMixedSpace (M := M) n s) S} {f : Map A B}
    (H : RelativeApertureChain (G := G) A B f) : UnaryFactorization G A B f := by
  induction H with
  | original h => exact special_factor h00 hc linear hκ hs hv hsmall hΓ h
  | relative A D =>
    refine UnaryFactorization.step (D.properHomeomorphism h00 hc linear hκ hs hv hsmall hΓ)
      (Or.inr ⟨D.coordinate, D.coordinate, VFUnaryRelativeAt.relativelyUnary (fun p j hj => ?_)⟩)
    change (D.point p.val).1 j = p.val.1 j
    exact Function.update_of_ne hj _ _
  | comp _ _ ihf ihg => exact UnaryFactorization.comp ihf ihg

/-- **Chains in the revised class through objects** (Definition 6.34,
repaired): for every object structure on the source, the transported structures
make the chain a factorization inside `μVF^◇[n]`. -/
theorem relative_objects (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S, ∅⟩ : ParameterBase M))
    {r s : ℕ} {A : DefSet (rawMixedSpace (M := M) n r) S}
    {B : DefSet (rawMixedSpace (M := M) n s) S} {f : Map A B}
    (H : RelativeApertureChain (G := G) A B f) :
    ∀ X : ObjOn A, ∃ Y : ObjOn B, ObjectFactorization G X.obj Y.obj f ∧
      ∀ p, gammaMapValue Y.form (f p) = gammaMapValue X.form p := by
  have : CharZero (VF M) := vf_charZero_of_model00 h00
  induction H with
  | original h => exact special_objects h00 hc linear hκ hs hv hsmall hΓ h
  | relative A D =>
    intro X
    have homeo := D.properHomeomorphism (G := G) h00 hc linear hκ hs hv hsmall hΓ
    have hu : n = 0 ∨ ∃ i j : Fin n, VFRelativelyUnary D.bijection i j :=
      Or.inr ⟨D.coordinate, D.coordinate, VFUnaryRelativeAt.relativelyUnary (fun p j hj => by
        change (D.point p.val).1 j = p.val.1 j
        exact Function.update_of_ne hj _ _)⟩
    have hunit := fun p hp => (RelativeApertureChain.relative (G := G) A D).unit_derivative_of_independent
      h00 hc hκ.le hs hsmall hv p hp
    exact ⟨transport h00 hc linear hκ hs hv hsmall hΓ X _ homeo hu,
      ObjectFactorization.step (transport_step h00 hc linear hκ hs hv hsmall hΓ X _ homeo hu hunit),
      transport_form h00 hc linear hκ hs hv hsmall hΓ X _ homeo hu⟩
  | comp _ _ ihf ihg =>
    intro X
    obtain ⟨Y, hXY, hY⟩ := ihf X
    obtain ⟨Z, hYZ, hZ⟩ := ihg Y
    exact ⟨Z, ObjectFactorization.comp hXY hYZ, fun p => (hZ _).trans (hY p)⟩

/-- Remark 6.15: a chain in the revised special class between objects of
`μVF^◇[n]`, with the forms agreeing outside a definable set of VF-dimension
`< n` (or everywhere in degree zero), is a morphism of `μVF^◇[n]`. -/
theorem remark_6_15 (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S, ∅⟩ : ParameterBase M))
    {A B : VFObject (M := M) S n} (F : Map A.carrier B.carrier)
    (H : RelativeApertureChain (G := G) A.carrier B.carrier F)
    (E : DefSet (rawMixedSpace (M := M) n A.labels) S)
    (hE : vfDim (rawRVSpace (M := M) 1) E < n ∨ E.carrier = ∅)
    (hform : ∀ p : A.carrier, p.val ∉ E.carrier → gammaMapValue A.form p = gammaMapValue B.form (F p)) :
    Nonempty (Morphism G A B) := by
  have : CharZero (VF M) := vf_charZero_of_model00 h00
  have hgenE : ∀ p : A.carrier, AlgebraicIndependent (vfParameterField S) p.val.1 → p.val ∉ E.carrier := by
    intro p hp
    rcases hE with h | h
    · exact not_mem_small_set_of_independent hc E h p.val hp
    · rw [h]
      exact Set.notMem_empty _
  obtain ⟨Y, hXY, hY⟩ := relative_objects h00 hc linear hκ hs hv hsmall hΓ H (ofObject A)
  have hYB : ∀ q : B.carrier, AlgebraicIndependent (vfParameterField S) q.val.1 →
      gammaMapValue Y.form q = gammaMapValue (ofObject B).form q := by
    intro q hq
    let g := F.inverse (H.bijective h00)
    have hg : Function.Bijective g := inverse_bijective F (H.bijective h00)
    have hp := independent_map_of_finiteFibres hc g (Map.finiteFibres_of_injective hg.1) q hq
    have hq' : F (g q) = q := Map.apply_inverse F (H.bijective h00) q
    rw [← hq', hY]
    exact hform (g q) (hgenE (g q) hp)
  have hchain : ObjectFactorization G A B F := by
    have h := ObjectFactorization.comp hXY
      (ObjectFactorization.step (id_step_generic h00 hc linear hκ hs hv hsmall hΓ Y (ofObject B) hYB))
    have e : (Map.id B.carrier).comp F = F := id_comp_map F
    exact e ▸ h
  refine morphism_of_generic h00 hc hs hsmall F (H.bijective h00) hchain (fun p hp => ?_)
  obtain ⟨L, hL, hdet⟩ := H.unit_derivative_of_independent h00 hc hκ.le hs hsmall hv p hp
  have hpE : p.val ∉ E.carrier := by
    rcases hE with h | h
    · exact not_mem_small_set_of_independent hc E h p.val hp
    · rw [h]
      exact Set.notMem_empty _
  refine ⟨L, hL, ?_⟩
  rw [hdet, hform p hpE, div_self']
  change Values.vfValueHom 1 = Values.gammaValHom 1
  rw [map_one, map_one]

end DiamondIntegral.Section6.DiamondSpecialIsomorphisms
