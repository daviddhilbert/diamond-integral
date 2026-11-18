import «section 6».DiamondGroupoid
import «section 6».BoundedVariableUnaryMatching
import «section 6».ProperComposition
import «section 6».InvariantOfCovariance
import «section 6».InvarianceTopology
import «section 6».GammaFormMaps

/-! Lemma 6.38 (`simul:special:dim:1`) from the category `μVF^◇[1]`.

Section 6's `lemma_6_38_bounded_variable_apertures` takes a single proper
covariant homeomorphism, open fixed-label form levels and the generic measure
identity as hypotheses. A morphism of `μVF^◇[1]` supplies all three: the
composite of its factorization is a proper covariant homeomorphism (Lemma 6.9;
intermediate sets are proper invariant), form levels are open because the
forms are proper covariant, and the measure identity holds at VF-generic
points.

`lemma_6_38_diamond_contractible` adds the final clauses of the lemma:
`rv`-contractibility of the transported forms and the `μRV^db[1]` morphism
between the degree-one contractions. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6.DiamondSimultaneous
open DiamondIntegral.Section6 DiamondIntegral.Section6.DiamondCategory DiamondIntegral.Section6.DiamondGroupoid

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

/-- The composite of a factorization starting at a proper invariant set is a
proper covariant homeomorphism onto a proper invariant set. -/
theorem factor_homeo (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S, ∅⟩ : ParameterBase M))
    {r s : ℕ} {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
    {f : Map A B} (hF : UnaryFactorization G A B f) :
    ProperInvariant S A.carrier → ProperCovariantHomeomorphism (G := G) f ∧ ProperInvariant S B.carrier := by
  induction hF with
  | id A =>
    intro hA
    exact ⟨identity_properHomeomorphism h00 hc linear hκ hs hv hsmall hΓ hA, hA⟩
  | step homeo _ =>
    intro _
    exact ⟨homeo, homeo.covariant.target_properInvariant h00 hc linear hκ hs hv hsmall hΓ
      homeo.bijective.surjective⟩
  | comp _ _ ihf ihg =>
    intro hA
    obtain ⟨h1, hB⟩ := ihf hA
    obtain ⟨h2, hC⟩ := ihg hB
    exact ⟨lemma_6_9 h00 hc linear hκ hs hv hsmall hΓ h1 h2, hC⟩

/-- The fixed-label level sets of the form of an object are open. -/
theorem form_levels_open (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (A : VFObject (M := M) S n) (u : Fin A.labels → RVInfinity M) (γ : Gamma M) :
    IsOpen {a : Fin n → VF M | (a, u) ∈ A.carrier.carrier ∧ gammaFormExtension A.form (a, u) = γ} := by
  have he : {a : Fin n → VF M | (a, u) ∈ A.carrier.carrier ∧ gammaFormExtension A.form (a, u) = γ} =
      vfFibre (A.levelSet γ) u := by
    ext a
    constructor
    · rintro ⟨h, hγ⟩
      exact ⟨h, (gammaFormExtension_at A.form ⟨(a, u), h⟩).symm.trans hγ⟩
    · rintro ⟨h, hγ⟩
      exact ⟨h, (gammaFormExtension_at A.form ⟨(a, u), h⟩).trans hγ⟩
  obtain ⟨α, hα⟩ := (A.levelSet_geometry γ).fibers u
  rw [he]
  exact hα.isOpen hv

/-- Lemma 6.38 for a morphism of `μVF^◇[1]` over a VF-generated base: there are
special covariant bijections (in the bounded variable-aperture class) on both
sides whose contractions are matched by a measured RV bijection, as in Section
6's matching export. -/
theorem lemma_6_38_diamond (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (T : LRV.Substructure M) (B₀ : VFGeneratedFieldBase T) (hsmall : Cardinal.mk (T : Set M) < κ)
    (hΓ : NontrivialDefinableGamma (⟨(T : Set M), ∅⟩ : ParameterBase M))
    (hnt : ∃ x : B₀.field, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    {A B : VFObject (M := M) (T : Set M) 1} (F : Morphism G A B) :
    ∃ H : UnaryRelativeMeasuredMatching (G := G) A.carrier B.carrier F.map h00 A.form B.form,
      RelativeApertureChain (G := G) A.carrier H.geometry.source H.geometry.sourceMap ∧
      RelativeApertureChain (G := G) B.carrier H.geometry.target H.geometry.targetMap :=
  lemma_6_38_bounded_variable_apertures h00 hc linear hκ hs hv T B₀ hsmall hΓ hnt A.carrier B.carrier F.map
    (factor_homeo h00 hc linear hκ hs hv hsmall hΓ F.factor A.proper).1 A.proper B.proper A.form B.form
    (form_levels_open hv A) (form_levels_open hv B)
    (fun a ha => by
      obtain ⟨L, ⟨Fc, hFc, hL⟩, hdet⟩ := Morphism.generic hc F a ha
      exact ⟨_, ⟨Fc, hFc, hL.hasJacobianAt⟩, hdet⟩)

/-- Lemma 6.38 for a morphism of `μVF^◇[1]`, with its final clauses: the
transported forms `ω' = ω ∘ T_A⁻¹`, `σ' = σ ∘ T_B⁻¹` are `rv`-contractible, and
the induced map `f♭_↓` is a morphism of `μRV^db[1]` from `(rv(A♭), ω')_1` to
`(rv(B♭), σ')_1` (doubly bounded measured RV objects whose finite-to-one volume
map is the leading-label projection, matched by a measured RV isomorphism
commuting with the label quotients). The finite RV fibres used for the
finite-to-one projection are those of the `μVF^◇[1]` object `A`. -/
theorem lemma_6_38_diamond_contractible (h00 : M ⊨ Axioms.ACVF00)
    (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (T : LRV.Substructure M) (B₀ : VFGeneratedFieldBase T) (hsmall : Cardinal.mk (T : Set M) < κ)
    (hΓ : NontrivialDefinableGamma (⟨(T : Set M), ∅⟩ : ParameterBase M))
    (hnt : ∃ x : B₀.field, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    {A B : VFObject (M := M) (T : Set M) 1} (F : Morphism G A B) :
    ∃ H : UnaryRelativeMeasuredMatching (G := G) A.carrier B.carrier F.map h00 A.form B.form,
      RelativeApertureChain (G := G) A.carrier H.geometry.source H.geometry.sourceMap ∧
      RelativeApertureChain (G := G) B.carrier H.geometry.target H.geometry.targetMap ∧
      (∀ p ∈ H.geometry.source.carrier, ∀ q ∈ H.geometry.source.carrier, p.2 = q.2 →
        gammaFormExtension (H.geometry.sourceForm h00 A.form) p =
          gammaFormExtension (H.geometry.sourceForm h00 A.form) q) ∧
      (∀ p ∈ H.geometry.target.carrier, ∀ q ∈ H.geometry.target.carrier, p.2 = q.2 →
        gammaFormExtension (H.geometry.targetForm h00 B.form) p =
          gammaFormExtension (H.geometry.targetForm h00 B.form) q) ∧
      ∃ (hA' : ∀ a : Fin 1 → VF M, {u : Fin H.geometry.sourceArity → RVInfinity M |
            (a, u) ∈ H.geometry.source.carrier}.Finite)
        (hB' : ∀ b : Fin 1 → VF M, {v : Fin H.geometry.targetArity → RVInfinity M |
            (b, v) ∈ H.geometry.target.carrier}.Finite),
        (H.sourceRV hA').doublyBounded ∧ (H.targetRV hB').doublyBounded ∧
        (∀ u, (H.sourceRV hA').object.value u = fun _ => u.val H.sourceIndex) ∧
        (∀ v, (H.targetRV hB').object.value v = fun _ => v.val H.targetIndex) ∧
        ∃ e : MeasuredRVIso (H.sourceRV hA') (H.targetRV hB'),
          ∀ p : H.geometry.source,
            e.iso.hom.map (pureRVTagQuotient H.geometry.source p) =
              pureRVTagQuotient H.geometry.target (H.geometry.map p) :=
  lemma_6_38_bounded_variable_apertures_contractible h00 hc linear hκ hs hv T B₀ hsmall hΓ hnt
    A.carrier B.carrier F.map (factor_homeo h00 hc linear hκ hs hv hsmall hΓ F.factor A.proper).1
    A.proper B.proper A.finiteRV A.form B.form (form_levels_open hv A) (form_levels_open hv B)
    (fun a ha => by
      obtain ⟨L, ⟨Fc, hFc, hL⟩, hdet⟩ := Morphism.generic hc F a ha
      exact ⟨_, ⟨Fc, hFc, hL.hasJacobianAt⟩, hdet⟩)

end DiamondIntegral.Section6.DiamondSimultaneous
