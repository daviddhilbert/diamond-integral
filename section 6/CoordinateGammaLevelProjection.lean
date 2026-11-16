import «section 6».CoordinateGammaDescent

/-! Descended Gamma levels are exactly the coordinate projections of
the source levels. Their common invariance radius therefore projects,
and all the descended levels are open without being named over S. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}
variable {A : DefSet (rawMixedSpace (M := M) (n+1) r) S}

theorem descended_gamma_level_fibre
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (η : Map (vfDropLast A).image (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hη : ∀ p : A, η ((vfDropLast A).toImage p) = ω p)
    (u : Fin r → RVInfinity M) (γ : Gamma M) :
    {b : Fin n → VF M | (b,u) ∈ (vfDropLast A).image.carrier ∧ gammaFormExtension η (b,u) = γ} =
      Fin.init '' {a : Fin (n+1) → VF M | (a,u) ∈ A.carrier ∧ gammaFormExtension ω (a,u) = γ} := by
  ext b
  constructor
  · rintro ⟨hb,hγ⟩
    obtain ⟨p,hp⟩ := hb
    have hTags : p.val.2 = u := congrArg (fun z : Mixed M n r => z.2) hp
    have hInit : Fin.init p.val.1 = b := congrArg (fun z : Mixed M n r => z.1) hp
    have hVal : gammaFormExtension η (b,u) = gammaFormExtension ω p.val := by
      have hAt : gammaFormExtension η ((vfDropLast A).toImage p).val = gammaFormExtension ω p.val := by
        rw [gammaFormExtension_at,gammaFormExtension_at]
        exact congrArg Subtype.val (hη p)
      have he : ((vfDropLast A).toImage p).val = (b,u) := hp
      rw [he] at hAt
      exact hAt
    refine ⟨p.val.1,⟨hTags ▸ p.property,?_⟩,hInit⟩
    rw [← hTags]
    exact hVal.symm.trans hγ
  · rintro ⟨a,⟨ha,hγ⟩,rfl⟩
    let p : A := ⟨(a,u),ha⟩
    refine ⟨⟨p,rfl⟩,?_⟩
    have hVal := congrArg Subtype.val (hη p)
    have hAt : gammaFormExtension η ((vfDropLast A).toImage p).val = gammaFormExtension ω p.val := by
      rw [gammaFormExtension_at,gammaFormExtension_at]
      exact hVal
    exact hAt.trans hγ

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem descended_gamma_levels_open
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hA : ProperInvariant S A.carrier)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hLevels : ∀ u γ, IsOpen {a : Fin (n+1) → VF M | (a,u) ∈ A.carrier ∧ gammaFormExtension ω (a,u) = γ})
    (η : Map (vfDropLast A).image (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hη : ∀ p : A, η ((vfDropLast A).toImage p) = ω p) :
    ∀ u γ, IsOpen {b : Fin n → VF M | (b,u) ∈ (vfDropLast A).image.carrier ∧ gammaFormExtension η (b,u) = γ} := by
  obtain ⟨δ,_,_,_,hInv⟩ := gamma_form_all_levels_uniform_invariant h00 hc linear hκ hs hv hsmall hΓ hA
    (gammaFormExtension ω) (gammaFormExtension_graph_definable ω) hLevels
  intro u γ
  rw [descended_gamma_level_fibre ω η hη]
  exact (hInv γ u).image_init.isOpen hv

end DiamondIntegral.Section6
