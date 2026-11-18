import «section 6».RowCarriedFormRootControl
import «section 6».RowCoordinateFormRootControl
import «section 6».RowCoordinateGammaObstacles
import «section 6».RowCoordinateMeasuredObstacles
import «section 6».RowForms
import «section 6».RowGammaCodeLocus
import «section 6».RowGammaFormBounds
import «section 6».RowGammaFormUniformFibres
import «section 6».RowSpecialGammaTransport
import «section 6».RowTransportedGammaLevels
import «section 6».RowCoordinateGammaDescent

/-! (Row-form version for Remark 6.20, translated from `CoordinateGammaLevelProjection`.)
 Descended Gamma levels are exactly the coordinate projections of
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
variable {qR : ℕ} [NeZero qR]

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}
variable {A : DefSet (rawMixedSpace (M := M) (n+1) r) S}

theorem descended_gamma_level_fibre_row
    (ω : RowFormOn A qR)
    (η : RowFormOn (vfDropLast A).image qR)
    (hη : ∀ p : A, η ((vfDropLast A).toImage p) = ω p)
    (u : Fin r → RVInfinity M) (γ : Set (rawRVSpace (M := M) qR).Carrier) :
    {b : Fin n → VF M | (b,u) ∈ (vfDropLast A).image.carrier ∧ rowFormExtension η (b,u) = γ} =
      Fin.init '' {a : Fin (n+1) → VF M | (a,u) ∈ A.carrier ∧ rowFormExtension ω (a,u) = γ} := by
  ext b
  constructor
  · rintro ⟨hb,hγ⟩
    obtain ⟨p,hp⟩ := hb
    have hTags : p.val.2 = u := congrArg (fun z : Mixed M n r => z.2) hp
    have hInit : Fin.init p.val.1 = b := congrArg (fun z : Mixed M n r => z.1) hp
    have hVal : rowFormExtension η (b,u) = rowFormExtension ω p.val := by
      have hAt : rowFormExtension η ((vfDropLast A).toImage p).val = rowFormExtension ω p.val := by
        rw [rowFormExtension_at,rowFormExtension_at]
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
    have hAt : rowFormExtension η ((vfDropLast A).toImage p).val = rowFormExtension ω p.val := by
      rw [rowFormExtension_at,rowFormExtension_at]
      exact hVal
    exact hAt.trans hγ

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem descended_gamma_levels_open_row
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hA : ProperInvariant S A.carrier)
    (ω : RowFormOn A qR)
    (hLevels : ∀ u γ, IsOpen {a : Fin (n+1) → VF M | (a,u) ∈ A.carrier ∧ rowFormExtension ω (a,u) = γ})
    (η : RowFormOn (vfDropLast A).image qR)
    (hη : ∀ p : A, η ((vfDropLast A).toImage p) = ω p) :
    ∀ u γ, IsOpen {b : Fin n → VF M | (b,u) ∈ (vfDropLast A).image.carrier ∧ rowFormExtension η (b,u) = γ} := by
  obtain ⟨δ,_,_,_,hInv⟩ := gamma_form_all_levels_uniform_invariant_row h00 hc linear hκ hs hv hsmall hΓ hA
    (rowFormExtension ω) (rowFormExtension_graph_definable ω) hLevels
  intro u γ
  rw [descended_gamma_level_fibre_row ω η hη]
  exact (hInv γ u).image_init.isOpen hv

end DiamondIntegral.Section6
