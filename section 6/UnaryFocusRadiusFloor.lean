import «section 6».FiniteInvariantRadii
import «section 6».UnaryCentripetalExistence

/-! A unary focus admits a permitted component beyond any named
radius floor. The original-base coefficient meets both the prescribed
floor and the source invariance bound. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {r : ℕ} {S : Set M}

namespace UnaryFocusData
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem exists_centripetal_data_above_radius (D : UnaryFocusData A)
    (ρ : Gamma M) (hρ : S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {ρ}})
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V, iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1) :
    ∃ E : CentripetalData (G := G) A, E.coordinate = 0 ∧ E.activeTags = D.activeTags ∧
      (∀ x u, E.focus x u = D.focus u) ∧ HEq E.focusMap D.focusMap ∧
      ∀ a ∈ scalarFocusImage D.focusMap,ρ.val < vfValue (E.coefficient*a) := by
  obtain ⟨α,hα,hα0,hInv⟩ := properInvariant_uniform_named_radius h00 hc linear hκ hs hv hsmall hΓ D.sourceProper
  let δ := max α ρ
  have hδ := gamma_max_named α ρ hα hρ
  have hInv' (u) : AlphaInvariant (fun _ => δ) (vfFibre A.carrier u) :=
    (hInv u).larger_radius (fun _ => le_max_left _ _)
  obtain ⟨c,hc0,hcpos,hcdef,hcdom⟩ := exists_named_aperture_coefficient Valued.v hv hc h00 V S
    hV hVS hSV hnt _ (scalarFocusImage_definable D.focusMap)
    (D.focusImage_finite hc hs hsmall) D.focusImage_nonzero δ hδ
  exact ⟨D.withCoefficient δ hδ hInv' c hc0 hcpos hcdef hcdom,rfl,rfl,fun _ _ => rfl,HEq.rfl,fun a ha =>
    (show ρ.val ≤ δ.val from le_max_right _ _).trans_lt (hcdom a ha)⟩

end UnaryFocusData
end DiamondIntegral.Section6
