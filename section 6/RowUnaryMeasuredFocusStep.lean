import «section 6».RowForms
import «section 6».RowGammaCodeLocus
import «section 6».RowGammaFormBounds
import «section 6».RowGammaFormUniformFibres
import «section 6».RowSpecialGammaTransport
import «section 6».RowTransportedGammaLevels
import «section 6».RowUnaryCoreFormConstancy
import «section 6».RowUnaryFormRootControl
import «section 6».RowUnaryGammaObstacles
import «section 6».RowUnaryFormControlStep

/-! (Row-form version for Remark 6.20, translated from `UnaryMeasuredFocusStep`.)
 A common actual unary aperture protects a finite proper family and
every level of a Gamma form simultaneously. Individual levels need not
be definable over S. All coefficients are constructed over the original
VF-generated base from the complete finite focus family. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6.UnaryFocusData
variable {qR : ℕ} [NeZero qR]

variable {M G : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable [LinearOrderedCommGroupWithZero G] [Valued (VF M) G] {r k : ℕ} {S : Set M}
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S}

theorem exists_measured_protected_family_step_row (X : UnaryFocusData A)
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V, iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (C : Fin k → DefSet (rawMixedSpace (M := M) 1 r) S)
    (hCA : ∀ i, (C i).carrier ⊆ A.carrier) (hC : ∀ i, ProperInvariant S (C i).carrier)
    (ω : RowFormOn A qR)
    (hLevels : ∀ u γ, IsOpen {a : Fin 1 → VF M | (a,u) ∈ A.carrier ∧ rowFormExtension ω (a,u) = γ}) :
    ∃ δ : Gamma M, ∃ E : CentripetalData (G := G) A,
      E.coordinate = 0 ∧ E.activeTags = X.activeTags ∧ (∀ x u, E.focus x u = X.focus u) ∧
      (∀ u, ∀ a ∈ vfFibre A.carrier u, ∀ b ∈ vfFibre A.carrier u,
        Congruent (fun _ => δ) a b → rowFormExtension ω (a,u) = rowFormExtension ω (b,u)) ∧
      (∀ p ∈ A.carrier, E.core p = true → δ.val ≤ vfValue (E.coefficient*E.extendedFocus p)) ∧
      ∀ i, ∃ F : CentripetalData (G := G) (C i), ∀ p ∈ (C i).carrier, F.point p = E.point p := by
  let H : Fin (k+1) → Set (Mixed M 1 r) := Fin.cons A.carrier (fun i => (C i).carrier)
  have hH : ∀ i, ProperInvariant S (H i) := Fin.cases X.sourceProper hC
  obtain ⟨β,hβ,hβ1,hInv⟩ := finite_properInvariant_uniform_named_radius h00 hc linear hκ hs hv hsmall hΓ H hH
  obtain ⟨α,hα,hα1,hInvA,hInvLevels⟩ := gamma_form_all_levels_uniform_invariant_row h00 hc linear hκ hs hv hsmall hΓ
    X.sourceProper (rowFormExtension ω) (rowFormExtension_graph_definable ω) hLevels
  let δ := max α β
  have hδ := gamma_max_named α β hα hβ
  have hAδ : ∀ u, AlphaInvariant (fun _ => δ) (vfFibre A.carrier u) :=
    fun u => (hInvA u).larger_radius (fun _ => le_max_left _ _)
  have hCδ (i : Fin k) : ∀ u, AlphaInvariant (fun _ => δ) (vfFibre (C i).carrier u) :=
    fun u => (hInv i.succ u).larger_radius (fun _ => le_max_right _ _)
  have hConst (u) (a) (ha : a ∈ vfFibre A.carrier u) (b) (hb : b ∈ vfFibre A.carrier u)
      (hab : Congruent (fun _ => δ) a b) : rowFormExtension ω (a,u) = rowFormExtension ω (b,u) := by
    have h := (hInvLevels (rowFormExtension ω (a,u)) u a b
      (hab.of_larger_radius (fun _ => le_max_left α β))).mp ⟨ha,rfl⟩
    exact h.2.symm
  obtain ⟨c,hc0,hcPos,hcDef,hcDom⟩ := exists_named_aperture_coefficient Valued.v hv hc h00 V S hV hVS hSV hnt
    _ (scalarFocusImage_definable X.focusMap) (X.focusImage_finite hc hs hsmall) X.focusImage_nonzero δ hδ
  let E := X.withCoefficient (G := G) δ hδ hAδ c hc0 hcPos hcDef hcDom
  refine ⟨δ,E,rfl,rfl,fun _ _ => rfl,hConst,?_,?_⟩
  · intro p hp hCore
    have hu : p.2 ∈ X.activeTags.carrier := by
      by_contra hn
      have hh := E.core_inactive hn
      rw [hCore] at hh
      cases hh
    rw [E.extendedFocus_active hp hu]
    change δ.val ≤ vfValue (c*X.focus p.2)
    exact (hcDom _ ⟨⟨p,hp,hu⟩,X.focusMap_eq ⟨p,hp,hu⟩⟩).le
  · intro i
    exact ⟨X.protectedStep δ hδ c hc0 hcPos hcDef hcDom (C i) (hCA i) (hC i) (hCδ i),
      fun p hp => X.protectedStep_point δ hδ hAδ c hc0 hcPos hcDef hcDom (C i) (hCA i) (hC i) (hCδ i) p hp⟩

end DiamondIntegral.Section6.UnaryFocusData
