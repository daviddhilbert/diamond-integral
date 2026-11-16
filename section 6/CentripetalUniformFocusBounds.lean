import «section 6».NamedGammaProducts

/-! The complete actual focus graph is continuous on its current
RV fibres. Its aperture values have an original-base named upper
bound constructed from the source's own invariant radius. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) n r) S}

theorem CentripetalData.focusMap_continuous (D : CentripetalData (G := G) A) (u : Fin r → RVInfinity M) :
    Continuous (FMT.focusFibre D.focusMap u) := by
  have hFocusCont : ContinuousOn (fun x : Fin n → VF M => D.focus (Function.update x D.coordinate 0) u)
      (vfFibre (focusActive A D.activeTags).carrier u) := by
    by_cases hu : u ∈ D.activeTags.carrier
    · exact (D.continuous u hu).mono (fun _ hp => hp.1)
    · have he : vfFibre (focusActive A D.activeTags).carrier u=∅ := by
        ext x
        exact ⟨fun hp => (hu hp.2).elim,fun hp => hp.elim⟩
      rw [he]
      exact continuousOn_empty _
  have h := continuousOn_iff_continuous_domRestrict.mp hFocusCont
  convert h using 1
  funext p
  exact D.focusMap_eq ⟨(p.val,u),p.property⟩

theorem CentripetalData.aperture_values_named_upper_bound
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (D : CentripetalData (G := G) A) :
    ∃ ρ : Gamma M,S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {ρ}} ∧
      ∀ p ∈ A.carrier,p.2 ∈ D.activeTags.carrier → vfValue (D.coefficient*D.extendedFocus p) ≤ ρ.val := by
  obtain ⟨δ,hδ,hδ1,hInv,hBound⟩ := properInvariant_uniform_named_upper_vf_bound
    h00 hc linear hκ hs hv hsmall hΓ D.sourceProper D.sourceDoublyBounded
  let γ := finiteValue D.coefficient D.coefficient_nonzero
  have hγ := finiteValue_named D.coefficient D.coefficient_nonzero D.coefficient_definable
  refine ⟨γ*δ,gamma_mul_named hc γ δ hγ hδ,?_⟩
  intro p hp hu
  have hFocus : vfValue (D.extendedFocus p)=vfValue (p.1 D.coordinate) := by
    rw [D.extendedFocus_active hp hu]
    exact congrArg Values.vrv (D.focusRV p hp hu)
  have hMul : vfValue (D.coefficient*D.extendedFocus p)=vfValue D.coefficient*vfValue (D.extendedFocus p) :=
    Values.vfValueHom.map_mul _ _
  rw [hMul,hFocus]
  exact mul_le_mul' le_rfl (hBound p hp D.coordinate)

end DiamondIntegral.Section6
