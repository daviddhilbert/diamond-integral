import «section 6».ProtectedUnaryContextSteps

/-! A named radius floor for a synchronized unary/ambient step. This
protects a whole membership relation even when its RV output is unbounded. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n m r s k l : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
namespace RVFocusData
theorem exists_paired_protected_components_above_radius
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V, iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) m s) S}
    (ρ : Gamma M) (hρ : S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {ρ}})
    (D : RVFocusData A) (E : RVFocusData B)
    (hImage : scalarFocusImage E.focusMap ⊆ scalarFocusImage D.focusMap)
    (P : Fin k → DefSet (rawMixedSpace (M := M) n r) S)
    (hPA : ∀ i, (P i).carrier ⊆ A.carrier) (hP : ∀ i, ProperInvariant S (P i).carrier)
    (Q : Fin l → DefSet (rawMixedSpace (M := M) m s) S)
    (hQB : ∀ i, (Q i).carrier ⊆ B.carrier) (hQ : ∀ i, ProperInvariant S (Q i).carrier) :
    ∃ F : RVFocusRealization (G := G) D, ∃ H : RVFocusRealization (G := G) E,
      H.component.coefficient = F.component.coefficient ∧
      (∀ a ∈ scalarFocusImage D.focusMap,ρ.val < vfValue (F.component.coefficient*a)) ∧
      (∀ i, ∃ J : CentripetalData (G := G) (P i), ApertureRestrictionData F.component J) ∧
      (∀ i, ∃ J : CentripetalData (G := G) (Q i), ApertureRestrictionData H.component J) := by
  let PA : Fin (k+1) → Set (Mixed M n r) := Fin.cons A.carrier (fun i => (P i).carrier)
  let QB : Fin (l+1) → Set (Mixed M m s) := Fin.cons B.carrier (fun i => (Q i).carrier)
  obtain ⟨α,hα,hα0,hInvA⟩ := finite_properInvariant_uniform_named_radius h00 hc linear hκ hs hv hsmall hΓ
    PA (Fin.cases D.sourceProper hP)
  obtain ⟨β,hβ,hβ0,hInvB⟩ := finite_properInvariant_uniform_named_radius h00 hc linear hκ hs hv hsmall hΓ
    QB (Fin.cases E.sourceProper hQ)
  let δ := max ρ (max α β)
  have hδ := gamma_max_named ρ (max α β) hρ (gamma_max_named α β hα hβ)
  have hIA (i) (u) : AlphaInvariant (fun _ => δ) (vfFibre (PA i) u) :=
    (hInvA i u).larger_radius (fun _ => (le_max_left α β).trans (le_max_right ρ (max α β)))
  have hIB (i) (u) : AlphaInvariant (fun _ => δ) (vfFibre (QB i) u) :=
    (hInvB i u).larger_radius (fun _ => (le_max_right α β).trans (le_max_right ρ (max α β)))
  obtain ⟨c,hc0,hcpos,hcdef,hcdom⟩ := exists_named_aperture_coefficient Valued.v hv hc h00 V S
    hV hVS hSV hnt _ (scalarFocusImage_definable D.focusMap)
    (D.focusImage_finite hc hs hsmall) D.focusImage_nonzero δ hδ
  have hcdomE : ∀ a ∈ scalarFocusImage E.focusMap, δ.val < vfValue (c*a) := fun a ha => hcdom a (hImage ha)
  let F : RVFocusRealization (G := G) D :=
    ⟨D.withCoefficient δ hδ (hIA 0) c hc0 hcpos hcdef hcdom,rfl,rfl,fun _ _ => rfl⟩
  let H : RVFocusRealization (G := G) E :=
    ⟨E.withCoefficient δ hδ (hIB 0) c hc0 hcpos hcdef hcdomE,rfl,rfl,fun _ _ => rfl⟩
  refine ⟨F,H,rfl,(fun a ha => (show ρ.val ≤ δ.val from le_max_left _ _).trans_lt (hcdom a ha)),
    fun i => ?_,fun i => ?_⟩
  · exact ⟨(D.restrict (P i) (hPA i) (hP i)).withCoefficient δ hδ (hIA i.succ) c hc0 hcpos hcdef
      (fun a ha => hcdom a (D.restrict_focusImage_subset (P i) (hPA i) (hP i) ha)),
      D.restriction_data δ hδ (hIA 0) c hc0 hcpos hcdef hcdom (P i) (hPA i) (hP i) (hIA i.succ)⟩
  · exact ⟨(E.restrict (Q i) (hQB i) (hQ i)).withCoefficient δ hδ (hIB i.succ) c hc0 hcpos hcdef
      (fun a ha => hcdomE a (E.restrict_focusImage_subset (Q i) (hQB i) (hQ i) ha)),
      E.restriction_data δ hδ (hIB 0) c hc0 hcpos hcdef hcdomE (Q i) (hQB i) (hQ i) (hIB i.succ)⟩

end RVFocusData
end DiamondIntegral.Section6
