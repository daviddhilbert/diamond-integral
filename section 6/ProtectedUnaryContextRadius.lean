import «section 6».PairedFocusRadiusFloor

/-! The actual unary context lift with a prescribed invariant-radius
floor for every data row. No bound on the set of row values is assumed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r m k l : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
theorem UnaryFocusData.exists_protected_context_step_above_radius
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V, iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    {A : DefSet (rawMixedSpace (M := M) 1 r) S} (D : UnaryFocusData A) {i : Fin m}
    (X : UnaryPreparationContext A i)
    (ρ : Gamma M) (hρ : S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {ρ}})
    (C : Fin k → DefSet (rawMixedSpace (M := M) 1 r) S)
    (hCA : ∀ j,(C j).carrier ⊆ A.carrier) (hC : ∀ j,ProperInvariant S (C j).carrier)
    (P : Fin l → DefSet (rawMixedSpace (M := M) m X.arity) S)
    (hPX : ∀ j,(P j).carrier ⊆ X.source.carrier) (hP : ∀ j,ProperInvariant S (P j).carrier) :
    ∃ E : CentripetalData (G := G) A,E.coordinate=0 ∧ E.activeTags=D.activeTags ∧
      (∀ x u,E.focus x u=D.focus u) ∧
      (∀ p ∈ A.carrier,E.core p=true → ρ.val ≤ vfValue (E.coefficient*E.extendedFocus p)) ∧
      (∀ j,∃ J : CentripetalData (G := G) (C j),ApertureRestrictionData E J) ∧
      Nonempty (UnaryContextLift (G := G) X (centripetalStepMap E) P) := by
  obtain ⟨F,H,hCoeff,hDom,hLower,hFull⟩ := RVFocusData.exists_paired_protected_components_above_radius
    h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt ρ hρ D.toRVFocusData
    (X.focusData D) (X.focusImage_subset D) C hCA hC P hPX hP
  let Y := X.afterStep h00 hc hκ hs hv D F H hCoeff
  let g := centripetalStepMap H.component
  have hg : Function.Bijective g := (regularization_bijective _).comp (H.component.bijective h00)
  have hCut (p) (hp : p ∈ A.carrier) (hCore : F.component.core p=true) :
      ρ.val ≤ vfValue (F.component.coefficient*F.component.extendedFocus p) := by
    have hu : p.2 ∈ F.component.activeTags.carrier := by
      by_contra hn
      have h := F.component.core_inactive hn
      rw [hCore] at h
      cases h
    have hu' : p.2 ∈ D.activeTags.carrier := by rw [F.activeTags] at hu; exact hu
    rw [F.component.extendedFocus_active hp hu,F.focus]
    apply (hDom _ _).le
    exact ⟨⟨p,hp,hu'⟩,D.focusMap_eq ⟨p,hp,hu'⟩⟩
  refine ⟨F.component,F.coordinate,F.activeTags,F.focus,hCut,hLower,⟨{
    target := Y
    map := g
    chain := synchronized_centripetal_step h00 hc hκ hs hv H.component P
      (fun j => (hFull j).choose) (fun j => (hFull j).choose_spec)
    commutes := ?_
    fixed := RVFocusRealization.context_fixed_coordinate X D H
    retainedLabels := fun j => Fin.natAdd m (Fin.natAdd 1 j)
    retained := fun p j => by
      change (regularize (H.component.point p.val)).2 (Fin.natAdd m (Fin.natAdd 1 j))=p.val.2 j
      simp only [regularize,CentripetalData.point,Fin.append_right] }⟩⟩
  intro p
  change centripetalStepMap F.component (X.projection (g.inverse hg (g p)))=_
  rw [Map.inverse_apply]

end DiamondIntegral.Section6
