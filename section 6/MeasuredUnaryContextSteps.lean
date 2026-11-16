import «section 6».PairedFocusRadiusFloor
import «section 6».FormCompatibleFocusSteps

/-! The preliminary unary base step is synchronized with its actual
ambient lift above a common radius for every Gamma level. The ambient
lift retains component form compatibility, including arbitrary proper
protected pieces in all the other VF coordinates. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r m k l : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem RVFocusRealization.core_cutoff_above_floor
    {A : DefSet (rawMixedSpace (M := M) m r) S} {D : RVFocusData A}
    (F : RVFocusRealization (G := G) D) (δ : Gamma M)
    (hFloor : ∀ a ∈ scalarFocusImage D.focusMap,δ.val < vfValue (F.component.coefficient*a)) :
    ∀ p ∈ A.carrier,F.component.core p=true → δ.val ≤ vfValue (F.component.coefficient*F.component.extendedFocus p) := by
  intro p hp hCore
  have hu := F.component.core_true_active p hCore
  have huD : p.2 ∈ D.activeTags.carrier := F.activeTags ▸ hu
  rw [F.component.extendedFocus_active hp hu,F.focus]
  exact (hFloor (D.focus p.2) ⟨⟨p,hp,huD⟩,D.focusMap_eq ⟨p,hp,huD⟩⟩).le

theorem UnaryFocusData.exists_form_compatible_protected_context_step
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V,iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V,x ≠ 0 ∧ Valued.v x.val ≠ 1)
    {A : DefSet (rawMixedSpace (M := M) 1 r) S} (D : UnaryFocusData A) {i : Fin m}
    (X : UnaryPreparationContext A i)
    (C : Fin k → DefSet (rawMixedSpace (M := M) 1 r) S)
    (hCA : ∀ j,(C j).carrier ⊆ A.carrier) (hC : ∀ j,ProperInvariant S (C j).carrier)
    (P : Fin l → DefSet (rawMixedSpace (M := M) m X.arity) S)
    (hPX : ∀ j,(P j).carrier ⊆ X.source.carrier) (hP : ∀ j,ProperInvariant S (P j).carrier)
    (ω : Map X.source (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hLevels : ∀ u γ,IsOpen {x : Fin m → VF M | (x,u) ∈ X.source.carrier ∧ gammaFormExtension ω (x,u)=γ}) :
    ∃ E : CentripetalData (G := G) A,E.coordinate=0 ∧ E.activeTags=D.activeTags ∧
      (∀ x u,E.focus x u=D.focus u) ∧
      (∀ j,∃ J : CentripetalData (G := G) (C j),ApertureRestrictionData E J) ∧
      ∃ U : UnaryContextLift (G := G) X (centripetalStepMap E) P,
        FormCompatibleSynchronizedChain (G := G) (Fin l) X.source U.target.source U.map P ω := by
  obtain ⟨α,hα,hα1,hInvA,hInvLevels⟩ := gamma_form_all_levels_uniform_invariant h00 hc linear hκ hs hv hsmall hΓ
    X.proper (gammaFormExtension ω) (gammaFormExtension_graph_definable ω) hLevels
  have hConst (u) (a) (ha : a ∈ vfFibre X.source.carrier u) (b) (hb : b ∈ vfFibre X.source.carrier u)
      (hab : Congruent (fun _ => α) a b) : gammaFormExtension ω (a,u)=gammaFormExtension ω (b,u) := by
    have h := (hInvLevels (gammaFormExtension ω (a,u)) u a b hab).mp ⟨ha,rfl⟩
    exact h.2.symm
  obtain ⟨F,H,hCoeff,hFloor,hLower,hFull⟩ := RVFocusData.exists_paired_protected_components_above_radius
    h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt α hα D.toRVFocusData
    (X.focusData D) (X.focusImage_subset D) C hCA hC P hPX hP
  have hUpperFloor (a) (ha : a ∈ scalarFocusImage (X.focusData D).focusMap) :
      α.val < vfValue (H.component.coefficient*a) := by
    rw [hCoeff]
    exact hFloor a (X.focusImage_subset D ha)
  have hForm := H.component.core_form_constant_of_uniform_radius α
    (H.core_cutoff_above_floor α hUpperFloor) ω hConst
  let Y := X.afterStep h00 hc hκ hs hv D F H hCoeff
  let g := centripetalStepMap H.component
  have hg : Function.Bijective g := (regularization_bijective _).comp (H.component.bijective h00)
  have hPhi := form_compatible_centripetal_step h00 hc hκ hs hv H.component P
    (fun j => (hFull j).choose) (fun j => (hFull j).choose_spec) ω hForm
  let U : UnaryContextLift (G := G) X (centripetalStepMap F.component) P := {
    target := Y
    map := g
    chain := hPhi.toSynchronized
    commutes := by
      intro p
      change centripetalStepMap F.component (X.projection (g.inverse hg (g p)))=_
      rw [Map.inverse_apply]
    fixed := RVFocusRealization.context_fixed_coordinate X D H
    retainedLabels := fun j => Fin.natAdd m (Fin.natAdd 1 j)
    retained := fun p j => by
      change (regularize (H.component.point p.val)).2 (Fin.natAdd m (Fin.natAdd 1 j))=p.val.2 j
      simp only [regularize,CentripetalData.point,Fin.append_right] }
  exact ⟨F.component,F.coordinate,F.activeTags,F.focus,hLower,U,hPhi⟩

end DiamondIntegral.Section6
