import «section 6».FrozenFormRootControl

/-! A repaired actual coordinate-root step protects the complete
Gamma form, every finite proper piece, and the strict root-count
invariant with one permitted original-base aperture coefficient. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r k : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem exists_measured_continuous_coordinate_root_step
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V, iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A : DefSet (rawMixedSpace (M := M) (n+2) r) S)
    (hA : ProperInvariant S A.carrier) (hAD : VFDoublyBounded A.carrier)
    (htag : ∀ p ∈ A.carrier, ∀ q ∈ A.carrier, p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1)
    (R : CoordinateRootFamily A) (N : ℕ) (hN : R.Bound N)
    (U : DefSet (rawRVSpace (M := M) r) S)
    (hNonempty : ∀ p ∈ A.carrier, p.2 ∈ U.carrier → (R.fibre (Fin.init p.1) p.2).Nonempty)
    (hTail : ∀ u a, Continuous (focusTailMap (R.meanMap h00 N hN (projectedActiveDomain A U)) u a))
    (P : Fin k → DefSet (rawMixedSpace (M := M) (n+2) r) S)
    (hPA : ∀ i, (P i).carrier ⊆ A.carrier) (hP : ∀ i, ProperInvariant S (P i).carrier)
    (hControl : ∀ i, CoordinateRootControl (G := G) R (P i).carrier)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hLevels : ∀ u γ, IsOpen {a : Fin (n+2) → VF M | (a,u) ∈ A.carrier ∧ gammaFormExtension ω (a,u) = γ})
    (hForm : CoordinateFormRootControl (G := G) R (gammaFormExtension ω)) :
    ∃ R' : CoordinateRootFamily A, ∃ δ : Gamma M, ∃ D : CentripetalData (G := G) A,
      R'.Bound N ∧ (Prod.snd '' R'.roots.carrier ⊆ Prod.snd '' R.roots.carrier) ∧
      (∀ i, CoordinateRootControl (G := G) R' (P i).carrier) ∧
      CoordinateFormRootControl (G := G) R' (gammaFormExtension ω) ∧
      D.coordinate = Fin.last (n+1) ∧ D.activeTags = U ∧
      (∀ p ∈ A.carrier, p.2 ∈ U.carrier →
        D.extendedFocus p = Barycentre.mean (R'.fibre (Fin.init p.1) p.2)) ∧
      (∀ u, ∀ a ∈ vfFibre A.carrier u, ∀ b ∈ vfFibre A.carrier u,
        Congruent (fun _ => δ) a b → gammaFormExtension ω (a,u) = gammaFormExtension ω (b,u)) ∧
      (∀ p ∈ A.carrier, D.core p = true → δ.val ≤ vfValue (D.coefficient*D.extendedFocus p)) ∧
      (∀ i, ∃ E : CentripetalData (G := G) (P i), ApertureRestrictionData D E) ∧
      SimultaneousCentripetalChain (G := G) (Fin k) A (regularizeMap D.map.image).image (centripetalStepMap D) P := by
  let C := projectedActiveDomain A U
  let f := R.meanMap h00 N hN C
  have hFocusRV := R.meanMap_leadingTerm h00 N hN U htag hNonempty
  obtain ⟨F,hCont,hRV,hProdA,hProdP,hProdLevels⟩ := exists_measured_projected_focus_freezing h00 hc linear hκ hs hv
    V hsmall hΓ hV hVS hSV hnt A hA U f hTail hFocusRV P hP ω hLevels
  let R' := R.frozen F.balls F.centers 0 F.separated F.balls_definable F.centers_definable hProdA
  have hN' : R'.Bound N := R.frozen_bound F.balls F.centers 0 F.separated F.balls_definable
    F.centers_definable hProdA N hN
  have hControl' (i) : CoordinateRootControl (G := G) R' (P i).carrier :=
    R.frozen_control F.balls F.centers 0 F.separated F.balls_definable F.centers_definable
      hProdA (P i).carrier (hProdP i) (hControl i)
  have hForm' : CoordinateFormRootControl (G := G) R' (gammaFormExtension ω) :=
    R.frozen_form_control F.balls F.centers 0 F.separated F.balls_definable F.centers_definable
      hProdA (gammaFormExtension ω) hProdLevels hForm
  obtain ⟨δ,D,hj,hU,hFocus,hConst,hCut,hE⟩ := exists_measured_continuous_focus_protected_components h00 hc linear hκ hs hv
    V hsmall hΓ hV hVS hSV hnt A hA hAD htag U (F.frozenMap f) hCont hRV P hPA hP ω hLevels
  have hMean (p : Mixed M (n+2) r) (hp : p ∈ A.carrier) (hu : p.2 ∈ U.carrier) :
      D.extendedFocus p = Barycentre.mean (R'.fibre (Fin.init p.1) p.2) := by
    rw [D.extendedFocus_active hp (by rw [hU]; exact hu),hFocus,hj,init_update_last]
    let pC : C := ⟨(Fin.init p.1,p.2),⟨⟨p,hp,hu⟩,rfl⟩⟩
    have hAt := congrFun (totalFocusFibre_at (F.frozenMap f) p.2 (Fin.init p.1) pC.property) 0
    have hFrozen := R.frozen_meanMap_value h00 N hN F hProdA pC
    calc
      _ = (F.frozenMap f pC).val 0 := hAt
      _ = (R'.meanMap h00 N hN' C pC).val 0 := hFrozen.symm
      _ = Barycentre.mean (R'.fibre (Fin.init p.1) p.2) := R'.meanMap_value h00 N hN' C pC
  let E (i) := (hE i).choose
  exact ⟨R',δ,D,hN',R.frozen_tags_subset F.balls F.centers 0 F.separated F.balls_definable
    F.centers_definable hProdA,hControl',hForm',hj,hU,hMean,hConst,hCut,hE,
    simultaneous_centripetal_step h00 hc hκ hs hv D P E (fun i => (hE i).choose_spec)⟩

end DiamondIntegral.Section6
