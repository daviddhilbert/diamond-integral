import «section 6».MeasuredContinuousCoordinateRootStep

/-! The binary active-root indicator becomes proper after one actual
finite continuity repair. Its balls simultaneously protect every Gamma
level, retaining the form's root control and the original root bound. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {r k : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem binary_measured_active_roots_proper_after_freezing
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V, iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A : DefSet (rawMixedSpace (M := M) 2 r) S) (hA : ProperInvariant S A.carrier)
    (R : CoordinateRootFamily A) (N : ℕ) (hN : R.Bound N)
    (P : Fin k → DefSet (rawMixedSpace (M := M) 2 r) S)
    (hP : ∀ i, ProperInvariant S (P i).carrier)
    (hControl : ∀ i, CoordinateRootControl (G := G) R (P i).carrier)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hLevels : ∀ u γ, IsOpen {a : Fin 2 → VF M | (a,u) ∈ A.carrier ∧ gammaFormExtension ω (a,u) = γ})
    (hForm : CoordinateFormRootControl (G := G) R (gammaFormExtension ω)) :
    ∃ R' : CoordinateRootFamily A, R'.Bound N ∧
      (∀ i, CoordinateRootControl (G := G) R' (P i).carrier) ∧
      CoordinateFormRootControl (G := G) R' (gammaFormExtension ω) ∧
      ProperInvariant S R'.activeBase.carrier := by
  let C := (vfDropLast A).image
  let f := scalarIndicatorMap C R.activeBase
  let H : Fin (k+1) → Set (Mixed M 2 r) := Fin.cons A.carrier (fun i => (P i).carrier)
  obtain ⟨β,hβ,hβ1,hInv⟩ := finite_properInvariant_uniform_named_radius h00 hc linear hκ hs hv hsmall hΓ
    H (Fin.cases hA hP)
  obtain ⟨α,hα,hα1,hInvA,hInvLevels⟩ := gamma_form_all_levels_uniform_invariant h00 hc linear hκ hs hv hsmall hΓ
    hA (gammaFormExtension ω) (gammaFormExtension_graph_definable ω) hLevels
  let δ := max α β
  have hδ := gamma_max_named α β hα hβ
  have hδ0 : 1 ≤ δ := hα1.trans (le_max_left _ _)
  have hCInv (u) : AlphaInvariant (fun _ => δ) (vfFibre C.carrier u) := by
    rw [vfDropLast_image_fibre]
    exact ((hInv 0 u).larger_radius (fun _ => le_max_right α β)).image_init
  obtain ⟨s,hs0,hsdef,hδs⟩ := exists_named_vf_above_radius Valued.v hv hc h00 V S hV hVS hSV hnt δ hδ0 hδ
  let Q : Fin (k+1) ⊕ Gamma M → Set (Mixed M 2 r) :=
    Sum.elim H (fun γ => {p | p ∈ A.carrier ∧ gammaFormExtension ω p = γ})
  have hQ : ∀ i u, AlphaInvariant (fun _ => δ) (vfFibre (Q i) u) := by
    rintro (i | γ) u
    · exact (hInv i u).larger_radius (fun _ => le_max_right _ _)
    · exact (hInvLevels γ u).larger_radius (fun _ => le_max_left _ _)
  obtain ⟨F,hCont,hProd⟩ := FMT.exists_continuous_focus_freezing_with_invariant_domains h00 hc hκ hs hsmall hv
    δ hCInv s hs0 hsdef hδs.le f (unary_focus_tail_continuous f) Q hQ (0 : Fin 1).castSucc
  let R' := R.frozen F.balls F.centers 0 F.separated F.balls_definable F.centers_definable (hProd (.inl 0))
  have hRange (p : C) : (F.frozenMap f p).val 0 = 0 ∨ (F.frozenMap f p).val 0 = 1 := by
    change (if FMT.mixedFamilyFreeze F.balls F.centers 0 p.val ∈ R.activeBase.carrier then 1 else 0) = 0 ∨
      (if FMT.mixedFamilyFreeze F.balls F.centers 0 p.val ∈ R.activeBase.carrier then 1 else 0) = 1
    split_ifs <;> simp
  have hProper := scalarLevelOne_properInvariant h00 hc hκ hs hv (vfDropLast_image_properInvariant hA)
    (F.frozenMap f) hCont hRange
  have hEq : (scalarLevelOne (F.frozenMap f)).carrier = R'.activeBase.carrier := by
    ext p
    rw [mem_scalarLevelOne]
    constructor
    · rintro ⟨hp,he⟩
      rw [totalFocusFibre_at (F.frozenMap f) p.2 p.1 hp] at he
      change (F.frozenMap f ⟨p,hp⟩).val 0 = 1 at he
      have hAt : (F.frozenMap f ⟨p,hp⟩).val 0 =
          if FMT.mixedFamilyFreeze F.balls F.centers 0 p ∈ R.activeBase.carrier then 1 else 0 := rfl
      have hm : FMT.mixedFamilyFreeze F.balls F.centers 0 p ∈ R.activeBase.carrier := by
        by_contra hn
        rw [hAt,if_neg hn] at he
        exact zero_ne_one he
      exact (R.frozen_activeBase F.balls F.centers 0 F.separated F.balls_definable F.centers_definable (hProd (.inl 0)) p).mpr hm
    · intro hp
      have hpC : p ∈ C.carrier := R'.activeBase_subset hp
      refine ⟨hpC,?_⟩
      rw [totalFocusFibre_at (F.frozenMap f) p.2 p.1 hpC]
      have hm := (R.frozen_activeBase F.balls F.centers 0 F.separated F.balls_definable F.centers_definable (hProd (.inl 0)) p).mp hp
      change (if FMT.mixedFamilyFreeze F.balls F.centers 0 p ∈ R.activeBase.carrier then 1 else 0) = 1
      exact if_pos hm
  refine ⟨R',R.frozen_bound F.balls F.centers 0 F.separated F.balls_definable F.centers_definable (hProd (.inl 0)) N hN,
    fun i => R.frozen_control F.balls F.centers 0 F.separated F.balls_definable F.centers_definable
      (hProd (.inl 0)) (P i).carrier (hProd (.inl i.succ)) (hControl i),
    R.frozen_form_control F.balls F.centers 0 F.separated F.balls_definable F.centers_definable
      (hProd (.inl 0)) (gammaFormExtension ω) (fun γ => hProd (.inr γ)) hForm,?_⟩
  rw [← hEq]
  exact hProper

end DiamondIntegral.Section6
