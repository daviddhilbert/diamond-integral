import «section 6».CentripetalUniformFocusBounds

/-! Uniform named focus covariance after erasing the active VF
coordinate. Matching source leading terms supplies an actual replacement
point in the ambient pullback; no continuity on an enlarged domain is assumed. -/

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

theorem CentripetalData.uniform_named_erased_covariance
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (D : CentripetalData (G := G) A) (hARV : IsRVPullback A.carrier)
    (ρ : Gamma M) (hρ : S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {ρ}}) :
    ∃ β : Gamma M,S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {β}} ∧ 1 ≤ β ∧
      ∀ u ∈ D.activeTags.carrier,∀ a ∈ vfFibre A.carrier u,∀ b ∈ vfFibre A.carrier u,
        Congruent (fun _ => β) (Function.update a D.coordinate 0) (Function.update b D.coordinate 0) →
          ρ.val < vfValue (D.focus (Function.update a D.coordinate 0) u-D.focus (Function.update b D.coordinate 0) u) := by
  obtain ⟨β,hβ,hβ1,hCov⟩ := continuous_mixed_focus_uniform_named_covariance h00 hc linear hκ hs hv hsmall hΓ
    D.focusMap (focusActive_properInvariant A D.sourceProper D.activeTags) D.focusMap_continuous ρ hρ
  refine ⟨β,hβ,hβ1,?_⟩
  intro u hu a ha b hb hab
  let c := Function.update a D.coordinate (b D.coordinate)
  have hTag : tupleRV M a=tupleRV M b := D.tagged (a,u) ha (b,u) hb rfl
  have hc : (c,u) ∈ A.carrier := by
    apply rvPullback_mem_of_sameRV (q := (c,u)) hARV ha ?_ rfl
    funext i
    change rv M (a i)=rv M (c i)
    by_cases hi : i=D.coordinate
    · subst i
      have h := congrFun hTag D.coordinate
      change rv M (a D.coordinate)=rv M (b D.coordinate) at h
      simpa only [c,Function.update_self] using h
    · simp only [c,Function.update_of_ne hi]
  have hClose : Congruent (fun _ => β) c b := by
    intro i
    by_cases hi : i=D.coordinate
    · subst i
      simp only [c,Function.update_self,sub_self]
      exact gamma_lt_value_zero β
    · simpa only [c,Function.update_of_ne hi] using hab i
  have h := (hCov u).2 c ⟨hc,hu⟩ b ⟨hb,hu⟩ hClose 0
  rw [totalFocusFibre_at D.focusMap u c ⟨hc,hu⟩,totalFocusFibre_at D.focusMap u b ⟨hb,hu⟩] at h
  rw [D.focusMap_eq ⟨(c,u),hc,hu⟩,D.focusMap_eq ⟨(b,u),hb,hu⟩] at h
  simpa only [c,Function.update_idem] using h

end DiamondIntegral.Section6
