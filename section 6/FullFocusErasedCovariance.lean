import «section 6».FullFocusGraphData

/-! A complete continuous focus graph on a pullback ambient has
uniform original-base named covariance after erasing its target
coordinate. Independence replaces that coordinate at an actual source point. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) n r) S}

theorem FullFocusGraphData.uniform_named_erased_covariance
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (F : FullFocusGraphData (G := G) A) (hARV : IsRVPullback A.carrier)
    (ρ : Gamma M) (hρ : S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {ρ}}) :
    ∃ β : Gamma M,S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {β}} ∧
      ∀ (u) (hu : u ∈ F.activeTags.carrier) (a) (ha : a ∈ vfFibre A.carrier u)
        (b) (hb : b ∈ vfFibre A.carrier u),
        Congruent (fun _ => β) (Function.update a F.coordinate 0) (Function.update b F.coordinate 0) →
          ρ.val < vfValue ((F.map ⟨(a,u),ha,hu⟩).val 0-(F.map ⟨(b,u),hb,hu⟩).val 0) := by
  obtain ⟨β,hβ,hβ1,hCov⟩ := continuous_mixed_focus_uniform_named_covariance h00 hc linear hκ hs hv hsmall hΓ
    F.map (focusActive_properInvariant A F.proper F.activeTags) F.continuous ρ hρ
  refine ⟨β,hβ,?_⟩
  intro u hu a ha b hb hab
  let c := Function.update a F.coordinate (b F.coordinate)
  have hTag := F.tagged (a,u) ha (b,u) hb rfl
  have hcA : (c,u) ∈ A.carrier := by
    apply rvPullback_mem_of_sameRV (p := (a,u)) (q := (c,u)) hARV ha _ rfl
    funext i
    change rv M (a i)=rv M (c i)
    by_cases hi : i=F.coordinate
    · subst i
      have h := congrFun hTag F.coordinate
      change rv M (a F.coordinate)=rv M (b F.coordinate) at h
      simpa only [c,Function.update_self] using h
    · simp only [c,Function.update_of_ne hi]
  have hClose : Congruent (fun _ => β) c b := by
    intro i
    by_cases hi : i=F.coordinate
    · subst i
      simp only [c,Function.update_self,sub_self]
      exact gamma_lt_value_zero β
    · simpa only [c,Function.update_of_ne hi] using hab i
  have h := (hCov u).2 c ⟨hcA,hu⟩ b ⟨hb,hu⟩ hClose 0
  rw [totalFocusFibre_at F.map u c ⟨hcA,hu⟩,totalFocusFibre_at F.map u b ⟨hb,hu⟩] at h
  have he := F.independent ⟨(c,u),hcA,hu⟩ ⟨(a,u),ha,hu⟩ rfl
    (fun i hi => Function.update_of_ne hi _ _)
  rwa [he] at h

theorem FullFocusGraphData.image_lowerBound (F : FullFocusGraphData (G := G) A) :
    ∃ η : Gamma M,∀ x ∈ scalarFocusImage F.map,η.val ≤ vfValue x := by
  obtain ⟨δ,hδ⟩ := F.doublyBounded
  refine ⟨δ⁻¹,?_⟩
  rintro x ⟨p,rfl⟩
  have hValue := congrArg Values.vrv (F.leadingTerm p)
  change vfValue ((F.map p).val 0)=vfValue (p.val.1 F.coordinate) at hValue
  rw [hValue]
  exact (hδ p.val p.property.1 F.coordinate).1

end DiamondIntegral.Section6
