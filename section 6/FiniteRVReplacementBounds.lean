import «section 6».FiniteMeasuredRVFactorizations

/-! All intermediate replacement volumes retain the double bounds of
the two original RV objects. No bound on the changing Gamma forms is
required for the measured category. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}

theorem rvPartialReplacement_doublyBounded {U V : RVObject (M := M) S n}
    (F : Map U.domain V.domain) (I : Finset (Fin n))
    (hU : RVObjectDoublyBounded U) (hV : RVObjectDoublyBounded V) :
    RVObjectDoublyBounded (rvPartialReplacement U (V.volume.comp F) I) := by
  refine ⟨hU.1,?_⟩
  obtain ⟨γ,hγ⟩ := hU.2
  obtain ⟨δ,hδ⟩ := hV.2
  let ε := max γ δ
  have hloγ : (ε⁻¹).val ≤ (γ⁻¹).val := show ε⁻¹ ≤ γ⁻¹ from inv_le_inv' (le_max_left _ _)
  have hloδ : (ε⁻¹).val ≤ (δ⁻¹).val := show ε⁻¹ ≤ δ⁻¹ from inv_le_inv' (le_max_right _ _)
  have hhiγ : γ.val ≤ ε.val := le_max_left _ _
  have hhiδ : δ.val ≤ ε.val := le_max_right _ _
  refine ⟨ε,?_⟩
  rintro t ⟨u,rfl⟩ j
  rw [rvPartialReplacement_value]
  split_ifs
  · have h := hδ (V.value (F u)) ⟨F u,rfl⟩ j
    exact ⟨hloδ.trans h.1,h.2.trans hhiδ⟩
  · have h := hγ (U.value u) ⟨u,rfl⟩ j
    exact ⟨hloγ.trans h.1,h.2.trans hhiγ⟩

theorem measuredPartialReplacement_doublyBounded (hc : CanonicalStructure.IsCanonical (M := M))
    {U V : MeasuredRVObject (M := M) S n} (e : MeasuredRVIso U V) (I : Finset (Fin n))
    (hFin : U.object.domain.carrier.Finite) (hU : U.doublyBounded) (hV : V.doublyBounded) :
    (measuredPartialReplacement hc e I hFin).doublyBounded :=
  rvPartialReplacement_doublyBounded e.iso.hom.map I hU hV

theorem MeasuredRVUnaryChain.comp_doublyBounded {U V W : MeasuredRVObject (M := M) S n}
    (T : MeasuredRVUnaryChain S n U V) (H : MeasuredRVUnaryChain S n V W)
    (hT : T.doublyBounded) (hH : H.doublyBounded) : (T.comp H).doublyBounded := by
  induction T with
  | identity U => exact hH
  | step i e h T ih => exact ⟨hT.1,ih H hT.2 hH⟩

theorem exists_finite_bounded_measured_replacement_chain (hc : CanonicalStructure.IsCanonical (M := M))
    {U V : MeasuredRVObject (M := M) S n} (e : MeasuredRVIso U V) (I : Finset (Fin n))
    (hFin : U.object.domain.carrier.Finite) (hU : U.doublyBounded) (hV : V.doublyBounded) :
    ∃ T : MeasuredRVUnaryChain S n (measuredPartialReplacement hc e ∅ hFin) (measuredPartialReplacement hc e I hFin),
      (∀ u, T.iso.iso.hom.map u = u) ∧ T.doublyBounded := by
  induction I using Finset.induction_on with
  | empty => exact ⟨.identity _,fun _ => rfl,measuredPartialReplacement_doublyBounded hc e ∅ hFin hU hV⟩
  | @insert i I hi ih =>
    obtain ⟨T,hT,hTB⟩ := ih
    let H : MeasuredRVUnaryChain S n (measuredPartialReplacement hc e I hFin)
        (measuredPartialReplacement hc e (insert i I) hFin) :=
      .step i (measuredPartialReplacementStep hc e I i hFin)
        (rvPartialReplacementStep_unary U.object _ I i hFin U.nonzero
          (fun u => V.nonzero (e.iso.hom.map u))) (.identity _)
    refine ⟨T.comp H,fun u => ?_,T.comp_doublyBounded H hTB ?_⟩
    · rw [MeasuredRVUnaryChain.comp_map,hT]
      rfl
    · exact ⟨measuredPartialReplacement_doublyBounded hc e I hFin hU hV,
        measuredPartialReplacement_doublyBounded hc e (insert i I) hFin hU hV⟩

end DiamondIntegral.Section6
