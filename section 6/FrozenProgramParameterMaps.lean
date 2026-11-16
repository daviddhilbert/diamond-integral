import «section 6».PackedRVDataBounds
import «section 6».UnaryIndexedTaggedDomains
import «section 6».MixedVFProjectionMaps

/-! The actual old frozen parameter on the prepared unary base.
Its full graph is definable over S, including the dependence on new RV
labels through the inverse preparation map. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r k l : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S}
variable {C : Fin k → DefSet (rawMixedSpace (M := M) 1 r) S} {hCA : ∀ i,(C i).carrier ⊆ A.carrier}
variable {X : UnaryPreparationContext A (0 : Fin (n+1))}
variable {P : Fin l → DefSet (rawMixedSpace (M := M) (n+1) X.arity) S}
namespace FrozenCoordinateProgramData

def oldParameterMap (h00 : M ⊨ Axioms.ACVF00)
    (F : FrozenCoordinateProgramData (G := G) A C hCA X P) :
    Map F.unary.target (DefSet.univ (rawVFSpace (M := M) 1) S) :=
  (mixedVFHeadMap (DefSet.univ (rawMixedSpace (M := M) 1 r) S)).comp
    ((FMT.mixedFamilyFreezeMap F.unary.freezing.balls F.unary.freezing.centers 0
      F.unary.freezing.separated F.unary.freezing.balls_definable F.unary.freezing.centers_definable A).comp
        (F.unary.map.inverse (F.unary.chain.toChain.toSpecial.bijective h00)))

theorem oldParameterMap_value (h00 : M ⊨ Axioms.ACVF00)
    (F : FrozenCoordinateProgramData (G := G) A C hCA X P) (b : F.unary.target) :
    unaryFamilyParameter (F.oldParameterMap h00) b=
      F.substitution.value (fun _ =>
        ((F.unary.map.inverse (F.unary.chain.toChain.toSpecial.bijective h00) b).val.1 0).val) := by
  funext i
  rfl

theorem oldParameterMap_at (h00 : M ⊨ Axioms.ACVF00)
    (F : FrozenCoordinateProgramData (G := G) A C hCA X P) (a : A) :
    unaryFamilyParameter (F.oldParameterMap h00) (F.unary.map a)=
      F.substitution.value (fun _ => (a.val.1 0).val) := by
  rw [F.oldParameterMap_value h00,Map.inverse_apply]

theorem choices_on_target_labels (h00 : M ⊨ Axioms.ACVF00)
    (F : FrozenCoordinateProgramData (G := G) A C hCA X P)
    (b c : F.unary.target) (hTags : b.val.2=c.val.2) :
    ∀ i,unaryFamilyParameter (F.oldParameterMap h00) b ∈ F.programs.choices i ↔
      unaryFamilyParameter (F.oldParameterMap h00) c ∈ F.programs.choices i := by
  let p := F.unary.map.inverse (F.unary.chain.toChain.toSpecial.bijective h00) b
  let q := F.unary.map.inverse (F.unary.chain.toChain.toSpecial.bijective h00) c
  have hEq : (F.unary.map p).val.2=(F.unary.map q).val.2 := by
    simpa only [p,q,Map.apply_inverse] using hTags
  simpa only [F.oldParameterMap_value h00,p,q] using F.choices_constant h00 p q hEq

theorem selected_rows_on_target_labels (h00 : M ⊨ Axioms.ACVF00)
    (F : FrozenCoordinateProgramData (G := G) A C hCA X P)
    (b c : F.unary.target) (hTags : b.val.2=c.val.2)
    (i : Fin F.programs.count) (hi : unaryFamilyParameter (F.oldParameterMap h00) b ∈ F.programs.choices i) :
    ∀ D ∈ (F.programs.programs i).2.rvTrace (headFibreTemplate X.source) (fun j => headFibreTemplate (P j)),
      (D.2.fibre (unaryFamilyParameter (F.oldParameterMap h00) b)).carrier=
        (D.2.fibre (unaryFamilyParameter (F.oldParameterMap h00) c)).carrier := by
  let p := F.unary.map.inverse (F.unary.chain.toChain.toSpecial.bijective h00) b
  let q := F.unary.map.inverse (F.unary.chain.toChain.toSpecial.bijective h00) c
  have hEq : (F.unary.map p).val.2=(F.unary.map q).val.2 := by
    simpa only [p,q,Map.apply_inverse] using hTags
  have hi' : F.substitution.value (fun _ => (p.val.1 0).val) ∈ F.programs.choices i := by
    simpa only [F.oldParameterMap_value h00,p] using hi
  intro D hD
  have h := F.selected_rows_constant h00 p q hEq i hi' D hD
  exact (congrArg (fun a => (D.2.fibre a).carrier) (F.oldParameterMap_value h00 b)).trans
    (h.trans (congrArg (fun a => (D.2.fibre a).carrier) (F.oldParameterMap_value h00 c)).symm)

theorem uniform_named_target_data_bound
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (F : FrozenCoordinateProgramData (G := G) A C hCA X P) :
    ∃ δ : Gamma M,S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {δ}} ∧
      ∀ b : F.unary.target,∀ i,unaryFamilyParameter (F.oldParameterMap h00) b ∈ F.programs.choices i →
        ∀ D ∈ (F.programs.programs i).2.rvTrace (headFibreTemplate X.source) (fun j => headFibreTemplate (P j)),
        ∀ u ∈ (D.2.fibre (unaryFamilyParameter (F.oldParameterMap h00) b)).carrier,∀ j,
          (δ⁻¹).val ≤ Values.vrv (u j) ∧ Values.vrv (u j) ≤ δ.val := by
  obtain ⟨δ,hδ,hBound⟩ := F.uniform_named_selected_data_bound h00 hc linear hκ hs hv hsmall hΓ
  refine ⟨δ,hδ,?_⟩
  intro b i hi D hD u hu j
  rw [F.oldParameterMap_value h00] at hi hu
  exact hBound _ i hi D hD u hu j

end FrozenCoordinateProgramData
end DiamondIntegral.Section6
