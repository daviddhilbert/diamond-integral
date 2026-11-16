import «section 6».CoordinateProgramData
import «section 6».FrozenUnaryRVTemplatePreparation
import «section 6».FrozenParameterPrograms

/-! Construct the complete finite-program data, freeze and prepare its
whole membership relation, and lift that unary preparation to the actual
ambient. Formula choices and every selected program row are retained,
with the original ambient and protected source sets unchanged by freezing. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r n k l : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

structure FrozenCoordinateProgramData
    (A : DefSet (rawMixedSpace (M := M) 1 r) S)
    (C : Fin k → DefSet (rawMixedSpace (M := M) 1 r) S) (hCA : ∀ i,(C i).carrier ⊆ A.carrier)
    (X : UnaryPreparationContext A (0 : Fin (n+1)))
    (P : Fin l → DefSet (rawMixedSpace (M := M) (n+1) X.arity) S) where
  programs : FiniteCoordinateProgramData X.source P
  unary : UnaryRVTemplateFreezeCertificate (G := G) A C hCA X P programs.completeData

namespace FrozenCoordinateProgramData
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S}
variable {C : Fin k → DefSet (rawMixedSpace (M := M) 1 r) S} {hCA : ∀ i,(C i).carrier ⊆ A.carrier}
variable {X : UnaryPreparationContext A (0 : Fin (n+1))}
variable {P : Fin l → DefSet (rawMixedSpace (M := M) (n+1) X.arity) S}

def substitution (F : FrozenCoordinateProgramData (G := G) A C hCA X P) :
    DefinableParameterSubstitution (M := M) S 1 1 :=
  FMT.freezingParameterSubstitution F.unary.freezing.balls F.unary.freezing.centers F.unary.freezing.separated
    F.unary.freezing.balls_definable F.unary.freezing.centers_definable

theorem sources_preserved (F : FrozenCoordinateProgramData (G := G) A C hCA X P) :
    ((headFibreTemplate X.source).substitute F.substitution).uncurry=X.source ∧
      ∀ i,((headFibreTemplate (P i)).substitute F.substitution).uncurry=P i :=
  ⟨FMT.uncurry_substituted_head_source _ _ _ _ _ X.source F.unary.ambientProduct,
    fun i => FMT.uncurry_substituted_head_source _ _ _ _ _ (P i) (F.unary.protectedProducts i)⟩

theorem choices_constant (h00 : M ⊨ Axioms.ACVF00)
    (F : FrozenCoordinateProgramData (G := G) A C hCA X P)
    (p z : A) (he : (F.unary.map p).val.2=(F.unary.map z).val.2) :
    ∀ i,F.substitution.value (fun _ => (p.val.1 0).val) ∈ F.programs.choices i ↔
      F.substitution.value (fun _ => (z.val.1 0).val) ∈ F.programs.choices i := by
  exact choices_eq_of_program_data_eq h00 F.programs.programs (headFibreTemplate X.source)
    (fun i => headFibreTemplate (P i)) F.programs.choices F.programs.choices_definable _ _ (F.unary.data p z he)

theorem selected_rows_constant (h00 : M ⊨ Axioms.ACVF00)
    (F : FrozenCoordinateProgramData (G := G) A C hCA X P)
    (p z : A) (he : (F.unary.map p).val.2=(F.unary.map z).val.2)
    (i : Fin F.programs.count) (hi : F.substitution.value (fun _ => (p.val.1 0).val) ∈ F.programs.choices i) :
    ∀ D ∈ (F.programs.programs i).2.rvTrace (headFibreTemplate X.source) (fun j => headFibreTemplate (P j)),
      (D.2.fibre (F.substitution.value (fun _ => (p.val.1 0).val))).carrier=
        (D.2.fibre (F.substitution.value (fun _ => (z.val.1 0).val))).carrier := by
  exact selected_trace_rows_eq_of_program_data_eq h00 F.programs.programs (headFibreTemplate X.source)
    (fun j => headFibreTemplate (P j)) F.programs.choices F.programs.choices_definable _ _ (F.unary.data p z he) i hi

theorem substituted_prepared_good
    (F : FrozenCoordinateProgramData (G := G) A C hCA X P) (a : Fin 1 → M)
    (i : Fin F.programs.count) (hi : F.substitution.value a ∈ F.programs.choices i) :
    a ∈ ((F.programs.programs i).2.substitute F.substitution).preparedGood
      ((headFibreTemplate X.source).substitute F.substitution)
      (fun j => (headFibreTemplate (P j)).substitute F.substitution) := by
  rw [(F.programs.programs i).2.substitute_preparedGood]
  exact (F.programs.choices_subset i hi).2

end FrozenCoordinateProgramData

theorem exists_frozen_coordinate_program_data
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (W : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hW : ∀ a ∈ W,iVF a) (hWS : W ⊆ S) (hSW : S ⊆ algebraicClosureSet W)
    (hnt : ∃ x : vfAlgebraicClosureField W,x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A : DefSet (rawMixedSpace (M := M) 1 r) S)
    (hA : ProperInvariant S A.carrier) (hAD : VFDoublyBounded A.carrier) (hARV : IsRVPullback A.carrier)
    (hTag : ∀ p ∈ A.carrier,∀ z ∈ A.carrier,p.2=z.2 → tupleRV M p.1=tupleRV M z.1)
    (C : Fin k → DefSet (rawMixedSpace (M := M) 1 r) S)
    (hCA : ∀ i,(C i).carrier ⊆ A.carrier) (hC : ∀ i,ProperInvariant S (C i).carrier)
    (X : UnaryPreparationContext A (0 : Fin (n+1)))
    (P : Fin l → DefSet (rawMixedSpace (M := M) (n+1) X.arity) S)
    (hPX : ∀ i,(P i).carrier ⊆ X.source.carrier) (hP : ∀ i,ProperInvariant S (P i).carrier)
    (hLocal : ∀ a : VF M,Nonempty (PreparedSynchronizedFamily (G := G)
      ((headFibreTemplate X.source).fibre (fun _ => a.val))
      (fun i => (headFibreTemplate (P i)).fibre (fun _ => a.val))
      (fun i => headFibreTemplate_subset (hPX i) a))) :
    Nonempty (FrozenCoordinateProgramData (G := G) A C hCA X P) := by
  obtain ⟨F⟩ := exists_finite_coordinate_program_data h00 hc linear hκ hs hv hsmall hΓ
    X.source X.proper X.doublyBounded X.pullback P hPX hP hLocal
  obtain ⟨R⟩ := frozen_unary_rv_template_preparation h00 hc linear hκ hs hv W hsmall hΓ hW hWS hSW hnt
    A hA hAD hARV hTag C hCA hC X P hPX hP F.completeData
  exact ⟨⟨F,R⟩⟩

end DiamondIntegral.Section6
