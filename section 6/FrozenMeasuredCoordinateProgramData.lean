import «section 6».MeasuredProgramGeometricData
import «section 6».MeasuredFrozenUnaryRVTemplatePreparation
import «section 6».FrozenCoordinateProgramData
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

theorem CentripetalProgramTemplate.substitute_measuredFormGood
    {p q d a b k : ℕ}
    (T : CentripetalProgramTemplate (M := M) S p d a b)
    (h : DefinableParameterSubstitution (M := M) S p q)
    (A : MixedSetParameterTemplate (M := M) S p d a)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p d a)
    (W : GammaFormParameterTemplate (M := M) S p d a) :
    (T.substitute h).measuredFormGood (A.substitute h) (fun i => (P i).substitute h) (W.substitute h)=
      h.value ⁻¹' T.measuredFormGood A P W := by
  unfold CentripetalProgramTemplate.measuredFormGood
  rw [T.substitute_measuredGood h A P W,T.substitute_coreFormGood h A W]
  rfl

structure FrozenMeasuredCoordinateProgramData
    (A : DefSet (rawMixedSpace (M := M) 1 r) S)
    (C : Fin k → DefSet (rawMixedSpace (M := M) 1 r) S) (hCA : ∀ i,(C i).carrier ⊆ A.carrier)
    (X : UnaryPreparationContext A (0 : Fin (n+2)))
    (P : Fin l → DefSet (rawMixedSpace (M := M) (n+2) X.arity) S)
    (ω : Map X.source (DefSet.univ (rawGammaPresentation (M := M)) S)) where
  programs : FiniteMeasuredCoordinateProgramData X.source P ω
  unary : MeasuredUnaryRVTemplateFreezeCertificate (G := G) A C hCA X P programs.completeData ω

namespace FrozenMeasuredCoordinateProgramData
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S}
variable {C : Fin k → DefSet (rawMixedSpace (M := M) 1 r) S} {hCA : ∀ i,(C i).carrier ⊆ A.carrier}
variable {X : UnaryPreparationContext A (0 : Fin (n+2))}
variable {P : Fin l → DefSet (rawMixedSpace (M := M) (n+2) X.arity) S}
variable {ω : Map X.source (DefSet.univ (rawGammaPresentation (M := M)) S)}

def substitution (F : FrozenMeasuredCoordinateProgramData (G := G) A C hCA X P ω) :
    DefinableParameterSubstitution (M := M) S 1 1 :=
  FMT.freezingParameterSubstitution F.unary.freezing.balls F.unary.freezing.centers F.unary.freezing.separated
    F.unary.freezing.balls_definable F.unary.freezing.centers_definable

theorem sources_preserved (F : FrozenMeasuredCoordinateProgramData (G := G) A C hCA X P ω) :
    ((headFibreTemplate X.source).substitute F.substitution).uncurry=X.source ∧
      ∀ i,((headFibreTemplate (P i)).substitute F.substitution).uncurry=P i :=
  ⟨FMT.uncurry_substituted_head_source _ _ _ _ _ X.source F.unary.ambientProduct,
    fun i => FMT.uncurry_substituted_head_source _ _ _ _ _ (P i) (F.unary.protectedProducts i)⟩

theorem choices_constant (h00 : M ⊨ Axioms.ACVF00)
    (F : FrozenMeasuredCoordinateProgramData (G := G) A C hCA X P ω)
    (p z : A) (he : (F.unary.map p).val.2=(F.unary.map z).val.2) :
    ∀ i,F.substitution.value (fun _ => (p.val.1 0).val) ∈ F.programs.choices i ↔
      F.substitution.value (fun _ => (z.val.1 0).val) ∈ F.programs.choices i := by
  exact choices_eq_of_measured_program_data_eq h00 F.programs.programs (headFibreTemplate X.source)
    (fun i => headFibreTemplate (P i)) (headGammaFormTemplate ω) F.programs.choices F.programs.choices_definable _ _ (F.unary.data p z he)

theorem selected_rows_constant (h00 : M ⊨ Axioms.ACVF00)
    (F : FrozenMeasuredCoordinateProgramData (G := G) A C hCA X P ω)
    (p z : A) (he : (F.unary.map p).val.2=(F.unary.map z).val.2)
    (i : Fin F.programs.count) (hi : F.substitution.value (fun _ => (p.val.1 0).val) ∈ F.programs.choices i) :
    ∀ D ∈ (F.programs.programs i).2.measuredRVTrace (headFibreTemplate X.source) (fun j => headFibreTemplate (P j)) (headGammaFormTemplate ω),
      (D.2.fibre (F.substitution.value (fun _ => (p.val.1 0).val))).carrier=
        (D.2.fibre (F.substitution.value (fun _ => (z.val.1 0).val))).carrier := by
  exact selected_trace_rows_eq_of_measured_program_data_eq h00 F.programs.programs (headFibreTemplate X.source)
    (fun j => headFibreTemplate (P j)) (headGammaFormTemplate ω) F.programs.choices F.programs.choices_definable _ _ (F.unary.data p z he) i hi

theorem substituted_measured_good
    (F : FrozenMeasuredCoordinateProgramData (G := G) A C hCA X P ω) (a : Fin 1 → M)
    (i : Fin F.programs.count) (hi : F.substitution.value a ∈ F.programs.choices i) :
    a ∈ ((F.programs.programs i).2.substitute F.substitution).measuredFormGood
      ((headFibreTemplate X.source).substitute F.substitution)
      (fun j => (headFibreTemplate (P j)).substitute F.substitution) ((headGammaFormTemplate ω).substitute F.substitution) := by
  rw [(F.programs.programs i).2.substitute_measuredFormGood]
  exact (F.programs.choices_subset i hi).2

end FrozenMeasuredCoordinateProgramData

theorem exists_frozen_measured_coordinate_program_data
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
    (X : UnaryPreparationContext A (0 : Fin (n+2)))
    (P : Fin l → DefSet (rawMixedSpace (M := M) (n+2) X.arity) S)
    (hPX : ∀ i,(P i).carrier ⊆ X.source.carrier) (hP : ∀ i,ProperInvariant S (P i).carrier)
    (ω : Map X.source (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hLevels : ∀ u γ,IsOpen {x : Fin (n+2) → VF M | (x,u) ∈ X.source.carrier ∧ gammaFormExtension ω (x,u)=γ})
    (hLocal : ∀ a : VF M,∃ F : MeasuredCoordinatePreparation (G := G)
      ((headFibreTemplate X.source).fibre (fun _ => a.val))
      (fun i => (headFibreTemplate (P i)).fibre (fun _ => a.val))
      (fun i => headFibreTemplate_subset (hPX i) a) (headGammaFormMap ω a),
        FormCompatibleSynchronizedChain (G := G) (Fin l)
          ((headFibreTemplate X.source).fibre (fun _ => a.val)) F.target F.map
          (fun i => (headFibreTemplate (P i)).fibre (fun _ => a.val)) (headGammaFormMap ω a)) :
    Nonempty (FrozenMeasuredCoordinateProgramData (G := G) A C hCA X P ω) := by
  obtain ⟨F⟩ := exists_finite_measured_coordinate_program_data h00 hc linear hκ hs hv hsmall hΓ
    X.source X.proper X.doublyBounded X.pullback P hPX hP ω hLocal
  obtain ⟨R⟩ := measured_frozen_unary_rv_template_preparation h00 hc linear hκ hs hv W hsmall hΓ hW hWS hSW hnt
    A hA hAD hARV hTag C hCA hC X P hPX hP F.completeData ω hLevels
  exact ⟨⟨F,R⟩⟩

end DiamondIntegral.Section6
