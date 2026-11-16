import «section 6».PaddedMeasuredRVObjects
import «section 6».FiniteRVCoordinateReplacement

/-! Replace one coordinate outside a finite coordinate head by the unit
RV value. Finite volume follows from the unchanged actual finite head;
the measured form retains total weight and double bounds. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n k : ℕ}

def rvTupleOnesMap {P : Space LRV M} (A : DefSet P S) (n : ℕ) :
    Map A (DefSet.univ (rawRVSpace (M := M) n) S) := by
  let Q := rawRVSpace (M := M) n
  let C (_ : P.Index → M) : Fin n → M := fun _ => iRVOne
  have hC : S.DefinableMap LRV C := fun _ =>
    SpecialTransformations.DefinableConstants.constant (SpecialTransformations.DefinableConstants.function_symbol
      (L := LRV) Fn.rvOne Fin.elim0 (fun i => i.elim0))
  have hDom (c : P.domain) : C c.val ∈ Q.domain :=
    ⟨fun _ => 1,funext (fun _ => RVOperations.one_val)⟩
  exact Map.ofCodes A (fun _ => fun _ => 1) C hC hDom (fun c =>
    rvValues_injective ((rvValues_decode _).trans (funext (fun _ => RVOperations.one_val.symm))))

def rvCoordinateUnitVolume (U : RVObject (M := M) S n) (i : Fin n) :=
  (rvPartialReplacement U (rvTupleOnesMap U.domain n) {i}).volume

theorem rvCoordinateUnitVolume_value (U : RVObject (M := M) S n) (i : Fin n) (u : U.domain) :
    (rvCoordinateUnitVolume U i u).val=Function.update (U.value u) i 1 := by
  funext j
  change (rvPartialReplacement U (rvTupleOnesMap U.domain n) {i}).value u j=_
  rw [rvPartialReplacement_value]
  by_cases hj : j=i
  · subst j
    simp only [Finset.mem_singleton,if_pos rfl,Function.update_self]
    rfl
  · simp only [Finset.mem_singleton,if_neg hj,Function.update_of_ne hj]

theorem rvCoordinateUnitVolume_finite (U : RVObject (M := M) S n) (v : Fin k → Fin n)
    (hv : (rvHeadVolume U v).FiniteFibres) (i : Fin n) (hi : ∀ j,v j ≠ i) :
    (rvCoordinateUnitVolume U i).FiniteFibres := by
  apply finiteFibres_of_value_reflection (rvHeadVolume U v) _ hv
  intro u w he
  apply Subtype.ext
  funext j
  change U.value u (v j)=U.value w (v j)
  have h := congrArg (fun z : DefSet.univ (rawRVSpace (M := M) n) S => z.val (v j)) he
  simpa only [rvCoordinateUnitVolume_value,Function.update_of_ne (hi j)] using h

theorem rvCoordinateUnitVolume_nonzero (U : MeasuredRVObject (M := M) S n) (i : Fin n)
    (u : U.object.domain) (j : Fin n) : ((rvCoordinateUnitVolume U.object i u).val j).val ≠ iRVZero := by
  rw [rvCoordinateUnitVolume_value]
  by_cases hj : j=i
  · subst j
    rw [Function.update_self]
    exact (rv_nonzero_code_iff _).mpr one_ne_zero
  · rw [Function.update_of_ne hj]
    exact U.nonzero u j

def measuredRVCoordinateUnit (hc : CanonicalStructure.IsCanonical (M := M))
    (U : MeasuredRVObject (M := M) S n) (v : Fin k → Fin n)
    (hv : (rvHeadVolume U.object v).FiniteFibres) (i : Fin n) (hi : ∀ j,v j ≠ i) :=
  U.withVolume hc (rvCoordinateUnitVolume U.object i)
    (rvCoordinateUnitVolume_finite U.object v hv i hi) (rvCoordinateUnitVolume_nonzero U i)

def measuredRVCoordinateUnitIso (hc : CanonicalStructure.IsCanonical (M := M))
    (U : MeasuredRVObject (M := M) S n) (v : Fin k → Fin n)
    (hv : (rvHeadVolume U.object v).FiniteFibres) (i : Fin n) (hi : ∀ j,v j ≠ i) :
    MeasuredRVIso U (measuredRVCoordinateUnit hc U v hv i hi) :=
  measuredVolumeChangeIso hc U _ (rvCoordinateUnitVolume_finite U.object v hv i hi)
    (rvCoordinateUnitVolume_nonzero U i)

theorem measuredRVCoordinateUnit_value (hc : CanonicalStructure.IsCanonical (M := M))
    (U : MeasuredRVObject (M := M) S n) (v : Fin k → Fin n)
    (hv : (rvHeadVolume U.object v).FiniteFibres) (i : Fin n) (hi : ∀ j,v j ≠ i) (u : U.object.domain) :
    (measuredRVCoordinateUnit hc U v hv i hi).object.value u=Function.update (U.object.value u) i 1 :=
  rvCoordinateUnitVolume_value U.object i u

theorem measuredRVCoordinateUnit_doublyBounded (hc : CanonicalStructure.IsCanonical (M := M))
    (U : MeasuredRVObject (M := M) S n) (v : Fin k → Fin n)
    (hv : (rvHeadVolume U.object v).FiniteFibres) (i : Fin n) (hi : ∀ j,v j ≠ i)
    (hU : U.doublyBounded) : (measuredRVCoordinateUnit hc U v hv i hi).doublyBounded := by
  refine ⟨hU.1,?_⟩
  obtain ⟨γ,hγ⟩ := hU.2
  let δ := max γ (1 : Gamma M)
  have hγδ : γ ≤ δ := le_max_left _ _
  have hOneδ : (1 : Gamma M) ≤ δ := le_max_right _ _
  refine ⟨δ,?_⟩
  rintro t ⟨u,rfl⟩ j
  rw [measuredRVCoordinateUnit_value]
  by_cases hj : j=i
  · subst j
    rw [Function.update_self,RVOperations.vrv_one]
    exact ⟨show δ⁻¹ ≤ (1 : Gamma M) from by simpa only [inv_one] using inv_le_inv' hOneδ,hOneδ⟩
  · rw [Function.update_of_ne hj]
    exact ⟨(show (δ⁻¹).val ≤ (γ⁻¹).val from inv_le_inv' hγδ).trans (hγ _ ⟨u,rfl⟩ j).1,
      (hγ _ ⟨u,rfl⟩ j).2.trans hγδ⟩

end DiamondIntegral.Section6
