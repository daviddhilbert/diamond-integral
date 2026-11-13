import «section 3».FullGammaDclFunctions
import «section 3».RVValueGammaClosure
import «section 3».MixedGammaTupleLogic
import «section 3».RVAngularQuotient
import «section 3».RVUnitSpace
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem gammaScalar_definable_iff_native (B : Base (M := M)) (T : Set (Values.Gamma (M := M))) :
    GammaDefinableOverBase B T ↔ FullGammaSyntax.Scalar (integrationGammaBase B) T := by
  exact integrationGammaDefinable_iff (fun z hz i => by
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    subst i
    exact hz.1)

def rvUnitGammaGraph {n : ℕ} (A : Set (Fin n → (CanonicalRV.RVSort M)ˣ)) (w : A → Values.Gamma (M := M))
    (a : Fin n → M) (γ : Fin 1 → Values.Gamma (M := M)) : Prop :=
  ∃ x : A, rvUnitValues x.val = a ∧ w x = γ 0

theorem rvUnitGammaGraph_point_definable (B : Base (M := M)) {n : ℕ}
    (A : Set (Fin n → (CanonicalRV.RVSort M)ˣ)) (w : A → Values.Gamma (M := M))
    (hw : mixedGammaTupleDefinable B (rvUnitGammaGraph A w)) (a : A) :
    GammaDefinableClosureAtBase ⟨B.real ∪ Set.range (rvUnitValues a.val),B.gamma⟩ (w a) := by
  let C : Base (M := M) := ⟨B.real ∪ Set.range (rvUnitValues a.val),B.gamma⟩
  have hh := hw.column (rvUnitValues a.val)
  have he : ∀ γ, rvUnitGammaGraph A w (rvUnitValues a.val) γ ↔ γ 0 = w a := by
    intro γ
    constructor
    · rintro ⟨b,hb,hv⟩
      have hab : b = a := Subtype.ext (rvUnitValues_injective hb)
      subst b
      exact hv.symm
    · intro hγ
      exact ⟨a,rfl,hγ.symm⟩
  have hval := (hh.congr he).congr (fun γ => Set.mem_singleton_iff.symm)
  exact (gammaScalar_definable_iff_native C {w a}).mpr ((FullGammaSyntax.scalar_definable_iff {w a}).mp hval)

/-- A definable Gamma-valued RV function takes each point value on an
original-ground Gamma function of that point's coordinate values. -/
theorem rvUnitGammaGraph_point_value_function {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (B : Base (M := M)) (hsmall : Cardinal.mk B.real < κ) {n : ℕ}
    (A : Set (Fin n → (CanonicalRV.RVSort M)ˣ)) (w : A → Values.Gamma (M := M))
    (hw : mixedGammaTupleDefinable B (rvUnitGammaGraph A w)) (a : A) :
    ∃ f : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M),
      FullGammaFunction (integrationGammaBase B) f ∧ f (rvUnitTupleValues a.val) = w a := by
  have hd := rvUnitGammaGraph_point_definable B A w hw a
  let c : Fin n → Code (M := M) := fun i => ⟨(a.val i).val,
    fun h => Units.ne_zero (a.val i) (Subtype.ext (h.trans RVOperations.zero_val.symm))⟩
  have ha : GammaAlgebraicAtBase ⟨B.real ∪ Set.range (rawTuple c),B.gamma⟩ (w a) :=
    ⟨{w a},hd,Set.finite_singleton _,Set.mem_singleton _⟩
  have hv := rv_tuple_gamma_algebraic_depends_on_values hκ hs h00 B hsmall c (w a) ha
  exact gammaDcl_tuple_function B (rvUnitTupleValues a.val) (w a) hv
end DiamondIntegral.Section3
