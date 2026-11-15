import «section 5».NativeValueFibreDomains
import «section 5».RealGammaGroundElimination
import Section3.GammaUniformCover

/-! The value of an already named nonzero RV element is definable over
the same real base, via the full value fibre. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M)

include hc in
theorem namedRV_value_definable (r : CanonicalRV.RVSort M) (hr : r.val ∈ S) (h0 : r.val ≠ iRVZero) :
    GammaDefinableClosureAtBase (EmptyGammaGround.base S) (Values.gammaOf r h0) := by
  apply (fullRawValueFibre_definable_iff hc S _).mp
  let a : LRV.Term (S ⊕ Fin 1) := .var (.inr 0)
  let b : LRV.Term (S ⊕ Fin 1) := .var (.inl ⟨r.val,hr⟩)
  let φ₁ : LRV.Formula (S ⊕ Fin 1) := Relations.formula₁ (L := LRV) Rel.memRV a
  let φ₂ : LRV.Formula (S ⊕ Fin 1) := Relations.formula₂ (L := LRV) Rel.rvLe a b
  let φ₃ : LRV.Formula (S ⊕ Fin 1) := Relations.formula₂ (L := LRV) Rel.rvLe b a
  let φ : LRV.Formula (S ⊕ Fin 1) := φ₁ ⊓ (φ₂ ⊓ φ₃)
  rw [Set.definable_iff_exists_formula_sum]
  refine ⟨φ,?_⟩
  ext u
  change (u ∈ fullRawValueFibre (Values.gammaOf r h0)) ↔ φ.Realize (Sum.elim Subtype.val u)
  have hp : φ.Realize (Sum.elim Subtype.val u) ↔
      iRV (u 0) ∧ iLe (u 0) r.val ∧ iLe r.val (u 0) := by
    simp only [φ,φ₁,φ₂,φ₃,Formula.realize_inf,Formula.realize_rel₁,Formula.realize_rel₂,Term.realize_var]
    rfl
  rw [hp,fullRawValueFibre_mem]
  constructor
  · rintro ⟨s,hs,hv⟩
    refine ⟨hs ▸ s.property,?_⟩
    exact hs ▸ (Values.vrv_eq_iff s r).mp hv
  · rintro ⟨hs,hle,hle'⟩
    exact ⟨⟨u 0,hs⟩,rfl,(Values.vrv_eq_iff _ r).mpr ⟨hle,hle'⟩⟩

include hc in
theorem realGroundValues_definable (α : Values.Gamma (M := M))
    (hα : ∃ r : CanonicalRV.RVSort M,∃ h0 : r.val ≠ iRVZero,r.val ∈ S ∧ α = Values.gammaOf r h0) :
    GammaDefinableClosureAtBase (EmptyGammaGround.base S) α := by
  obtain ⟨r,h0,hr,rfl⟩ := hα
  exact namedRV_value_definable hc S r hr h0

end DiamondIntegral.Section5
