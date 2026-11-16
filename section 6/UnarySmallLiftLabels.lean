import «section 6».OriginalBaseMeasuredRVLifting
import Section4.VFFibreFiniteness

/-! A unary VF-small set has finite VF projection. Inside an actual
finite-volume RV lift it is finite, and its old-label image is finite.
Thus the entire bad label discs can be replaced in the unary case. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r : ℕ}

theorem unary_vfSmall_finite_vfProjection
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal} (hs : Saturated M κ)
    (hsmall : Cardinal.mk S < κ) (E : DefSet (rawMixedSpace (M := M) 1 r) S)
    (hDim : vfDim (rawRVSpace (M := M) 1) E < 1) : (Prod.fst '' E.carrier).Finite := by
  have hZero : vfDim (rawRVSpace (M := M) 1) E = 0 := Nat.lt_one_iff.mp hDim
  have hAlg (p : E) : AlgebraicAt S .vf (p.val.1 0).val := by
    by_contra hn
    have hi : AlgebraicIndependent (vfParameterField S) p.val.1 := by
      apply algebraicIndependent_unique_type_iff.mpr
      intro h
      exact hn ((algebraicAt_vf_iff_parameterField S _).mpr h)
    have hRank := (tupleField_trdeg_eq_arity_iff (vfParameterField S) p.val.1).mpr hi
    have hRank' : vfTupleTrdeg S p.val.1 = (1 : Cardinal) := hRank
    have hLe := vfTupleTrdeg_le_vfDim hc (rawRVSpace (M := M) 1) (rawRVSpace_rvCoded 1) E p
    rw [hRank',hZero] at hLe
    simpa using hLe
  exact finite_vf_projection_of_algebraic hs hsmall E (fun p i => by fin_cases i; exact hAlg p)

theorem unary_vfSmall_finite_of_finite_rvFibres
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal} (hs : Saturated M κ)
    (hsmall : Cardinal.mk S < κ) (E : DefSet (rawMixedSpace (M := M) 1 r) S)
    (hDim : vfDim (rawRVSpace (M := M) 1) E < 1)
    (A : Set (Mixed M 1 r)) (hEA : E.carrier ⊆ A)
    (hFin : ∀ a : Fin 1 → VF M, {u : Fin r → RVInfinity M | (a,u) ∈ A}.Finite) : E.carrier.Finite := by
  apply Set.Finite.of_finite_fibers Prod.fst (unary_vfSmall_finite_vfProjection hc hs hsmall E hDim)
  intro a ha
  apply ((hFin a).image (fun u => (a,u))).subset
  rintro p ⟨hp,hpa⟩
  have he : p.1 = a := hpa
  exact ⟨p.2,he ▸ hEA hp,by rw [← he]⟩

def unaryBadLiftLabels (U : MeasuredRVObject (M := M) S 1)
    (E : DefSet (rawMixedSpace (M := M) 1 U.object.arity) S)
    (hE : E.carrier ⊆ (rvLift U.object).carrier) := ((liftLabelMap U.object).restrict hE).image

theorem unaryBadLiftLabels_subset (U : MeasuredRVObject (M := M) S 1)
    (E : DefSet (rawMixedSpace (M := M) 1 U.object.arity) S)
    (hE : E.carrier ⊆ (rvLift U.object).carrier) : (unaryBadLiftLabels U E hE).carrier ⊆ U.object.domain.carrier := by
  rintro q ⟨p,hp⟩
  exact hp ▸ (liftLabelMap U.object ⟨p.val,hE p.property⟩).property

theorem unaryBadLiftLabels_finite
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal} (hs : Saturated M κ)
    (hsmall : Cardinal.mk S < κ) (U : MeasuredRVObject (M := M) S 1)
    (E : DefSet (rawMixedSpace (M := M) 1 U.object.arity) S)
    (hE : E.carrier ⊆ (rvLift U.object).carrier) (hDim : vfDim (rawRVSpace (M := M) 1) E < 1) :
    (unaryBadLiftLabels U E hE).carrier.Finite := by
  have hEF := unary_vfSmall_finite_of_finite_rvFibres hc hs hsmall E hDim (rvLift U.object).carrier hE
    (rvLift_finite_rv_fibres U.object U.finiteVolume)
  apply (hEF.image Prod.snd).subset
  rintro q ⟨p,hp⟩
  exact ⟨p.val,p.property,hp⟩

theorem unaryBadLiftLabels_cover (U : MeasuredRVObject (M := M) S 1)
    (E : DefSet (rawMixedSpace (M := M) 1 U.object.arity) S)
    (hE : E.carrier ⊆ (rvLift U.object).carrier) (p : rvLift U.object)
    (hp : p.val.2 ∉ (unaryBadLiftLabels U E hE).carrier) : p.val ∉ E.carrier := by
  intro h
  exact hp ⟨⟨p.val,h⟩,rfl⟩

end DiamondIntegral.Section6
