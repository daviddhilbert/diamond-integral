import «section 6».TupleCoordinateMaps

/-! Finite original-base RV objects have actual definable VF centers in
every structural volume coordinate, using the proved unary finite-family
choice theorem on their literal original label domains. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem exists_finite_rv_object_coordinate_centers
    (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (W : Set M) (hW : ∀ a ∈ W, iVF a) (hWS : W ⊆ S) (hSW : S ⊆ algebraicClosureSet W)
    (hnt : ∃ x : vfAlgebraicClosureField W, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (hsmall : Cardinal.mk S < κ) (U : RVObject (M := M) S n) (hFin : U.domain.carrier.Finite) :
    ∃ a : Fin n → Map U.domain (DefSet.univ (rawVFSpace (M := M) 1) S),
      ∀ i u, rv M ((a i u).val 0) = U.value u i := by
  have h (i : Fin n) : ∃ a : Map U.domain (DefSet.univ (rawVFSpace (M := M) 1) S),
      ∀ u, rv M ((a u).val 0) = U.value u i := by
    let Uᵢ : RVObject (M := M) S 1 :=
      ⟨U.arity,U.domain,(rvTupleSelectMap S (fun _ : Fin 1 => i)).comp U.volume⟩
    exact exists_finite_unary_rv_object_centers hc h00 hs hv W hW hWS hSW hnt hsmall Uᵢ hFin
  choose a ha using h
  exact ⟨a,ha⟩

theorem exists_finite_rv_object_tuple_centers
    (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (W : Set M) (hW : ∀ a ∈ W, iVF a) (hWS : W ⊆ S) (hSW : S ⊆ algebraicClosureSet W)
    (hnt : ∃ x : vfAlgebraicClosureField W, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (hsmall : Cardinal.mk S < κ) (U : RVObject (M := M) S n) (hFin : U.domain.carrier.Finite) :
    ∃ a : Map U.domain (DefSet.univ (rawVFSpace (M := M) n) S),
      ∀ u, SpecialTransformations.Section4.tupleRV (a u).val = U.value u := by
  obtain ⟨a,ha⟩ := exists_finite_rv_object_coordinate_centers hc h00 hs hv W hW hWS hSW hnt hsmall U hFin
  refine ⟨vfTupleAssembleMap U.domain n a,fun u => ?_⟩
  rw [vfTupleAssembleMap_value]
  exact funext (fun i => ha i u)

end DiamondIntegral.Section6
