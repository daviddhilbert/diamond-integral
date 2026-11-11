import «section 2».ScalarBoundaryDefinability

/-! Finite RV sets have dimension zero when nonempty and dimension minus
infinity when empty. The actual map has target RV^0, so there is no hidden
choice of a nonzero RV constant or of representatives. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- A finite ground-definable RV-infinity set maps finitely to RV^0.
Its graph is defined over exactly the original real parameter set. -/
theorem rvHasFiniteMap_zero_of_finite (S : Set M) {m : ℕ}
    (U : Set (Fin m → RVInfinity M)) (hfin : U.Finite)
    (hU : DefinableOver S (fun _ => .rv) (rvInputValues '' U)) : RVHasFiniteMap S U 0 := by
  let f : U → Fin 0 → RV M := fun _ => Fin.elim0
  haveI : Finite U := Set.finite_coe_iff.mpr hfin
  refine ⟨f, fun _ => Set.toFinite _, ?_⟩
  let B : ParameterBase M := ⟨S, ∅⟩
  let π : Fin m → Fin (m+0) := fun j => finSumFinEquiv (Sum.inl j)
  have hΓ : GammaParameters.DefinableOverBase B (fun _ : Fin m => .rv)
      (rvInputValues '' U) := (GammaParameters.base_empty_iff S _ _).mpr hU
  have hp := hΓ.preimage_real (fun _ : Fin (m+0) => .rv) π
  apply (GammaParameters.base_empty_iff S _ _).mp
  change GammaParameters.DefinableOverBase B (fun _ : Fin (m+0) => .rv) (rvMapGraph U f)
  convert hp using 1
  ext z
  constructor
  · rintro ⟨u, hcode, _⟩
    refine ⟨⟨u.val, u.property, hcode⟩, ?_⟩
    intro i
    obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective i
    cases j with
    | inl j =>
      change iRV (z (finSumFinEquiv (Sum.inl j)))
      have he := congrFun hcode j
      change (u.val j).val = z (finSumFinEquiv (Sum.inl j)) at he
      rw [← he]
      exact (u.val j).property
    | inr j => exact j.elim0
  · rintro ⟨⟨u, hu, hcode⟩, _⟩
    refine ⟨⟨u, hu⟩, hcode, ?_⟩
    funext j
    exact j.elim0

/-- The minimum in the dimension definition is zero for every nonempty
finite definable set, over its original real base. -/
theorem rvDimension_finite_eq_zero (S : Set M) {m : ℕ}
    (U : Set (Fin m → RVInfinity M)) (hfin : U.Finite) (hne : U.Nonempty)
    (hU : DefinableOver S (fun _ => .rv) (rvInputValues '' U)) : rvDimension S U = 0 := by
  have hk : sInf {k | RVHasFiniteMap S U k} = 0 :=
    Nat.eq_zero_of_le_zero (Nat.sInf_le (rvHasFiniteMap_zero_of_finite S U hfin hU))
  simp only [rvDimension, ite_eq_left hne, hk, Nat.cast_zero]

/-- This formulation includes the empty set with its approved −∞ value. -/
theorem rvDimension_finite_lt_one (S : Set M) {m : ℕ}
    (U : Set (Fin m → RVInfinity M)) (hfin : U.Finite)
    (hU : DefinableOver S (fun _ => .rv) (rvInputValues '' U)) :
    rvDimension S U < (1 : WithBot ℕ) := by
  by_cases hne : U.Nonempty
  · rw [rvDimension_finite_eq_zero S U hfin hne hU]
    exact_mod_cast (Nat.zero_lt_succ 0)
  · rw [Set.not_nonempty_iff_eq_empty.mp hne]
    exact rvDimension_empty_lt S m 1

/-- Lemma 2.35 in one VF coordinate, in the real-ground scope of the
current RV-dimension interface. Boundary finiteness and definability also
have separate theorems over genuine Gamma parameter bases. -/
theorem lemma_2_35_unary (S : Set M) (A : Set M) (hA : DefinableAt S .vf A) :
    rvDimension S (scalarBoundaryTuples A) < (1 : WithBot ℕ) := by
  let B : ParameterBase M := ⟨S, ∅⟩
  have hΓ : GammaParameters.DefinableAtBase B .vf A :=
    (GammaParameters.at_base_empty_iff S .vf A).mpr hA
  have hfin := scalarBoundaryTuples_finite B A hΓ
  have hdef := scalarBoundaryTuples_definable B A hΓ
  exact rvDimension_finite_lt_one S _ hfin ((GammaParameters.base_empty_iff S _ _).mp hdef)

/-- The zero-VF-coordinate boundary has dimension −∞ even when auxiliary
RV labels are retained, and hence satisfies the strict bound by zero. -/
theorem rvBoundary_zero_arity_dimension (S : Set M) {m : ℕ} (A : Set (Mixed M 0 m)) :
    rvDimension S (Prod.snd '' rvBoundary A) < (0 : WithBot ℕ) := by
  rw [rvBoundary_zero_arity, Set.image_empty]
  exact rvDimension_empty_lt S m 0

end DiamondIntegral.Section2
