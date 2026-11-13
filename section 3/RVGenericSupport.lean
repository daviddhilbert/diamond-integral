import «section 3».RVGenericFinitePartition
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}

/-- A selected coordinate row has an actual point in the original set
with exactly the same complete value tuple. -/
theorem rvGenericCoordinate_support (A : Set (Fin n → M)) (i : Fin n)
    (u : Fin n → (CanonicalRV.RVSort M)ˣ)
    (hu : rvUnitValues u ∈ rvGenericCoordinate A i) :
    ∃ v : Fin n → (CanonicalRV.RVSort M)ˣ,
      rvUnitTupleValues u = rvUnitTupleValues v ∧ rvUnitValues v ∈ A := by
  have hproper : ∀ j, sortEval .rv (rvUnitValues u j) := by
    intro j
    simpa only [sortEval,iRV,rvUnitValues] using (u j).val.property
  obtain ⟨_,hi⟩ := (mem_rvGenericCoordinate_iff A i _ hproper).mp hu
  obtain ⟨z,hz,hA⟩ := hi.nonempty
  let t : (CanonicalRV.RVSort M)ˣ := Units.mk0 (⟨z,hz.1.1⟩ : CanonicalRV.RVSort M)
    (fun h => hz.1.2 ((congrArg Subtype.val h).trans RVOperations.zero_val))
  let v := Function.update u i t
  have he : rvUnitValues v = Function.update (rvUnitValues u) i z := by
    funext j
    by_cases hj : j = i <;> simp [v,rvUnitValues,hj,t]
  refine ⟨v,?_,?_⟩
  · funext j
    by_cases hj : j = i
    · subst j
      simp only [v,Function.update_self,rvUnitTupleValues]
      apply Subtype.ext
      apply (Values.vrv_eq_iff _ _).mpr
      exact ⟨hz.2.2.2,hz.2.2.1⟩
    · simp only [rvUnitTupleValues,v,Function.update_of_ne hj]
  · rwa [he]

/-- Finite generic iteration never creates a new value fibre. -/
theorem rvGenericCoordinate_fold_support (A : Set (Fin n → M)) (L : List (Fin n))
    (u : Fin n → (CanonicalRV.RVSort M)ˣ)
    (hu : rvUnitValues u ∈ L.foldl rvGenericCoordinate A) :
    ∃ v : Fin n → (CanonicalRV.RVSort M)ˣ,
      rvUnitTupleValues u = rvUnitTupleValues v ∧ rvUnitValues v ∈ A := by
  induction L generalizing A u with
  | nil => exact ⟨u,rfl,hu⟩
  | cons i L ih =>
    obtain ⟨v,hv,hvA⟩ := ih (rvGenericCoordinate A i) u hu
    obtain ⟨w,hw,hwA⟩ := rvGenericCoordinate_support A i v hvA
    exact ⟨w,hv.trans hw,hwA⟩

theorem rvFullFibreGeneric_support (A : Set (Fin n → M))
    (u : Fin n → (CanonicalRV.RVSort M)ˣ) (hu : rvUnitValues u ∈ rvFullFibreGeneric A) :
    ∃ v : Fin n → (CanonicalRV.RVSort M)ˣ,
      rvUnitTupleValues u = rvUnitTupleValues v ∧ rvUnitValues v ∈ A :=
  rvGenericCoordinate_fold_support A (List.finRange n) u hu

end DiamondIntegral.Section3
