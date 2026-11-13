import «section 3».RVSourcePatternDefinability
import «section 3».RVAngularCell
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GuardedRVNormalForm
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}

/-- An actual RV-definable set has a finite disjoint partition over the
same real ground into cells with integral monomial angular normal form.
This precedes the residue/Gamma rectangle and categorical assembly. -/
theorem definableRV_finite_angular_partition (A : Set (Fin n → M))
    (hA : DefinableOver S (fun _ => .rv) A) :
    ∃ N : ℕ, ∃ X : Fin N → DefSet (rawRVUnitSpace (M := M) n) S,
      (∀ i, Nonempty (RVAngularCell (X i).carrier)) ∧
      (∀ i j, i ≠ j → Disjoint (X i).carrier (X j).carrier) ∧
      ∀ x : Fin n → (CanonicalRV.RVSort M)ˣ, rvUnitValues x ∈ A ↔ ∃ i, x ∈ (X i).carrier := by
  obtain ⟨p,D,hD⟩ := definableRV_guarded_DNF hA
  let J := RVDNFGlobalPattern D
  letI := Fintype.ofFinite J
  let e : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  have hmatch : ∀ x : Fin n → (CanonicalRV.RVSort M)ˣ, rvUnitValues x ∈ A ↔
      PolarityDNF.holds (RVLiteral.comparison (sourceVFFixedValues p n) (sourceRVFixedParameters p)
        (fun i => (x i : CanonicalRV.RVSort M))) D := fun x => (hD x).1
  let X : Fin (Fintype.card J) → DefSet (rawRVUnitSpace (M := M) n) S := fun i =>
    ⟨rvDNFPatternCell D (sourceVFFixedValues p n) (sourceRVFixedParameters p) (e i),
      sourceDNFPatternCell_definable p D (e i) A hA.raw_definable hmatch⟩
  refine ⟨Fintype.card J,X,?_,?_,?_⟩
  · intro i
    exact rvDNFPatternCell_angularCell D (sourceVFFixedValues p n) (sourceRVFixedParameters p) (e i)
  · intro i j hij
    exact rvDNFPatternCells_disjoint D (sourceVFFixedValues p n) (sourceRVFixedParameters p) (e i) (e j)
      (fun he => hij (e.injective he))
  · intro x
    rw [hmatch x,rvDNFPatternCells_cover]
    constructor
    · rintro ⟨b,hb⟩
      obtain ⟨i,rfl⟩ := e.surjective b
      exact ⟨i,hb⟩
    · rintro ⟨i,hi⟩
      exact ⟨e i,hi⟩
end DiamondIntegral.Section3
