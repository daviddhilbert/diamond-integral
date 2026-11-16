import «section 6».RVIndexedRowBounds
import «section 6».ParameterCodeImages
import «section 2».RVValueFamilies
import «section 2».RawFibreRelationalImages
import «section 2».RVBoundCoordinates

/-! Complete RV-valued rows over a doubly bounded RV base have one
original-base named bound when each row is bounded separately. Project
the coordinate values to full Gamma rows and apply the checked bound;
there is no choice of real representatives or VF-indexed uniform bound. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n m : ℕ}

def typedRVRowRelation (R : Set (Fin n ⊕ Fin m → M)) : Set (Fin n ⊕ Fin m → M) :=
  {z | z ∈ R ∧ z ∘ Sum.inr ∈ (rawRVSpace (M := M) m).domain}

theorem typedRVRowRelation_definable (R : Set (Fin n ⊕ Fin m → M)) (hR : S.Definable LRV R) :
    S.Definable LRV (typedRVRowRelation R) :=
  hR.inter (((rawRVSpace (M := M) m).definable_domain S).preimage_comp Sum.inr)

def rvRowCoordinateCode (j : Fin m) (z : Fin n ⊕ Fin m → M) : Fin 1 → M := fun _ => z (.inr j)

def rvRowScalarRelation (R : Set (Fin n ⊕ Fin m → M)) : Set (Fin n ⊕ Fin 1 → M) :=
  ⋃ j,parameterCodeImage (typedRVRowRelation R) (rvRowCoordinateCode j)

theorem rvRowScalarRelation_definable (R : Set (Fin n ⊕ Fin m → M)) (hR : S.Definable LRV R) :
    S.Definable LRV (rvRowScalarRelation R) :=
  Set.definable_iUnion_of_finite (fun j => parameterCodeImage_definable _ (typedRVRowRelation_definable R hR)
    (rvRowCoordinateCode j) (fun _ => Set.DefinableFun.proj LRV))

theorem rvRowScalarRelation_at (R : Set (Fin n ⊕ Fin m → M)) (x : Fin n → M) (y : M) :
    Sum.elim x (fun _ : Fin 1 => y) ∈ rvRowScalarRelation R ↔
      ∃ u : Fin m → RVInfinity M,Sum.elim x (rvValues u) ∈ R ∧ ∃ j,(u j).val=y := by
  constructor
  · intro h
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp h
    have hImage : (fun _ : Fin 1 => y) ∈
        {z | Sum.elim x z ∈ parameterCodeImage (typedRVRowRelation R) (rvRowCoordinateCode j)} := hj
    rw [parameterCodeImage_at] at hImage
    obtain ⟨w,⟨hwR,hwDom⟩,hwOut⟩ := hImage
    let u : Fin m → RVInfinity M := (rawRVSpace (M := M) m).decode ⟨w,hwDom⟩
    have hu : rvValues u=w := SpecialTransformations.Section4.rvValues_decode _
    refine ⟨u,?_,j,?_⟩
    · rw [hu]
      exact hwR
    · have h := congrFun hwOut 0
      change w j=y at h
      rw [← hu] at h
      exact h
  · rintro ⟨u,hu,j,hj⟩
    apply Set.mem_iUnion.mpr
    refine ⟨j,?_⟩
    apply (Set.ext_iff.mp (parameterCodeImage_at (typedRVRowRelation R) (rvRowCoordinateCode j) x) _).mpr
    refine ⟨rvValues u,⟨hu,⟨u,rfl⟩⟩,?_⟩
    funext i
    exact hj

def rvRowGammaValues (R : Set (Fin n ⊕ Fin m → M)) (x : Fin n → M) : Set (Gamma M) :=
  {γ | ∃ u : Fin m → RVInfinity M,Sum.elim x (rvValues u) ∈ R ∧
    ∃ j,u j ≠ rvZero M ∧ GammaParameters.codeValue (u j).val=γ}

theorem rvRowGammaValues_graph
    (D : Set (Fin n → M)) (R : Set (Fin n ⊕ Fin m → M)) :
    rawGammaFamilyGraph D (rvRowGammaValues R)=
      (fun z : Fin n ⊕ Fin 1 → M => z ∘ Sum.inl) ⁻¹' D ∩
        rawFibreRelationalImage (rvRowScalarRelation R) GammaParameters.SameScalar := by
  ext z
  constructor
  · rintro ⟨hD,hNZ,u,hu,j,hj0,hjValue⟩
    refine ⟨hD,(u j).val,(rvRowScalarRelation_at R _ _).mpr ⟨u,hu,j,rfl⟩,?_⟩
    have huNZ : GammaParameters.NonzeroRV (u j).val := ⟨(u j).property,fun h => hj0 (Subtype.ext h)⟩
    exact (sameScalar_iff_codeValue_eq _ _ huNZ hNZ).mpr hjValue
  · rintro ⟨hD,v,hv,hSame⟩
    obtain ⟨u,hu,j,hj⟩ := (rvRowScalarRelation_at R _ _).mp hv
    refine ⟨hD,hSame.2.1,u,hu,j,?_,?_⟩
    · intro hz
      exact hSame.1.2 (hj.symm.trans (congrArg Subtype.val hz))
    · rw [hj]
      exact hSame.codeValue_eq

theorem rvRowGammaValues_definable
    (D : Set (Fin n → M)) (hD : S.Definable LRV D)
    (R : Set (Fin n ⊕ Fin m → M)) (hR : S.Definable LRV R) :
    S.Definable LRV (rawGammaFamilyGraph D (rvRowGammaValues R)) := by
  rw [rvRowGammaValues_graph]
  exact (hD.preimage_comp Sum.inl).inter (rawFibreRelationalImage_definable S _
    (rvRowScalarRelation_definable R hR) GammaParameters.SameScalar (GammaParameters.same_scalar_definable S))

theorem rv_indexed_rv_rows_named_bound
    (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (D : Set (Fin n → M)) (hD : S.Definable LRV D)
    (hNZ : ∀ x ∈ D,∀ i,GammaParameters.NonzeroRV (x i)) (hDB : RVCodeDoublyBounded D)
    (R : Set (Fin n ⊕ Fin m → M)) (hR : S.Definable LRV R)
    (hRows : ∀ x ∈ D,RVValueDoublyBounded {u : Fin m → RVInfinity M | Sum.elim x (rvValues u) ∈ R}) :
    ∃ δ : Gamma M,S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {δ}} ∧
      ∀ x ∈ D,∀ u : Fin m → RVInfinity M,Sum.elim x (rvValues u) ∈ R →
        ∀ i,(δ⁻¹).val ≤ Values.vrv (u i) ∧ Values.vrv (u i) ≤ δ.val := by
  have hGammaRows (x) (hx : x ∈ D) :
      ∃ γ : Gamma M,∀ a ∈ rvRowGammaValues R x,γ⁻¹ ≤ a ∧ a ≤ γ := by
    obtain ⟨γ,hγ⟩ := hRows x hx
    refine ⟨γ,?_⟩
    rintro a ⟨u,hu,j,hj0,hja⟩
    have h := hγ u hu j
    rw [← nonzero_rv_codeValue_val (u j) hj0,hja] at h
    exact h
  obtain ⟨δ,hδ,hBound⟩ := rv_indexed_gamma_rows_named_bound hc h00 linear hκ hs hsmall hΓ D hD hNZ hDB
    (rvRowGammaValues R) (rvRowGammaValues_definable D hD R hR) hGammaRows
  refine ⟨δ,hδ,?_⟩
  intro x hx u hu i
  have hui0 := (hRows x hx).nonzero u hu i
  have h := hBound x hx (GammaParameters.codeValue (u i).val) ⟨u,hu,i,hui0,rfl⟩
  change (δ⁻¹).val ≤ Values.vrv (u i) ∧ Values.vrv (u i) ≤ δ.val
  rw [← nonzero_rv_codeValue_val (u i) hui0]
  exact h

end DiamondIntegral.Section6
