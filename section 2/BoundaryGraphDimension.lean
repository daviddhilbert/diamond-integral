import «section 2».BoundaryRVGraphs

/-! Each retained-tag graph C_ij is finite over its input RV coordinates.
No bound on fibre cardinalities and no uniform enumeration are assumed. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n : ℕ}

theorem boundaryRVGraph_finite_projection (i : Fin (n+1)) (V : Set (Fin n → M))
    (F : (Fin n → M) → Set M) (hfinite : ∀ a ∈ V, (F a).Finite)
    (hconstant : RVPolydiscRowsConstant F V) (θ : Fin n → RVInfinity M) :
    {u : boundaryRVGraph i V F | u.val ∘ i.succAbove = θ}.Finite := by
  classical
  let H : Set (boundaryRVGraph i V F) := {u | u.val ∘ i.succAbove = θ}
  by_cases hne : H.Nonempty
  · obtain ⟨u₀,hu₀⟩ := hne
    have hθ : θ ∈ rawRVInterior V := by
      have h := ((boundaryRVGraph_mem_iff i V F u₀.val).mp u₀.property).1
      change u₀.val ∘ i.succAbove ∈ rawRVInterior V at h
      rwa [hu₀] at h
    have hsub := (rawRVInterior_iff V θ).mp hθ
    obtain ⟨a₀,ha₀⟩ := rawRVPolydisc_nonempty θ
    have hf := (hfinite a₀ (hsub ha₀)).image iRv
    have htag : ∀ u ∈ H, (u.val i).val ∈ iRv '' F a₀ := by
      intro u hu
      obtain ⟨_,a,hat,ha,y,hy,hyVF,hyt⟩ := (boundaryRVGraph_mem_iff i V F u.val).mp u.property
      change a ∈ rawRVPolydisc (u.val ∘ i.succAbove) at hat
      rw [hu] at hat
      have he := hconstant θ hsub a hat a₀ ha₀
      rw [← he]
      exact ⟨y,hy,hyt⟩
    apply Set.Finite.of_finite_image (f := fun u : boundaryRVGraph i V F => (u.val i).val)
    · apply hf.subset
      rintro _ ⟨u,hu,rfl⟩
      exact htag u hu
    · intro u hu v hv he
      apply Subtype.ext
      funext j
      refine Fin.succAboveCases i ?_ (fun q => ?_) j
      · exact Subtype.ext he
      · exact congrFun (hu.trans hv.symm) q
  · change H.Finite
    rw [Set.not_nonempty_iff_eq_empty.mp hne]
    exact Set.finite_empty

theorem boundaryRVGraph_dimension_lt (hc : CanonicalStructure.IsCanonical (M := M))
    (S : Set M) (i : Fin (n+1)) (V : Set (Fin n → M))
    (hV : DefinableOver S (fun _ => .vf) V) (F : (Fin n → M) → Set M)
    (hF : DefinableOver S (fun _ => .vf) (rawScalarCorrespondenceGraph V F))
    (hfinite : ∀ a ∈ V, (F a).Finite) (hconstant : RVPolydiscRowsConstant F V) :
    rvDimension S (boundaryRVGraph i V F) < ((n+1 : ℕ) : WithBot ℕ) :=
  rvDimension_lt_of_finite_projection hc S _ (boundaryRVGraph_definable hc S i V hV F hF)
    i.succAbove (boundaryRVGraph_finite_projection i V F hfinite hconstant) (Nat.lt_succ_self n)

end DiamondIntegral.Section2
