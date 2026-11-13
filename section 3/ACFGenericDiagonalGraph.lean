import «section 3».GenericFieldDiagonalActions
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language FirstOrder.Ring
noncomputable section
namespace DiamondIntegral.Section3
variable {K : Type} [Field K] [IsAlgClosed K] [CharZero K] [CompatibleRing K]
variable {n m : ℕ}

/-- Diagonal invariance of the actual definable graph forces the same
diagonal action on its generated output field. -/
theorem acf_generic_diagonal_graph_output (E : Subfield K)
    (R : Set (Fin n ⊕ Fin m → K)) (hR : (E : Set K).Definable Language.ring R)
    (x : Fin n → K) (y : Fin m → K) (hxy : Sum.elim x y ∈ R)
    (hu : ∀ u v w, Sum.elim u v ∈ R → Sum.elim u w ∈ R → v = w)
    (hx : AlgebraicIndependent E x)
    (a : Fin n → Eˣ) (b : Fin m → Eˣ)
    (hscale : Sum.elim (fun i => (a i : K) * x i) (fun j => (b j : K) * y j) ∈ R)
    (j : Fin m) :
    let F := IntermediateField.adjoin E (Set.range x)
    let hy := acf_definable_relation_coordinates_mem_adjoin E R hR x y hxy
      (fun z hz => hu x z y hz hxy)
    (genericFieldDiagonalEquiv x hx a ⟨y j,hy j⟩ : K) = (b j : K) * y j := by
  dsimp only
  let F := IntermediateField.adjoin E (Set.range x)
  let σ := genericFieldDiagonalEquiv x hx a
  have hy := acf_definable_relation_coordinates_mem_adjoin E R hR x y hxy
    (fun z hz => hu x z y hz hxy)
  let z : Fin n ⊕ Fin m → F := Sum.elim
    (fun i => ⟨x i,IntermediateField.subset_adjoin E _ (Set.mem_range_self i)⟩)
    (fun j => ⟨y j,hy j⟩)
  have hz : (fun i => (z i : K)) ∈ R := by
    have he : (fun i => (z i : K)) = Sum.elim x y := by
      funext i
      cases i <;> rfl
    rw [he]
    exact hxy
  have hσ := (acf_definable_intermediate_embedding E F
    (F.val.comp σ.toAlgHom) R hR z).mp hz
  have hσ' : Sum.elim (fun i => (a i : K) * x i)
      (fun j => (σ ⟨y j,hy j⟩ : K)) ∈ R := by
    convert hσ using 1
    funext i
    cases i with
    | inl i => exact (genericFieldDiagonalEquiv_coordinate x hx a i).symm
    | inr i => rfl
  exact congrFun (hu _ _ _ hσ' hscale) j

/-- The rational function field isomorphism extracted from an actual
partial graph intertwines any diagonal action preserving that graph. -/
theorem acfGenericBirationalEquiv_diagonal (E : Subfield K)
    (R : Set (Fin n ⊕ Fin m → K)) (hR : (E : Set K).Definable Language.ring R)
    (x : Fin n → K) (y : Fin m → K) (hxy : Sum.elim x y ∈ R)
    (hu : ∀ u v w, Sum.elim u v ∈ R → Sum.elim u w ∈ R → v = w)
    (hv : ∀ z : Fin n → K, Sum.elim z y ∈ R → z = x)
    (hx : AlgebraicIndependent E x) (hy : AlgebraicIndependent E y)
    (a : Fin n → Eˣ) (b : Fin m → Eˣ)
    (hscale : Sum.elim (fun i => (a i : K) * x i) (fun j => (b j : K) * y j) ∈ R)
    (w : TorusRationalFunction E n) :
    acfGenericBirationalEquiv E R hR x y hxy (fun z hz => hu x z y hz hxy) hv hx hy
      (diagonalRationalEquiv a w) =
    diagonalRationalEquiv b
      (acfGenericBirationalEquiv E R hR x y hxy (fun z hz => hu x z y hz hxy) hv hx hy w) := by
  let F := IntermediateField.adjoin E (Set.range x)
  let G := IntermediateField.adjoin E (Set.range y)
  have hFG := acf_definable_bijection_adjoin_eq E R hR x y hxy
    (fun z hz => hu x z y hz hxy) hv
  let q : TorusRationalFunction E m ≃ₐ[E] F :=
    hy.aevalEquivField.trans (IntermediateField.equivOfEq hFG.symm)
  let σ := genericFieldDiagonalEquiv x hx a
  let s : F →ₐ[E] K := F.val.comp σ.toAlgHom
  let ev : TorusRationalFunction E m →ₐ[E] K := F.val.comp q.toAlgHom
  have hq (j : Fin m) : (q (torusRationalVariable E j) : K) = y j := by
    change (hy.aevalEquivField (torusRationalVariable E j) : K) = y j
    rw [torusRationalVariable,hy.aevalEquivField_algebraMap_apply_coe]
    simp
  have heval : s.comp q.toAlgHom = ev.comp (diagonalRationalEquiv b).toAlgHom := by
    apply torusRational_algHom_ext
    intro j
    change (σ (q (torusRationalVariable E j)) : K) =
      (q (diagonalRationalEquiv b (torusRationalVariable E j)) : K)
    rw [diagonalRationalEquiv_variable,map_mul]
    have hj := acf_generic_diagonal_graph_output E R hR x y hxy hu hx a b hscale j
    have heq : q (torusRationalVariable E j) =
        ⟨y j,acf_definable_relation_coordinates_mem_adjoin E R hR x y hxy
          (fun z hz => hu x z y hz hxy) j⟩ := Subtype.ext (hq j)
    rw [heq]
    simpa [σ,Subfield.algebraMap_ofSubfield] using hj
  let e := acfGenericBirationalEquiv E R hR x y hxy (fun z hz => hu x z y hz hxy) hv hx hy
  have hqe (z : TorusRationalFunction E n) : q (e z) = hx.aevalEquivField z := by
    apply Subtype.ext
    exact acfGenericBirationalEquiv_evaluate E R hR x y hxy
      (fun z hz => hu x z y hz hxy) hv hx hy z
  apply q.injective
  apply Subtype.ext
  have he := AlgHom.congr_fun heval (e w)
  change (σ (q (e w)) : K) = (q (diagonalRationalEquiv b (e w)) : K) at he
  rw [hqe] at he
  rw [hqe]
  change (hx.aevalEquivField (diagonalRationalEquiv a w) : K) = _
  convert he using 1
  simp [σ,genericFieldDiagonalEquiv]

end DiamondIntegral.Section3
