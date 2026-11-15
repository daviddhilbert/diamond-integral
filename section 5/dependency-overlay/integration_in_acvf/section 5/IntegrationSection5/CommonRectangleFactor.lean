import IntegrationSection5.CommonRectangleSlices
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section5.pointSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5

namespace IntegrationInACVF.Section5.PositionedCellLabelInjection.CommonProductHeadPair
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : SpecialTransformations.Section3.GammaParameters.Base (M := M)} {m : ℕ}
variable {A : Set (Point (M := M) 2 m)} {T : PositionedCellLabelInjection G A}

theorem leftR_first (P : CommonProductHeadPair T) :
    Nonempty (SharedProductFirst (G := G) P.rectangle.source P.rectangle.sourceD P.rectangle.sourceE P.rectangle.targetD P.rectangle.specialD) := by
  have hProd : carrier P.rectangle.source = {p | activeUnaryProjection 0 id p ∈ carrier P.rectangle.sourceD ∧ activeUnaryProjection 1 id p ∈ carrier P.rectangle.sourceE} := by
    change carrier P.rectangle.source = {p | activeUnaryProjection 0 id p ∈ carrier P.rectangle.sourceD ∧ activeUnaryProjection 1 id p ∈ carrier P.rectangle.sourceE}
    rw [P.rectangle.source_eq,P.rectangle.sourceD_eq,P.rectangle.sourceE_eq]
    exact mixed_rectangle_projection_eq _ (rectangleFamilyBranch_rectangles T.target)
  exact shared_product_first P.rectangle.specialD P.rectangle.gammaD P.rectangle.pullbackD P.leftR_gamma hProd

theorem leftR_padding_oldIndex (P : CommonProductHeadPair T)
    (F : SharedProductFirst (G := G) P.rectangle.source P.rectangle.sourceD P.rectangle.sourceE P.rectangle.targetD P.rectangle.specialD) :
    factorHeadProjection P.completeLeft.head.projection F.projection F.projection_bijective ∘
      (Fin.natAdd 1 ∘ suffixIndex F.arity_le) =
        headPaddingProjection (suffixIndex (specialRelative_rvArity_le P.completeLeft.preparation.special)) ∘ stripPassiveIndex T.arity := by
  funext j
  change headPaddingProjection (P.completeLeft.head.projection ∘ (Equiv.ofBijective F.projection F.projection_bijective).symm)
    (Fin.natAdd 1 (suffixIndex F.arity_le j)) =
      headPaddingProjection (suffixIndex (specialRelative_rvArity_le P.completeLeft.preparation.special)) (Fin.natAdd 1 (Fin.natAdd 1 j))
  rw [headPaddingProjection,Fin.append_right,headPaddingProjection,Fin.append_right]
  have hInv : (Equiv.ofBijective F.projection F.projection_bijective).symm (suffixIndex F.arity_le j) =
      suffixIndex (special_chain_rvArity_le P.rectangle.specialD.chain) j := by
    apply F.projection_bijective.1
    exact ((Equiv.ofBijective F.projection F.projection_bijective).apply_symm_apply _).trans (F.compatibility j).symm
  change Fin.natAdd 1 (P.completeLeft.head.projection ((Equiv.ofBijective F.projection F.projection_bijective).symm (suffixIndex F.arity_le j))) = _
  rw [hInv,P.completeLeft.head.compatibility]
  apply Fin.ext
  change 1 + (P.completeLeft.head.preparation.arity - (1+(1+T.arity)) + (1+(1+j.val))) =
    1 + (P.completeLeft.preparation.arity - (1+T.arity) + (1+j.val))
  have hle := P.completeLeft.head.arity_le
  change 1+(1+T.arity) ≤ P.completeLeft.head.preparation.arity at hle
  change 1 + (P.completeLeft.head.preparation.arity - (1+(1+T.arity)) + (1+(1+j.val))) =
    1 + (P.completeLeft.head.preparation.arity - (1+T.arity) + (1+j.val))
  omega

theorem rightR_first (P : CommonProductHeadPair T) :
    Nonempty (SharedProductFirst (G := G) P.rectangle.swap.source P.rectangle.sourceE P.rectangle.sourceD P.rectangle.targetE P.rectangle.specialE) := by
  have hProd : carrier P.rectangle.swap.source = {p | activeUnaryProjection 0 id p ∈ carrier P.rectangle.sourceE ∧ activeUnaryProjection 1 id p ∈ carrier P.rectangle.sourceD} := by
    change carrier P.rectangle.swap.source = {p | activeUnaryProjection 0 id p ∈ carrier P.rectangle.swap.sourceD ∧ activeUnaryProjection 1 id p ∈ carrier P.rectangle.swap.sourceE}
    rw [P.rectangle.swap.source_eq,P.rectangle.swap.sourceD_eq,P.rectangle.swap.sourceE_eq]
    exact mixed_rectangle_projection_eq _ (rvFibreRectangles_vfSwap _ (rectangleFamilyBranch_rectangles T.target))
  exact shared_product_first P.rectangle.specialE P.rectangle.gammaE P.rectangle.pullbackE P.rightR_gamma hProd

theorem rightR_padding_oldIndex (P : CommonProductHeadPair T)
    (F : SharedProductFirst (G := G) P.rectangle.swap.source P.rectangle.sourceE P.rectangle.sourceD P.rectangle.targetE P.rectangle.specialE) :
    factorHeadProjection P.completeRight.head.projection F.projection F.projection_bijective ∘
      (Fin.natAdd 1 ∘ suffixIndex F.arity_le) =
        headPaddingProjection (suffixIndex (specialRelative_rvArity_le P.completeRight.preparation.special)) ∘ stripPassiveIndex T.arity := by
  funext j
  change headPaddingProjection (P.completeRight.head.projection ∘ (Equiv.ofBijective F.projection F.projection_bijective).symm)
    (Fin.natAdd 1 (suffixIndex F.arity_le j)) =
      headPaddingProjection (suffixIndex (specialRelative_rvArity_le P.completeRight.preparation.special)) (Fin.natAdd 1 (Fin.natAdd 1 j))
  rw [headPaddingProjection,Fin.append_right,headPaddingProjection,Fin.append_right]
  have hInv : (Equiv.ofBijective F.projection F.projection_bijective).symm (suffixIndex F.arity_le j) =
      suffixIndex (special_chain_rvArity_le P.rectangle.specialE.chain) j := by
    apply F.projection_bijective.1
    exact ((Equiv.ofBijective F.projection F.projection_bijective).apply_symm_apply _).trans (F.compatibility j).symm
  change Fin.natAdd 1 (P.completeRight.head.projection ((Equiv.ofBijective F.projection F.projection_bijective).symm (suffixIndex F.arity_le j))) = _
  rw [hInv,P.completeRight.head.compatibility]
  apply Fin.ext
  change 1 + (P.completeRight.head.preparation.arity - (1+(1+T.arity)) + (1+(1+j.val))) =
    1 + (P.completeRight.preparation.arity - (1+T.arity) + (1+j.val))
  have hle := P.completeRight.head.arity_le
  change 1+(1+T.arity) ≤ P.completeRight.head.preparation.arity at hle
  change 1 + (P.completeRight.head.preparation.arity - (1+(1+T.arity)) + (1+(1+j.val))) =
    1 + (P.completeRight.head.preparation.arity - (1+T.arity) + (1+j.val))
  omega

end IntegrationInACVF.Section5.PositionedCellLabelInjection.CommonProductHeadPair
