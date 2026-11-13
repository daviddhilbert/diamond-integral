import «section 4».GammaGraphPartitionEndpoints
import «section 4».GammaBoundaryStacks

/-! The finite family of cylindrical shapes determined by a definable
boundary graph partition. Labels are points, pairs of endpoints, upper
rays, lower rays and a whole line. Every base and every stack is definable
over the original base, and each stack is contained in the original set. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaBoundaryStackFamily
open GammaOrderLogic GammaFiniteGraphPartition GammaGraphPartitionEndpoints
open GammaCellSections GammaCellUnboundedSections GammaBoundaryStacks GammaBoundaryStackBases
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n : ℕ}

abbrev Label (N : ℕ) := Fin N ⊕ ((Fin N × Fin N) ⊕ (Fin N ⊕ (Fin N ⊕ Unit)))

def base (R : Set (Fin (n + 1) → Values.Gamma (M := M)))
    (P : FiniteGraphPartition B (GammaFamilyBoundary.Boundary R)) : Label P.size → Set (Fin n → Values.Gamma (M := M))
  | .inl i => pointBase R (P.domain i) (endpoint P i)
  | .inr (.inl (i, j)) => bandBase R (P.domain i ∩ P.domain j) (endpoint P i) (endpoint P j)
  | .inr (.inr (.inl i)) => upperBase R (P.domain i) (endpoint P i)
  | .inr (.inr (.inr (.inl i))) => lowerBase R (P.domain i) (endpoint P i)
  | .inr (.inr (.inr (.inr _))) => lineBase R Set.univ

def shape (R : Set (Fin (n + 1) → Values.Gamma (M := M)))
    (P : FiniteGraphPartition B (GammaFamilyBoundary.Boundary R))
    (label : Label P.size) (C : Set (Fin n → Values.Gamma (M := M))) : Set (Fin (n + 1) → Values.Gamma (M := M)) :=
  match label with
  | .inl i => graphCell C (endpoint P i)
  | .inr (.inl (i, j)) => bandCell C (endpoint P i) (endpoint P j)
  | .inr (.inr (.inl i)) => upperRayCell C (endpoint P i)
  | .inr (.inr (.inr (.inl i))) => lowerRayCell C (endpoint P i)
  | .inr (.inr (.inr (.inr _))) => lineCell C

def stack (R : Set (Fin (n + 1) → Values.Gamma (M := M)))
    (P : FiniteGraphPartition B (GammaFamilyBoundary.Boundary R)) (label : Label P.size) :=
  shape R P label (base R P label)

def dimensionRaise {N : ℕ} : Label N → ℕ
  | .inl _ => 0
  | .inr _ => 1

theorem base_definable (R : Set (Fin (n + 1) → Values.Gamma (M := M))) (hR : GammaDefinable B R)
    (P : FiniteGraphPartition B (GammaFamilyBoundary.Boundary R)) (label : Label P.size) : GammaDefinable B (base R P label) := by
  rcases label with i | (⟨i, j⟩ | (i | (i | u)))
  · exact pointBase_definable B R hR _ (P.domain_definable i) _ (endpoint_definable P i)
  · exact bandBase_definable B R hR _
      (GammaRelationLogic.inter_definable_base B _ _ (P.domain_definable i) (P.domain_definable j))
      _ _ (endpoint_definable P i) (endpoint_definable P j)
  · exact upperBase_definable B R hR _ (P.domain_definable i) _ (endpoint_definable P i)
  · exact lowerBase_definable B R hR _ (P.domain_definable i) _ (endpoint_definable P i)
  · exact lineBase_definable B R hR _ (GammaIntegerFamilies.univ_definable_base B n)

theorem shape_definable (R : Set (Fin (n + 1) → Values.Gamma (M := M)))
    (P : FiniteGraphPartition B (GammaFamilyBoundary.Boundary R)) (label : Label P.size)
    (C : Set (Fin n → Values.Gamma (M := M))) (hC : GammaDefinable B C) : GammaDefinable B (shape R P label C) := by
  rcases label with i | (⟨i, j⟩ | (i | (i | u)))
  · exact GammaPartialCellDefinability.graph_definable B C hC _ (endpoint_definable P i)
  · exact GammaPartialCellDefinability.band_definable B C hC _ _ (endpoint_definable P i) (endpoint_definable P j)
  · exact GammaPartialCellDefinability.upperRay_definable B C hC _ (endpoint_definable P i)
  · exact GammaPartialCellDefinability.lowerRay_definable B C hC _ (endpoint_definable P i)
  · exact GammaPartialCellDefinability.line_definable B C hC

theorem stack_definable (R : Set (Fin (n + 1) → Values.Gamma (M := M))) (hR : GammaDefinable B R)
    (P : FiniteGraphPartition B (GammaFamilyBoundary.Boundary R)) (label : Label P.size) : GammaDefinable B (stack R P label) :=
  shape_definable R P label _ (base_definable R hR P label)

theorem stack_subset (h00 : M ⊨ Axioms.ACVF00) (R : Set (Fin (n + 1) → Values.Gamma (M := M)))
    (hR : GammaDefinable B R) (P : FiniteGraphPartition B (GammaFamilyBoundary.Boundary R))
    (label : Label P.size) : stack R P label ⊆ R := by
  rcases label with i | (⟨i, j⟩ | (i | (i | u)))
  · exact pointStack_subset R (P.domain i) (endpoint P i)
  · exact bandStack_subset B R hR _ h00 _ _
  · exact upperStack_subset B R hR _ h00 _
  · exact lowerStack_subset B R hR _ h00 _
  · exact lineStack_subset B R hR _ h00

theorem shape_mono (R : Set (Fin (n + 1) → Values.Gamma (M := M)))
    (P : FiniteGraphPartition B (GammaFamilyBoundary.Boundary R)) (label : Label P.size)
    {C D : Set (Fin n → Values.Gamma (M := M))} (hCD : C ⊆ D) : shape R P label C ⊆ shape R P label D := by
  rcases label with i | (⟨i, j⟩ | (i | (i | u)))
  · exact fun _ hz => ⟨hCD hz.1, hz.2⟩
  · exact fun _ hz => ⟨hCD hz.1, hz.2⟩
  · exact fun _ hz => ⟨hCD hz.1, hz.2⟩
  · exact fun _ hz => ⟨hCD hz.1, hz.2⟩
  · exact fun _ hz => hCD hz

end DiamondIntegral.Section4.GammaBoundaryStackFamily
