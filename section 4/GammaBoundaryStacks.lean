import «section 4».GammaBoundaryStackBases
import «section 4».GammaBoundaryComponents

/-! Definable cylindrical stacks selected by an interior member and absence
of boundary points. Each stack is proved to lie in the original definable
set. Finite coverage and disjointness are separate assembly obligations. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaBoundaryStacks
open GammaOrderLogic GammaDefinableMaps GammaCellSections GammaCellUnboundedSections GammaPartialCellDefinability GammaBoundaryStackBases
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def pointBase {n : ℕ} (R : Set (Fin (n + 1) → Values.Gamma (M := M)))
    (C : Set (Fin n → Values.Gamma (M := M)))
    (T : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) := fibreBase (R ∩ graphCell C T)
def pointStack {n : ℕ} (R : Set (Fin (n + 1) → Values.Gamma (M := M)))
    (C : Set (Fin n → Values.Gamma (M := M)))
    (T : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) := graphCell (pointBase R C T) T
def bandStack {n : ℕ} (R : Set (Fin (n + 1) → Values.Gamma (M := M)))
    (C : Set (Fin n → Values.Gamma (M := M)))
    (l u : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) := bandCell (bandBase R C l u) l u
def upperStack {n : ℕ} (R : Set (Fin (n + 1) → Values.Gamma (M := M)))
    (C : Set (Fin n → Values.Gamma (M := M)))
    (l : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) := upperRayCell (upperBase R C l) l
def lowerStack {n : ℕ} (R : Set (Fin (n + 1) → Values.Gamma (M := M)))
    (C : Set (Fin n → Values.Gamma (M := M)))
    (u : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) := lowerRayCell (lowerBase R C u) u
def lineStack {n : ℕ} (R : Set (Fin (n + 1) → Values.Gamma (M := M)))
    (C : Set (Fin n → Values.Gamma (M := M))) := lineCell (lineBase R C)

variable (B : Base (M := M)) {n : ℕ}
variable (R : Set (Fin (n + 1) → Values.Gamma (M := M))) (hR : GammaDefinable B R)
variable (C : Set (Fin n → Values.Gamma (M := M))) (hC : GammaDefinable B C)
include hR hC

theorem pointBase_definable (T : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hT : MapDefinable B T) : GammaDefinable B (pointBase R C T) :=
  fibreBase_definable B _ (GammaRelationLogic.inter_definable_base B _ _ hR (graph_definable B C hC T hT))
theorem pointStack_definable (T : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hT : MapDefinable B T) : GammaDefinable B (pointStack R C T) :=
  graph_definable B _ (pointBase_definable B R hR C hC T hT) T hT
theorem bandBase_definable (l u : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hl : MapDefinable B l) (hu : MapDefinable B u) : GammaDefinable B (bandBase R C l u) :=
  GammaRelationLogic.inter_definable_base B _ _
    (GammaRelationLogic.inter_definable_base B _ _ hC (GammaMapOrder.lt_maps_definable B _ _ hl hu))
    (activeBase_definable B R _ hR (band_definable B C hC l u hl hu))
theorem bandStack_definable (l u : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hl : MapDefinable B l) (hu : MapDefinable B u) : GammaDefinable B (bandStack R C l u) :=
  band_definable B _ (bandBase_definable B R hR C hC l u hl hu) l u hl hu
theorem upperBase_definable (l : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hl : MapDefinable B l) : GammaDefinable B (upperBase R C l) :=
  GammaRelationLogic.inter_definable_base B _ _ hC
    (activeBase_definable B R _ hR (upperRay_definable B C hC l hl))
theorem upperStack_definable (l : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hl : MapDefinable B l) : GammaDefinable B (upperStack R C l) :=
  upperRay_definable B _ (upperBase_definable B R hR C hC l hl) l hl
theorem lowerBase_definable (u : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hu : MapDefinable B u) : GammaDefinable B (lowerBase R C u) :=
  GammaRelationLogic.inter_definable_base B _ _ hC
    (activeBase_definable B R _ hR (lowerRay_definable B C hC u hu))
theorem lowerStack_definable (u : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hu : MapDefinable B u) : GammaDefinable B (lowerStack R C u) :=
  lowerRay_definable B _ (lowerBase_definable B R hR C hC u hu) u hu
theorem lineBase_definable : GammaDefinable B (lineBase R C) :=
  GammaRelationLogic.inter_definable_base B _ _ hC (activeBase_definable B R _ hR (line_definable B C hC))
theorem lineStack_definable : GammaDefinable B (lineStack R C) :=
  line_definable B _ (lineBase_definable B R hR C hC)

omit hR hC
theorem pointStack_subset (T : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) : pointStack R C T ⊆ R := by
  intro z hz
  obtain ⟨t, htR, htC, he⟩ := (mem_fibreBase (R ∩ graphCell C T) (Fin.tail z)).mp hz.1
  change t = T (Fin.tail z) at he
  have hr : Fin.cons (z 0) (Fin.tail z) ∈ R := by
    rw [hz.2, ← he]
    exact htR
  simpa only [Fin.cons_self_tail] using hr

variable (h00 : M ⊨ Axioms.ACVF00)
include h00 hR

theorem bandStack_subset (l u : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) : bandStack R C l u ⊆ R := by
  apply GammaBoundaryComponents.band_subset h00 B R hR (bandBase R C l u) l u
  · intro y hy t hlt htu
    exact ((mem_activeBase R (bandCell C l u) y).mp hy.2).2 t ⟨hy.1.1, hlt, htu⟩
  · intro y hy
    obtain ⟨t, htR, htC, hlt, htu⟩ := ((mem_activeBase R (bandCell C l u) y).mp hy.2).1
    exact ⟨t, hlt, htu, htR⟩

theorem upperStack_subset (l : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) : upperStack R C l ⊆ R := by
  apply GammaBoundaryComponents.upperRay_subset h00 B R hR (upperBase R C l) l
  · intro y hy t hlt
    exact ((mem_activeBase R (upperRayCell C l) y).mp hy.2).2 t ⟨hy.1, hlt⟩
  · intro y hy
    obtain ⟨t, htR, htC, hlt⟩ := ((mem_activeBase R (upperRayCell C l) y).mp hy.2).1
    exact ⟨t, hlt, htR⟩

theorem lowerStack_subset (u : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) : lowerStack R C u ⊆ R := by
  apply GammaBoundaryComponents.lowerRay_subset h00 B R hR (lowerBase R C u) u
  · intro y hy t htu
    exact ((mem_activeBase R (lowerRayCell C u) y).mp hy.2).2 t ⟨hy.1, htu⟩
  · intro y hy
    obtain ⟨t, htR, htC, htu⟩ := ((mem_activeBase R (lowerRayCell C u) y).mp hy.2).1
    exact ⟨t, htu, htR⟩

theorem lineStack_subset : lineStack R C ⊆ R := by
  apply GammaBoundaryComponents.line_subset h00 B R hR (lineBase R C)
  · intro y hy t
    exact ((mem_activeBase R (lineCell C) y).mp hy.2).2 t hy.1
  · intro y hy
    obtain ⟨t, htR, htC⟩ := ((mem_activeBase R (lineCell C) y).mp hy.2).1
    exact ⟨t, htR⟩

end DiamondIntegral.Section4.GammaBoundaryStacks
