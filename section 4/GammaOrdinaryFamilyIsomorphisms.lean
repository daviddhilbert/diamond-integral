import «section 4».GammaOrdinaryFiniteFamilies
import «section 4».FiniteFamilyBijections

/-! Actual original-base RV-contracted bijections between finite formally
labelled Gamma unions split into matching chart isomorphisms. There is no volume condition. Both the
Gamma bijection and its RV lift are actual equivalences of the tagged
sets, with definability on each finite component graph. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaOrdinaryFamilyIsomorphisms
open GammaOrdinaryCharts GammaRVChartPresentation GammaOrdinaryFiniteFamilies GammaOrdinaryFinitePartitions
open GammaOrderLogic FiniteFamilyBijections
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

abbrev gammaDomain {B : Base (M := M)} {ι : Type*} {n : ℕ} (a : ι → Chart B n) :=
  Domain (fun i => (a i).support)
abbrev rvDomain {B : Base (M := M)} {ι : Type*} {n : ℕ} (a : ι → Chart B n) :=
  Domain (fun i => sharp (a i).support)

def codeDomain {B : Base (M := M)} {ι : Type*} {n : ℕ} (a : ι → Chart B n) : rvDomain a → gammaDomain a :=
  mapDomain codeValues (fun _ _ h => h.2)

structure Iso {B : Base (M := M)} {ι κ : Type*} {n : ℕ} (a : ι → Chart B n) (b : κ → Chart B n) where
  equiv : gammaDomain a ≃ gammaDomain b
  lift : rvDomain a ≃ rvDomain b
  source_definable : ∀ i j, GammaDefinable B (sourcePiece equiv i j)
  target_definable : ∀ i j, GammaDefinable B (targetPiece equiv i j)
  graph_definable : ∀ i j, GammaDefinable B
    (GammaBijectiveRelations.graphOn (sourcePiece equiv i j) (pieceMap equiv (fun _ => 1) i))
  lift_definable : ∀ i j, DefinableOverBase B (fun _ : Fin (n + n) => .rv)
    (rawGraphOn (sourcePiece equiv i j) (pieceMap lift (fun _ => iRVZero) i))
  contraction : ∀ p, codeDomain b (lift p) = equiv (codeDomain a p)

theorem sourcePiece_lift {B : Base (M := M)} {ι κ : Type*} {n : ℕ}
    {a : ι → Chart B n} {b : κ → Chart B n} (f : Iso a b) (i : ι) (j : κ) :
    sourcePiece f.lift i j = sharp (sourcePiece f.equiv i j) := by
  rw [sourcePiece_pullback f.lift f.equiv codeValues codeValues
    (fun _ _ h => h.2) (fun _ _ h => h.2) f.contraction]
  ext z
  change (z ∈ sharp (a i).support ∧ codeValues z ∈ sourcePiece f.equiv i j) ↔
    Proper z ∧ codeValues z ∈ sourcePiece f.equiv i j
  constructor
  · intro h
    exact ⟨h.1.1, h.2⟩
  · intro h
    exact ⟨⟨h.1, sourcePiece_subset f.equiv i j h.2⟩, h.2⟩

theorem targetPiece_lift {B : Base (M := M)} {ι κ : Type*} {n : ℕ}
    {a : ι → Chart B n} {b : κ → Chart B n} (f : Iso a b) (i : ι) (j : κ) :
    targetPiece f.lift i j = sharp (targetPiece f.equiv i j) := by
  rw [targetPiece_pullback f.lift f.equiv codeValues codeValues
    (fun _ _ h => h.2) (fun _ _ h => h.2) f.contraction]
  ext z
  change (z ∈ sharp (b j).support ∧ codeValues z ∈ targetPiece f.equiv i j) ↔
    Proper z ∧ codeValues z ∈ targetPiece f.equiv i j
  constructor
  · intro h
    exact ⟨h.1.1, h.2⟩
  · intro h
    exact ⟨⟨h.1, sourcePiece_subset f.equiv.symm j i h.2⟩, h.2⟩

def pieceIso {B : Base (M := M)} {ι κ : Type*} {n : ℕ}
    {a : ι → Chart B n} {b : κ → Chart B n} (f : Iso a b) (i : ι) (j : κ) :
    GammaOrdinaryCharts.Iso (restrict (a i) (sourcePiece f.equiv i j) (f.source_definable i j))
      (restrict (b j) (targetPiece f.equiv i j) (f.target_definable i j)) where
  map := pieceMap f.equiv (fun _ => 1) i
  graph_definable := f.graph_definable i j
  bijective := pieceMap_bijOn f.equiv (fun _ => 1) i j
  lift := pieceMap f.lift (fun _ => iRVZero) i
  lift_definable := f.lift_definable i j
  lift_bijective := by
    have h := pieceMap_bijOn f.lift (fun _ => iRVZero) i j
    rw [sourcePiece_lift f i j, targetPiece_lift f i j] at h
    exact h
  contraction := by
    intro z hz
    have ha : z ∈ sharp (a i).support := ⟨hz.1, sourcePiece_subset f.equiv i j hz.2⟩
    change codeValues (pieceMap f.lift (fun _ => iRVZero) i z) = pieceMap f.equiv (fun _ => 1) i (codeValues z)
    rw [pieceMap_on f.lift (fun _ => iRVZero) i z ha,
      pieceMap_on f.equiv (fun _ => 1) i (codeValues z) ha.2]
    exact congrArg (fun q : gammaDomain b => q.val.2) (f.contraction ⟨(i, z), ha⟩)

def partitionIso {B : Base (M := M)} {ι κ : Type*} [Fintype ι] [Fintype κ] {n : ℕ}
    {a : ι → Chart B n} {b : κ → Chart B n} (f : Iso a b) : PartitionIso a b where
  sourcePiece := sourcePiece f.equiv
  targetPiece := targetPiece f.equiv
  source_definable := f.source_definable
  target_definable := f.target_definable
  source_disjoint := fun i _ _ h => sourcePiece_disjoint f.equiv i h
  target_disjoint := fun j _ _ h => sourcePiece_disjoint f.equiv.symm j h
  source_cover i := by simpa only [support, GammaRVFinitePartitions.support, Finset.mem_univ, Set.iUnion_true] using sourcePiece_cover f.equiv i
  target_cover j := by simpa only [support, GammaRVFinitePartitions.support, targetPiece, Finset.mem_univ, Set.iUnion_true] using sourcePiece_cover f.equiv.symm j
  pieceIso := pieceIso f

theorem familyClass_iso {B : Base (M := M)} {ι κ : Type*} [Fintype ι] [Fintype κ] {n : ℕ}
    {a : ι → Chart B n} {b : κ → Chart B n} (f : Iso a b) : familyClass a = familyClass b :=
  familyClass_partitionIso (partitionIso f)

end DiamondIntegral.Section4.GammaOrdinaryFamilyIsomorphisms
