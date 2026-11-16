import «section 6».PairedCenterOffsetMaps

/-! The actual union of all selected source cores is carried exactly
onto the selected target-core union by the original bijection. This uses
the whole-disc equality, including every center point. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.UniformFinitePairedCores
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r s : ℕ}
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S} {B : DefSet (rawMixedSpace (M := M) 1 s) S}
variable {f : Map A B} {E : DefSet (rawMixedSpace (M := M) 1 r) S} {hEA : E.carrier ⊆ A.carrier} {α β : Gamma M}
variable (D : UniformFinitePairedCores f E hEA α β)

def sourceCoreSet : Set (Mixed M 1 r) := {x | x ∈ A.carrier ∧ ∃ p : E,p.val.2=x.2 ∧
  vfValue ((D.sourceOffset p).val 0) < vfValue (x.1 0-p.val.1 0)}

def targetCoreSet : Set (Mixed M 1 s) := {y | y ∈ B.carrier ∧ ∃ p : E,
  (f ⟨p.val,hEA p.property⟩).val.2=y.2 ∧
    vfValue ((D.targetOffset p).val 0) < vfValue (y.1 0-(f ⟨p.val,hEA p.property⟩).val.1 0)}

theorem source_core_iff_target (hf : Function.Injective f) (x : A) :
    x.val ∈ D.sourceCoreSet ↔ (f x).val ∈ D.targetCoreSet := by
  constructor
  · rintro ⟨hx,p,hpu,hClose⟩
    have hDisc : x.val.1 0 ∈ centeredGammaDisc (p.val.1 0)
        (finiteValue ((D.sourceOffset p).val 0) (D.sourceNonzero p)) := (mem_centeredGammaDisc _ _ _).mpr hClose
    obtain ⟨hTarget,hLabels⟩ := (D.mixed_image_iff f E hEA α β p (f x)).mpr ⟨x,hDisc,hpu.symm,rfl⟩
    exact ⟨(f x).property,p,hLabels.symm,(mem_centeredGammaDisc _ _ _).mp hTarget⟩
  · rintro ⟨hy,p,hpu,hClose⟩
    have hDisc : (f x).val.1 0 ∈ centeredGammaDisc ((f ⟨p.val,hEA p.property⟩).val.1 0)
        (finiteValue ((D.targetOffset p).val 0) (D.targetNonzero p)) := (mem_centeredGammaDisc _ _ _).mpr hClose
    obtain ⟨a,ha,hau,haMap⟩ := (D.mixed_image_iff f E hEA α β p (f x)).mp ⟨hDisc,hpu.symm⟩
    have hEq : a=x := hf haMap
    subst a
    exact ⟨x.property,p,hau.symm,(mem_centeredGammaDisc _ _ _).mp ha⟩

theorem sourceCoreSet_eq_labelled
    (hUnique : ∀ p q : E,p.val.2=q.val.2 → p=q)
    (hA : ProperInvariant S A.carrier) (hAD : VFDoublyBounded A.carrier)
    (hTag : ∀ p ∈ A.carrier,∀ q ∈ A.carrier,p.2=q.2 → tupleRV M p.1=tupleRV M q.1) :
    D.sourceCoreSet=(labelledCenterCore E hUnique D.sourceOffset hEA hA hAD hTag).carrier := by
  ext x
  exact (mem_labelledCenterCore E hUnique D.sourceOffset hEA hA hAD hTag x).symm

theorem targetCoreSet_eq_labelled (hf : Function.Injective f)
    (hUnique : ∀ p q : matchedCenterImage f E hEA,p.val.2=q.val.2 → p=q)
    (hB : ProperInvariant S B.carrier) (hBD : VFDoublyBounded B.carrier)
    (hTag : ∀ p ∈ B.carrier,∀ q ∈ B.carrier,p.2=q.2 → tupleRV M p.1=tupleRV M q.1) :
    D.targetCoreSet=(labelledCenterCore (matchedCenterImage f E hEA) hUnique
      (matchedTargetOffsetMap f E hEA hf D.targetOffset) (matchedCenterImage_subset f E hEA) hB hBD hTag).carrier := by
  ext y
  rw [mem_labelledCenterCore]
  constructor
  · rintro ⟨hy,p,hpu,hClose⟩
    refine ⟨hy,matchedCenterMap f E hEA p,hpu,?_⟩
    simpa only [matchedTargetOffsetMap_at,matchedCenterMap_value] using hClose
  · rintro ⟨hy,q,hqu,hClose⟩
    obtain ⟨p,hp⟩ := (matchedCenterMap_bijective f E hEA hf).surjective q
    subst q
    refine ⟨hy,p,hqu,?_⟩
    simpa only [matchedTargetOffsetMap_at,matchedCenterMap_value] using hClose

end DiamondIntegral.Section6.UniformFinitePairedCores
