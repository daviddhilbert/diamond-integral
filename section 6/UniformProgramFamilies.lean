import «section 6».ProgramPrimitiveImages
import «section 6».UnaryParameterFreezing

/-! Uniform data for the remaining finite fusion program. Removing
an admissible prefix or freezing the unary parameter retains actual
local geometry, full preparation, all RV rows and their named bound. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s t v k : ℕ}
variable {B : DefSet (rawMixedSpace (M := M) 1 r) S}

theorem CentripetalProgramTemplate.preparedGood_comp
    (F : CentripetalProgramTemplate (M := M) S 1 n s t)
    (H : CentripetalProgramTemplate (M := M) S 1 n t v)
    (A : MixedSetParameterTemplate (M := M) S 1 n s)
    (P : Fin k → MixedSetParameterTemplate (M := M) S 1 n s) :
    (F.comp H).preparedGood A P=F.good A P ∩
      H.preparedGood (F.target A) (fun i => F.pieceTarget A (P i)) := by
  simp only [preparedGood,good,pieceTarget_comp,Set.inter_assoc]

structure UniformProgramFamily
    (η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S))
    (T : CentripetalProgramTemplate (M := M) S 1 n s t)
    (A : MixedSetParameterTemplate (M := M) S 1 n s)
    (P : Fin k → MixedSetParameterTemplate (M := M) S 1 n s) where
  geometry : ∀ b : B,TemplateFibreGeometry A P (unaryFamilyParameter η b)
  pullback : ∀ b : B,IsRVPullback (A.fibre (unaryFamilyParameter η b)).carrier
  prepared : ∀ b : B,unaryFamilyParameter η b ∈ T.preparedGood A P
  rows : ∀ D ∈ T.rvTrace A P,∀ b c : B,b.val.2=c.val.2 →
    (D.2.fibre (unaryFamilyParameter η b)).carrier=(D.2.fibre (unaryFamilyParameter η c)).carrier
  radius : Gamma M
  named : S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {radius}}
  bound : ∀ D ∈ T.rvTrace A P,∀ b : B,∀ u ∈ (D.2.fibre (unaryFamilyParameter η b)).carrier,
    ∀ i,(radius⁻¹).val ≤ Values.vrv (u i) ∧ Values.vrv (u i) ≤ radius.val

namespace UniformProgramFamily
variable {η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S)}
variable {T : CentripetalProgramTemplate (M := M) S 1 n s t}
variable {A : MixedSetParameterTemplate (M := M) S 1 n s}
variable {P : Fin k → MixedSetParameterTemplate (M := M) S 1 n s}

def freeze {q : ℕ} {C : DefSet (rawMixedSpace (M := M) (n+1) q) S}
    (U : UniformProgramFamily η T A P) (D : FMT.FocusFreezingData C)
    (hB : ∀ E : D.balls,FMT.CoordinateProductDomain B.carrier (FMT.vfOpenBall E.val) (D.centers E) 0) :
    UniformProgramFamily (D.unaryParameter hB η) T A P where
  geometry b := U.geometry (D.unaryBaseFreeze hB b)
  pullback b := U.pullback (D.unaryBaseFreeze hB b)
  prepared := D.unaryParameter_good hB η _ U.prepared
  rows V hV := D.unaryParameter_rows_constant hB η V.2 (U.rows V hV)
  radius := U.radius
  named := U.named
  bound V hV := D.unaryParameter_bound hB η V.2 U.radius (U.bound V hV)

theorem identity_prepared {A : MixedSetParameterTemplate (M := M) S 1 n s}
    {P : Fin k → MixedSetParameterTemplate (M := M) S 1 n s}
    (U : UniformProgramFamily η (.identity s) A P) :
    ∀ b : B,∀ i,IsRVPullback ((P i).fibre (unaryFamilyParameter η b)).carrier :=
  fun b => (identity_preparedGood_iff A P _ (U.geometry b).subset).mp (U.prepared b)

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

def afterPrefix
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {F : CentripetalProgramTemplate (M := M) S 1 n s t}
    {H : CentripetalProgramTemplate (M := M) S 1 n t v}
    (U : UniformProgramFamily η (F.comp H) A P) :
    UniformProgramFamily η H (F.target A) (fun i => F.pieceTarget A (P i)) := by
  have hGood (b : B) : unaryFamilyParameter η b ∈ F.good A P ∧
      unaryFamilyParameter η b ∈ H.preparedGood (F.target A) (fun i => F.pieceTarget A (P i)) := by
    have h := U.prepared b
    rw [CentripetalProgramTemplate.preparedGood_comp] at h
    exact h
  have hReal (b : B) := F.exists_realization h00 hc hκ hs hv A P _ (hGood b).1
    (U.geometry b).proper (U.geometry b).doublyBounded (U.geometry b).subset (U.geometry b).piecesProper
  let R (b : B) := Classical.choice (hReal b)
  exact {
    geometry := fun b => (R b).outputGeometry h00 hc hκ hs hv (U.geometry b)
    pullback := fun b => (R b).output_rvPullback h00 (U.pullback b)
    prepared := fun b => (hGood b).2
    rows := fun D hD => U.rows D (List.mem_append.mpr (Or.inr hD))
    radius := U.radius
    named := U.named
    bound := fun D hD => U.bound D (List.mem_append.mpr (Or.inr hD)) }

end UniformProgramFamily
end DiamondIntegral.Section6
