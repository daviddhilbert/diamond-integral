import «section 6».SelectedJointDomains
import «section 6».UnaryIndexedFrozenFamilies

/-! Product conditions transfer from the prepared unary base and
the joint ambient to the actual source carrying extra RV labels.
Consequently one continuity repair preserves its complete protected sets. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s q : ℕ}

theorem selectedUnaryBasePoint_update_zero (π : Fin r → Fin q)
    (p : Mixed M (n+1) q) (c : VF M) :
    selectedUnaryBasePoint π (Function.update p.1 0 c,p.2)=
      (Function.update (selectedUnaryBasePoint π p).1 0 c,(selectedUnaryBasePoint π p).2) := by
  apply Prod.ext
  · funext i
    fin_cases i
    simp only [selectedUnaryBasePoint,Function.update_self]
    change c=Function.update (fun _ : Fin 1 => p.1 0) 0 c 0
    rw [Function.update_self]
  · rfl

theorem selectRVPoint_update (σ : Fin r → Fin s) (p : Mixed M n s) (j : Fin n) (c : VF M) :
    selectRVPoint σ (Function.update p.1 j c,p.2)=
      (Function.update (selectRVPoint σ p).1 j c,(selectRVPoint σ p).2) := rfl

theorem unary_base_product_of_tagged_pullback
    (B : DefSet (rawMixedSpace (M := M) 1 r) S)
    (C : DefSet (rawMixedSpace (M := M) (n+1) q) S) (π : Fin r → Fin q)
    (hC : IsRVPullback C.carrier)
    (hSource : ∀ p ∈ C.carrier,selectedUnaryBasePoint π p ∈ B.carrier)
    (hTag : ∀ b ∈ B.carrier,∀ d ∈ B.carrier,b.2=d.2 → tupleRV M b.1=tupleRV M d.1)
    (D : Set (VF M)) (c : VF M) (hB : FMT.CoordinateProductDomain B.carrier D c 0) :
    FMT.CoordinateProductDomain C.carrier D c 0 := by
  intro p hpD
  let z : Mixed M (n+1) q := (Function.update p.1 0 c,p.2)
  have hBase : selectedUnaryBasePoint π p ∈ B.carrier ↔ selectedUnaryBasePoint π z ∈ B.carrier := by
    rw [selectedUnaryBasePoint_update_zero]
    exact hB (selectedUnaryBasePoint π p) hpD
  have hRV (hp : selectedUnaryBasePoint π p ∈ B.carrier)
      (hz : selectedUnaryBasePoint π z ∈ B.carrier) : tupleRV M p.1=tupleRV M z.1 := by
    have h := congrFun (hTag _ hp _ hz rfl) 0
    change rv M (p.1 0)=rv M (Function.update p.1 0 c 0) at h
    funext i
    by_cases hi : i=0
    · subst i
      exact h
    · change rv M (p.1 i)=rv M (Function.update p.1 0 c i)
      rw [Function.update_of_ne hi]
  constructor
  · intro hp
    have hpB := hSource p hp
    exact rvPullback_mem_of_sameRV hC hp (hRV hpB (hBase.mp hpB)) rfl
  · intro hz
    have hzB := hSource z hz
    exact rvPullback_mem_of_sameRV hC hz (hRV (hBase.mpr hzB) hzB).symm rfl

theorem rvLabelPullback_product
    (C : DefSet (rawMixedSpace (M := M) n s) S) (σ : Fin r → Fin s)
    (Q : DefSet (rawMixedSpace (M := M) n r) S)
    (D : Set (VF M)) (c : VF M) (j : Fin n)
    (hC : FMT.CoordinateProductDomain C.carrier D c j)
    (hQ : FMT.CoordinateProductDomain Q.carrier D c j) :
    FMT.CoordinateProductDomain (rvLabelPullback C σ Q).carrier D c j := by
  intro p hpD
  rw [mem_rvLabelPullback,mem_rvLabelPullback,selectRVPoint_update]
  exact and_congr (hC p hpD) (hQ (selectRVPoint σ p) hpD)

theorem selected_joint_family_preserved_by_freezing
    {Z : DefSet (rawMixedSpace (M := M) (n+1) s) S} (F : FMT.FocusFreezingData Z)
    {B : DefSet (rawMixedSpace (M := M) 1 r) S}
    (hB : ∀ E : F.balls,FMT.CoordinateProductDomain B.carrier (FMT.vfOpenBall E.val) (F.centers E) 0)
    (η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S))
    {t : ℕ} (T : MixedSetParameterTemplate (M := M) S 1 n t)
    (C : DefSet (rawMixedSpace (M := M) (n+1) q) S) (π : Fin r → Fin q) (σ : Fin t → Fin q)
    (hC : ∀ E : F.balls,FMT.CoordinateProductDomain C.carrier (FMT.vfOpenBall E.val) (F.centers E) 0)
    (hQ : ∀ E : F.balls,FMT.CoordinateProductDomain
      (rvLabelPullback C (Fin.addCases π σ) (unaryIndexedMixedFamily η T)).carrier
      (FMT.vfOpenBall E.val) (F.centers E) 0) :
    rvLabelPullback C (Fin.addCases π σ) (unaryIndexedMixedFamily (F.unaryParameter hB η) T)=
      rvLabelPullback C (Fin.addCases π σ) (unaryIndexedMixedFamily η T) := by
  apply defSet_eq_of_carrier_eq
  ext p
  rw [mem_rvLabelPullback,mem_rvLabelPullback,F.unaryIndexed_mem_iff_freeze hB η T]
  have hCAt := FMT.mixedFamilyFreeze_mem_iff F.balls F.centers 0 F.separated C.carrier hC p
  have hQAt := FMT.mixedFamilyFreeze_mem_iff F.balls F.centers 0 F.separated
    (rvLabelPullback C (Fin.addCases π σ) (unaryIndexedMixedFamily η T)).carrier hQ p
  have hQAt' := ((mem_rvLabelPullback C (Fin.addCases π σ) (unaryIndexedMixedFamily η T)
    (FMT.mixedFamilyFreeze F.balls F.centers 0 p)).symm.trans hQAt).trans
      (mem_rvLabelPullback C (Fin.addCases π σ) (unaryIndexedMixedFamily η T) p)
  have hCommute : selectRVPoint (Fin.addCases π σ) (FMT.mixedFamilyFreeze F.balls F.centers 0 p)=
      FMT.mixedFamilyFreeze F.balls F.centers 0 (selectRVPoint (Fin.addCases π σ) p) := rfl
  rw [hCommute] at hQAt'
  exact (and_congr hCAt.symm Iff.rfl).trans hQAt'

end DiamondIntegral.Section6
