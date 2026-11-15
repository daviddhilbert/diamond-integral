import «section 5».Completed18RVGradedComparison
import «section 3».GammaGroundRVGenerators
import IntegrationSection6.GammaNonzeroBasicRelation

/-! The elementary relation in [18] is exactly the local positive
special relation, including the degree-zero contribution of RV infinity. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.Section4.rawRVSpace
  SpecialTransformations.Section4.realSpace SpecialTransformations.DefinableGeometry.Space.ofEmbedding
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
open DiamondIntegral.Section3 DiamondIntegral.Section4
namespace DiamondIntegral.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)
local instance : Fact (B.real ⊆ (Set.univ : Set M)) := ⟨Set.subset_univ _⟩

def completed18OneGroundBijection : GammaGroundBijection
    (GammaGroundRVObject.ofReal (hc := hc) (rvOneObject B.real)).domain
    (nativeRVGroundDomain (hc := hc) (gammaOneAt (B := B) (Set.subset_univ _))) := by
  let f := (rvRightTagMap (RVObject.unit (M := M) B.real).domain 0).toImage
  let e : GammaGroundBijection
      (GammaGroundDefSet.ofReal (hc := hc) (RVObject.unit (M := M) B.real).domain)
      (GammaGroundRVObject.ofReal (hc := hc) (rvOneObject B.real)).domain :=
    ⟨GammaGroundMap.ofReal f,rvRightTagMap_toImage_bijective _ _⟩
  let g : GammaGroundBijection
      (GammaGroundDefSet.ofReal (hc := hc) (RVObject.unit (M := M) B.real).domain)
      (nativeRVGroundDomain (hc := hc) (gammaOneAt (B := B) (Set.subset_univ _))) := by
    apply GammaGroundBijection.ofCarrierEq
    rw [nativeRVGroundDomain_carrier]
    rfl
  exact g.comp e.symm

theorem completed18Positive_domain :
    (nativeRVGroundDomain (hc := hc)
      (gammaHighRestrictionAt (gammaPositiveAt (B := B) (S := Set.univ) (Set.subset_univ _)))).carrier=
    (GammaGroundRVObject.ofReal (hc := hc) (rvPositiveObject hc B.real)).domain.carrier := by
  rw [nativeRVGroundDomain_carrier]
  ext t
  let u : Fin 1 → CanonicalRV.RVSort M := t
  rw [gammaPositiveNonzeroAt_domain]
  have hz : @iRVZero M N=@iRVZero M sM := CanonicalStructure.sortZero_normalize .rv
  have ho : @iRVOne M N=@iRVOne M sM :=
    CanonicalStructure.normalize_fun Fn.rvOne (fun i => i.elim0) (fun i => i.elim0)
  change (¬ @iLe M N (u 0).val (@iRVOne M N) ∧ (u 0).val≠@iRVZero M N) ↔
    ((u 0).val≠@iRVZero M sM ∧ @iLe M N (@iRVOne M sM) (u 0).val ∧
      ¬ @iLe M N (u 0).val (@iRVOne M sM))
  rw [hz,ho]
  constructor
  · rintro ⟨hl,hn⟩
    have hp : @iRV M N (@iRVOne M sM) := ho ▸ (@rv_one_mem M N hN)
    have ht := @RVCalc.le_total_rv M N hN (@iRVOne M sM) (u 0).val hp (u 0).property
    exact ⟨hn,ht.resolve_right hl,hl⟩
  · rintro ⟨hn,hl,hr⟩
    exact ⟨hr,hn⟩

theorem completed18RVPositiveEquiv_oneFactor :
    completed18RVPositiveEquiv (gammaGroundRVSemiringClass
      (GammaGroundRVObject.ofReal (hc := hc) (rvOneObject B.real)))=
      DirectSum.of (GammaNonzeroClassesAt (B := B) (S := Set.univ)) 1 gammaNonzeroOneClassAt := by
  rw [completed18RVPositiveEquiv_class]
  apply congrArg (DirectSum.of (GammaNonzeroClassesAt (B := B) (S := Set.univ)) 1)
  apply Subtype.ext
  exact gammaIsoClassAt_iso (groundRVAtToNativeIso _ _ (gammaOneAt_fullWeight _) completed18OneGroundBijection)

theorem completed18RVPositiveEquiv_positiveFactor :
    completed18RVPositiveEquiv (gammaGroundRVSemiringClass
      (GammaGroundRVObject.ofReal (hc := hc) (rvPositiveObject hc B.real)))=
      DirectSum.of (GammaNonzeroClassesAt (B := B) (S := Set.univ)) 1 gammaNonzeroPositiveClassAt := by
  rw [completed18RVPositiveEquiv_class]
  apply congrArg (DirectSum.of (GammaNonzeroClassesAt (B := B) (S := Set.univ)) 1)
  apply Subtype.ext
  exact gammaIsoClassAt_iso (groundRVAtToNativeIso _ _ (gammaHighRestriction_fullWeight _)
    (GammaGroundBijection.ofCarrierEq completed18Positive_domain.symm))

theorem completed18RVSpecial_iff (x y : GammaGroundRVPositiveSemiring hc B) :
    gammaGroundRVSpecialCongruence hc B x y ↔
      ringConGen (gammaNonzeroBasicRelation (B := B))
        (completed18RVPositiveEquiv x) (completed18RVPositiveEquiv y) := by
  let F := completed18RVPositiveEquiv (hc := hc) (B := B)
  let A := gammaGroundRVSemiringClass (GammaGroundRVObject.ofReal (hc := hc) (rvOneObject B.real))
  let C := gammaGroundRVSemiringClass (GammaGroundRVObject.ofReal (hc := hc) (rvPositiveObject hc B.real))+1
  let a := DirectSum.of (GammaNonzeroClassesAt (B := B) (S := Set.univ)) 1 gammaNonzeroOneClassAt
  let c := 1+DirectSum.of (GammaNonzeroClassesAt (B := B) (S := Set.univ)) 1 gammaNonzeroPositiveClassAt
  have ha : F A=a := completed18RVPositiveEquiv_oneFactor
  have hc' : F C=c := by
    let P : GammaGroundRVPositiveSemiring hc B := gammaGroundRVSemiringClass
      (GammaGroundRVObject.ofReal (hc := hc) (rvPositiveObject hc B.real))
    have hp : F P=DirectSum.of (GammaNonzeroClassesAt (B := B) (S := Set.univ)) 1 gammaNonzeroPositiveClassAt :=
      completed18RVPositiveEquiv_positiveFactor
    change F (P+1)=c
    exact (F.map_add P 1).trans ((congrArg₂ (· + ·) hp F.map_one).trans (add_comm _ _))
  let K := ringConGen (gammaNonzeroBasicRelation (B := B))
  let φ : GammaGroundRVPositiveSemiring hc B →+* K.Quotient := K.mk'.comp F.toRingHom
  have h₁ : gammaGroundRVSpecialCongruence hc B ≤ RingCon.ker φ := by
    apply RingCon.ringConGen_le.mpr
    rintro u v ⟨rfl,rfl⟩
    change K.mk' (F A)=K.mk' (F C)
    apply K.eq.mpr
    rw [ha,hc']
    exact RingConGen.Rel.of _ _ ⟨rfl,rfl⟩
  let J := gammaGroundRVSpecialCongruence hc B
  let ψ : GammaNonzeroGradedAt (B := B) (S := Set.univ) →+* J.Quotient := J.mk'.comp F.symm.toRingHom
  have h₂ : K ≤ RingCon.ker ψ := by
    apply RingCon.ringConGen_le.mpr
    rintro u v ⟨rfl,rfl⟩
    change J.mk' (F.symm a)=J.mk' (F.symm c)
    apply J.eq.mpr
    rw [← ha,← hc',F.symm_apply_apply,F.symm_apply_apply]
    exact RingConGen.Rel.of _ _ ⟨rfl,rfl⟩
  constructor
  · intro h
    exact K.eq.mp (h₁ h)
  · intro h
    have hh := J.eq.mp (h₂ h)
    change gammaGroundRVSpecialCongruence hc B (F.symm (F x)) (F.symm (F y)) at hh
    simpa only [F.symm_apply_apply] using hh

end DiamondIntegral.Section5
