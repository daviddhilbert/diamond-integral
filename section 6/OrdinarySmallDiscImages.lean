import «section 6».OrdinaryChainSmallDiscTags
import «section 6».PairedCenteredDiscs

/-! Exact RV-pullback geometry of every sufficiently small whole zero
disc carried by an ordinary unary chain. The endpoint field identity
and complete retained-tag formula establish saturation of the full image. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S R : Set M} {r s : ℕ}
variable {A : SpecialTransformations.Section5.DefSet (M := M) R 1 r}
variable {B : SpecialTransformations.Section5.DefSet (M := M) R 1 s}

def ordinaryZeroDiscImage (T : SpecialTransformations.Section5.Chain R 1 A B)
    (γ : Gamma M) (u : Fin r → RVInfinity M) : Set (Mixed M 1 s) :=
  {q | ∃ p : A,p.val.1 0 ∈ centeredGammaDisc (0 : VF M) γ ∧ p.val.2=u ∧ (T.toMap p).val=q}

theorem ordinary_zero_disc_image_rvPullback_of_formula
    (T : SpecialTransformations.Section5.Chain R 1 A B) (γ : Gamma M) (u : Fin r → RVInfinity M)
    (hBall : ∀ x ∈ centeredGammaDisc (0 : VF M) γ,
      ((fun _ : Fin 1 => x),u) ∈ SpecialTransformations.Section5.carrier A)
    (hFormula : ∀ p : A,p.val.1 0 ∈ centeredGammaDisc (0 : VF M) γ →
      (T.toMap p).val.1=p.val.1 ∧
      (T.toMap p).val.2=ordinaryChainZeroDiscTags T (tupleRV M p.val.1) p.val.2) :
    IsRVPullback (ordinaryZeroDiscImage T γ u) := by
  apply Set.Subset.antisymm _ (subset_rvHull _)
  intro q hq
  obtain ⟨p,hp,hVF,hRV⟩ := (mem_rvHull_iff (ordinaryZeroDiscImage T γ u) q).mp hq
  obtain ⟨a,haDisc,haTags,haMap⟩ := hp
  obtain ⟨haField,haEndTags⟩ := hFormula a haDisc
  have hpField : p.1=a.val.1 := (congrArg Prod.fst haMap).symm.trans haField
  rw [hpField] at hVF
  have hVal : vfValue (q.1 0)=vfValue (a.val.1 0) := congrArg Values.vrv (congrFun hVF 0).symm
  have hqDisc : q.1 0 ∈ centeredGammaDisc (0 : VF M) γ := by
    apply (mem_centeredGammaDisc _ _ _).mpr
    have hh := (mem_centeredGammaDisc (0 : VF M) _ γ).mp haDisc
    simpa only [sub_zero,hVal] using hh
  have hEta : (fun _ : Fin 1 => q.1 0)=q.1 := by funext i; fin_cases i; rfl
  have hbA : (q.1,u) ∈ SpecialTransformations.Section5.carrier A := by
    simpa only [hEta] using hBall (q.1 0) hqDisc
  let b : A := ⟨(q.1,u),hbA⟩
  obtain ⟨hbField,hbTags⟩ := hFormula b hqDisc
  refine ⟨b,hqDisc,rfl,Prod.ext hbField ?_⟩
  calc
    (T.toMap b).val.2=ordinaryChainZeroDiscTags T (tupleRV M q.1) u := hbTags
    _=ordinaryChainZeroDiscTags T (tupleRV M a.val.1) u := congrArg (fun t => ordinaryChainZeroDiscTags T t u) hVF.symm
    _=(T.toMap a).val.2 := by rw [haEndTags,haTags]
    _=p.2 := congrArg (fun z : Mixed M 1 s => z.2) haMap
    _=q.2 := hRV

theorem ordinary_chain_small_zero_disc_images_rvPullback
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal} (hs : Saturated M κ)
    (hsmall : Cardinal.mk S < κ)
    (T : SpecialTransformations.Section5.Chain R 1 A B)
    (hT : SpecialTransformations.Section5.GammaChainDefinable (ordinaryNamedGammaBase S) T) :
    ∃ η : Gamma M,1 ≤ η ∧ ∀ γ : Gamma M,η ≤ γ → ∀ u : Fin r → RVInfinity M,
      (∀ x ∈ centeredGammaDisc (0 : VF M) γ,
        ((fun _ : Fin 1 => x),u) ∈ SpecialTransformations.Section5.carrier A) →
      IsRVPullback (ordinaryZeroDiscImage T γ u) := by
  obtain ⟨η,hη1,hFormula⟩ := ordinary_chain_whole_zero_disc_formula hc hs hsmall T hT
  refine ⟨η,hη1,fun γ hηγ u hBall => ordinary_zero_disc_image_rvPullback_of_formula T γ u hBall ?_⟩
  intro p hpDisc
  have hh := (mem_centeredGammaDisc (0 : VF M) (p.val.1 0) γ).mp hpDisc
  have hVal : γ.val < vfValue (p.val.1 0) := by simpa only [sub_zero] using hh
  exact hFormula p ((show η.val ≤ γ.val from hηγ).trans_lt hVal)

end DiamondIntegral.Section6
