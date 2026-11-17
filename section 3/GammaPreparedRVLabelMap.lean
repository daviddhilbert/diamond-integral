import «section 3».GammaSpecialDensityTransport
import «section 3».GammaNativePullbackForms

/-! Prepared RV full keys recover every original label by an explicit
coordinate projection. Arbitrary original Gamma densities can therefore
be attached to the entire actual chain output. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.Section4.rawRVSpace
  SpecialTransformations.Section4.realSpace SpecialTransformations.DefinableGeometry.Space.ofEmbedding
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n l : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

def gammaPreparedRVLabelMap
    (U : GammaObjectAt B Set.univ n)
    {A : SpecialTransformations.Section5.DefSet (M := M) Set.univ n (rvObjectArity U.object.obj)}
    {D : SpecialTransformations.Section5.DefSet (M := M) Set.univ n l}
    (h : @PresentsLift M N hN Set.univ n U.object.obj (normalizedPointSet A))
    (T : SpecialBijection A D) (hT : GammaChainDefinable B T.chain)
    (hDF : SpecialTransformations.Section5.Map.FiniteFibres (rvObjectVolume (pullbackObject D))) :
    GammaGroundMap (Section5.nativeRVGroundDomain
      (gammaPullbackAt (Set.subset_univ _) D (GammaChainDefinable.target B T.chain hT) hDF))
      (Section5.nativeRVGroundDomain (hc := hc) U) :=
  (gammaGroundRVSelectCoordinates (fun j => Fin.natAdd n (gammaChainOldLabelIndex T.chain j))
    (Section5.nativeRVGroundDomain
      (gammaPullbackAt (Set.subset_univ _) D (GammaChainDefinable.target B T.chain hT) hDF))).corestrict (fun q => by
        let hD := GammaChainDefinable.target B T.chain hT
        obtain ⟨p,hp⟩ := gammaNativePullbackKeyMap_surjective D hD hDF q
        let a : A := T.inverseMap ⟨p.val,p.property⟩
        obtain ⟨u,hu,_⟩ := (h a.val).mp a.property
        apply (Section5.nativeRVGroundDomain_carrier U).ge
        have hq : q.val = Fin.append (Section2.tupleRV M p.val.1) p.val.2 := by
          have hh := (congrArg Subtype.val hp).symm
          change q.val = (Section5.nativeMixedFullKeyMap (Section5.nativeGammaPointDomain (carrier D) hD) p).val at hh
          exact hh.trans (Section5.nativeMixedFullKeyMap_value _ p)
        have ha : a.val.2 = p.val.2 ∘ gammaChainOldLabelIndex T.chain := gammaSpecial_inverse_old_labels T ⟨p.val,p.property⟩
        change q.val ∘ (fun j => Fin.natAdd n (gammaChainOldLabelIndex T.chain j)) ∈
          (@DefSet.carrier LRV M N _ Set.univ (rvObjectDomain U.object.obj))
        have he : q.val ∘ (fun j => Fin.natAdd n (gammaChainOldLabelIndex T.chain j)) = u.val := by
          funext j
          rw [hq]
          exact (Fin.append_right _ _ _).trans ((congrFun ha j).symm.trans (congrFun hu.symm j))
        exact Eq.mp (congrArg (fun t : Fin (rvObjectArity U.object.obj) → CanonicalRV.RVSort M =>
          t ∈ (@DefSet.carrier LRV M N _ Set.univ (rvObjectDomain U.object.obj))) he.symm) u.property)

@[simp] theorem gammaPreparedRVLabelMap_val
    (U : GammaObjectAt B Set.univ n)
    {A : SpecialTransformations.Section5.DefSet (M := M) Set.univ n (rvObjectArity U.object.obj)}
    {D : SpecialTransformations.Section5.DefSet (M := M) Set.univ n l}
    (h : @PresentsLift M N hN Set.univ n U.object.obj (normalizedPointSet A))
    (T : SpecialBijection A D) (hT : GammaChainDefinable B T.chain)
    (hDF : SpecialTransformations.Section5.Map.FiniteFibres (rvObjectVolume (pullbackObject D)))
    (q : Section5.nativeRVGroundDomain (hc := hc)
      (gammaPullbackAt (Set.subset_univ _) D (GammaChainDefinable.target B T.chain hT) hDF)) :
    (gammaPreparedRVLabelMap U h T hT hDF q).val =
      q.val ∘ (fun j => Fin.natAdd n (gammaChainOldLabelIndex T.chain j)) := rfl

theorem gammaPreparedRVLabelMap_at_source
    (U : GammaObjectAt B Set.univ n)
    {A : SpecialTransformations.Section5.DefSet (M := M) Set.univ n (rvObjectArity U.object.obj)}
    {D : SpecialTransformations.Section5.DefSet (M := M) Set.univ n l}
    (h : @PresentsLift M N hN Set.univ n U.object.obj (normalizedPointSet A))
    (T : SpecialBijection A D) (hT : GammaChainDefinable B T.chain)
    (hDF : SpecialTransformations.Section5.Map.FiniteFibres (rvObjectVolume (pullbackObject D)))
    (p : Section5.nativeGammaPointDomain (hc := hc) (carrier A) (GammaChainDefinable.source B T.chain hT)) :
    (gammaPreparedRVLabelMap U h T hT hDF
      (gammaNativePullbackKeyMap D (GammaChainDefinable.target B T.chain hT) hDF
        ((gammaNativeSpecialBijection T hT).map p))).val = p.val.2 := by
  rw [gammaPreparedRVLabelMap_val]
  change Fin.append (Section2.tupleRV M ((gammaNativeSpecialBijection T hT).map p).val.1)
    ((gammaNativeSpecialBijection T hT).map p).val.2 ∘
      (fun j => Fin.natAdd n (gammaChainOldLabelIndex T.chain j)) = p.val.2
  funext j
  rw [Function.comp_apply,Fin.append_right,gammaNativeSpecialBijection_apply]
  exact congrFun (gammaChain_old_labels T.chain ⟨p.val,p.property⟩) j

end DiamondIntegral.Section3
