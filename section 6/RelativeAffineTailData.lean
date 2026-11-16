import «section 6».OriginalBaseAffineTailData

/-! For a relatively unary RV tail change, choose the target tail
centres equal to the source centres in every inactive coordinate. The
constructed determinant correction and exact Gamma identity are retained. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k m : ℕ}

def vfRelativeTargetMap {P : Space LRV M} {A : DefSet P S}
    (a b : Map A (DefSet.univ (rawVFSpace (M := M) m) S)) (j : Fin m) :
    Map A (DefSet.univ (rawVFSpace (M := M) m) S) :=
  vfTupleMap (fun l => (vfTupleSelectMap S (fun _ : Fin 1 => l)).comp (if l=j then b else a))

theorem vfRelativeTargetMap_value {P : Space LRV M} {A : DefSet P S}
    (a b : Map A (DefSet.univ (rawVFSpace (M := M) m) S)) (j : Fin m) (p : A) :
    (vfRelativeTargetMap a b j p).val=Function.update (a p).val j ((b p).val j) := by
  funext l
  by_cases hl : l=j
  · subst l
    simp only [vfRelativeTargetMap,vfTupleMap_apply,if_pos rfl,Function.update_self]
    rfl
  · simp only [vfRelativeTargetMap,vfTupleMap_apply,if_neg hl,Function.update_of_ne hl]
    rfl

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem exists_relative_fullAffineTailData_vfGenerated
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (S : LRV.Substructure M) (B : VFGeneratedFieldBase S) (hsmall : Cardinal.mk (S : Set M) < κ)
    {U V : MeasuredRVObject (M := M) (S : Set M) ((k+1)+m)} (e : MeasuredRVIso U V)
    (hU : (rvHeadVolume U.object (productLeft (k+1) m)).FiniteFibres)
    (hV : (rvHeadVolume V.object (productLeft (k+1) m)).FiniteFibres)
    (F : EverywhereMeasuredRVLift (measuredRVHeadIso hc e
      (productLeft (k+1) m) (productLeft (k+1) m) hU hV)) (j : Fin m)
    (hRelative : RVUnaryRelativeAt e.iso.hom.map (productRight (k+1) m j)) :
    ∃ T : FullAffineTailData (G := G) hc e hU hV F,
      ∀ p l,l ≠ j → (T.b p).val l=(T.a p).val l := by
  let T := Classical.choice (exists_fullAffineTailData_vfGenerated h00 hc hκ hs hv S B hsmall e hU hV F)
  let b := vfRelativeTargetMap T.a T.b j
  have hb (p) (l : Fin m) : (b p).val l=if l=j then (T.b p).val l else (T.a p).val l := by
    rw [vfRelativeTargetMap_value]
    by_cases hl : l=j
    · subst l
      simp only [Function.update_self,ite_true]
    · simp only [Function.update_of_ne hl,if_neg hl]
  have hbNZ (p) (l : Fin m) : (b p).val l ≠ 0 := by
    rw [hb]
    split_ifs
    · exact T.b_nonzero p l
    · exact T.a_nonzero p l
  have hTag (p) : liftLabelMap (measuredRVHead hc V (productLeft (k+1) m) hV).object (F.map p)=
      e.iso.hom.map (liftLabelMap (measuredRVHead hc U (productLeft (k+1) m) hU).object p) :=
    liftLabelMap_target_of_graph (measuredRVHeadIso hc e _ _ hU hV).iso.hom.map F.map F.labels p
  have hbRV (p) : tupleRV (b p).val=V.object.value
      (liftLabelMap (measuredRVHead hc V (productLeft (k+1) m) hV).object (F.map p)) ∘ productRight (k+1) m := by
    funext l
    change CanonicalRV.encodedRv ((b p).val l)=_
    rw [hb]
    by_cases hl : l=j
    · rw [if_pos hl]
      exact congrFun (T.b_rv p) l
    · rw [if_neg hl,hTag]
      exact (congrFun (T.a_rv p) l).trans (hRelative _ (productRight (k+1) m l)
        (fun he => hl ((productRight (k+1) m).injective he))).symm
  have hbVal (p) (l : Fin m) : Valued.v ((b p).val l)=Valued.v ((T.b p).val l) := by
    apply (vfValue_eq_iff Valued.v hv _ _).mp
    exact congrArg Values.vrv ((congrFun (hbRV p) l).trans (congrFun (T.b_rv p) l).symm)
  have hCorrection (p) : affineTailCorrectionGood Valued.v (T.a p).val (b p).val ((T.D p).val 0) ((T.c p).val 0) := by
    refine ⟨(T.correction p).1,?_⟩
    change Valued.v ((T.D p).val 0) * (∏ l,Valued.v ((b p).val l) / Valued.v ((T.a p).val l))=_
    simp_rw [hbVal]
    exact (T.correction p).2
  refine ⟨{T with b := b, b_nonzero := hbNZ, b_rv := hbRV, correction := hCorrection},fun p l hl => ?_⟩
  rw [hb,if_neg hl]

end DiamondIntegral.Section6
