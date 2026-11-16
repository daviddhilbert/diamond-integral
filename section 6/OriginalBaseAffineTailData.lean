import «section 6».EverywhereMeasuredLiftWeights
import «section 6».AffineLiftHeadJacobians
import Section9.VFCoordinateAssembly
import Section9.MixedJacobianValue

/-! Actual original-field-base centres and determinant corrections
for an affine tail over a given everywhere measured finite-head lift.
Every coefficient is constructed; no representative is an extra input. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M G : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable [LinearOrderedCommGroupWithZero G] [Valued (VF M) G] {S : Set M} {k m : ℕ}

structure FullAffineTailData (hc : CanonicalStructure.IsCanonical (M := M))
    {U V : MeasuredRVObject (M := M) S ((k+1)+m)} (e : MeasuredRVIso U V)
    (hU : (rvHeadVolume U.object (productLeft (k+1) m)).FiniteFibres)
    (hV : (rvHeadVolume V.object (productLeft (k+1) m)).FiniteFibres)
    (F : EverywhereMeasuredRVLift (measuredRVHeadIso hc e
      (productLeft (k+1) m) (productLeft (k+1) m) hU hV)) where
  a : Map (rvLift (measuredRVHead hc U (productLeft (k+1) m) hU).object)
    (DefSet.univ (rawVFSpace (M := M) m) S)
  b : Map (rvLift (measuredRVHead hc U (productLeft (k+1) m) hU).object)
    (DefSet.univ (rawVFSpace (M := M) m) S)
  D : Map (rvLift (measuredRVHead hc U (productLeft (k+1) m) hU).object)
    (DefSet.univ (rawVFSpace (M := M) 1) S)
  c : Map (rvLift (measuredRVHead hc U (productLeft (k+1) m) hU).object)
    (DefSet.univ (rawVFSpace (M := M) 1) S)
  a_nonzero : ∀ p i,(a p).val i ≠ 0
  b_nonzero : ∀ p i,(b p).val i ≠ 0
  a_rv : ∀ p,tupleRV (a p).val = U.object.value
    (liftLabelMap (measuredRVHead hc U (productLeft (k+1) m) hU).object p) ∘ productRight (k+1) m
  b_rv : ∀ p,tupleRV (b p).val = V.object.value
    (liftLabelMap (measuredRVHead hc V (productLeft (k+1) m) hV).object (F.map p)) ∘ productRight (k+1) m
  head_det : ∀ p L,HasMixedVFDerivativeAt F.map p L → (D p).val 0 = (LinearMap.toMatrix' L).det
  correction : ∀ p,affineTailCorrectionGood Valued.v (a p).val (b p).val ((D p).val 0) ((c p).val 0)
  c_value : ∀ p,vfValue ((c p).val 0) =
    (gammaMapValue U.form (liftLabelMap (measuredRVHead hc U (productLeft (k+1) m) hU).object p) /
      gammaMapValue V.form (e.iso.hom.map
        (liftLabelMap (measuredRVHead hc U (productLeft (k+1) m) hU).object p))).val

theorem exists_fullAffineTailData_vfGenerated
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (S : LRV.Substructure M) (B : VFGeneratedFieldBase S) (hsmall : Cardinal.mk (S : Set M) < κ)
    {U V : MeasuredRVObject (M := M) (S : Set M) ((k+1)+m)} (e : MeasuredRVIso U V)
    (hU : (rvHeadVolume U.object (productLeft (k+1) m)).FiniteFibres)
    (hV : (rvHeadVolume V.object (productLeft (k+1) m)).FiniteFibres)
    (F : EverywhereMeasuredRVLift (measuredRVHeadIso hc e
      (productLeft (k+1) m) (productLeft (k+1) m) hU hV)) :
    Nonempty (FullAffineTailData (G := G) hc e hU hV F) := by
  let l := productLeft (k+1) m
  let r := productRight (k+1) m
  let UH := measuredRVHead hc U l hU
  let VH := measuredRVHead hc V l hV
  choose A hA using fun i : Fin m => exists_liftLabelRepresentative_vfGenerated hc h00 hκ hs S B hsmall
    ⟨UH.object,UH.finiteVolume⟩ (rvHeadVolume U.object (fun _ : Fin 1 => r i)) (fun u => U.nonzero u (r i))
  choose B₁ hB₁ using fun i : Fin m => exists_liftLabelRepresentative_vfGenerated hc h00 hκ hs S B hsmall
    ⟨VH.object,VH.finiteVolume⟩ (rvHeadVolume V.object (fun _ : Fin 1 => r i)) (fun u => V.nonzero u (r i))
  obtain ⟨c,hC⟩ := exists_liftLabelRepresentative_vfGenerated hc h00 hκ hs S B hsmall
    ⟨UH.object,UH.finiteVolume⟩ (rvVolumeRatioMap (U := U.object) (V := V.object) e.iso.hom.map)
      (rvVolumeRatioMap_nonzero (U := U) (V := V) e.iso.hom.map)
  obtain ⟨D,hD⟩ := exists_totalMixedJacobianMap_of_pos (Nat.zero_lt_succ k) F.map
  let a := vfTupleMap A
  let b := (vfTupleMap B₁).comp F.map
  have haRV (p : rvLift UH.object) : tupleRV (a p).val =
      U.object.value (liftLabelMap UH.object p) ∘ r := funext (fun i => hA i p)
  have hbRV (p : rvLift UH.object) : tupleRV (b p).val =
      V.object.value (liftLabelMap VH.object (F.map p)) ∘ r := funext (fun i => hB₁ i (F.map p))
  have hne (z : VF M) (t : RVInfinity M) (ht : t.val ≠ iRVZero)
      (hz : CanonicalRV.encodedRv z = t) : z ≠ 0 := by
    intro he
    exact ht ((congrArg Subtype.val hz).symm.trans
      ((CanonicalRV.encodedRv_zero_iff z).mpr he))
  have ha (p : rvLift UH.object) (i : Fin m) : (a p).val i ≠ 0 :=
    hne _ _ (U.nonzero _ (r i)) (congrFun (haRV p) i)
  have hb (p : rvLift UH.object) (i : Fin m) : (b p).val i ≠ 0 :=
    hne _ _ (V.nonzero _ (r i)) (congrFun (hbRV p) i)
  have hTag (p : rvLift UH.object) : liftLabelMap VH.object (F.map p) =
      e.iso.hom.map (liftLabelMap UH.object p) :=
    liftLabelMap_target_of_graph (measuredRVHeadIso hc e l l hU hV).iso.hom.map F.map F.labels p
  have hprod (x : Fin (k+1) → VF M) (y : Fin m → VF M) :
      (∏ i,Valued.v (productTuple x y i)) = (∏ i,Valued.v (x i)) * ∏ i,Valued.v (y i) := by
    rw [← (finSumFinEquiv : Fin (k+1) ⊕ Fin m ≃ Fin ((k+1)+m)).prod_comp,Fintype.prod_sum_type]
    change (∏ i,Valued.v (productTuple x y (l i))) *
      ∏ i,Valued.v (productTuple x y (r i)) = _
    simp only [l,r,productTuple_left,productTuple_right]
  have hLiftNonzero {d : ℕ} (W : MeasuredRVObject (M := M) (S : Set M) d)
      (p : rvLift W.object) (i : Fin d) : p.val.1 i ≠ 0 :=
    hne _ _ (W.nonzero (liftLabelMap W.object p) i) (congrFun (liftLabelMap_volume W.object p) i).symm
  have hCorrection (p : rvLift UH.object) :
      affineTailCorrectionGood Valued.v (a p).val (b p).val ((D p).val 0) ((c p).val 0) := by
    obtain ⟨L,hL,hVal⟩ := EverywhereMeasuredRVLift.weighted_measure F Valued.v hv p
    have hDJ := hD p L hL
    let u := liftLabelMap UH.object p
    let x := productTuple p.val.1 (a p).val
    let y := productTuple (F.map p).val.1 (b p).val
    have hx : tupleRV x = U.object.value u := by
      obtain ⟨u',hu',hVol⟩ := (rvLift_product_mem_iff_tail ⟨U.object,U.finiteVolume⟩ hU p _).mpr (haRV p)
      have he : u' = u := Subtype.ext hu'
      exact (he ▸ hVol).symm
    have hy : tupleRV y = V.object.value (e.iso.hom.map u) := by
      obtain ⟨u',hu',hVol⟩ := (rvLift_product_mem_iff_tail ⟨V.object,V.finiteVolume⟩ hV (F.map p) _).mpr (hbRV p)
      have he : u' = liftLabelMap VH.object (F.map p) := Subtype.ext hu'
      exact ((he.trans (hTag p)) ▸ hVol).symm
    have hRep : CanonicalRV.encodedRv ((c p).val 0) =
        CanonicalRV.encodedRv ((∏ i,y i) / ∏ i,x i) := by
      rw [hC p,rvVolumeRatioMap_value]
      change _ = RVOperations.rvHom (_ / _)
      rw [map_div₀,map_prod,map_prod]
      change _ = (∏ i,tupleRV y i) / ∏ i,tupleRV x i
      rw [hx,hy]
    have hCanonical : vfValue ((c p).val 0) = vfValue ((∏ i,y i) / ∏ i,x i) :=
      congrArg Values.vrv hRep
    have hvc := (vfValue_eq_iff Valued.v hv _ _).mp hCanonical
    simp only [map_div₀,map_prod] at hvc
    change Valued.v ((c p).val 0) = (∏ i,Valued.v (productTuple (F.map p).val.1 (b p).val i)) /
      ∏ i,Valued.v (productTuple p.val.1 (a p).val i) at hvc
    rw [hprod,hprod] at hvc
    apply affineTailCorrectionGood_of_weighted_head Valued.v _ _ _ _ _ _
      (Finset.prod_ne_zero_iff.mpr (fun i _ => Valued.v.ne_zero_iff.mpr (hLiftNonzero UH p i)))
      (Finset.prod_ne_zero_iff.mpr (fun i _ => Valued.v.ne_zero_iff.mpr (hLiftNonzero VH (F.map p) i)))
      (hDJ.symm ▸ hVal) hvc
  exact ⟨⟨a,b,D,c,ha,hb,haRV,hbRV,hD,hCorrection,
    fun p => rvVolumeRatio_representative_value e (liftLabelMap UH.object p) _ (hC p)⟩⟩

end DiamondIntegral.Section6
