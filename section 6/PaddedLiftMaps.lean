import «section 6».PaddedMeasuredRVObjects
import Section9.AppendTailMap
import Section9.VFCoordinateAssembly

/-! Extend an actual VF lift by carrying an entire unit-RV tail fixed.
The definable map and its bijection on the full padded objects are explicit. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k m : ℕ}

theorem tupleRV_productTuple (x : Fin k → VF M) (y : Fin m → VF M) :
    tupleRV (productTuple x y)=productTuple (tupleRV x) (tupleRV y) := by
  apply productTuple_ext
  · intro i
    change CanonicalRV.encodedRv (productTuple x y (productLeft k m i))=
      productTuple (tupleRV x) (tupleRV y) (productLeft k m i)
    rw [productTuple_left,productTuple_left]
    rfl
  · intro i
    change CanonicalRV.encodedRv (productTuple x y (productRight k m i))=
      productTuple (tupleRV x) (tupleRV y) (productRight k m i)
    rw [productTuple_right,productTuple_right]
    rfl

def rvPadOnesLiftHeadMap (U : MeasuredRVObject (M := M) S k) (m : ℕ) :
    Map (rvLift (measuredRVPadOnes U m).object) (rvLift U.object) :=
  (vfSelect (productLeft k m) (rvLift (measuredRVPadOnes U m).object)).corestrict (fun p => by
    let u := liftLabelMap (measuredRVPadOnes U m).object p
    refine ⟨u,rfl,funext (fun i => ?_)⟩
    change U.object.value u i=CanonicalRV.encodedRv (p.val.1 (productLeft k m i))
    have h := congrFun (liftLabelMap_volume (measuredRVPadOnes U m).object p) (productLeft k m i)
    change productTuple (U.object.value u) (fun _ : Fin m => 1) (productLeft k m i)=
      CanonicalRV.encodedRv (p.val.1 (productLeft k m i)) at h
    simpa only [productTuple_left] using h)

theorem rvPadOnesLiftHeadMap_value (U : MeasuredRVObject (M := M) S k) (m : ℕ)
    (p : rvLift (measuredRVPadOnes U m).object) :
    (rvPadOnesLiftHeadMap U m p).val=(p.val.1 ∘ productLeft k m,p.val.2) := rfl

theorem rvPadOnesLift_tail (U : MeasuredRVObject (M := M) S k) (m : ℕ)
    (p : rvLift (measuredRVPadOnes U m).object) :
    tupleRV (p.val.1 ∘ productRight k m)=fun _ : Fin m => 1 := by
  funext j
  have h := congrFun (liftLabelMap_volume (measuredRVPadOnes U m).object p) (productRight k m j)
  change productTuple (U.object.value (liftLabelMap (measuredRVPadOnes U m).object p)) (fun _ : Fin m => 1) (productRight k m j)=
    CanonicalRV.encodedRv (p.val.1 (productRight k m j)) at h
  exact (productTuple_right _ _ j ▸ h).symm

theorem rvPadOnesLift_mem_product (U : MeasuredRVObject (M := M) S k) (m : ℕ)
    (p : rvLift U.object) (y : Fin m → VF M) (hy : tupleRV y=fun _ : Fin m => 1) :
    (productTuple p.val.1 y,p.val.2) ∈ (rvLift (measuredRVPadOnes U m).object).carrier := by
  refine ⟨liftLabelMap U.object p,rfl,?_⟩
  change productTuple (U.object.value (liftLabelMap U.object p)) (fun _ : Fin m => 1)=tupleRV (productTuple p.val.1 y)
  rw [tupleRV_productTuple,hy,liftLabelMap_volume]

def paddedRVLiftMap {U V : MeasuredRVObject (M := M) S k}
    (f : Map (rvLift U.object) (rvLift V.object)) (m : ℕ) :
    Map (rvLift (measuredRVPadOnes U m).object) (rvLift (measuredRVPadOnes V m).object) := by
  let A := rvLift (measuredRVPadOnes U m).object
  let H := rvPadOnesLiftHeadMap U m
  let tail := (vfTupleSelectMap S (productRight k m)).comp
    (Map.fst (rawVFSpace (M := M) (k+m)) (rawRVSpace U.object.arity) S A)
  exact (appendTailMap (f.comp H) tail).corestrict (fun p =>
    rvPadOnesLift_mem_product V m (f (H p)) _ (rvPadOnesLift_tail U m p))

theorem paddedRVLiftMap_value {U V : MeasuredRVObject (M := M) S k}
    (f : Map (rvLift U.object) (rvLift V.object)) (m : ℕ)
    (p : rvLift (measuredRVPadOnes U m).object) :
    (paddedRVLiftMap f m p).val=(productTuple (f (rvPadOnesLiftHeadMap U m p)).val.1
      (p.val.1 ∘ productRight k m),(f (rvPadOnesLiftHeadMap U m p)).val.2) := rfl

theorem paddedRVLiftMap_bijective {U V : MeasuredRVObject (M := M) S k}
    (f : Map (rvLift U.object) (rvLift V.object)) (hf : Function.Bijective f) (m : ℕ) :
    Function.Bijective (paddedRVLiftMap f m) := by
  let H := rvPadOnesLiftHeadMap U m
  constructor
  · intro p q h
    have hh : f (H p)=f (H q) := by
      apply Subtype.ext
      apply Prod.ext
      · funext i
        have he := congrArg (fun z : rvLift (measuredRVPadOnes V m).object => z.val.1 (productLeft k m i)) h
        simpa only [paddedRVLiftMap_value,productTuple_left] using he
      · exact congrArg (fun z : rvLift (measuredRVPadOnes V m).object => z.val.2) h
    have he := hf.1 hh
    apply Subtype.ext
    apply Prod.ext
    · apply productTuple_ext
      · intro i
        exact congrArg (fun z : rvLift U.object => z.val.1 i) he
      · intro i
        have ht := congrArg (fun z : rvLift (measuredRVPadOnes V m).object => z.val.1 (productRight k m i)) h
        simpa only [paddedRVLiftMap_value,productTuple_right,Function.comp_apply] using ht
    · exact congrArg (fun z : rvLift U.object => z.val.2) he
  · intro q
    obtain ⟨x,hx⟩ := hf.2 (rvPadOnesLiftHeadMap V m q)
    let p : rvLift (measuredRVPadOnes U m).object :=
      ⟨(productTuple x.val.1 (q.val.1 ∘ productRight k m),x.val.2),
        rvPadOnesLift_mem_product U m x _ (rvPadOnesLift_tail V m q)⟩
    have hp : H p=x := by
      apply Subtype.ext
      exact Prod.ext (funext (productTuple_left _ _)) rfl
    refine ⟨p,Subtype.ext ?_⟩
    rw [paddedRVLiftMap_value]
    change (productTuple (f (H p)).val.1 (p.val.1 ∘ productRight k m),(f (H p)).val.2)=q.val
    rw [hp,hx]
    apply Prod.ext
    · apply productTuple_ext
      · intro i
        change productTuple (rvPadOnesLiftHeadMap V m q).val.1 (p.val.1 ∘ productRight k m) (productLeft k m i)=_
        rw [productTuple_left]
        rfl
      · intro j
        change productTuple (rvPadOnesLiftHeadMap V m q).val.1 (p.val.1 ∘ productRight k m) (productRight k m j)=_
        rw [productTuple_right]
        exact productTuple_right _ _ j
    · rfl

end DiamondIntegral.Section6
