import «section 6».RVCoordinateBundleGeometry
import «section 6».MixedVFProjectionMaps
import Section9.AppendTailMap
import Section9.VFCoordinateAssembly

/-! An arbitrary actual definable map that retains a disc label lifts
to its full RV-disc bundle, carrying the additional VF coordinate fixed.
The full original-base map and its bijection are constructed explicitly. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s : ℕ}

theorem productTuple_singleton_eq_snoc {X : Type*} (x : Fin n → X) (y : X) :
    productTuple x (fun _ : Fin 1 => y)=Fin.snoc x y := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · have he : productRight n 1 (0 : Fin 1)=Fin.last n := Fin.ext rfl
    rw [← he,productTuple_right]
    simp only [he,Fin.snoc_last]
  · have he : productLeft n 1 j=j.castSucc := Fin.ext rfl
    rw [← he,productTuple_left]
    simp only [he,Fin.snoc_castSucc]

theorem bundleProjection_value (A : DefSet (rawMixedSpace (M := M) n r) S) (k : Fin r)
    (p : rvCoordinateBundle A k) : (bundleProjection A k p).val=(Fin.init p.val.1,p.val.2) := rfl

def carryLastMap {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
    (f : Map A B) (k : Fin r) (l : Fin s) (hLabels : ∀ p : A,(f p).val.2 l=p.val.2 k) :
    Map (rvCoordinateBundle A k) (rvCoordinateBundle B l) := by
  let X := rvCoordinateBundle A k
  let H := f.comp (bundleProjection A k)
  let T := (vfTupleSelectMap S (fun _ : Fin 1 => Fin.last n)).comp (mixedVFHeadMap X)
  let R := appendTailMap H T
  refine R.corestrict ?_
  intro p
  change (productTuple (f (bundleProjection A k p)).val.1 (fun _ : Fin 1 => p.val.1 (Fin.last n)),
    (f (bundleProjection A k p)).val.2) ∈ (rvCoordinateBundle B l).carrier
  rw [productTuple_singleton_eq_snoc]
  constructor
  · simpa only [Fin.init_snoc,Prod.eta] using (f (bundleProjection A k p)).property
  · simpa only [Fin.snoc_last] using p.property.2.trans (hLabels (bundleProjection A k p)).symm

theorem carryLastMap_value {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
    (f : Map A B) (k : Fin r) (l : Fin s) (hLabels : ∀ p : A,(f p).val.2 l=p.val.2 k)
    (p : rvCoordinateBundle A k) :
    (carryLastMap f k l hLabels p).val=
      (Fin.snoc (f (bundleProjection A k p)).val.1 (p.val.1 (Fin.last n)),(f (bundleProjection A k p)).val.2) := by
  change (productTuple ((f (bundleProjection A k p)).val.1 : Fin n → VF M)
    (fun _ : Fin 1 => p.val.1 (Fin.last n)),(f (bundleProjection A k p)).val.2)=_
  rw [productTuple_singleton_eq_snoc]

theorem carryLastMap_base {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
    (f : Map A B) (k : Fin r) (l : Fin s) (hLabels : ∀ p : A,(f p).val.2 l=p.val.2 k)
    (p : rvCoordinateBundle A k) :
    bundleProjection B l (carryLastMap f k l hLabels p)=f (bundleProjection A k p) := by
  apply Subtype.ext
  rw [bundleProjection_value,carryLastMap_value,Fin.init_snoc]
  rfl

theorem carryLastMap_fixed {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
    (f : Map A B) (k : Fin r) (l : Fin s) (hLabels : ∀ p : A,(f p).val.2 l=p.val.2 k)
    (p : rvCoordinateBundle A k) :
    (carryLastMap f k l hLabels p).val.1 (Fin.last n)=p.val.1 (Fin.last n) := by
  simp only [carryLastMap_value,Fin.snoc_last]

theorem carryLastMap_bijective {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
    (f : Map A B) (k : Fin r) (l : Fin s) (hLabels : ∀ p : A,(f p).val.2 l=p.val.2 k)
    (hf : Function.Bijective f) : Function.Bijective (carryLastMap f k l hLabels) := by
  constructor
  · intro p q hpq
    have hBase : bundleProjection A k p=bundleProjection A k q := by
      apply hf.1
      rw [← carryLastMap_base f k l hLabels p,← carryLastMap_base f k l hLabels q,hpq]
    have hLast : p.val.1 (Fin.last n)=q.val.1 (Fin.last n) :=
      (carryLastMap_fixed f k l hLabels p).symm.trans
        ((congrArg (fun z : rvCoordinateBundle B l => z.val.1 (Fin.last n)) hpq).trans (carryLastMap_fixed f k l hLabels q))
    apply Subtype.ext
    apply Prod.ext
    · funext i
      refine Fin.lastCases hLast (fun j => ?_) i
      exact congrArg (fun a : A => a.val.1 j) hBase
    · exact congrArg (fun a : A => a.val.2) hBase
  · intro q
    obtain ⟨a,ha⟩ := hf.2 (bundleProjection B l q)
    let p : rvCoordinateBundle A k :=
      ⟨(Fin.snoc a.val.1 (q.val.1 (Fin.last n)),a.val.2),by
        constructor
        · simpa only [Fin.init_snoc,Prod.eta] using a.property
        · simpa only [Fin.snoc_last] using q.property.2.trans
            ((congrArg (fun b : B => b.val.2 l) ha).symm.trans (hLabels a))⟩
    have hBase : bundleProjection A k p=a := Subtype.ext (by
      rw [bundleProjection_value]
      simp only [p,Fin.init_snoc]
      rfl)
    refine ⟨p,Subtype.ext ?_⟩
    rw [carryLastMap_value,hBase,ha,bundleProjection_value]
    simp only [p,Fin.snoc_last,Fin.snoc_init_self]
    rfl

end DiamondIntegral.Section6
