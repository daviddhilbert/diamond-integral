import «section 3».RVCategories
import Section4.RVProductMorphisms
import Section4.ProductBijections

/-! Genuine cartesian RV products. Both the domain labels and nonzero
finite-to-one target coordinates are concatenated. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4

noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k l : ℕ}

def RVObject.product (U : RVObject (M := M) S k) (V : RVObject (M := M) S l) :
    RVObject S (k + l) where
  arity := U.arity + V.arity
  domain := rvProductDomain U.domain V.domain
  volume := (rvProductObject U.toCompanion.obj V.toCompanion.obj).volume
  finite := rvProductObject_finite_volume _ _ U.finite V.finite
  nonzero a i := by
    let ab := rvUnpack U.domain V.domain a
    change ((rvAppend (U.volume ⟨ab.val.1, ab.property.1⟩).val
      (V.volume ⟨ab.val.2, ab.property.2⟩).val i)).val ≠ iRVZero
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [rvAppend, Fin.append_left] using U.nonzero ⟨ab.val.1, ab.property.1⟩ j
    · simpa only [rvAppend, Fin.append_right] using V.nonzero ⟨ab.val.2, ab.property.2⟩ j

def rvProductBijection {U U' : RVObject (M := M) S k} {V V' : RVObject (M := M) S l}
    (f : DefinableBijection U.domain U'.domain) (g : DefinableBijection V.domain V'.domain) :
    DefinableBijection (U.product V).domain (U'.product V').domain where
  map := rvProductMap (U := U.toCompanion.obj) (U' := U'.toCompanion.obj)
    (V := V.toCompanion.obj) (V' := V'.toCompanion.obj) f.map g.map
  bijective := (rvPackToImage_bijective U'.domain V'.domain).comp
    ((Map.prodMap_bijective f.map g.map f.bijective g.bijective).comp
      (Equiv.ofBijective (rvPack U.domain V.domain).toImage
        (rvPackToImage_bijective U.domain V.domain)).symm.bijective)

def rvProductLeft (U : RVObject (M := M) S k) (V : RVObject (M := M) S l) :
    Map (U.product V).domain U.domain := (Map.prodFst U.domain V.domain).comp (rvUnpack U.domain V.domain)

def rvProductRight (U : RVObject (M := M) S k) (V : RVObject (M := M) S l) :
    Map (U.product V).domain V.domain := (Map.prodSnd U.domain V.domain).comp (rvUnpack U.domain V.domain)

theorem rvProductLeft_map {U U' : RVObject (M := M) S k} {V V' : RVObject (M := M) S l}
    (f : DefinableBijection U.domain U'.domain) (g : DefinableBijection V.domain V'.domain)
    (a : (U.product V).domain) :
    rvProductLeft U' V' ((rvProductBijection f g).map a) = f.map (rvProductLeft U V a) := by
  apply Subtype.ext
  exact congrArg (fun p : U'.domain.prod V'.domain => p.val.1)
    (rvProductMap_unpack (U := U.toCompanion.obj) (U' := U'.toCompanion.obj)
      (V := V.toCompanion.obj) (V' := V'.toCompanion.obj) f.map g.map a)

theorem rvProductRight_map {U U' : RVObject (M := M) S k} {V V' : RVObject (M := M) S l}
    (f : DefinableBijection U.domain U'.domain) (g : DefinableBijection V.domain V'.domain)
    (a : (U.product V).domain) :
    rvProductRight U' V' ((rvProductBijection f g).map a) = g.map (rvProductRight U V a) := by
  apply Subtype.ext
  exact congrArg (fun p : U'.domain.prod V'.domain => p.val.2)
    (rvProductMap_unpack (U := U.toCompanion.obj) (U' := U'.toCompanion.obj)
      (V := V.toCompanion.obj) (V' := V'.toCompanion.obj) f.map g.map a)

theorem RVObject.product_res {U : RVObject (M := M) S k} {V : RVObject (M := M) S l}
    (hU : resProperty S k U) (hV : resProperty S l V) : resProperty S (k + l) (U.product V) := by
  let appendValues (p : (Fin U.arity → Section2.GammaInfinity M) ×
      (Fin V.arity → Section2.GammaInfinity M)) := Fin.append p.1 p.2
  apply ((hU.prod hV).image appendValues).subset
  rintro _ ⟨t, ⟨a, ha⟩, rfl⟩
  let u : U.domain := ⟨a.val.1, a.property.1⟩
  let v : V.domain := ⟨a.val.2, a.property.2⟩
  refine ⟨((fun i => Values.vrv (u.val i)), (fun i => Values.vrv (v.val i))),
    ⟨⟨u.val, u.property, rfl⟩, ⟨v.val, v.property, rfl⟩⟩, ?_⟩
  change Fin.append (fun i => Values.vrv (u.val i)) (fun i => Values.vrv (v.val i)) = _
  rw [← ha]
  funext i
  change Fin.append (fun j => Values.vrv (u.val j)) (fun j => Values.vrv (v.val j)) i =
    Values.vrv (rvAppend a.val.1 a.val.2 i)
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp only [rvAppend, Fin.append_left, Fin.append_right] <;> rfl

end DiamondIntegral.Section3
