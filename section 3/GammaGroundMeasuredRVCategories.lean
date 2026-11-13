import «section 3».GammaGroundRVCategories
import «section 3».RVVolumeForms
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open scoped BigOperators
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)} {k : ℕ}

def GammaGroundRVObject.target (U : GammaGroundRVObject hc ground k) (a : U.domain) : Fin k → Section2.RV M :=
  fun i => ⟨(U.volume a).val i, fun he => U.nonzero a i (congrArg Subtype.val he)⟩

abbrev GammaGroundVolumeForm (hc : CanonicalStructure.IsCanonical (M := M))
    (ground : GammaParameters.Base (M := M)) {Q : Space LRV M} (A : GammaGroundDefSet hc ground Q) :=
  GammaGroundMap A (GammaGroundDefSet.univ hc ground (volumeGammaSpace hc))

def gammaGroundFormValue {Q : Space LRV M} {A : GammaGroundDefSet hc ground Q}
    (ω : GammaGroundVolumeForm hc ground A) (a : A) : Values.Gamma (M := M) := cast (gammaCarrier hc) (ω a).val

structure GammaGroundMeasuredRVObject (hc : CanonicalStructure.IsCanonical (M := M))
    (ground : GammaParameters.Base (M := M)) (k : ℕ) where
  underlying : GammaGroundRVObject hc ground k
  form : GammaGroundVolumeForm hc ground underlying.domain

def GammaGroundMeasuredRVObject.combinedWeight (U : GammaGroundMeasuredRVObject hc ground k)
    (a : U.underlying.domain) : Values.Gamma (M := M) :=
  gammaGroundFormValue U.form a * ∏ i, Section2.rvFiniteValue (U.underlying.target a i)

structure GammaGroundMeasuredRVHom (U V : GammaGroundMeasuredRVObject hc ground k) where
  bijection : GammaGroundBijection U.underlying.domain V.underlying.domain
  preserves : ∀ a, U.combinedWeight a = V.combinedWeight (bijection.map a)

@[ext] theorem GammaGroundMeasuredRVHom.ext {U V : GammaGroundMeasuredRVObject hc ground k}
    {f g : GammaGroundMeasuredRVHom U V} (h : f.bijection = g.bijection) : f = g := by
  cases f
  cases g
  cases h
  rfl

def GammaGroundMeasuredRVHom.id (U : GammaGroundMeasuredRVObject hc ground k) : GammaGroundMeasuredRVHom U U :=
  ⟨GammaGroundBijection.id U.underlying.domain, fun _ => rfl⟩

def GammaGroundMeasuredRVHom.comp {U V W : GammaGroundMeasuredRVObject hc ground k}
    (g : GammaGroundMeasuredRVHom V W) (f : GammaGroundMeasuredRVHom U V) : GammaGroundMeasuredRVHom U W :=
  ⟨g.bijection.comp f.bijection, fun a => (f.preserves a).trans (g.preserves (f.bijection.map a))⟩

def GammaGroundMeasuredRVHom.symm {U V : GammaGroundMeasuredRVObject hc ground k}
    (f : GammaGroundMeasuredRVHom U V) : GammaGroundMeasuredRVHom V U where
  bijection := f.bijection.symm
  preserves b := by
    have h := f.preserves (f.bijection.symm.map b)
    rw [GammaGroundBijection.symm, GammaGroundMap.apply_inverse] at h
    exact h.symm

instance gammaGroundMeasuredRVGroupoid : Groupoid (GammaGroundMeasuredRVObject hc ground k) where
  Hom := GammaGroundMeasuredRVHom
  id := GammaGroundMeasuredRVHom.id
  comp f g := g.comp f
  inv f := f.symm
  id_comp f := by apply GammaGroundMeasuredRVHom.ext; apply GammaGroundBijection.ext; apply GammaGroundMap.ext; intro a; rfl
  comp_id f := by apply GammaGroundMeasuredRVHom.ext; apply GammaGroundBijection.ext; apply GammaGroundMap.ext; intro a; rfl
  assoc f g h := by apply GammaGroundMeasuredRVHom.ext; apply GammaGroundBijection.ext; apply GammaGroundMap.ext; intro a; rfl
  inv_comp f := by apply GammaGroundMeasuredRVHom.ext; apply GammaGroundBijection.ext; apply GammaGroundMap.ext; intro a; exact f.bijection.map.apply_inverse f.bijection.bijective a
  comp_inv f := by apply GammaGroundMeasuredRVHom.ext; apply GammaGroundBijection.ext; apply GammaGroundMap.ext; intro a; exact f.bijection.map.inverse_apply f.bijection.bijective a

def gammaGroundMeasuredResProperty : ObjectProperty (GammaGroundMeasuredRVObject hc ground k) :=
  fun U => gammaGroundResProperty U.underlying

abbrev GammaGroundMeasuredRESObject (hc : CanonicalStructure.IsCanonical (M := M)) (ground : GammaParameters.Base (M := M)) (k : ℕ) :=
  (gammaGroundMeasuredResProperty (hc := hc) (ground := ground) (k := k)).FullSubcategory


end DiamondIntegral.Section3
