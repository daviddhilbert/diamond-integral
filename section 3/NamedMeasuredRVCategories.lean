import «section 3».NamedRVCategories
import «section 3».RVFormGraphs

/-! Pointwise measured RV and RES categories over fixed imaginary names.
All Gamma forms, including degree-zero forms, retain complete named graphs. -/
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
variable {P : Space LRV M} {p : P.Carrier} {S : Set M} {k : ℕ}
variable {hc : CanonicalStructure.IsCanonical (M := M)}

def NamedRVObject.target (U : NamedRVObject P p S k) (a : U.domain) : Fin k → Section2.RV M :=
  fun i => ⟨(U.volume a).val i, fun he => U.nonzero a i (congrArg Subtype.val he)⟩

abbrev NamedGammaVolumeForm (P : Space LRV M) (p : P.Carrier)
    (hc : CanonicalStructure.IsCanonical (M := M)) {Q : Space LRV M} {S : Set M}
    (A : NamedDefSet P p Q S) := NamedMap A (NamedDefSet.univ P p (volumeGammaSpace hc) S)

def namedGammaFormValue {Q : Space LRV M} {A : NamedDefSet P p Q S}
    (ω : NamedGammaVolumeForm P p hc A) (a : A) : Values.Gamma (M := M) := cast (gammaCarrier hc) (ω a).val

structure NamedMeasuredRVObject (P : Space LRV M) (p : P.Carrier)
    (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) (k : ℕ) where
  underlying : NamedRVObject P p S k
  form : NamedGammaVolumeForm P p hc underlying.domain

def NamedMeasuredRVObject.combinedWeight (U : NamedMeasuredRVObject P p hc S k)
    (a : U.underlying.domain) : Values.Gamma (M := M) :=
  namedGammaFormValue U.form a * ∏ i, Section2.rvFiniteValue (U.underlying.target a i)

structure NamedMeasuredRVHom (U V : NamedMeasuredRVObject P p hc S k) where
  bijection : NamedBijection U.underlying.domain V.underlying.domain
  preserves : ∀ a, U.combinedWeight a = V.combinedWeight (bijection.map a)

@[ext] theorem NamedMeasuredRVHom.ext {U V : NamedMeasuredRVObject P p hc S k}
    {f g : NamedMeasuredRVHom U V} (h : f.bijection = g.bijection) : f = g := by
  cases f
  cases g
  cases h
  rfl

def NamedMeasuredRVHom.id (U : NamedMeasuredRVObject P p hc S k) : NamedMeasuredRVHom U U :=
  ⟨NamedBijection.id U.underlying.domain, fun _ => rfl⟩

def NamedMeasuredRVHom.comp {U V W : NamedMeasuredRVObject P p hc S k}
    (g : NamedMeasuredRVHom V W) (f : NamedMeasuredRVHom U V) : NamedMeasuredRVHom U W :=
  ⟨g.bijection.comp f.bijection, fun a => (f.preserves a).trans (g.preserves (f.bijection.map a))⟩

def NamedMeasuredRVHom.symm {U V : NamedMeasuredRVObject P p hc S k}
    (f : NamedMeasuredRVHom U V) : NamedMeasuredRVHom V U where
  bijection := f.bijection.symm
  preserves b := by
    have h := f.preserves (f.bijection.symm.map b)
    rw [NamedBijection.symm, NamedMap.apply_inverse] at h
    exact h.symm

instance namedMeasuredRVGroupoid : Groupoid (NamedMeasuredRVObject P p hc S k) where
  Hom := NamedMeasuredRVHom
  id := NamedMeasuredRVHom.id
  comp f g := g.comp f
  inv f := f.symm
  id_comp f := by apply NamedMeasuredRVHom.ext; apply NamedBijection.ext; apply NamedMap.ext; intro a; rfl
  comp_id f := by apply NamedMeasuredRVHom.ext; apply NamedBijection.ext; apply NamedMap.ext; intro a; rfl
  assoc f g h := by apply NamedMeasuredRVHom.ext; apply NamedBijection.ext; apply NamedMap.ext; intro a; rfl
  inv_comp f := by apply NamedMeasuredRVHom.ext; apply NamedBijection.ext; apply NamedMap.ext; intro a; exact f.bijection.map.apply_inverse f.bijection.bijective a
  comp_inv f := by apply NamedMeasuredRVHom.ext; apply NamedBijection.ext; apply NamedMap.ext; intro a; exact f.bijection.map.inverse_apply f.bijection.bijective a

def NamedMeasuredRVObject.overRealCode (U : NamedMeasuredRVObject P p hc S k) (c : P.domain) (hp : P.decode c = p) :
    MeasuredRVObject (realCodeParameters S c) k where
  underlying := U.underlying.overRealCode c hp
  form := GammaVolumeForm.toRVVolumeForm hc (U.form.overRealCode c hp)

theorem NamedMeasuredRVObject.overRealCode_combined (U : NamedMeasuredRVObject P p hc S k)
    (c : P.domain) (hp : P.decode c = p) (a : U.underlying.domain) :
    (U.overRealCode c hp).combinedWeight a = U.combinedWeight a := rfl

def NamedMeasuredRVHom.overRealCode {U V : NamedMeasuredRVObject P p hc S k}
    (f : NamedMeasuredRVHom U V) (c : P.domain) (hp : P.decode c = p) :
    MeasuredRVHom (U.overRealCode c hp) (V.overRealCode c hp) :=
  ⟨f.bijection.overRealCode c hp, f.preserves⟩

def namedMeasuredRVToRealCode (P : Space LRV M) (p : P.Carrier)
    (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) (k : ℕ) (c : P.domain) (hp : P.decode c = p) :
    NamedMeasuredRVObject P p hc S k ⥤ MeasuredRVObject (realCodeParameters S c) k where
  obj U := U.overRealCode c hp
  map f := f.overRealCode c hp
  map_id U := by apply MeasuredRVHom.ext; apply DefinableBijection.ext; apply Map.ext; intro a; rfl
  map_comp f g := by apply MeasuredRVHom.ext; apply DefinableBijection.ext; apply Map.ext; intro a; rfl

instance namedMeasuredRVToRealCodeFaithful (c : P.domain) (hp : P.decode c = p) :
    (namedMeasuredRVToRealCode P p hc S k c hp).Faithful where
  map_injective := by
    intro U V f g h
    apply NamedMeasuredRVHom.ext
    apply NamedBijection.ext
    apply NamedMap.ext
    intro a
    exact congrArg (fun f : U.overRealCode c hp ⟶ V.overRealCode c hp => f.bijection.map a) h

def namedMeasuredResProperty : ObjectProperty (NamedMeasuredRVObject P p hc S k) :=
  fun U => namedResProperty U.underlying

abbrev NamedMeasuredRESObject (P : Space LRV M) (p : P.Carrier)
    (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) (k : ℕ) :=
  (namedMeasuredResProperty (P := P) (p := p) (hc := hc) (S := S) (k := k)).FullSubcategory

end DiamondIntegral.Section3
