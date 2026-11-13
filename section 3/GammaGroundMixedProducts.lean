import «section 3».GammaGroundFiniteVFScissors
import Section4.MixedProducts

/-! Genuine mixed products over the complete Gamma ground preserve
finite RV fibres and keep all coordinate sorts. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)}
variable {n r m s : ℕ}

def gammaGroundMixedPack (A : GammaGroundDefSet hc ground (rawMixedSpace (M := M) n r))
    (B : GammaGroundDefSet hc ground (rawMixedSpace (M := M) m s)) :
    GammaGroundMap (A.prod B) (GammaGroundDefSet.univ hc ground (rawMixedSpace (n + m) (r + s))) :=
  GammaGroundMap.ofGlobal (A.prod B) (GammaGroundDefSet.univ hc ground (rawMixedSpace (n + m) (r + s)))
    (mixedAppendMap ground.real n r m s) (fun _ => Set.mem_univ _)

theorem gammaGroundMixedPack_injective (A : GammaGroundDefSet hc ground (rawMixedSpace (M := M) n r))
    (B : GammaGroundDefSet hc ground (rawMixedSpace (M := M) m s)) : Function.Injective (gammaGroundMixedPack A B) := by
  intro a b he
  have he' := (mixedAppendMap_bijective ground.real n r m s).injective
    (show mixedAppendMap ground.real n r m s ⟨a.val, Set.mem_univ _⟩ =
      mixedAppendMap ground.real n r m s ⟨b.val, Set.mem_univ _⟩ from he)
  exact Subtype.ext (congrArg
    (fun z : DefSet.univ ((rawMixedSpace (M := M) n r).prod (rawMixedSpace m s)) ground.real => z.val) he')

def gammaGroundMixedProductDomain (A : GammaGroundDefSet hc ground (rawMixedSpace (M := M) n r))
    (B : GammaGroundDefSet hc ground (rawMixedSpace (M := M) m s)) := (gammaGroundMixedPack A B).image

theorem mem_gammaGroundMixedProductDomain (A : GammaGroundDefSet hc ground (rawMixedSpace (M := M) n r))
    (B : GammaGroundDefSet hc ground (rawMixedSpace (M := M) m s))
    (p : (rawMixedSpace (M := M) (n + m) (r + s)).Carrier) :
    p ∈ (gammaGroundMixedProductDomain A B).carrier ↔
      (p.1 ∘ Fin.castAdd m, p.2 ∘ Fin.castAdd s) ∈ A.carrier ∧
      (p.1 ∘ Fin.natAdd n, p.2 ∘ Fin.natAdd r) ∈ B.carrier := by
  constructor
  · rintro ⟨a, ha⟩
    change (vfAppend a.val.1.1 a.val.2.1, rvAppend a.val.1.2 a.val.2.2) = p at ha
    rw [← ha]
    have hA : (a.val.1.1, a.val.1.2) ∈ A.carrier ∧ (a.val.2.1, a.val.2.2) ∈ B.carrier := a.property
    simpa only [vfAppend, rvAppend, Function.comp_def, Fin.append_left, Fin.append_right] using hA
  · rintro ⟨ha, hb⟩
    refine ⟨⟨((p.1 ∘ Fin.castAdd m, p.2 ∘ Fin.castAdd s),
      (p.1 ∘ Fin.natAdd n, p.2 ∘ Fin.natAdd r)), ha, hb⟩, ?_⟩
    exact Prod.ext Fin.append_castAdd_natAdd Fin.append_castAdd_natAdd

def gammaGroundMixedUnpack (A : GammaGroundDefSet hc ground (rawMixedSpace (M := M) n r))
    (B : GammaGroundDefSet hc ground (rawMixedSpace (M := M) m s)) :
    GammaGroundMap (gammaGroundMixedProductDomain A B) (A.prod B) :=
  (gammaGroundMixedPack A B).toImage.inverse ((gammaGroundMixedPack A B).toImage_bijective (gammaGroundMixedPack_injective A B))

theorem gammaGroundMixedProduct_finite {A : GammaGroundDefSet hc ground (rawMixedSpace (M := M) n r)}
    {B : GammaGroundDefSet hc ground (rawMixedSpace (M := M) m s)}
    (hA : ∀ a, {t | (a, t) ∈ A.carrier}.Finite) (hB : ∀ b, {t | (b, t) ∈ B.carrier}.Finite) :
    ∀ a, {t | (a, t) ∈ (gammaGroundMixedProductDomain A B).carrier}.Finite := by
  intro a
  let au := a ∘ Fin.castAdd m
  let av := a ∘ Fin.natAdd n
  apply (((hA au).prod (hB av)).image (fun ts => rvAppend ts.1 ts.2)).subset
  intro t ht
  have hab := (mem_gammaGroundMixedProductDomain A B (a, t)).mp ht
  exact ⟨(t ∘ Fin.castAdd s, t ∘ Fin.natAdd r), hab, Fin.append_castAdd_natAdd⟩

def GammaGroundFiniteVFObject.product (U V : GammaGroundFiniteVFObject hc ground) : GammaGroundFiniteVFObject hc ground where
  vfArity := U.vfArity + V.vfArity
  rvArity := U.rvArity + V.rvArity
  domain := gammaGroundMixedProductDomain U.domain V.domain
  finite := gammaGroundMixedProduct_finite U.finite V.finite

end DiamondIntegral.Section3
