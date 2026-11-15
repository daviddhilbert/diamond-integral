import «section 5».AffineBranchCertificates
import «section 5».ReducedImmersionLifts
import Mathlib.AlgebraicGeometry.ResidueField

/-! Compatible complex-point branches determine the same output on all
scheme points, by lifting residue-field spectra through reduced immersions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical AlgebraicGeometry CategoryTheory
universe u

def reducedImmersionPointLift {X Y : Scheme.{u}} [AlgebraicGeometry.IsReduced X]
    (f : X ⟶ Y) [IsImmersion f] (x : Y) (hx : x ∈ Set.range f) :
    Spec (Y.residueField x) ⟶ X :=
  reducedImmersionLift f (Y.fromSpecResidueField x) (by
    rw [Scheme.range_fromSpecResidueField]
    exact Set.singleton_subset_iff.mpr hx)

@[reassoc]
theorem reducedImmersionPointLift_fac {X Y : Scheme.{u}} [AlgebraicGeometry.IsReduced X]
    (f : X ⟶ Y) [IsImmersion f] (x : Y) (hx : x ∈ Set.range f) :
    reducedImmersionPointLift f x hx ≫ f = Y.fromSpecResidueField x :=
  reducedImmersionLift_fac _ _ _

theorem affine_branches_point_functional {S T A B : Type}
    [CommRing S] [CommRing T] [CommRing A] [CommRing B]
    [Algebra ℂ S] [Algebra ℂ T] [Algebra ℂ A] [Algebra ℂ B]
    [Algebra.FiniteType ℂ A] [Algebra.FiniteType ℂ B]
    [IsReduced A] [IsReduced B]
    (f : S →ₐ[ℂ] A) (g : S →ₐ[ℂ] B) (a : T →ₐ[ℂ] A) (b : T →ₐ[ℂ] B)
    [IsImmersion (Spec.map (CommRingCat.ofHom f.toRingHom))]
    [IsImmersion (Spec.map (CommRingCat.ofHom g.toRingHom))]
    (hc : ∀ (φ : A →ₐ[ℂ] ℂ) (ψ : B →ₐ[ℂ] ℂ),
      φ.comp f = ψ.comp g → φ.comp a = ψ.comp b)
    (x : Spec (.of A)) (y : Spec (.of B))
    (he : Spec.map (CommRingCat.ofHom f.toRingHom) x =
      Spec.map (CommRingCat.ofHom g.toRingHom) y) :
    Spec.map (CommRingCat.ofHom a.toRingHom) x =
      Spec.map (CommRingCat.ofHom b.toRingHom) y := by
  let F := Spec.map (CommRingCat.ofHom f.toRingHom)
  let G := Spec.map (CommRingCat.ofHom g.toRingHom)
  let z := F x
  have hzF : z ∈ Set.range F := ⟨x, rfl⟩
  have hzG : z ∈ Set.range G := ⟨y, he.symm⟩
  let p := reducedImmersionPointLift F z hzF
  let q := reducedImmersionPointLift G z hzG
  have hin : p ≫ F = q ≫ G := by
    rw [reducedImmersionPointLift_fac, reducedImmersionPointLift_fac]
  have hout := scheme_complex_overlap_agreement f g a b hc p q hin
  let t := IsLocalRing.closedPoint ((Spec (.of S)).residueField z)
  have hpx : p t = x := by
    apply F.isEmbedding.injective
    have hh := congrArg (fun h => h t) (reducedImmersionPointLift_fac F z hzF)
    change F (p t) = (Spec (.of S)).fromSpecResidueField z t at hh
    exact hh.trans (Scheme.fromSpecResidueField_apply _ _)
  have hqy : q t = y := by
    apply G.isEmbedding.injective
    have hh := congrArg (fun h => h t) (reducedImmersionPointLift_fac G z hzG)
    change G (q t) = (Spec (.of S)).fromSpecResidueField z t at hh
    exact (hh.trans (Scheme.fromSpecResidueField_apply _ _)).trans he
  have hh := congrArg (fun h => h t) hout
  change Spec.map (CommRingCat.ofHom a.toRingHom) (p t) =
    Spec.map (CommRingCat.ofHom b.toRingHom) (q t) at hh
  simpa only [hpx, hqy] using hh

end DiamondIntegral.Section5
