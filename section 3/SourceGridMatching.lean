import «section 3».NativeTensorGridSelection
import «section 3».MatchedResidualBijections
import Mathlib.RingTheory.Congruence.BigOperators
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)} {r m N : ℕ}
variable {P Q : Space LRV M} {U0 : GammaGroundDefSet hc B P} {V0 : GammaGroundDefSet hc B Q}

/-- Each covered source grid cell is matched once, using a source cut
of one original local match. Target parents may repeat. -/
structure GammaGroundTensorSourceGridMatching (F : GammaGroundBijection U0 V0)
    (X : GammaGroundRESUnitChart hc B r) (G : GammaGroundGammaPiece hc B m)
    (a : GammaGroundMap (gammaGroundNativeProductDomain X G) U0)
    (Y : Fin N → GammaGroundRESUnitChart hc B r) (H : Fin N → GammaGroundGammaPiece hc B m)
    (b : ∀ i, GammaGroundMap (gammaGroundNativeProductDomain (Y i) (H i)) V0)
    (E : ∀ i, GammaGroundTensorLocalMatch F X G a (Y i) (H i) (b i)) where
  targetIndex : GammaGroundTensorGridCoveredIndex X G (fun i => (E i).source.residue) (fun i => (E i).source.gamma) → Fin N
  target : ∀ c, GammaGroundTensorBox (Y (targetIndex c)) (H (targetIndex c))
  data : ∀ c, GammaGroundTensorBoxMatch F X G a (Y (targetIndex c)) (H (targetIndex c)) (b (targetIndex c))
    (gammaGroundTensorGridBox X G (fun i => (E i).source.residue) (fun i => (E i).source.gamma) c.val) (target c)

def gammaGroundTensorSourceGridMatching (F : GammaGroundBijection U0 V0)
    (X : GammaGroundRESUnitChart hc B r) (G : GammaGroundGammaPiece hc B m)
    (a : GammaGroundMap (gammaGroundNativeProductDomain X G) U0)
    (Y : Fin N → GammaGroundRESUnitChart hc B r) (H : Fin N → GammaGroundGammaPiece hc B m)
    (b : ∀ i, GammaGroundMap (gammaGroundNativeProductDomain (Y i) (H i)) V0)
    (E : ∀ i, GammaGroundTensorLocalMatch F X G a (Y i) (H i) (b i)) :
    GammaGroundTensorSourceGridMatching F X G a Y H b E := by
  let A := fun i => (E i).source.residue
  let K := fun i => (E i).source.gamma
  let I := GammaGroundTensorGridCoveredIndex X G A K
  let index : I → Fin N := fun c => Classical.choose c.property.2
  have hindex (c : I) : c.val.1 (index c) = true ∧ c.val.2 (index c) = true := Classical.choose_spec c.property.2
  have hcut (c : I) : ∃ R : GammaGroundTensorBox (Y (index c)) (H (index c)),
      Nonempty (GammaGroundTensorBoxMatch F X G a (Y (index c)) (H (index c)) (b (index c))
        (gammaGroundTensorGridBox X G A K c.val) R) := by
    obtain ⟨hA,hK⟩ := gammaGroundTensorGridBox_factors_subset X G A K c.val (index c) (hindex c)
    exact (E (index c)).sourceCuts _ hA hK c.property.1.1 c.property.1.2
  choose R hR using hcut
  exact ⟨index,R,fun c => Classical.choice (hR c)⟩

namespace GammaGroundTensorSourceGridMatching
variable {F : GammaGroundBijection U0 V0}
variable {X : GammaGroundRESUnitChart hc B r} {G : GammaGroundGammaPiece hc B m}
variable {a : GammaGroundMap (gammaGroundNativeProductDomain X G) U0}
variable {Y : Fin N → GammaGroundRESUnitChart hc B r} {H : Fin N → GammaGroundGammaPiece hc B m}
variable {b : ∀ i, GammaGroundMap (gammaGroundNativeProductDomain (Y i) (H i)) V0}
variable {E : ∀ i, GammaGroundTensorLocalMatch F X G a (Y i) (H i) (b i)}

abbrev Cell := GammaGroundTensorGridCoveredIndex X G (fun i => (E i).source.residue) (fun i => (E i).source.gamma)

def sourceMap (_R : GammaGroundTensorSourceGridMatching F X G a Y H b E) (c : Cell (E := E)) :
    GammaGroundMap (gammaGroundTensorGridBox X G (fun i => (E i).source.residue) (fun i => (E i).source.gamma) c.val).source U0 :=
  a.comp (gammaGroundTensorGridBox X G (fun i => (E i).source.residue) (fun i => (E i).source.gamma) c.val).inclusion

def targetMap (R : GammaGroundTensorSourceGridMatching F X G a Y H b E) (c : Cell (E := E)) :
    GammaGroundMap (R.target c).source V0 := (b (R.targetIndex c)).comp (R.target c).inclusion

theorem congruence (R : GammaGroundTensorSourceGridMatching F X G a Y H b E) :
    gammaGroundUnmeasuredCoefficientCongruence
      (∑ c : Cell (E := E), (gammaGroundTensorGridBox X G (fun i => (E i).source.residue) (fun i => (E i).source.gamma) c.val).value)
      (∑ c : Cell (E := E), (R.target c).value) :=
  gammaGroundUnmeasuredCoefficientCongruence.finsetSum Finset.univ (fun c _ => (R.data c).congruence)

theorem sourceMap_disjoint (R : GammaGroundTensorSourceGridMatching F X G a Y H b E)
    (ha : Function.Injective a) (c d : Cell (E := E)) (hcd : c ≠ d) :
    Disjoint (R.sourceMap c).image.carrier (R.sourceMap d).image.carrier := by
  apply Set.disjoint_left.mpr
  rintro z ⟨u,hu⟩ ⟨v,hv⟩
  have he : a ((gammaGroundTensorGridBox X G (fun i => (E i).source.residue) (fun i => (E i).source.gamma) c.val).inclusion u) =
      a ((gammaGroundTensorGridBox X G (fun i => (E i).source.residue) (fun i => (E i).source.gamma) d.val).inclusion v) :=
    Subtype.ext (hu.trans hv.symm)
  have hp := congrArg (fun z : gammaGroundNativeProductDomain X G => z.val) (ha he)
  have huv : u.val = v.val := Prod.ext (congrArg Prod.fst hp) (congrArg Prod.snd hp)
  have hd' := gammaGroundTensorGridBox_disjoint X G (fun i => (E i).source.residue) (fun i => (E i).source.gamma)
    c.val d.val (fun he => hcd (Subtype.ext he))
  have h2 : u.val ∈ (gammaGroundTensorGridBox X G (fun i => (E i).source.residue) (fun i => (E i).source.gamma) d.val).source.carrier := huv.symm ▸ v.property
  exact Set.disjoint_left.mp hd' u.property h2

theorem targetMap_disjoint (R : GammaGroundTensorSourceGridMatching F X G a Y H b E)
    (ha : Function.Injective a) (c d : Cell (E := E)) (hcd : c ≠ d) :
    Disjoint (R.targetMap c).image.carrier (R.targetMap d).image.carrier :=
  gammaGroundMatchedImages_disjoint F (fun c => (R.data c).bijection) R.sourceMap R.targetMap
    (fun c u => (R.data c).agrees u) c d (R.sourceMap_disjoint ha c d hcd)

/-- Every original source patch remains covered after selecting one
match for each disjoint source cell. -/
theorem original_source_covered (R : GammaGroundTensorSourceGridMatching F X G a Y H b E) (i : Fin N) :
    (a.comp (E i).source.inclusion).image.carrier ⊆
      (gammaGroundDefSetFiniteUnion Finset.univ (fun c : Cell (E := E) => (R.sourceMap c).image)).carrier := by
  rintro z ⟨u,hu⟩
  let x := (E i).source.inclusion u
  have hxu : x.val = u.val := Prod.eta u.val
  have hx : x.val ∈ (E i).source.source.carrier := hxu.symm ▸ u.property
  obtain ⟨c,hc⟩ := (gammaGroundTensorGrid_selected_source_cover X G
    (fun i => (E i).source.residue) (fun i => (E i).source.gamma) x).mp ⟨i,hx⟩
  let v : (gammaGroundTensorGridBox X G (fun i => (E i).source.residue) (fun i => (E i).source.gamma) c.val).source := ⟨x.val,hc⟩
  have he : (gammaGroundTensorGridBox X G (fun i => (E i).source.residue) (fun i => (E i).source.gamma) c.val).inclusion v = x :=
    Subtype.ext (Prod.eta x.val)
  have hh : (R.sourceMap c v).val = (a x).val := congrArg (fun p : gammaGroundNativeProductDomain X G => (a p).val) he
  exact ⟨c,Finset.mem_univ c,v,hh.trans hu⟩

/-- The corresponding old target patch is still covered, including
patches supplied by the inverse generic cover. -/
theorem original_target_covered (R : GammaGroundTensorSourceGridMatching F X G a Y H b E) (i : Fin N) :
    ((b i).comp (E i).target.inclusion).image.carrier ⊆
      (gammaGroundDefSetFiniteUnion Finset.univ (fun c : Cell (E := E) => (R.targetMap c).image)).carrier :=
  gammaGroundMatchedImages_target_subset_union F (fun c => (R.data c).bijection) R.sourceMap R.targetMap
    (fun c u => (R.data c).agrees u) (E i).data.bijection (a.comp (E i).source.inclusion)
      ((b i).comp (E i).target.inclusion) (E i).data.agrees (R.original_source_covered i)
end GammaGroundTensorSourceGridMatching
end DiamondIntegral.Section3
