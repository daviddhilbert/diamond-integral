import «section 4».RVCoefficientTranslation
import «section 4».RVChartRestrictions
import «section 4».RVOrdinaryRing

/-! Variable RV apertures cancel after forgetting volume. The actual
positive-ray bundle is scaled by a retained nonzero RV coordinate; its
image is the deeper ray bundle. Scissors cancel the complementary
annulus without selecting any globally named RV representative. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section4

namespace DiamondIntegral.Section4.VariableApertureRayCancellation
open RVMeasuredCharts RVMeasuredProduct RVMeasuredProductProperties RVRealProducts
open FiniteTupleBlocks RVCoefficientShearGraphs RVChartDisjointUnion RVChartRestrictions
open GammaGroupNames

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {k : ℕ}

def rayProduct (r : Chart B k) : Chart B (1+k) :=
  product r (RVSharpCharts.sharpChart (RVMeasuredSpecialClasses.rayChart B))

def deepDomain (r : Chart B k) (j : Fin r.arity) : Set (Fin (1+r.arity) → M) :=
  shear j '' (rayProduct r).domain

theorem deepDomain_definable (r : Chart B k) (j : Fin r.arity) :
    DefinableOverBase B (fun _ : Fin (1+r.arity) => .rv) (deepDomain r j) := by
  have h := (RVCoefficientShearGraphs.graph_definable B (rayProduct r).domain
    (rayProduct r).domain_definable j).image_real
      (tailIndex (1+r.arity) (1+r.arity))
  change DefinableOverBase B (fun _ : Fin (1+r.arity) => .rv)
    ((fun w => w ∘ tailIndex (1+r.arity) (1+r.arity)) ''
      graphOn (rayProduct r).domain (shear j)) at h
  have he : deepDomain r j =
      (fun w => w ∘ tailIndex (1+r.arity) (1+r.arity)) ''
        graphOn (rayProduct r).domain (shear j) := by
    ext z
    constructor
    · rintro ⟨x,hx,rfl⟩
      refine ⟨join (1+r.arity) (1+r.arity) x (shear j x), ?_, ?_⟩
      · exact (RVRealProducts.graphOn_exists _ _ _).mpr ⟨x,hx,rfl⟩
      · exact funext (join_tail _ _ _ _)
    · rintro ⟨w,hw,rfl⟩
      obtain ⟨x,hx,rfl⟩ := (RVRealProducts.graphOn_exists _ _ _).mp hw
      exact ⟨x,hx,(funext (join_tail _ _ _ _)).symm⟩
  rw [he]
  exact h

theorem shear_injective (r : Chart B k) (j : Fin r.arity)
    (hp : ∀ x ∈ r.domain, NonzeroRV (x j)) :
    Set.InjOn (shear j) (rayProduct r).domain := by
  intro u hu v hv he
  obtain ⟨x,hx,z,hz,rfl⟩ := (productSet_exists r.domain _ u).mp hu
  obtain ⟨y,hy,w,hw,rfl⟩ := (productSet_exists r.domain _ v).mp hv
  rw [shear_join,shear_join] at he
  have hxy : x=y := by
    funext i
    have h := congrFun he (headIndex 1 r.arity i)
    simpa only [join_head] using h
  subst y
  have hzw : z=w := by
    let t := RVCoefficientTranslation.coefficientCode j x (hp x hx)
    apply RVScaledRays.scale_injective t (hz.1 0) (hw.1 0)
    funext i
    change RVNamedMultiplication.scale (x j) z i = RVNamedMultiplication.scale (x j) w i
    have h := congrFun he (tailIndex 1 r.arity i)
    simpa only [join_tail] using h
  rw [hzw]

theorem shear_mapsTo (r : Chart B k) (j : Fin r.arity)
    (hp : ∀ x ∈ r.domain, NonzeroRV (x j))
    (hn : ∀ x ∈ r.domain, 1 ≤ codeValue (x j)) :
    Set.MapsTo (shear j) (rayProduct r).domain (rayProduct r).domain := by
  intro u hu
  obtain ⟨x,hx,z,hz,rfl⟩ := (productSet_exists r.domain _ u).mp hu
  change Proper z ∧ 1 < codeValue (z 0) at hz
  change shear j (join 1 r.arity x z) ∈ productSet r.domain _
  rw [shear_join,productSet_join]
  refine ⟨hx,?_,?_⟩
  · intro i
    fin_cases i
    exact RVScaledRays.scale_nonzero
      (RVCoefficientTranslation.coefficientCode j x (hp x hx)) (hz.1 0)
  · change 1 < codeValue (iRVMul (x j) (z 0))
    rw [codeValue_mul _ _ (hp x hx) (hz.1 0)]
    exact (hn x hx).trans_lt (by simpa only [mul_one] using mul_lt_mul_right hz.2 (codeValue (x j)))

theorem deepDomain_subset (r : Chart B k) (j : Fin r.arity)
    (hp : ∀ x ∈ r.domain, NonzeroRV (x j))
    (hn : ∀ x ∈ r.domain, 1 ≤ codeValue (x j)) :
    deepDomain r j ⊆ (rayProduct r).domain := by
  rintro _ ⟨u,hu,rfl⟩
  exact shear_mapsTo r j hp hn hu

def deepChart (r : Chart B k) (j : Fin r.arity) : Chart B (1+k) :=
  (inside (ofChart (rayProduct r)) (deepDomain r j) (deepDomain_definable r j)).toChart

def annularChart (r : Chart B k) (j : Fin r.arity) : Chart B (1+k) :=
  (outside (ofChart (rayProduct r)) (deepDomain r j) (deepDomain_definable r j)).toChart

def rayToDeep (r : Chart B k) (j : Fin r.arity)
    (hp : ∀ x ∈ r.domain, NonzeroRV (x j))
    (hn : ∀ x ∈ r.domain, 1 ≤ codeValue (x j)) :
    RVForgetScissors.UnderlyingIso (rayProduct r) (deepChart r j) := by
  apply RVForgetScissors.ofMap _ _ (shear j)
    (RVCoefficientShearGraphs.graph_definable B _ (rayProduct r).domain_definable j)
  refine ⟨?_,shear_injective r j hp,?_⟩
  · intro u hu
    exact ⟨shear_mapsTo r j hp hn hu,⟨u,hu,rfl⟩⟩
  · intro u hu
    exact hu.2

theorem annular_class_zero (r : Chart B k) (j : Fin r.arity)
    (hp : ∀ x ∈ r.domain, NonzeroRV (x j))
    (hn : ∀ x ∈ r.domain, 1 ≤ codeValue (x j)) :
    RVOrdinaryRing.objectClass (annularChart r j) = 0 := by
  let a := ofChart (rayProduct r)
  let I := deepDomain r j
  let hI := deepDomain_definable r j
  have hP := RVOrdinaryRing.objectClass_iso
    (RVForgetScissors.ofMeasured (partitionIso a I hI))
  have hU := RVChartUnionProperties.ordinary_class (outside a I hI) (inside a I hI)
    (pieces_disjoint a I hI)
  have hD := RVOrdinaryRing.objectClass_iso (rayToDeep r j hp hn)
  change RVOrdinaryRing.objectClass (rayProduct r) =
    RVOrdinaryRing.objectClass (deepChart r j) at hD
  have hSplit : RVOrdinaryRing.objectClass (rayProduct r) =
      RVOrdinaryRing.objectClass (annularChart r j)+RVOrdinaryRing.objectClass (deepChart r j) :=
    hP.symm.trans hU
  rw [hD] at hSplit
  exact (add_right_cancel (show (0 : RVOrdinaryRing.Ring B) +
      RVOrdinaryRing.objectClass (deepChart r j) =
      RVOrdinaryRing.objectClass (annularChart r j)+RVOrdinaryRing.objectClass (deepChart r j) by
      simpa only [zero_add] using hSplit)).symm

end DiamondIntegral.Section4.VariableApertureRayCancellation
