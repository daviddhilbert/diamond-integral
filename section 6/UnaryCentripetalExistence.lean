import «section 6».FiniteFocusImages
import Section5.RootConstruction

/-! Every actual original-base unary RV-indexed focus has a permitted
finite-aperture centripetal realization. The finite image, named common
coefficient, and complete covariance data are constructed, rather than
supplied as a preparation or special-bijection existence input. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {r : ℕ} {S : Set M}

structure UnaryFocusData (A : DefSet (rawMixedSpace (M := M) 1 r) S) where
  activeTags : DefSet (rawRVSpace (M := M) r) S
  focus : (Fin r → RVInfinity M) → VF M
  focusMap : Map (focusActive A activeTags) (DefSet.univ (rawVFSpace 1) S)
  focusMap_eq : ∀ p : focusActive A activeTags, (focusMap p).val 0 = focus p.val.2
  sourceProper : ProperInvariant S A.carrier
  sourceDoublyBounded : VFDoublyBounded A.carrier
  tagged : ∀ p ∈ A.carrier, ∀ q ∈ A.carrier, p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1
  focusRV : ∀ p ∈ A.carrier, p.2 ∈ activeTags.carrier → rv M (focus p.2) = rv M (p.1 0)

namespace UnaryFocusData

variable {A : DefSet (rawMixedSpace (M := M) 1 r) S}

theorem focusImage_finite (D : UnaryFocusData A)
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal} (hs : Saturated M κ)
    (hsmall : Cardinal.mk S < κ) : (scalarFocusImage D.focusMap).Finite :=
  scalarFocusImage_finite hc hs hsmall D.focusMap (fun p q he => by
    rw [D.focusMap_eq,D.focusMap_eq,he])

theorem focusImage_nonzero (D : UnaryFocusData A) :
    ∀ a ∈ scalarFocusImage D.focusMap, a ≠ 0 := by
  rintro _ ⟨p,rfl⟩ he
  have hr := D.focusRV p.val p.property.1 p.property.2
  have he' : (D.focusMap p).val 0 = 0 := he
  have hzero : D.focus p.val.2 = 0 := (D.focusMap_eq p).symm.trans he'
  rw [hzero] at hr
  exact D.sourceDoublyBounded.nonzero p.property.1 0
    ((SpecialTransformations.Section5.rv_eq_zero_iff _).mp hr.symm)

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

def withCoefficient (D : UnaryFocusData A) (δ : Gamma M)
    (hδ : S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {δ}})
    (hInv : ∀ u, AlphaInvariant (fun _ => δ) (vfFibre A.carrier u))
    (c : VF M) (hc0 : c ≠ 0) (hcpos : (1 : GammaInfinity M) ≤ vfValue c)
    (hcdef : S.Definable₁ LRV {c.val})
    (hcdom : ∀ a ∈ scalarFocusImage D.focusMap, δ.val < vfValue (c*a)) :
    CentripetalData (G := G) A where
  coordinate := 0
  activeTags := D.activeTags
  focus := fun _ u => D.focus u
  focusMap := D.focusMap
  focusMap_eq := D.focusMap_eq
  sourceProper := D.sourceProper
  sourceDoublyBounded := D.sourceDoublyBounded
  tagged := D.tagged
  continuous := fun _ _ => continuous_const.continuousOn
  focusRV := D.focusRV
  coefficient := c
  coefficient_nonzero := hc0
  coefficient_nonnegative := hcpos
  coefficient_definable := hcdef
  covariance := by
    intro u hu
    have hn : (S ∪ Set.range (rvValues u)).Definable LRV
        {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {δ}} := hδ.mono Set.subset_union_left
    refine ⟨δ,fun _ => δ,hn,fun _ => hn,?_,?_,?_⟩
    · simpa only [ite_self] using hInv u
    · intro a ha b hb hab
      simpa only [sub_self,valueHom_eq_value] using gamma_lt_value_zero δ
    · intro a ha
      let p : focusActive A D.activeTags := ⟨(a,u),ha,hu⟩
      have hm : D.focus u ∈ scalarFocusImage D.focusMap :=
        ⟨p,D.focusMap_eq p⟩
      exact (hcdom _ hm).le

/-- Existence of a permitted unary finite-aperture step for the supplied
actual focus. The base and all old RV tags stay unchanged. -/
theorem exists_centripetal_data (D : UnaryFocusData A)
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V, iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1) :
    ∃ E : CentripetalData (G := G) A, E.coordinate = 0 ∧ E.activeTags = D.activeTags ∧
      (∀ x u, E.focus x u = D.focus u) ∧ HEq E.focusMap D.focusMap := by
  obtain ⟨δ,hδ,hδ0,hInv⟩ := properInvariant_uniform_named_radius h00 hc linear hκ hs hv hsmall hΓ D.sourceProper
  obtain ⟨c,hc0,hcpos,hcdef,hcdom⟩ := exists_named_aperture_coefficient Valued.v hv hc h00 V S
    hV hVS hSV hnt _ (scalarFocusImage_definable D.focusMap)
    (D.focusImage_finite hc hs hsmall) D.focusImage_nonzero δ hδ
  exact ⟨D.withCoefficient δ hδ hInv c hc0 hcpos hcdef hcdom,rfl,rfl,fun _ _ => rfl,HEq.rfl⟩

end UnaryFocusData
end DiamondIntegral.Section6
