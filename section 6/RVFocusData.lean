import «section 6».CarriedRootControl

/-! Actual scalar focus data independent of all VF inputs, in arbitrary
VF arity and at any coordinate. These retain the original-base graph
and permit a single coefficient to protect arbitrary proper subsets. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}

structure RVFocusData (A : DefSet (rawMixedSpace (M := M) n r) S) where
  coordinate : Fin n
  activeTags : DefSet (rawRVSpace (M := M) r) S
  focus : (Fin r → RVInfinity M) → VF M
  focusMap : Map (focusActive A activeTags) (DefSet.univ (rawVFSpace 1) S)
  focusMap_eq : ∀ p : focusActive A activeTags, (focusMap p).val 0 = focus p.val.2
  sourceProper : ProperInvariant S A.carrier
  sourceDoublyBounded : VFDoublyBounded A.carrier
  tagged : ∀ p ∈ A.carrier, ∀ q ∈ A.carrier, p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1
  focusRV : ∀ p ∈ A.carrier, p.2 ∈ activeTags.carrier → rv M (focus p.2) = rv M (p.1 coordinate)

namespace RVFocusData

variable {A : DefSet (rawMixedSpace (M := M) n r) S}

theorem focusImage_finite (D : RVFocusData A)
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal} (hs : Saturated M κ)
    (hsmall : Cardinal.mk S < κ) : (scalarFocusImage D.focusMap).Finite :=
  scalarFocusImage_finite hc hs hsmall D.focusMap (fun p q he => by
    rw [D.focusMap_eq,D.focusMap_eq,he])

theorem focusImage_nonzero (D : RVFocusData A) :
    ∀ a ∈ scalarFocusImage D.focusMap, a ≠ 0 := by
  rintro _ ⟨p,rfl⟩ he
  have hr := D.focusRV p.val p.property.1 p.property.2
  have hzero : D.focus p.val.2 = 0 := (D.focusMap_eq p).symm.trans he
  rw [hzero] at hr
  exact D.sourceDoublyBounded.nonzero p.property.1 D.coordinate
    ((SpecialTransformations.Section5.rv_eq_zero_iff _).mp hr.symm)

def restrict (D : RVFocusData A) (P : DefSet (rawMixedSpace (M := M) n r) S)
    (hPA : P.carrier ⊆ A.carrier) (hP : ProperInvariant S P.carrier) : RVFocusData P where
  coordinate := D.coordinate
  activeTags := D.activeTags
  focus := D.focus
  focusMap := D.focusMap.comp (Map.inclusion (fun _ hp => ⟨hPA hp.1,hp.2⟩))
  focusMap_eq := fun p => D.focusMap_eq ⟨p.val,hPA p.property.1,p.property.2⟩
  sourceProper := hP
  sourceDoublyBounded := by
    obtain ⟨γ,hγ⟩ := D.sourceDoublyBounded
    exact ⟨γ,fun p hp => hγ p (hPA hp)⟩
  tagged := fun p hp q hq => D.tagged p (hPA hp) q (hPA hq)
  focusRV := fun p hp hu => D.focusRV p (hPA hp) hu

theorem restrict_focusImage_subset (D : RVFocusData A)
    (P : DefSet (rawMixedSpace (M := M) n r) S)
    (hPA : P.carrier ⊆ A.carrier) (hP : ProperInvariant S P.carrier) :
    scalarFocusImage (D.restrict P hPA hP).focusMap ⊆ scalarFocusImage D.focusMap := by
  rintro _ ⟨p,rfl⟩
  exact ⟨⟨p.val,hPA p.property.1,p.property.2⟩,rfl⟩

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

def withCoefficient (D : RVFocusData A) (δ : Gamma M)
    (hδ : S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {δ}})
    (hInv : ∀ u, AlphaInvariant (fun _ => δ) (vfFibre A.carrier u))
    (c : VF M) (hc0 : c ≠ 0) (hcpos : (1 : GammaInfinity M) ≤ vfValue c)
    (hcdef : S.Definable₁ LRV {c.val})
    (hcdom : ∀ a ∈ scalarFocusImage D.focusMap, δ.val < vfValue (c*a)) :
    CentripetalData (G := G) A where
  coordinate := D.coordinate
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
      exact (hcdom _ ⟨p,D.focusMap_eq p⟩).le

theorem restriction_data (D : RVFocusData A) (δ : Gamma M)
    (hδ : S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {δ}})
    (hInv : ∀ u, AlphaInvariant (fun _ => δ) (vfFibre A.carrier u))
    (c : VF M) (hc0 : c ≠ 0) (hcpos : (1 : GammaInfinity M) ≤ vfValue c)
    (hcdef : S.Definable₁ LRV {c.val})
    (hcdom : ∀ a ∈ scalarFocusImage D.focusMap, δ.val < vfValue (c*a))
    (P : DefSet (rawMixedSpace (M := M) n r) S)
    (hPA : P.carrier ⊆ A.carrier) (hP : ProperInvariant S P.carrier)
    (hInvP : ∀ u, AlphaInvariant (fun _ => δ) (vfFibre P.carrier u)) :
    ApertureRestrictionData (D.withCoefficient (G := G) δ hδ hInv c hc0 hcpos hcdef hcdom)
      ((D.restrict P hPA hP).withCoefficient δ hδ hInvP c hc0 hcpos hcdef
        (fun a ha => hcdom a (D.restrict_focusImage_subset P hPA hP ha))) := by
  refine ⟨hPA,rfl,rfl,fun p hp => ?_⟩
  let E := D.withCoefficient (G := G) δ hδ hInv c hc0 hcpos hcdef hcdom
  let F := (D.restrict P hPA hP).withCoefficient (G := G) δ hδ hInvP c hc0 hcpos hcdef
    (fun a ha => hcdom a (D.restrict_focusImage_subset P hPA hP ha))
  change F.extendedFocus p = E.extendedFocus p
  by_cases hu : p.2 ∈ D.activeTags.carrier
  · rw [F.extendedFocus_active hp hu,E.extendedFocus_active (hPA hp) hu]
    rfl
  · rw [F.extendedFocus_inactive hu,E.extendedFocus_inactive hu]

end RVFocusData

def UnaryFocusData.toRVFocusData {A : DefSet (rawMixedSpace (M := M) 1 r) S}
    (D : UnaryFocusData A) : RVFocusData A :=
  ⟨0,D.activeTags,D.focus,D.focusMap,D.focusMap_eq,D.sourceProper,D.sourceDoublyBounded,D.tagged,D.focusRV⟩

end DiamondIntegral.Section6
