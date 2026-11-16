import «section 6».UnaryRootFoci
import «section 6».FiniteInvariantRadii

/-! A single actual unary centripetal step can protect every member of
a finite proper invariant partition. The common aperture and all focus
restrictions are constructed over the original base. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6.UnaryFocusData

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {r k : ℕ} {S : Set M}
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S}

def restrict (D : UnaryFocusData A) (C : DefSet (rawMixedSpace (M := M) 1 r) S)
    (hCA : C.carrier ⊆ A.carrier) (hC : ProperInvariant S C.carrier) : UnaryFocusData C where
  activeTags := D.activeTags
  focus := D.focus
  focusMap := D.focusMap.comp (Map.inclusion (fun _ hp => ⟨hCA hp.1,hp.2⟩))
  focusMap_eq := fun p => D.focusMap_eq ⟨p.val,hCA p.property.1,p.property.2⟩
  sourceProper := hC
  sourceDoublyBounded := by
    obtain ⟨γ,hγ⟩ := D.sourceDoublyBounded
    exact ⟨γ,fun p hp => hγ p (hCA hp)⟩
  tagged := fun p hp q hq he => D.tagged p (hCA hp) q (hCA hq) he
  focusRV := fun p hp hu => D.focusRV p (hCA hp) hu

theorem restrict_focusImage_subset (D : UnaryFocusData A)
    (C : DefSet (rawMixedSpace (M := M) 1 r) S)
    (hCA : C.carrier ⊆ A.carrier) (hC : ProperInvariant S C.carrier) :
    scalarFocusImage (D.restrict C hCA hC).focusMap ⊆ scalarFocusImage D.focusMap := by
  rintro _ ⟨p,rfl⟩
  exact ⟨⟨p.val,hCA p.property.1,p.property.2⟩,rfl⟩

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

def protectedStep (D : UnaryFocusData A) (δ : Gamma M)
    (hδ : S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {δ}})
    (c : VF M) (hc0 : c ≠ 0) (hcpos : (1 : GammaInfinity M) ≤ vfValue c)
    (hcdef : S.Definable₁ LRV {c.val})
    (hcdom : ∀ a ∈ scalarFocusImage D.focusMap, δ.val < vfValue (c*a))
    (C : DefSet (rawMixedSpace (M := M) 1 r) S)
    (hCA : C.carrier ⊆ A.carrier) (hC : ProperInvariant S C.carrier)
    (hInvC : ∀ u, AlphaInvariant (fun _ => δ) (vfFibre C.carrier u)) : CentripetalData (G := G) C :=
  (D.restrict C hCA hC).withCoefficient δ hδ hInvC c hc0 hcpos hcdef
    (fun a ha => hcdom a (D.restrict_focusImage_subset C hCA hC ha))

theorem protectedStep_point (D : UnaryFocusData A) (δ : Gamma M)
    (hδ : S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {δ}})
    (hInv : ∀ u, AlphaInvariant (fun _ => δ) (vfFibre A.carrier u))
    (c : VF M) (hc0 : c ≠ 0) (hcpos : (1 : GammaInfinity M) ≤ vfValue c)
    (hcdef : S.Definable₁ LRV {c.val})
    (hcdom : ∀ a ∈ scalarFocusImage D.focusMap, δ.val < vfValue (c*a))
    (C : DefSet (rawMixedSpace (M := M) 1 r) S)
    (hCA : C.carrier ⊆ A.carrier) (hC : ProperInvariant S C.carrier)
    (hInvC : ∀ u, AlphaInvariant (fun _ => δ) (vfFibre C.carrier u))
    (p : Mixed M 1 r) (hp : p ∈ C.carrier) :
    (D.protectedStep δ hδ c hc0 hcpos hcdef hcdom C hCA hC hInvC).point p =
      (D.withCoefficient (G := G) δ hδ hInv c hc0 hcpos hcdef hcdom).point p := by
  let E := D.withCoefficient (G := G) δ hδ hInv c hc0 hcpos hcdef hcdom
  let F := D.protectedStep (G := G) δ hδ c hc0 hcpos hcdef hcdom C hCA hC hInvC
  have hExt : F.extendedFocus p = E.extendedFocus p := by
    by_cases hu : p.2 ∈ D.activeTags.carrier
    · rw [F.extendedFocus_active hp hu,E.extendedFocus_active (hCA hp) hu]
      rfl
    · rw [F.extendedFocus_inactive hu,E.extendedFocus_inactive hu]
  have hCore : F.core p = E.core p := by
    change decide (vfValue (c*F.extendedFocus p) < vfValue (p.1 0-F.extendedFocus p)) =
      decide (vfValue (c*E.extendedFocus p) < vfValue (p.1 0-E.extendedFocus p))
    rw [hExt]
  change F.point p = E.point p
  have hCoord : F.coordinate = E.coordinate := rfl
  have hCoeff : F.coefficient = E.coefficient := rfl
  simp only [CentripetalData.point,hExt,hCore,hCoord,hCoeff]

/-- One common permitted step on the ambient set and every protected
proper invariant subset, with identical formulas on their actual points. -/
theorem exists_protected_family_step (D : UnaryFocusData A)
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V, iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (C : Fin k → DefSet (rawMixedSpace (M := M) 1 r) S)
    (hCA : ∀ i, (C i).carrier ⊆ A.carrier) (hC : ∀ i, ProperInvariant S (C i).carrier) :
    ∃ E : CentripetalData (G := G) A, E.coordinate = 0 ∧ E.activeTags = D.activeTags ∧
      (∀ x u, E.focus x u = D.focus u) ∧
      ∀ i, ∃ F : CentripetalData (G := G) (C i), ∀ p ∈ (C i).carrier, F.point p = E.point p := by
  let H : Fin (k+1) → Set (Mixed M 1 r) := Fin.cons A.carrier (fun i => (C i).carrier)
  have hH : ∀ i, ProperInvariant S (H i) := Fin.cases D.sourceProper hC
  obtain ⟨δ,hδ,hδ0,hInv⟩ := finite_properInvariant_uniform_named_radius h00 hc linear hκ hs hv hsmall hΓ H hH
  have hInvA : ∀ u, AlphaInvariant (fun _ => δ) (vfFibre A.carrier u) := hInv 0
  have hInvC (i : Fin k) : ∀ u, AlphaInvariant (fun _ => δ) (vfFibre (C i).carrier u) := hInv i.succ
  obtain ⟨c,hc0,hcpos,hcdef,hcdom⟩ := exists_named_aperture_coefficient Valued.v hv hc h00 V S
    hV hVS hSV hnt _ (scalarFocusImage_definable D.focusMap)
    (D.focusImage_finite hc hs hsmall) D.focusImage_nonzero δ hδ
  refine ⟨D.withCoefficient δ hδ hInvA c hc0 hcpos hcdef hcdom,rfl,rfl,fun _ _ => rfl,fun i => ?_⟩
  exact ⟨D.protectedStep δ hδ c hc0 hcpos hcdef hcdom (C i) (hCA i) (hC i) (hInvC i),
    fun p hp => D.protectedStep_point δ hδ hInvA c hc0 hcpos hcdef hcdom (C i) (hCA i) (hC i) (hInvC i) p hp⟩

end DiamondIntegral.Section6.UnaryFocusData
