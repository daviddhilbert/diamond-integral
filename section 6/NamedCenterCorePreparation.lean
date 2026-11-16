import «section 6».NamedUnaryOffsets

/-! Prepared neighborhoods of actual separated centers. The offset
coefficient is named over the original base; the domains contain every
center and their special preparations are explicitly constructed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r : ℕ}
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem unaryLabelCenterFocusData_centers
    (E : DefSet (rawMixedSpace (M := M) 1 r) S)
    (hUnique : ∀ p q : E,p.val.2=q.val.2 → p=q) (hEA : E.carrier ⊆ A.carrier)
    (hA : ProperInvariant S A.carrier) (hD : VFDoublyBounded A.carrier)
    (hTag : ∀ p ∈ A.carrier,∀ q ∈ A.carrier,p.2=q.2 → tupleRV M p.1=tupleRV M q.1)
    (u : Fin r → RVInfinity M) (hu : u ∈ (pureRVTagDomain E).carrier) :
    ((fun _ : Fin 1 => (unaryLabelCenterFocusData E hUnique hEA hA hD hTag).focus u),u) ∈ A.carrier := by
  obtain ⟨p,hp⟩ := (pureRVTagQuotient_surjective E) ⟨u,hu⟩
  have hpu : p.val.2=u := congrArg Subtype.val hp
  have hPoint : ((fun _ : Fin 1 => unaryLabelCenter E hUnique u),u)=p.val := by
    apply Prod.ext
    · funext i
      fin_cases i
      rw [← hpu,unaryLabelCenter_at E hUnique p]
      rfl
    · exact hpu.symm
  change ((fun _ : Fin 1 => unaryLabelCenter E hUnique u),u) ∈ A.carrier
  rw [hPoint]
  exact hEA p.property

theorem UnaryFocusData.exists_named_coefficient_core_preparation (F : UnaryFocusData A)
    (hRV : IsRVPullback A.carrier)
    (hCenters : ∀ u ∈ F.activeTags.carrier,((fun _ : Fin 1 => F.focus u),u) ∈ A.carrier)
    (c : VF M) (hc0 : c ≠ 0) (hcDef : S.Definable₁ LRV {c.val})
    (hcPos : (1 : GammaInfinity M) < vfValue c)
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V,iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V,x ≠ 0 ∧ Valued.v x.val ≠ 1) :
    Nonempty (UnaryTagPreparation (G := G) (F.offsetCoreDomain (F.namedOffsetMap c hcDef))) := by
  let d (u) := c*F.focus u
  have hf0 (u) (hu : u ∈ F.activeTags.carrier) : F.focus u ≠ 0 :=
    F.sourceDoublyBounded.nonzero (hCenters u hu) 0
  exact F.exists_offset_core_preparation (F.namedOffsetMap c hcDef) d (F.namedOffsetMap_value c hcDef)
    hRV hCenters (fun u hu => mul_ne_zero hc0 (hf0 u hu))
    (fun u hu => vf_value_lt_positive_named_offset (F.focus u) c (hf0 u hu) hc0 hcPos)
    h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt

theorem unaryLabelCenterFocusData_centers_mem_core
    (E : DefSet (rawMixedSpace (M := M) 1 r) S)
    (hUnique : ∀ p q : E,p.val.2=q.val.2 → p=q) (hEA : E.carrier ⊆ A.carrier)
    (hA : ProperInvariant S A.carrier) (hD : VFDoublyBounded A.carrier)
    (hTag : ∀ p ∈ A.carrier,∀ q ∈ A.carrier,p.2=q.2 → tupleRV M p.1=tupleRV M q.1)
    (c : VF M) (hc0 : c ≠ 0) (hcDef : S.Definable₁ LRV {c.val}) :
    let F := unaryLabelCenterFocusData E hUnique hEA hA hD hTag
    E.carrier ⊆ (F.offsetCoreDomain (F.namedOffsetMap c hcDef)).carrier := by
  intro F p hp
  let q : E := ⟨p,hp⟩
  let d (u) := c*F.focus u
  rw [F.mem_offsetCoreDomain (F.namedOffsetMap c hcDef) d (F.namedOffsetMap_value c hcDef)]
  have hu : p.2 ∈ F.activeTags.carrier := (pureRVTagQuotient E q).property
  have hCenter : F.focus p.2=p.1 0 := unaryLabelCenter_at E hUnique q
  refine ⟨hEA hp,hu,?_⟩
  have hd : d p.2 ≠ 0 := mul_ne_zero hc0 (by rw [hCenter]; exact hD.nonzero (hEA hp) 0)
  rw [hCenter,sub_self]
  exact gamma_lt_value_zero (finiteValue (d p.2) hd)

end DiamondIntegral.Section6
