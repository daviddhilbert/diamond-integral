import «section 6».NamedCenterCorePreparation

/-! Actual prepared neighborhoods of any label-separated center family.
The named VF coefficient can be chosen beyond a prescribed named floor,
and every original center belongs to its constructed core. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem exists_prepared_separated_center_neighborhoods
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V,iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V,x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A E : DefSet (rawMixedSpace (M := M) 1 r) S) (hEA : E.carrier ⊆ A.carrier)
    (hUnique : ∀ p q : E,p.val.2=q.val.2 → p=q)
    (hA : ProperInvariant S A.carrier) (hD : VFDoublyBounded A.carrier) (hRV : IsRVPullback A.carrier)
    (hTag : ∀ p ∈ A.carrier,∀ q ∈ A.carrier,p.2=q.2 → tupleRV M p.1=tupleRV M q.1)
    (ρ : Gamma M) (hρ1 : 1 ≤ ρ)
    (hρ : S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {ρ}}) :
    ∃ (c : VF M) (hc0 : c ≠ 0) (hcDef : S.Definable₁ LRV {c.val}),ρ.val < vfValue c ∧
      let F := unaryLabelCenterFocusData E hUnique hEA hA hD hTag
      E.carrier ⊆ (F.offsetCoreDomain (F.namedOffsetMap c hcDef)).carrier ∧
      Nonempty (UnaryTagPreparation (G := G) (F.offsetCoreDomain (F.namedOffsetMap c hcDef))) := by
  obtain ⟨c,hc0,hcDef,hρc⟩ := exists_named_vf_above_radius Valued.v hv hc h00 V S hV hVS hSV hnt ρ hρ1 hρ
  refine ⟨c,hc0,hcDef,hρc,?_⟩
  let F := unaryLabelCenterFocusData E hUnique hEA hA hD hTag
  have hPos : (1 : GammaInfinity M) < vfValue c := (show (1 : GammaInfinity M) ≤ ρ.val from hρ1).trans_lt hρc
  exact ⟨unaryLabelCenterFocusData_centers_mem_core E hUnique hEA hA hD hTag c hc0 hcDef,
    F.exists_named_coefficient_core_preparation hRV
      (unaryLabelCenterFocusData_centers E hUnique hEA hA hD hTag) c hc0 hcDef hPos
      h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt⟩

end DiamondIntegral.Section6
