import «section 7».FibreInvariance
import «section 7».Corollary715

/-! Comparing fibre classes at nearby points (for Corollary 7.15).

* Support data `V` for a substructure `T` give support data `V ∪ b` for
  `S⟨b⟩ = adjoin T b` (`support_names`, `support_subset`, `adjoin_subset_acl`,
  `acl_field_mono`).
* `cls_fibreObject_eq`: if two VF points `a`, `b` have the same RV fibre in a
  mixed set and the form agrees on it, and definability over `S⟨b⟩` implies
  definability over `S⟨a⟩`, then the class of the fibre object at `a` over
  `S⟨a⟩` is the base extension of the class of the fibre object at `b`. The
  charts have the same domain, coordinates and volumes, so the identity is an
  isomorphism.
* `ispRel_one_iff`: `μIsp^db` in degree one is `MuIsp`. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section9
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section7.FibreComparison
open DiamondIntegral.Section6 DiamondIntegral.Section2
open DiamondIntegral.Section4 DiamondIntegral.Section4.RVMeasuredCharts
open DiamondIntegral.Section7.BoundedClasses DiamondIntegral.Section7.ChartOfMeasured
open DiamondIntegral.Section7.KernelBaseChange DiamondIntegral.Section7.BaseExtension
open DiamondIntegral.Section7.FibreObjects DiamondIntegral.Section7.LiftClasses
open DiamondIntegral.Section7.FiberwiseInput DiamondIntegral.Section7.BlowupCongruence

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable (hc : CanonicalStructure.IsCanonical (M := M)) {T : LRV.Substructure M} {m : ℕ}

/-! ### Support data for `S⟨b⟩` -/

include hc in
theorem adjoin_subset_acl (V : Set M) (hTV : (T : Set M) ⊆ algebraicClosureSet V) (b : Fin m → VF M) :
    (adjoin T b : Set M) ⊆ algebraicClosureSet (V ∪ Set.range (vfValues b)) := by
  have hTV' : (T : Set M) ∪ Set.range (vfValues b) ⊆ algebraicClosureSet (V ∪ Set.range (vfValues b)) := by
    rintro y (hy | ⟨j, rfl⟩)
    · exact algebraicClosureSet_mono Set.subset_union_left (hTV hy)
    · exact subset_algebraicClosureSet _ (Or.inr ⟨j, rfl⟩)
  intro x hx
  have hle : adjoin T b ≤ algebraicClosureSubstructure hc (V ∪ Set.range (vfValues b)) :=
    (Substructure.closure_le (L := LRV)).mpr hTV'
  exact hle hx

theorem acl_field_mono (V : Set M) (b : Fin m → VF M)
    (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1) :
    ∃ x : vfAlgebraicClosureField (V ∪ Set.range (vfValues b)), x ≠ 0 ∧ Valued.v x.val ≠ 1 := by
  obtain ⟨x, hx0, hxv⟩ := hnt
  have hmem : x.val ∈ vfAlgebraicClosureField (V ∪ Set.range (vfValues b)) :=
    (mem_vfAlgebraicClosureField _ _).mpr
      (((mem_vfAlgebraicClosureField V x.val).mp x.property).mono Set.subset_union_left)
  refine ⟨⟨x.val, hmem⟩, fun h => hx0 ?_, hxv⟩
  have h' : x.val = 0 := congrArg Subtype.val h
  exact Subtype.ext h'

omit [M ⊨ Axioms.ACVF] in
theorem support_names (V : Set M) (hV : ∀ x ∈ V, iVF x) (b : Fin m → VF M) :
    ∀ x ∈ V ∪ Set.range (vfValues b), iVF x := by
  rintro x (hx | ⟨j, rfl⟩)
  · exact hV x hx
  · exact (b j).property

theorem support_subset (V : Set M) (hVT : V ⊆ (T : Set M)) (b : Fin m → VF M) :
    V ∪ Set.range (vfValues b) ⊆ (adjoin T b : Set M) := by
  rintro x (hx | ⟨j, rfl⟩)
  · exact subset_adjoin b (hVT hx)
  · exact coordinate_mem_adjoin b j

/-! ### Fibre classes at nearby points -/

section Compare
variable {r k : ℕ} (A : DefSet (rawMixedSpace (M := M) m r) (T : Set M))
variable (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) (T : Set M)))

theorem fibreObject_domain (a : Fin m → VF M) (π : Fin k → Fin r) (hF) (hNZ) (u : Fin r → RVInfinity M) :
    u ∈ (fibreObject T A ω a π hF hNZ).object.domain.carrier ↔ (a, u) ∈ A.carrier :=
  mem_fibreDomain A a u

theorem fibreObject_value (a : Fin m → VF M) (π : Fin k → Fin r) (hF) (hNZ)
    (u : (fibreObject T A ω a π hF hNZ).object.domain) :
    (fibreObject T A ω a π hF hNZ).object.value u = u.val ∘ π := rfl

theorem fibreObject_form (a : Fin m → VF M) (π : Fin k → Fin r) (hF) (hNZ)
    (u : (fibreObject T A ω a π hF hNZ).object.domain) :
    gammaMapValue (fibreObject T A ω a π hF hNZ).form u =
      gammaMapValue ω ⟨(a, u.val), (mem_fibreDomain A a u.val).mp u.property⟩ :=
  fibreForm_apply A ω a u.val _

/-- **Fibre classes at nearby points.** -/
theorem cls_fibreObject_eq (a b : Fin m → VF M) (π : Fin k → Fin r)
    (hFa : ∀ t : Fin k → RVInfinity M, {u : Fin r → RVInfinity M | (a, u) ∈ A.carrier ∧ u ∘ π = t}.Finite)
    (hFb : ∀ t : Fin k → RVInfinity M, {u : Fin r → RVInfinity M | (b, u) ∈ A.carrier ∧ u ∘ π = t}.Finite)
    (hNZ : ∀ p ∈ A.carrier, ∀ i, (p.2 (π i)).val ≠ iRVZero)
    (hdom : ∀ u, (a, u) ∈ A.carrier ↔ (b, u) ∈ A.carrier)
    (hform : ∀ u (ha : (a, u) ∈ A.carrier) (hb : (b, u) ∈ A.carrier), ω ⟨_, ha⟩ = ω ⟨_, hb⟩)
    (ht : Transfer (BT (adjoin T b)) (BT (adjoin T a)))
    (hUa : (fibreObject T A ω a π hFa hNZ).doublyBounded) (hUb : (fibreObject T A ω b π hFb hNZ).doublyBounded) :
    cls (objOf hc (adjoin T a) (fibreObject T A ω a π hFa hNZ) hUa) =
      clsExt ht (cls (objOf hc (adjoin T b) (fibreObject T A ω b π hFb hNZ) hUb)) := by
  rw [clsExt_cls]
  apply cls_eq_iff.mpr
  let Xa := fibreObject T A ω a π hFa hNZ
  let Xb := fibreObject T A ω b π hFb hNZ
  have hD : rawDom Xa = rawDom Xb := by
    ext w
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u, (fibreObject_domain A ω b π hFb hNZ u).mpr ((hdom u).mp ((fibreObject_domain A ω a π hFa hNZ u).mp hu)), rfl⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u, (fibreObject_domain A ω a π hFa hNZ u).mpr ((hdom u).mpr ((fibreObject_domain A ω b π hFb hNZ u).mp hu)), rfl⟩
  have hpt (w : Fin r → M) (hwa : w ∈ rawDom Xa) (hwb : w ∈ rawDom Xb) : (pt Xa hwa).val = (pt Xb hwb).val :=
    rvValues_injective ((pt_val Xa hwa).trans (pt_val Xb hwb).symm)
  refine ⟨isoOfMap (objOf hc (adjoin T a) Xa hUa).toChart (objExt ht (objOf hc (adjoin T b) Xb hUb)).toChart id
    (RVSharpCharts.identity_graph_definable _ _ (chartOf hc Xa).domain_definable) ?_ ?_⟩
  · change Set.BijOn id (rawDom Xa) (rawDom Xb)
    rw [← hD]
    exact Set.bijOn_id _
  · have key : ∀ w : Fin r → M, w ∈ rawDom Xa →
        rawVol Xa w * ∏ i, codeValue (rawCoord Xa w i) = rawVol Xb w * ∏ i, codeValue (rawCoord Xb w i) := by
      intro w hw
      have hwb : w ∈ rawDom Xb := hD ▸ hw
      have hcoord : rawCoord Xa w = rawCoord Xb w := by
        unfold rawCoord
        rw [dif_pos hw, dif_pos hwb]
        change rvValues ((pt Xa hw).val ∘ π) = rvValues ((pt Xb hwb).val ∘ π)
        rw [hpt w hw hwb]
      have hvol : rawVol Xa w = rawVol Xb w := by
        unfold rawVol
        rw [dif_pos hw, dif_pos hwb, fibreObject_form, fibreObject_form]
        have hu := hpt w hw hwb
        have ha := (mem_fibreDomain A a _).mp (pt Xa hw).property
        have hb := (mem_fibreDomain A b _).mp (pt Xb hwb).property
        have h1 := hform (pt Xa hw).val ha (by rw [hu]; exact hb)
        unfold gammaMapValue
        rw [h1]
        congr 2
        exact Subtype.ext (Prod.ext rfl hu)
      rw [hcoord, hvol]
    intro w hw
    exact key w hw

end Compare

/-! ### Degree one -/

theorem ispRel_one_iff {B : GammaParameters.Base (M := M)} (x y : Cls B 1) :
    IspRel x y ↔ MuIsp (k := 0) x y :=
  ispRel_iff (show 1 = 1 + 0 from rfl) x y

end DiamondIntegral.Section7.FibreComparison
