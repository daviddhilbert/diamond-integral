import «section 6».DefinableFreezing

/-! Original-base finite freezing on actual open balls. Equal-radius
balls are disjoint or equal, and their VF realizations are clopen. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open DiamondIntegral.Section2

namespace DiamondIntegral.Section6.FMT

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

def vfOpenBall (D : OpenBallCodes.OpenBall M) : Set (VF M) :=
  {x | x.val ∈ OpenBallCodes.underlying D}

theorem vfOpenBall_clopen
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (D : OpenBallCodes.OpenBall M) : IsClopen (vfOpenBall D) := by
  obtain ⟨q,rfl⟩ := Quotient.exists_rep D
  change IsClopen (OpenBallCodes.ball q.val)
  rw [OpenBallCodes.ball_eq_open Valued.v hv q.val q.property]
  let a : VF M := ⟨q.val 0,q.property.1 0⟩
  let r : VF M := ⟨q.val 1,q.property.1 1⟩
  change IsClopen {x : VF M | Valued.v (x-a) < Valued.v r}
  have hcl := (Valued.isClopen_ball (VF M) (Valued.v.restrict r)).preimage
    (continuous_id.sub continuous_const : Continuous (fun x : VF M => x-a))
  convert hcl using 1
  ext x
  exact (Valuation.restrict_lt_iff Valued.v).symm

def SameOpenRadius (A : Set (OpenBallCodes.OpenBall M)) (r : VF M) : Prop :=
  ∀ D ∈ A, ∃ a : VF M, vfOpenBall D = {x | Valued.v (x-a) < Valued.v r}

theorem sameOpenRadius_separated (A : Set (OpenBallCodes.OpenBall M)) (r : VF M)
    (hR : SameOpenRadius (G := G) A r) :
    ∀ D E : A, ∀ x, x ∈ OpenBallCodes.underlying D.val →
      x ∈ OpenBallCodes.underlying E.val → D = E := by
  intro D E x hx hE
  obtain ⟨a,ha⟩ := hR D.val D.property
  obtain ⟨b,hb⟩ := hR E.val E.property
  let z : VF M := ⟨x,OpenBallCodes.underlying_subset_vf D.val hx⟩
  have hza : Valued.v (z-a) < Valued.v r := (Set.ext_iff.mp ha z).mp hx
  have hzb : Valued.v (z-b) < Valued.v r := (Set.ext_iff.mp hb z).mp hE
  have he : vfOpenBall D.val = vfOpenBall E.val := by
    rw [ha,hb]
    ext y
    exact (Balls.strictDisc_recenter_iff Valued.v a z y r hza).symm.trans
      (Balls.strictDisc_recenter_iff Valued.v b z y r hzb)
  apply Subtype.ext
  apply OpenBallCodes.underlying_injective
  ext y
  by_cases hy : iVF y
  · exact Set.ext_iff.mp he (⟨y,hy⟩ : VF M)
  · exact iff_of_false (fun h => hy (OpenBallCodes.underlying_subset_vf D.val h))
      (fun h => hy (OpenBallCodes.underlying_subset_vf E.val h))

theorem vfFamilyFreeze_continuous
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (A : Set (OpenBallCodes.OpenBall M)) (hA : A.Finite) (c : A → VF M)
    (hsep : ∀ D E : A, ∀ x, x ∈ OpenBallCodes.underlying D.val →
      x ∈ OpenBallCodes.underlying E.val → D = E) : Continuous (vfFamilyFreeze A c) := by
  letI : Finite A := hA.to_subtype
  have he : vfFamilyFreeze A c = familyFreeze (fun D : A => vfOpenBall D.val) c :=
    funext (vfFamilyFreeze_eq A c hsep)
  rw [he]
  exact familyFreeze_continuous _ _ (fun D E x hx hE => hsep D E x.val hx hE)
    (fun D => vfOpenBall_clopen hv D.val)

/-- Complete finite freezing data over the original real base. The
remaining product-domain premise belongs to each focus domain where
the freezing operation is subsequently applied. -/
theorem exists_original_base_finite_freezing
    (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V S : Set M) (hV : ∀ a ∈ V, iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A : Set (OpenBallCodes.OpenBall M)) (hA : A.Finite)
    (hAdef : S.Definable LRV (OpenBallCodes.pullback A))
    (r : VF M) (hR : SameOpenRadius (G := G) A r) :
    ∃ c : A → VF M, (∀ D, c D ∈ vfOpenBall D.val) ∧
      S.DefinableFun LRV (fun z : Fin 1 → M => rawFamilyFreeze A c (z 0)) ∧
      Continuous (vfFamilyFreeze A c) ∧
      (∀ D : A, ∀ x ∈ vfOpenBall D.val, vfFamilyFreeze A c x = c D) ∧
      (∀ x : VF M, (∀ D : A, x ∉ vfOpenBall D.val) → vfFamilyFreeze A c x = x) := by
  obtain ⟨c,hcMem,hcGraph⟩ := exists_original_base_open_center_graph hc h00 hv V S hV hVS hSV hnt A hA hAdef
  have hsep := sameOpenRadius_separated A r hR
  refine ⟨c,hcMem,rawFamilyFreeze_definable A c hsep hAdef hcGraph,
    vfFamilyFreeze_continuous hv A hA c hsep,?_,?_⟩
  · intro D x hx
    rw [vfFamilyFreeze_eq A c hsep]
    exact familyFreeze_inside _ _ (fun D E y hy hE => hsep D E y.val hy hE) D x hx
  · intro x hx
    rw [vfFamilyFreeze_eq A c hsep]
    exact familyFreeze_outside _ _ x hx

end DiamondIntegral.Section6.FMT
