import «section 6».UnaryNoncoreFibres
import «section 6».OrdinaryMaps
import Section5.UnarySets
import Section3.BallTranslation

/-! The partition invariant for unary root preparation. A root-free
open disc contained in the actual ambient fiber has constant membership
in every controlled piece. Initial root families are constructed from
the checked original-base finite obstacle theorem. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {r : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

def UnaryRootControl {A : DefSet (rawMixedSpace (M := M) 1 r) S}
    (R : UnaryRootFamily A) (C : Set (Mixed M 1 r)) : Prop :=
  ∀ (u : Fin r → RVInfinity M) (a : VF M) (ρ : Balls.OpenRadius G),
    (∀ x ∈ Balls.openDisc Valued.v a ρ, ((fun _ : Fin 1 => x),u) ∈ A.carrier) →
    (∀ x ∈ R.fibre u, x ∉ Balls.openDisc Valued.v a ρ) →
    ∀ x ∈ Balls.openDisc Valued.v a ρ, ∀ y ∈ Balls.openDisc Valued.v a ρ,
      (((fun _ : Fin 1 => x),u) ∈ C ↔ ((fun _ : Fin 1 => y),u) ∈ C)

def UnaryObstacleControl (Q : Finset (VF M)) (C : Set (Mixed M 1 r)) : Prop :=
  ∀ (a : VF M) (ρ : Balls.OpenRadius G),
    (∀ x ∈ Q, x ∉ Balls.openDisc Valued.v a ρ) →
    ∀ x ∈ Balls.openDisc Valued.v a ρ, ∀ y ∈ Balls.openDisc Valued.v a ρ,
    ∀ u : Fin r → RVInfinity M, (((fun _ : Fin 1 => x),u) ∈ C ↔ ((fun _ : Fin 1 => y),u) ∈ C)

namespace UnaryRootFamily

variable {A : DefSet (rawMixedSpace (M := M) 1 r) S}

def fromObstacles (A : DefSet (rawMixedSpace (M := M) 1 r) S) (Q : Finset (VF M))
    (hQ : S.Definable₁ LRV (Subtype.val '' (Q : Set (VF M)))) : UnaryRootFamily A := by
  let H : Set (Mixed M 1 r) := {p | p ∈ A.carrier ∧ p.1 0 ∈ Q}
  have hH : (rawMixedSpace (M := M) 1 r).Definable S H := by
    apply (mixed_definable_iff_values_image S H).mpr
    change S.Definable LRV {z : Fin 1 → M | z 0 ∈ Subtype.val '' (Q : Set (VF M))} at hQ
    have h := ((mixed_definable_iff_values_image S _).mp A.definable).inter
      (hQ.preimage_comp (fun _ : Fin 1 => (Sum.inl (0 : Fin 1) : Fin 1 ⊕ Fin r)))
    convert h using 1
    ext z
    constructor
    · rintro ⟨p,⟨hp,hpQ⟩,he⟩
      exact ⟨⟨p,hp,he⟩,p.1 0,hpQ,congrFun he (.inl 0)⟩
    · rintro ⟨⟨p,hp,he⟩,x,hx,hxz⟩
      have hxp : x = p.1 0 := Subtype.ext (hxz.trans (congrFun he (.inl 0)).symm)
      exact ⟨p,⟨hp,hxp ▸ hx⟩,he⟩
  exact ⟨⟨H,hH⟩,fun _ hp => hp.1,fun u => Q.finite_toSet.subset (fun _ hx => hx.2)⟩

theorem fromObstacles_control (Q : Finset (VF M))
    (hQ : S.Definable₁ LRV (Subtype.val '' (Q : Set (VF M))))
    (C : Set (Mixed M 1 r)) (hC : UnaryObstacleControl (G := G) Q C) :
    UnaryRootControl (G := G) (fromObstacles A Q hQ) C := by
  intro u a ρ hambient havoid x hx y hy
  apply hC a ρ ?_ x hx y hy u
  intro z hz hzd
  apply havoid z _ hzd
  exact ((fromObstacles A Q hQ).mem_fibre u z).mpr ⟨hambient z hzd,hz⟩

end UnaryRootFamily

theorem exists_unary_obstacles
    (hc : CanonicalStructure.IsCanonical (M := M))
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (C : DefSet (rawMixedSpace (M := M) 1 r) S) :
    ∃ Q : Finset (VF M), S.Definable₁ LRV (Subtype.val '' (Q : Set (VF M))) ∧
      UnaryObstacleControl (G := G) Q C.carrier := by
  let C' := toOrdinarySet hc C
  let U := SpecialTransformations.Section5.rawUnarySet C'
  obtain ⟨Q,hQne,hQdef,hO,hOclosed⟩ := mixed_finite_definable_obstacles Valued.v hv S U
    (SpecialTransformations.Section5.rawUnarySet_definable C')
  refine ⟨Q,hQdef.raw_definable,?_⟩
  intro a ρ havoid x hx y hy u
  have h := hO a ρ havoid x hx y hy (rvValues u) (fun i => (u i).property)
  have he (z : VF M) : Fin.cons z.val (rvValues u) ∈ U ↔
      ((fun _ : Fin 1 => z),u) ∈ C.carrier :=
    SpecialTransformations.Section5.mem_rawUnarySet_values C' ((fun _ => z),u)
  exact (he x).symm.trans (h.trans (he y))

theorem UnaryRootControl.empty_roots_rvPullback
    {A : DefSet (rawMixedSpace (M := M) 1 r) S} {R : UnaryRootFamily A} {C : Set (Mixed M 1 r)}
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hcontrol : UnaryRootControl (G := G) R C) (hR : R.roots.carrier = ∅)
    (hA : IsRVPullback A.carrier) (hD : VFDoublyBounded A.carrier) (hCA : C ⊆ A.carrier) :
    IsRVPullback C := by
  apply Set.Subset.antisymm _ (subset_rvHull _)
  intro q hq
  obtain ⟨p,hp,hVF,hRV⟩ := (mem_rvHull_iff C q).mp hq
  have hpA := hCA hp
  have hp0 : p.1 0 ≠ 0 := hD.nonzero hpA 0
  let ρ : Balls.OpenRadius G := Balls.openRadius (Valued.v (p.1 0))
    ((map_ne_zero (Valued.v : Valuation (VF M) G)).mpr hp0)
  have hdisc := Balls.rvFibre_eq_openDisc Valued.v hv (p.1 0) hp0
  have hrv (x : VF M) : x ∈ Balls.openDisc Valued.v (p.1 0) ρ ↔ rv M x = rv M (p.1 0) := by
    rw [← hdisc]
    change iRv x.val = iRv (p.1 0).val ↔ rv M x = rv M (p.1 0)
    exact ⟨fun h => Subtype.ext h,fun h => congrArg Subtype.val h⟩
  have hambient (x : VF M) (hx : x ∈ Balls.openDisc Valued.v (p.1 0) ρ) :
      ((fun _ : Fin 1 => x),p.2) ∈ A.carrier := rvPullback_mem_of_sameRV hA hpA (by
    funext i
    fin_cases i
    exact ((hrv x).mp hx).symm) rfl
  have havoid (x : VF M) (hx : x ∈ R.fibre p.2) : x ∉ Balls.openDisc Valued.v (p.1 0) ρ := by
    have hh := (R.mem_fibre _ _).mp hx
    rw [hR] at hh
    exact False.elim hh
  have hpdisc := Balls.centre_mem_openDisc Valued.v (p.1 0) ρ
  have hqdisc : q.1 0 ∈ Balls.openDisc Valued.v (p.1 0) ρ := (hrv _).mpr (congrFun hVF 0).symm
  have he := hcontrol p.2 (p.1 0) ρ hambient havoid (p.1 0) hpdisc (q.1 0) hqdisc
  have hpEta : ((fun _ : Fin 1 => p.1 0),p.2) = p := by
    apply Prod.ext
    · funext i
      fin_cases i
      rfl
    · rfl
  have hqEta : ((fun _ : Fin 1 => q.1 0),p.2) = q := by
    apply Prod.ext
    · funext i
      fin_cases i
      rfl
    · exact hRV
  rw [hpEta,hqEta] at he
  exact he.mp hp

end DiamondIntegral.Section6
