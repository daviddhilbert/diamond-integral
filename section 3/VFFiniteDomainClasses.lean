import «section 3».VFSemiring
import «section 3».VFPositiveComparison

/-! Unbounded VF classes of actual finite-RV-fibre domains obey the
ordinary union/intersection scissors. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
variable (C : BaseContext M) (hc : CanonicalStructure.IsCanonical (M := M))
variable (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
variable {n r : ℕ}

abbrev MixedFiniteFibres (X : DefSet (rawMixedSpace (M := M) n r) (C.base : Set M)) :=
  ∀ a : Fin n → Section2.VF M, {t | (a, t) ∈ X.carrier}.Finite

def vfFiniteDomainClass (X : DefSet (rawMixedSpace (M := M) n r) (C.base : Set M))
    (hf : MixedFiniteFibres C X) : VFPositiveSemiring C hc hv :=
  vfSemiringClass C hc hv (vfObjectOfFiniteFibres X hf)

theorem vfFiniteDomainClass_empty :
    vfFiniteDomainClass C hc hv (DefSet.empty (rawMixedSpace (M := M) n r) (C.base : Set M))
      (fun _ => Set.finite_empty) = 0 := by
  exact (vfSemiringClass_bijection C hc hv
    (V := VFObject.empty (C.base : Set M) 0) (DefinableBijection.ofEmpty rfl rfl)).trans
      (vfSemiringClass_empty C hc hv)

theorem vfFiniteDomainClass_disjoint_union
    (X Y : DefSet (rawMixedSpace (M := M) n r) (C.base : Set M))
    (hX : MixedFiniteFibres C X) (hY : MixedFiniteFibres C Y)
    (hd : Disjoint X.carrier Y.carrier) :
    vfFiniteDomainClass C hc hv (X.union Y) (fun a => (hX a).union (hY a)) =
      vfFiniteDomainClass C hc hv X hX + vfFiniteDomainClass C hc hv Y hY := by
  let U := vfObjectOfFiniteFibres (X.union Y) (fun a => (hX a).union (hY a))
  have hsub : X.carrier ⊆ U.domain.carrier := fun _ h => Or.inl h
  have he : (U.difference X).carrier = Y.carrier := by
    ext t
    constructor
    · rintro ⟨ht, hn⟩
      exact ht.resolve_left hn
    · intro ht
      exact ⟨Or.inr ht, fun hx => Set.disjoint_left.mp hd hx ht⟩
  have hcut := vfSemiringClass_scissor C hc hv
    (show VFScissor (U.restrict X hsub) (U.restrict (U.difference X) (fun _ h => h.1)) U
      (VFObject.empty (C.base : Set M) n) from ⟨U, X, hsub, rfl, rfl, rfl, rfl⟩)
  rw [vfSemiringClass_empty, add_zero] at hcut
  have hx := vfSemiringClass_bijection C hc hv
    (U := U.restrict X hsub) (V := vfObjectOfFiniteFibres X hX) (DefinableBijection.id X)
  have hy := vfSemiringClass_bijection C hc hv
    (U := U.restrict (U.difference X) (fun _ h => h.1))
    (V := vfObjectOfFiniteFibres Y hY) (DefinableBijection.ofCarrierEq he)
  exact hcut.symm.trans (congrArg₂ (· + ·) hx hy)

theorem vfFiniteDomainClass_union_inter
    (X Y : DefSet (rawMixedSpace (M := M) n r) (C.base : Set M))
    (hX : MixedFiniteFibres C X) (hY : MixedFiniteFibres C Y) :
    vfFiniteDomainClass C hc hv X hX + vfFiniteDomainClass C hc hv Y hY =
      vfFiniteDomainClass C hc hv (X.union Y) (fun a => (hX a).union (hY a)) +
        vfFiniteDomainClass C hc hv (X.inter Y) (fun a => (hX a).subset (fun _ h => h.1)) := by
  let D := X.sdiff Y
  let I := X.inter Y
  have hD : MixedFiniteFibres C D := fun a => (hX a).subset (fun _ h => h.1)
  have hI : MixedFiniteFibres C I := fun a => (hX a).subset (fun _ h => h.1)
  have hdI : Disjoint D.carrier I.carrier := Set.disjoint_left.mpr (fun _ hd hi => hd.2 hi.2)
  have hdY : Disjoint D.carrier Y.carrier := Set.disjoint_left.mpr (fun _ hd hy => hd.2 hy)
  have heX : (D.union I).carrier = X.carrier := by ext t; change ((t ∈ X.carrier ∧ t ∉ Y.carrier) ∨ (t ∈ X.carrier ∧ t ∈ Y.carrier)) ↔ t ∈ X.carrier; tauto
  have heU : (D.union Y).carrier = (X.union Y).carrier := by ext t; change ((t ∈ X.carrier ∧ t ∉ Y.carrier) ∨ t ∈ Y.carrier) ↔ (t ∈ X.carrier ∨ t ∈ Y.carrier); tauto
  have h1 := vfFiniteDomainClass_disjoint_union C hc hv D I hD hI hdI
  have h2 := vfFiniteDomainClass_disjoint_union C hc hv D Y hD hY hdY
  have hx : vfFiniteDomainClass C hc hv X hX =
      vfFiniteDomainClass C hc hv D hD + vfFiniteDomainClass C hc hv I hI :=
    (vfSemiringClass_bijection C hc hv (U := vfObjectOfFiniteFibres X hX)
      (V := vfObjectOfFiniteFibres (D.union I) (fun a => (hD a).union (hI a)))
      (DefinableBijection.ofCarrierEq heX.symm)).trans h1
  have hu : vfFiniteDomainClass C hc hv (X.union Y) (fun a => (hX a).union (hY a)) =
      vfFiniteDomainClass C hc hv D hD + vfFiniteDomainClass C hc hv Y hY :=
    (vfSemiringClass_bijection C hc hv
      (U := vfObjectOfFiniteFibres (X.union Y) (fun a => (hX a).union (hY a)))
      (V := vfObjectOfFiniteFibres (D.union Y) (fun a => (hD a).union (hY a)))
      (DefinableBijection.ofCarrierEq heU.symm)).trans h2
  rw [hx, hu]
  ac_rfl

end DiamondIntegral.Section3
