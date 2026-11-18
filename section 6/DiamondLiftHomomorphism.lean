import «section 6».DiamondSurjectivity
import «section 6».DiamondEmpty
import «section 6».ZeroArityRVIsomorphismLifts
import «section 6».MeasuredRVRestrictionBounds

/-! Corollary 6.37 (`L:sur:c`): the lifting maps `μL_k` induce surjective
homomorphisms `K_+ μRV^db[k] → K_+ μVF^◇[k]`.

`K_+ μRV^db[k]` is the positive scissor presentation of doubly bounded
measured RV objects (isomorphism: measured RV isomorphism; scissor: a
definable piece of the domain and its complement). The lift respects
isomorphisms (Lemma 6.33 in positive degree over a VF-generated base, and the
degree-zero relabelling of Lemma 6.31), empty objects and scissors, so it
descends; surjectivity is `DiamondSurjectivity`. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6.DiamondLiftHomomorphism
open DiamondIntegral.Section6 DiamondIntegral.Section6.DiamondCategory
open DiamondIntegral.Section6.DiamondGrothendieck DiamondIntegral.Section6.DiamondLift
open DiamondIntegral.Section6.DiamondEmpty DiamondIntegral.Section6.DiamondSurjectivity

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

/-- In degree zero every bijection between definable sets with doubly bounded
RV support is a proper covariant homeomorphism. -/
theorem homeo_zero {r s : ℕ} {A : DefSet (rawMixedSpace (M := M) 0 r) S}
    {B : DefSet (rawMixedSpace (M := M) 0 s) S} (f : Map A B) (hf : Function.Bijective f)
    (hA : RVSupportDoublyBounded A.carrier) (hB : RVSupportDoublyBounded B.carrier) :
    ProperCovariantHomeomorphism (G := G) f := by
  have cov : ∀ {r s : ℕ} {A : DefSet (rawMixedSpace (M := M) 0 r) S}
      {B : DefSet (rawMixedSpace (M := M) 0 s) S} (g : Map A B),
      RVSupportDoublyBounded A.carrier → RVSupportDoublyBounded B.carrier → ProperCovariant g := by
    intro r s A B g hA hB
    refine ⟨⟨1, fun _ _ i => i.elim0⟩, ⟨1, fun _ _ i => i.elim0⟩, hA,
      hB.mono (fun _ ⟨p, hp⟩ => hp ▸ (g p).property), fun u v => ?_⟩
    refine ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
      fun a b _ => ?_, fun a b _ => ?_, fun _ _ _ _ _ i => i.elim0⟩
    · rw [Subsingleton.elim a b]
    · rw [Subsingleton.elim a b]
  have cont : ∀ {r s : ℕ} {A : DefSet (rawMixedSpace (M := M) 0 r) S}
      {B : DefSet (rawMixedSpace (M := M) 0 s) S} (g : Map A B), ContinuousOnGraphFibres (G := G) g :=
    fun g u v => Set.subsingleton_of_subsingleton.continuousOn _
  exact ⟨hf, cov f hA hB, cont f, cov _ hB hA, cont _⟩

/-- Degree zero: the lift of a measured RV isomorphism, a morphism of `μVF^◇[0]`
(the Lemma 6.31 zero-arity relabelling). -/
def zeroMorphism {U V : MeasuredRVObject (M := M) S 0} (e : MeasuredRVIso U V)
    (hU : ProperInvariant S (rvLift U.object).carrier) (hV : ProperInvariant S (rvLift V.object).carrier) :
    Morphism G (liftObject U hU) (liftObject V hV) where
  map := zeroArityRVLift e.iso
  bijective := zeroArityRVLift_bijective e.iso
  factor := UnaryFactorization.step
    (homeo_zero _ (zeroArityRVLift_bijective e.iso) hU.rvBounded hV.rvBounded) (Or.inl rfl)
  bad := DefSet.empty _ S
  bad_subset := Set.empty_subset _
  bad_small := Or.inr rfl
  measure p _ := by
    refine ⟨_, mixedDerivative_zero_arity _ p, ?_⟩
    change vfValue (LinearMap.toMatrix' LinearMap.id).det =
      (gammaMapValue U.form (liftLabelMap U.object p) /
        gammaMapValue V.form (liftLabelMap V.object (zeroArityRVLift e.iso p))).val
    rw [LinearMap.toMatrix'_id, Matrix.det_one, zeroArityRVLift_label, e.gamma_jacobian]
    simp only [rvGammaJacobian, rvVolumeGamma, Finset.prod_empty, Finset.univ_eq_empty, div_self']
    change Values.vfValueHom 1 = Values.gammaValHom 1
    rw [map_one, map_one]

/-- Degree zero: measured RV isomorphisms lift to isomorphisms of `μVF^◇[0]`. -/
theorem lift_isomorphic_zero {U V : MeasuredRVObject (M := M) S 0} (e : MeasuredRVIso U V)
    (hU : ProperInvariant S (rvLift U.object).carrier) (hV : ProperInvariant S (rvLift V.object).carrier) :
    Isomorphic G (liftObject U hU) (liftObject V hV) :=
  ⟨zeroMorphism e hU hV⟩

/-- Positive degree: measured RV isomorphisms of doubly bounded objects over a
VF-generated base lift to isomorphisms of `μVF^◇[k]` (Lemma 6.33). -/
theorem lift_isomorphic_pos (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (T : LRV.Substructure M) (B₀ : VFGeneratedFieldBase T) (hsmall : Cardinal.mk (T : Set M) < κ)
    (hΓ : NontrivialDefinableGamma (⟨(T : Set M), ∅⟩ : ParameterBase M))
    (hnt : ∃ x : B₀.field, x ≠ 0 ∧ Valued.v x.val ≠ 1) (hk : 0 < k)
    {U V : MeasuredRVObject (M := M) (T : Set M) k} (e : MeasuredRVIso U V)
    (hUd : U.doublyBounded) (hVd : V.doublyBounded)
    (hU : ProperInvariant (T : Set M) (rvLift U.object).carrier)
    (hV : ProperInvariant (T : Set M) (rvLift V.object).carrier) :
    Isomorphic G (liftObject U hU) (liftObject V hV) := by
  obtain ⟨L, _, _, hprop, _⟩ := lemma_6_33_doublyBounded_vfGenerated (G := G) h00 hc linear hκ hs hv
    T B₀ hsmall hΓ hnt hk e hUd hVd
  exact ⟨liftMorphism hU hV L hprop⟩

/-- Lemma 6.33 in every degree, in the `μVF^◇` interface: a measured RV
isomorphism of doubly bounded objects over a VF-generated base lifts to a
morphism of `μVF^◇[k]` between the lifts, compatible with the given RV map on
labels. In positive degree the lift is Section 6's chain of relatively unary
proper covariant measured lifts; in degree zero it is the relabelling. -/
theorem lemma_6_33_diamond (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (T : LRV.Substructure M) (B₀ : VFGeneratedFieldBase T) (hsmall : Cardinal.mk (T : Set M) < κ)
    (hΓ : NontrivialDefinableGamma (⟨(T : Set M), ∅⟩ : ParameterBase M))
    (hnt : ∃ x : B₀.field, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    {U V : MeasuredRVObject (M := M) (T : Set M) k} (e : MeasuredRVIso U V)
    (hUd : U.doublyBounded) (hVd : V.doublyBounded)
    (hU : ProperInvariant (T : Set M) (rvLift U.object).carrier)
    (hV : ProperInvariant (T : Set M) (rvLift V.object).carrier) :
    ∃ F : Morphism G (liftObject U hU) (liftObject V hV),
      ∀ p, e.iso.hom.map.graph p.val.2 (F.map p).val.2 := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    exact ⟨zeroMorphism e hU hV, fun p => ⟨liftLabelMap U.object p, rfl, rfl⟩⟩
  · obtain ⟨L, hL, _, hprop, _⟩ := lemma_6_33_doublyBounded_vfGenerated (G := G) h00 hc linear hκ hs hv
      T B₀ hsmall hΓ hnt hk e hUd hVd
    refine ⟨liftMorphism hU hV L hprop, fun p => ?_⟩
    have h := L.lift.labels p
    rw [hL] at h
    exact h

/-- The empty measured RV object. -/
def emptyRV (S : Set M) (k : ℕ) : MeasuredRVObject (M := M) S k where
  object := RVObject.empty S k
  finiteVolume := Map.finiteFibres_of_injective (fun a => False.elim a.property)
  nonzero u := False.elim u.property
  form := Map.fromEmpty rfl _

theorem emptyRV_doublyBounded : (emptyRV (M := M) S k).doublyBounded :=
  ⟨⟨1, fun _ hu => False.elim hu⟩, ⟨1, fun _ ⟨u, _⟩ => False.elim u.property⟩⟩

variable (S k) in
/-- Doubly bounded measured RV objects, the objects of `μRV^db[k]`. -/
abbrev DBObject := {U : MeasuredRVObject (M := M) S k // U.doublyBounded}

/-- The complementary restriction. -/
def restrictCompl (U : MeasuredRVObject (M := M) S k) (D : DefSet (rawRVSpace (M := M) U.object.arity) S) :
    MeasuredRVObject (M := M) S k :=
  U.restrict (U.object.domain.sdiff D) (fun _ h => h.1)

/-- RV scissors: an object, a definable piece of its domain, the complement and
the empty object. -/
def RVScissor (a b c d : DBObject S k) : Prop :=
  ∃ U : MeasuredRVObject (M := M) S k, ∃ hU : U.doublyBounded,
    ∃ D : DefSet (rawRVSpace (M := M) U.object.arity) S, ∃ hD : D.carrier ⊆ U.object.domain.carrier,
      a = ⟨U.restrict D hD, U.restrict_doublyBounded D hD hU⟩ ∧
      b = ⟨restrictCompl U D, U.restrict_doublyBounded _ _ hU⟩ ∧
      c = ⟨U, hU⟩ ∧ d = ⟨emptyRV S k, emptyRV_doublyBounded⟩

variable (S k) in
/-- The positive scissor presentation of `μRV^db[k]`. -/
def rvPresentation : DiamondIntegral.Section3.ScissorPresentation (DBObject S k) where
  iso a b := Nonempty (MeasuredRVIso a.1 b.1)
  empty := ⟨emptyRV S k, emptyRV_doublyBounded⟩
  scissor := RVScissor

theorem mem_rvLift_restrict (U : MeasuredRVObject (M := M) S k)
    (D : DefSet (rawRVSpace (M := M) U.object.arity) S) (hD : D.carrier ⊆ U.object.domain.carrier)
    (p : Mixed M k U.object.arity) :
    p ∈ (rvLift (U.restrict D hD).object).carrier ↔ p ∈ (rvLift U.object).carrier ∧ p.2 ∈ D.carrier := by
  constructor
  · rintro ⟨u, hu, hv⟩
    exact ⟨⟨⟨u.val, hD u.property⟩, hu, hv⟩, hu ▸ u.property⟩
  · rintro ⟨⟨w, hw, hv⟩, hp⟩
    exact ⟨⟨w.val, hw ▸ hp⟩, hw, hv⟩

/-- The lift of a restriction is the restriction of the lift. -/
theorem lift_restrict (U : MeasuredRVObject (M := M) S k)
    (D : DefSet (rawRVSpace (M := M) U.object.arity) S) (hD : D.carrier ⊆ U.object.domain.carrier)
    (hU : ProperInvariant S (rvLift U.object).carrier)
    (hP : ProperInvariant S (rvLift (U.restrict D hD).object).carrier) :
    liftObject (U.restrict D hD) hP =
      restrictObject (liftObject U hU) (rvLift (U.restrict D hD).object)
        (fun p hp => ((mem_rvLift_restrict U D hD p).mp hp).1) hP := rfl

theorem restrictObject_congr (A : VFObject (M := M) S k)
    {X Y : DefSet (rawMixedSpace (M := M) k A.labels) S} (hXY : X.carrier = Y.carrier)
    (hX : X.carrier ⊆ A.carrier.carrier) (hY : Y.carrier ⊆ A.carrier.carrier)
    (pX : ProperInvariant S X.carrier) (pY : ProperInvariant S Y.carrier) :
    restrictObject A X hX pX = restrictObject A Y hY pY := by
  obtain rfl : X = Y := DefSet.eq_of_carrier_eq hXY
  rfl

/-- The lift of the complementary restriction is the complementary piece of
the lift. -/
theorem lift_restrictCompl (U : MeasuredRVObject (M := M) S k)
    (D : DefSet (rawRVSpace (M := M) U.object.arity) S) (hD : D.carrier ⊆ U.object.domain.carrier)
    (hU : ProperInvariant S (rvLift U.object).carrier)
    (hD' : ProperInvariant S (rvLift (U.restrict D hD).object).carrier)
    (hC : ProperInvariant S (rvLift (restrictCompl U D).object).carrier) :
    liftObject (restrictCompl U D) hC =
      complObject (liftObject U hU) (rvLift (U.restrict D hD).object) hD' := by
  rw [show liftObject (restrictCompl U D) hC =
      liftObject (U.restrict (U.object.domain.sdiff D) (fun _ h => h.1)) hC from rfl,
    lift_restrict U _ _ hU hC]
  apply restrictObject_congr
  ext p
  rw [mem_rvLift_restrict]
  change _ ↔ p ∈ (rvLift U.object).carrier ∧ p ∉ (rvLift (U.restrict D hD).object).carrier
  rw [mem_rvLift_restrict]
  constructor
  · rintro ⟨hp, hpD, hnD⟩
    exact ⟨hp, fun h => hnD h.2⟩
  · rintro ⟨hp, hn⟩
    obtain ⟨w, hw, hv⟩ := hp
    exact ⟨⟨w, hw, hv⟩, hw ▸ w.property, fun hpD => hn ⟨⟨w, hw, hv⟩, hpD⟩⟩

section Homomorphism
variable (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
  (linear : GammaPiecewiseRationalAffineInput (M := M))
  {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
  (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
  (T : LRV.Substructure M) (B₀ : VFGeneratedFieldBase T) (hsmall : Cardinal.mk (T : Set M) < κ)
  (hΓ : NontrivialDefinableGamma (⟨(T : Set M), ∅⟩ : ParameterBase M))
  (hnt : ∃ x : B₀.field, x ≠ 0 ∧ Valued.v x.val ≠ 1)

variable (G k) in
/-- The lift `μL_k` as a scissor invariant with values in `K_+ μVF^◇[k]`. -/
def liftInvariant : PositiveAdditiveGrothendieck.Invariant (rvPresentation (T : Set M) k)
    (A := KPlus (T : Set M) G hc k) where
  toFun a := vfClass G hc (liftObject a.1 (measuredRVLift_properInvariant h00 hc hκ hs hv a.1 a.2))
  iso := by
    rintro a b ⟨e⟩
    apply vfClass_iso hc
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      exact lift_isomorphic_zero e _ _
    · exact lift_isomorphic_pos h00 hc linear hκ hs hv T B₀ hsmall hΓ hnt hk e a.2 b.2 _ _
  empty := vfClass_of_empty hc (Set.eq_empty_of_forall_notMem (fun _ ⟨u, _⟩ => False.elim u.property))
  scissor := by
    rintro a b c d ⟨U, hU, D, hD, rfl, rfl, rfl, rfl⟩
    have hP := measuredRVLift_properInvariant (S := (T : Set M)) (n := k) (G := G) h00 hc hκ hs hv
    change vfClass G hc (liftObject (U.restrict D hD) _) +
        vfClass G hc (liftObject (restrictCompl U D) _) =
      vfClass G hc (liftObject U _) + vfClass G hc (liftObject (emptyRV (T : Set M) k) _)
    rw [lift_restrict U D hD (hP U hU),
      lift_restrictCompl U D hD (hP U hU) (hP _ (U.restrict_doublyBounded D hD hU)), vfClass_scissor,
      vfClass_of_empty hc (A := liftObject (emptyRV (T : Set M) k) _)
        (Set.eq_empty_of_forall_notMem (fun _ ⟨u, _⟩ => False.elim u.property)), add_zero]

variable (G k) in
/-- Corollary 6.37: the homomorphism `K_+ μRV^db[k] → K_+ μVF^◇[k]` induced by `μL_k`. -/
def liftHom : DiamondIntegral.Section3.KPlus (rvPresentation (T : Set M) k) →+ KPlus (T : Set M) G hc k :=
  PositiveAdditiveGrothendieck.lift _ (liftInvariant k G h00 hc linear hκ hs hv T B₀ hsmall hΓ hnt)

theorem liftHom_class (a : DBObject (T : Set M) k) :
    liftHom k G h00 hc linear hκ hs hv T B₀ hsmall hΓ hnt
        (DiamondIntegral.Section3.positiveClass (rvPresentation (T : Set M) k) a) =
      vfClass G hc (liftObject a.1 (measuredRVLift_properInvariant h00 hc hκ hs hv a.1 a.2)) :=
  PositiveAdditiveGrothendieck.lift_of _ _ a

/-- Corollary 6.37: `μL_k : K_+ μRV^db[k] → K_+ μVF^◇[k]` is surjective. -/
theorem liftHom_surjective :
    Function.Surjective (liftHom k G h00 hc linear hκ hs hv T B₀ hsmall hΓ hnt) := by
  have hgen : ∀ A : VFObject (M := M) (T : Set M) k,
      vfClass G hc A ∈ AddMonoidHom.mrange (liftHom k G h00 hc linear hκ hs hv T B₀ hsmall hΓ hnt) := by
    intro A
    by_cases hk : k = 0
    · subst hk
      obtain ⟨U, hU, hiso⟩ := exists_isomorphic_lift_zero (G := G) h00 hc linear hκ hs hv hsmall hΓ A
      exact ⟨_, (liftHom_class h00 hc linear hκ hs hv T B₀ hsmall hΓ hnt ⟨U, hU⟩).trans
        (vfClass_iso hc hiso).symm⟩
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
      obtain ⟨U, hU, hiso⟩ := exists_isomorphic_lift (G := G) h00 hc linear hκ hs hv T B₀ hsmall hΓ hnt A
      exact ⟨_, (liftHom_class h00 hc linear hκ hs hv T B₀ hsmall hΓ hnt ⟨U, hU⟩).trans
        (vfClass_iso hc hiso).symm⟩
  intro x
  obtain ⟨f, rfl⟩ := AddCon.mk'_surjective x
  change (PositiveAdditiveGrothendieck.congruence (presentation G hc k)).mk' f ∈
    AddMonoidHom.mrange (liftHom k G h00 hc linear hκ hs hv T B₀ hsmall hΓ hnt)
  refine Finsupp.induction f ?_ ?_
  · rw [map_zero]
    exact zero_mem _
  · intro a b f _ _ ih
    rw [map_add]
    refine add_mem ?_ ih
    rw [← Finsupp.smul_single_one, map_nsmul]
    exact nsmul_mem (hgen a) b

end Homomorphism

end DiamondIntegral.Section6.DiamondLiftHomomorphism
