import «section 7».TwoStageContractions
import «section 7».PullbackStages
import «section 7».RelabelClasses
import «section 6».UnaryStandardContractionStages
import «section 6».ZeroCenteredBoundedTrace

/-! Lemma 7.21 for product cells.

A `2`-cell whose positioning function is constant, or has narrow image, is a
product `D × E` of two open discs. Over a family indexed by RV labels, a set
`W ⊆ VF² × RV^m` whose label fibres are such products is the fibre product
`P ×_w Q` of its two coordinate projections `P`, `Q ⊆ VF × RV^m`
(`PullbackStages.pullbackProd`).

Choose unary standard contraction stages `H_P` of `P` and `H_Q` of `Q` (Section 6,
Lemma 6.27 for `n = 1`). The contraction in the order that contracts the second
coordinate first pulls back `H_Q` to `P ×_w Q`, then `H_P` to the contracted set
(`productProgram`). The other order pulls back `H_P` first, then `H_Q`. The
final RV targets consist of the points `(w, w_Q, w_P)`, respectively
`(w, w_P, w_Q)`, with `w_P` in the contracted set of `H_P`, `w_Q` in the
contracted set of `H_Q` and both retaining `w` (`mem_productTarget`). So the two
targets differ by swapping the two blocks of new labels. The volume labels are
the leading labels of `H_P` and `H_Q` in both orders, and the forms depend only
on `w`. Hence the identity, read through the block swap, is an isomorphism, and
the two head-start-`0` classes agree (`cls_product_orders`). This is the first
case of the paper's proof ("The first case is obvious since we can simply use
the identity map").

Stages are transported between sets with equal carriers by `stageOn`, which
keeps the target, so that contracted sets stay definitionally equal. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section9
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.ProductCells
open DiamondIntegral.Section6 DiamondIntegral.Section2
open DiamondIntegral.Section7.PullbackStages

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

/-! ### Transport of a stage along equal carriers -/

section Transport
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G] {S : Set M} {n r : ℕ}

theorem defSet_eq_of_carrier {P : Space LRV M} {A A' : DefSet P S} (h : A'.carrier = A.carrier) : A' = A := by
  cases A; cases A'
  cases h
  rfl

/-- A stage of `A`, as a stage of a set with the same carrier. It keeps the
target, so the contracted set is the same. -/
def stageOn {A A' : DefSet (rawMixedSpace (M := M) (n + 1) r) S} (H : StandardContractionStage (G := G) A)
    (h : A'.carrier = A.carrier) : StandardContractionStage (G := G) A' where
  arity := H.arity
  target := H.target
  lift := H.lift.comp (Map.inclusion (h ▸ subset_rfl))
  home := by
    obtain rfl := defSet_eq_of_carrier h
    exact H.home
  proper := H.proper
  doublyBounded := H.doublyBounded
  relative := fun p => H.relative _
  oldLabels := H.oldLabels
  oldLabels_injective := H.oldLabels_injective
  retained := fun p => H.retained _
  leading := H.leading
  bundle := H.bundle
  exceptional := H.exceptional
  exceptional_subset := h ▸ H.exceptional_subset
  exceptional_dim := H.exceptional_dim
  unitDerivative := by
    obtain rfl := defSet_eq_of_carrier h
    exact H.unitDerivative

theorem stageOn_contracted {A A' : DefSet (rawMixedSpace (M := M) (n + 1) r) S}
    (H : StandardContractionStage (G := G) A) (h : A'.carrier = A.carrier) :
    (stageOn H h).contracted = H.contracted := rfl

theorem stageOn_contraction {A A' : DefSet (rawMixedSpace (M := M) (n + 1) r) S}
    (H : StandardContractionStage (G := G) A) (h : A'.carrier = A.carrier) (p : A') :
    (stageOn H h).contraction p = H.contraction ⟨p.val, h ▸ p.property⟩ := rfl

end Transport

/-! ### Unary stages: points of the contracted set come from the source -/

section Unary
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G] {S : Set M} {r : ℕ}

/-- A point of the contracted set of a unary stage retains the labels of a point
of the source. -/
theorem exists_source_of_contracted {E : DefSet (rawMixedSpace (M := M) 1 r) S}
    (H : StandardContractionStage (G := G) E) {z : Fin H.arity → RVInfinity M}
    (hz : ((Fin.elim0, z) : Mixed M 0 H.arity) ∈ H.contracted.carrier) :
    ∃ y : Fin 1 → VF M, ((y, z ∘ H.oldLabels) : Mixed M 1 r) ∈ E.carrier := by
  obtain ⟨t, ht⟩ := hz
  obtain ⟨p, hp⟩ := H.home.bijective.surjective t
  have h2 : t.val.2 = z := congrArg Prod.snd ht
  refine ⟨p.val.1, ?_⟩
  have hl : z ∘ H.oldLabels = p.val.2 := by
    funext i
    rw [Function.comp_apply, ← h2, ← hp]
    exact H.retained p i
  rw [hl]
  exact p.property

end Unary

/-! ### The two-stage program on a fibre product -/

section Program
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G] {S : Set M} {m : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal} (hs : Saturated M κ)
variable (hsmall : Cardinal.mk S < κ)
variable (P Q : DefSet (rawMixedSpace (M := M) 1 m) S)
variable (hP : ProperInvariant S P.carrier) (hPb : VFDoublyBounded P.carrier)
variable (HP : StandardContractionStage (G := G) P) (HQ : StandardContractionStage (G := G) Q)

/-- The first stage: `H_Q` pulled back to `P ×_w Q`. -/
abbrev firstStage : StandardContractionStage (G := G) (pullbackProd P Q id) :=
  pullbackStage P id HQ hP hPb hc hs hsmall

/-- The labels of the first contracted set. -/
abbrev labelSet : DefSet (rawMixedSpace (M := M) 0 (m + HQ.arity)) S :=
  (vfDropLast (firstStage hc hs hsmall P Q hP hPb HQ).contracted).image

theorem mem_firstContracted (y : Fin 1 → VF M) (w : Fin (m + HQ.arity) → RVInfinity M) :
    ((y, w) : Mixed M 1 (m + HQ.arity)) ∈ (firstStage hc hs hsmall P Q hP hPb HQ).contracted.carrier ↔
      ((y, fun i => w (Fin.castAdd HQ.arity i)) : Mixed M 1 m) ∈ P.carrier ∧
      ((Fin.elim0, fun j => w (Fin.natAdd m j)) : Mixed M 0 HQ.arity) ∈ HQ.contracted.carrier ∧
      ∀ i, w (Fin.natAdd m (HQ.oldLabels i)) = w (Fin.castAdd HQ.arity i) :=
  mem_pullbackStage_contracted P id HQ hP hPb hc hs hsmall y w

theorem mem_labelSet (w : Fin (m + HQ.arity) → RVInfinity M) :
    ((Fin.elim0, w) : Mixed M 0 (m + HQ.arity)) ∈ (labelSet hc hs hsmall P Q hP hPb HQ).carrier ↔
      (∃ y : Fin 1 → VF M, ((y, fun i => w (Fin.castAdd HQ.arity i)) : Mixed M 1 m) ∈ P.carrier) ∧
      ((Fin.elim0, fun j => w (Fin.natAdd m j)) : Mixed M 0 HQ.arity) ∈ HQ.contracted.carrier ∧
      ∀ i, w (Fin.natAdd m (HQ.oldLabels i)) = w (Fin.castAdd HQ.arity i) := by
  constructor
  · rintro ⟨q, hq⟩
    have h2 : q.val.2 = w := congrArg Prod.snd hq
    have hm := (mem_firstContracted hc hs hsmall P Q hP hPb HQ q.val.1 q.val.2).mp q.property
    rw [h2] at hm
    exact ⟨⟨q.val.1, hm.1⟩, hm.2⟩
  · rintro ⟨⟨y, hy⟩, h2, h3⟩
    have hm : ((y, w) : Mixed M 1 (m + HQ.arity)) ∈ (firstStage hc hs hsmall P Q hP hPb HQ).contracted.carrier :=
      (mem_firstContracted hc hs hsmall P Q hP hPb HQ y w).mpr ⟨hy, h2, h3⟩
    refine ⟨⟨(y, w), hm⟩, ?_⟩
    change ((Fin.init y, w) : Mixed M 0 (m + HQ.arity)) = (Fin.elim0, w)
    exact Prod.ext (Subsingleton.elim _ _) rfl

theorem labelSet_rvBounded : RVSupportDoublyBounded (labelSet hc hs hsmall P Q hP hPb HQ).carrier :=
  vfDropLast_image_rvBounded (firstStage hc hs hsmall P Q hP hPb HQ).contracted_proper.rvBounded

/-- The first contracted set is the fibre product of its labels with `P`. -/
theorem firstContracted_eq :
    (pullbackProd (labelSet hc hs hsmall P Q hP hPb HQ) P (Fin.castAdd HQ.arity)).carrier =
      (firstStage hc hs hsmall P Q hP hPb HQ).contracted.carrier := by
  ext ⟨y, w⟩
  rw [mem_pullbackProd_zero, mem_labelSet, mem_firstContracted]
  constructor
  · rintro ⟨⟨_, h2, h3⟩, hy⟩
    exact ⟨hy, h2, h3⟩
  · rintro ⟨hy, h2, h3⟩
    exact ⟨⟨⟨y, hy⟩, h2, h3⟩, hy⟩

/-- The second stage: `H_P` pulled back to the first contracted set. -/
def secondStage : StandardContractionStage (G := G) (firstStage hc hs hsmall P Q hP hPb HQ).contracted :=
  stageOn (pullbackStageZero (labelSet hc hs hsmall P Q hP hPb HQ) (Fin.castAdd HQ.arity) HP
    (labelSet_rvBounded hc hs hsmall P Q hP hPb HQ) hc hs hsmall)
    (firstContracted_eq hc hs hsmall P Q hP hPb HQ).symm

theorem secondStage_arity : (secondStage hc hs hsmall P Q hP hPb HP HQ).arity = (m + HQ.arity) + HP.arity := rfl

theorem secondStage_oldLabels :
    (secondStage hc hs hsmall P Q hP hPb HP HQ).oldLabels = Fin.castAdd HP.arity := rfl

theorem secondStage_leading :
    (secondStage hc hs hsmall P Q hP hPb HP HQ).leading = Fin.natAdd (m + HQ.arity) HP.leading := rfl

/-- **The final RV target.** A label tuple `(w, w_Q, w_P)` lies in it exactly
when `w_Q` lies in the contracted set of `H_Q`, `w_P` in that of `H_P`, and both
retain `w`. -/
theorem mem_productTarget (u : Fin ((m + HQ.arity) + HP.arity) → RVInfinity M) :
    ((Fin.elim0, u) : Mixed M 0 _) ∈ (secondStage hc hs hsmall P Q hP hPb HP HQ).contracted.carrier ↔
      ((Fin.elim0, fun j => u (Fin.castAdd HP.arity (Fin.natAdd m j))) : Mixed M 0 HQ.arity) ∈
          HQ.contracted.carrier ∧
        (∀ i, u (Fin.castAdd HP.arity (Fin.natAdd m (HQ.oldLabels i))) =
          u (Fin.castAdd HP.arity (Fin.castAdd HQ.arity i))) ∧
        ((Fin.elim0, fun j => u (Fin.natAdd (m + HQ.arity) j)) : Mixed M 0 HP.arity) ∈ HP.contracted.carrier ∧
        ∀ i, u (Fin.natAdd (m + HQ.arity) (HP.oldLabels i)) = u (Fin.castAdd HP.arity (Fin.castAdd HQ.arity i)) := by
  change ((Fin.elim0, u) : Mixed M 0 _) ∈ (pullbackStageZero (labelSet hc hs hsmall P Q hP hPb HQ)
    (Fin.castAdd HQ.arity) HP (labelSet_rvBounded hc hs hsmall P Q hP hPb HQ) hc hs hsmall).contracted.carrier ↔ _
  refine (mem_pullbackStage_contracted (labelSet hc hs hsmall P Q hP hPb HQ) (Fin.castAdd HQ.arity) HP
    (properInvariant_zero (labelSet_rvBounded hc hs hsmall P Q hP hPb HQ))
    (vfDoublyBounded_zero _) hc hs hsmall Fin.elim0 u).trans ?_
  rw [mem_labelSet]
  constructor
  · rintro ⟨⟨_, hQ, hQl⟩, hPc, hPl⟩
    exact ⟨hQ, hQl, hPc, hPl⟩
  · rintro ⟨hQ, hQl, hPc, hPl⟩
    refine ⟨⟨?_, hQ, hQl⟩, hPc, hPl⟩
    obtain ⟨y, hy⟩ := exists_source_of_contracted HP hPc
    refine ⟨y, ?_⟩
    have he : ((fun j => u (Fin.natAdd (m + HQ.arity) j)) ∘ HP.oldLabels) =
        fun i => u (Fin.castAdd HP.arity (Fin.castAdd HQ.arity i)) := funext fun i => hPl i
    rw [he] at hy
    exact hy

end Program

/-! ### Forms descended to the RV target -/

section Forms
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G] {S : Set M}
variable (h00 : M ⊨ Axioms.ACVF00)
variable {r q : ℕ} {X : DefSet (rawMixedSpace (M := M) 2 r) S}
variable {ω : Map X (DefSet.univ (rawGammaPresentation (M := M)) S)}
variable (hω : ∀ p z : X, p.val.2 = z.val.2 → ω p = ω z)
variable (D : ZeroCenteredData X) (e : Equiv.Perm (Fin 2))
open DiamondIntegral.Section7.TwoStageContractions

theorem prepOf_labels (p : X) (i : Fin r) : (prepOf D e p).val.2 (Fin.natAdd 2 i) = p.val.2 i := by
  change Fin.append (fun j => branchTag (M := M) (D.core p.val j)) p.val.2 (Fin.natAdd 2 i) = _
  rw [Fin.append_right]

include hω in
theorem preparedFormOf_labels (y y' : reindexedVFSet D.map.image e) (h : y.val.2 = y'.val.2) :
    preparedFormOf (ω := ω) h00 D e y = preparedFormOf (ω := ω) h00 D e y' := by
  obtain ⟨p, rfl⟩ := (prepOf_bijective h00 D e).surjective y
  obtain ⟨p', rfl⟩ := (prepOf_bijective h00 D e).surjective y'
  apply Subtype.ext
  rw [preparedFormOf_transport, preparedFormOf_transport]
  have hp : p.val.2 = p'.val.2 := funext fun i => by
    rw [← prepOf_labels D e p i, ← prepOf_labels D e p' i, h]
  rw [hω p p' hp]

variable {U : DefSet (rawMixedSpace (M := M) 0 q) S}
variable (Pg : OrderedStandardContractionProgram (G := G) S (reindexedVFSet D.map.image e) U)

/-- The form, descended to the RV target of a program on the prepared set. -/
def descForm : Map U (DefSet.univ (rawGammaPresentation (M := M)) S) :=
  descendSurjectiveMap Pg.toMap Pg.surjective (preparedFormOf h00 D e) (fun a b hab =>
    preparedFormOf_labels h00 hω D e a b (funext fun i =>
      (Pg.retained a i).symm.trans ((congrArg (fun z : U => z.val.2 (Pg.oldLabels i)) hab).trans (Pg.retained b i))))

theorem descForm_factor (p : X) :
    (descForm h00 hω D e Pg (Pg.toMap (prepOf D e p))).val = (ω p).val :=
  (congrArg Subtype.val (descendSurjectiveMap_factor Pg.toMap Pg.surjective (preparedFormOf h00 D e) _ _)).trans
    (preparedFormOf_transport h00 D e p)

/-- The descended form at `z` is the form at any point whose labels are the old
labels of `z`. -/
theorem descForm_labels (z : U) (p : X) (h : ∀ i, z.val.2 (Pg.oldLabels (Fin.natAdd 2 i)) = p.val.2 i) :
    (descForm h00 hω D e Pg z).val = (ω p).val := by
  obtain ⟨y, rfl⟩ := Pg.surjective z
  obtain ⟨p', rfl⟩ := (prepOf_bijective h00 D e).surjective y
  rw [descForm_factor]
  have hp : p'.val.2 = p.val.2 := funext fun i => by
    rw [← h i, Pg.retained, prepOf_labels]
  rw [hω p' p hp]

end Forms

/-! ### The two contractions of a family of product cells -/

section Object
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
variable (linear : GammaPiecewiseRationalAffineInput (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
variable (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
variable {S : Set M} (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S, ∅⟩ : ParameterBase M))
variable {r : ℕ} {X : DefSet (rawMixedSpace (M := M) 2 r) S}
variable (D : ZeroCenteredData X)
open DiamondIntegral.Section7.TwoStageContractions

/-- The projection to the first coordinate, with all labels, of the normalized
image. -/
abbrev proj0 : DefSet (rawMixedSpace (M := M) 1 (2 + r)) S := (vfDropLast D.map.image).image

/-- The projection to the second coordinate, with all labels, of the normalized
image. -/
abbrev proj1 : DefSet (rawMixedSpace (M := M) 1 (2 + r)) S :=
  (vfDropLast (reindexedVFSet D.map.image (Equiv.swap 0 1))).image

theorem mem_proj0 (y : Fin 1 → VF M) (w : Fin (2 + r) → RVInfinity M) :
    ((y, w) : Mixed M 1 (2 + r)) ∈ (proj0 D).carrier ↔
      ∃ x : Fin 2 → VF M, ((x, w) : Mixed M 2 (2 + r)) ∈ D.map.image.carrier ∧ x 0 = y 0 := by
  constructor
  · rintro ⟨p, hp⟩
    have h1 : Fin.init p.val.1 = y := congrArg Prod.fst hp
    have h2 : p.val.2 = w := congrArg Prod.snd hp
    refine ⟨p.val.1, ?_, ?_⟩
    · rw [← h2]; exact p.property
    · rw [← h1]; rfl
  · rintro ⟨x, hx, h0⟩
    refine ⟨⟨(x, w), hx⟩, ?_⟩
    change ((Fin.init x, w) : Mixed M 1 (2 + r)) = (y, w)
    refine Prod.ext (FibreRestriction.fin_one_ext ?_) rfl
    exact h0

theorem mem_proj1 (y : Fin 1 → VF M) (w : Fin (2 + r) → RVInfinity M) :
    ((y, w) : Mixed M 1 (2 + r)) ∈ (proj1 D).carrier ↔
      ∃ x : Fin 2 → VF M, ((x, w) : Mixed M 2 (2 + r)) ∈ D.map.image.carrier ∧ x 1 = y 0 := by
  constructor
  · rintro ⟨p, hp⟩
    have h1 : Fin.init p.val.1 = y := congrArg Prod.fst hp
    have h2 : p.val.2 = w := congrArg Prod.snd hp
    have hm := (mem_reindexedVFSet _ _ p.val).mp p.property
    refine ⟨p.val.1 ∘ (Equiv.swap (0 : Fin 2) 1).symm, ?_, ?_⟩
    · rw [← h2]; exact hm
    · rw [← h1]
      simp only [Function.comp_apply, Equiv.symm_swap, Equiv.swap_apply_right]
      rfl
  · rintro ⟨x, hx, h1⟩
    have hm : ((x ∘ Equiv.swap (0 : Fin 2) 1, w) : Mixed M 2 (2 + r)) ∈
        (reindexedVFSet D.map.image (Equiv.swap 0 1)).carrier := by
      refine (mem_reindexedVFSet _ _ _).mpr ?_
      change ((x ∘ Equiv.swap (0 : Fin 2) 1) ∘ (Equiv.swap (0 : Fin 2) 1).symm, w) ∈ _
      have he : (x ∘ Equiv.swap (0 : Fin 2) 1) ∘ (Equiv.swap (0 : Fin 2) 1).symm = x := by
        funext i; simp only [Function.comp_apply, Equiv.symm_swap, Equiv.swap_apply_self]
      rw [he]; exact hx
    refine ⟨⟨_, hm⟩, ?_⟩
    change ((Fin.init (x ∘ Equiv.swap (0 : Fin 2) 1), w) : Mixed M 1 (2 + r)) = (y, w)
    refine Prod.ext (FibreRestriction.fin_one_ext ?_) rfl
    change x (Equiv.swap (0 : Fin 2) 1 0) = y 0
    rw [Equiv.swap_apply_left]
    exact h1

/-- The normalized image is a fibre product over its labels. -/
def ImageProduct : Prop :=
  ∀ (x : Fin 2 → VF M) (w : Fin (2 + r) → RVInfinity M), ((x, w) : Mixed M 2 (2 + r)) ∈ D.map.image.carrier ↔
    (∃ y : Fin 2 → VF M, ((y, w) : Mixed M 2 (2 + r)) ∈ D.map.image.carrier ∧ y 0 = x 0) ∧
    (∃ y : Fin 2 → VF M, ((y, w) : Mixed M 2 (2 + r)) ∈ D.map.image.carrier ∧ y 1 = x 1)

/-- Membership in the normalized image of a doubly bounded set: the VF
coordinates are kept and `false` core tags are prepended. -/
theorem mem_image_doublyBounded (hXb : VFDoublyBounded X.carrier) (x : Fin 2 → VF M)
    (w : Fin (2 + r) → RVInfinity M) :
    ((x, w) : Mixed M 2 (2 + r)) ∈ D.map.image.carrier ↔
      ∃ u : Fin r → RVInfinity M, ((x, u) : Mixed M 2 r) ∈ X.carrier ∧
        w = Fin.append (fun _ : Fin 2 => branchTag (M := M) false) u := by
  constructor
  · rintro ⟨p, hp⟩
    have hpt : D.point p.val = (x, w) := hp
    have h1 := D.point_field_of_doublyBounded hXb p.property
    have h2 := D.point_tags_of_doublyBounded hXb p.property
    rw [hpt] at h1 h2
    refine ⟨p.val.2, ?_, h2⟩
    have hx : p.val = (x, p.val.2) := Prod.ext h1.symm rfl
    rw [← hx]
    exact p.property
  · rintro ⟨u, hu, rfl⟩
    refine ⟨⟨(x, u), hu⟩, ?_⟩
    change D.point (x, u) = _
    have h1 := D.point_field_of_doublyBounded hXb hu
    have h2 := D.point_tags_of_doublyBounded hXb hu
    exact Prod.ext h1 h2

/-- A doubly bounded set whose label fibres are products has a normalized image
whose label fibres are products. -/
theorem imageProduct_of_product (hXb : VFDoublyBounded X.carrier)
    (hprod : ∀ (x : Fin 2 → VF M) (u : Fin r → RVInfinity M), ((x, u) : Mixed M 2 r) ∈ X.carrier ↔
      (∃ y : Fin 2 → VF M, ((y, u) : Mixed M 2 r) ∈ X.carrier ∧ y 0 = x 0) ∧
      (∃ y : Fin 2 → VF M, ((y, u) : Mixed M 2 r) ∈ X.carrier ∧ y 1 = x 1)) :
    ImageProduct D := by
  have happ : ∀ u u' : Fin r → RVInfinity M,
      Fin.append (fun _ : Fin 2 => branchTag (M := M) false) u =
        Fin.append (fun _ : Fin 2 => branchTag (M := M) false) u' → u = u' := fun u u' h =>
    funext fun i => by simpa only [Fin.append_right] using congrFun h (Fin.natAdd 2 i)
  intro x w
  constructor
  · intro hx
    exact ⟨⟨x, hx, rfl⟩, ⟨x, hx, rfl⟩⟩
  · rintro ⟨⟨y, hy, h0⟩, ⟨y', hy', h1⟩⟩
    obtain ⟨u, hu, rfl⟩ := (mem_image_doublyBounded D hXb y w).mp hy
    obtain ⟨u', hu', hw⟩ := (mem_image_doublyBounded D hXb y' _).mp hy'
    obtain rfl := happ u u' hw
    exact (mem_image_doublyBounded D hXb x _).mpr ⟨u, (hprod x u).mpr ⟨⟨y, hu, h0⟩, ⟨y', hu', h1⟩⟩, rfl⟩

variable {D}

theorem prepared_one_eq (hW : ImageProduct D) :
    (reindexedVFSet D.map.image 1).carrier = (pullbackProd (proj0 D) (proj1 D) id).carrier := by
  ext ⟨x, w⟩
  rw [mem_reindexedVFSet, mem_pullbackProd, mem_proj0, mem_proj1]
  change ((x ∘ ⇑(1 : Equiv.Perm (Fin 2)).symm, w) : Mixed M 2 (2 + r)) ∈ _ ↔ _
  have hx : x ∘ ⇑(1 : Equiv.Perm (Fin 2)).symm = x := rfl
  rw [hx, hW]
  rfl

theorem prepared_swap_eq (hW : ImageProduct D) :
    (reindexedVFSet D.map.image (Equiv.swap 0 1)).carrier = (pullbackProd (proj1 D) (proj0 D) id).carrier := by
  ext ⟨x, w⟩
  rw [mem_reindexedVFSet, mem_pullbackProd, mem_proj0, mem_proj1]
  change ((x ∘ ⇑(Equiv.swap (0 : Fin 2) 1).symm, w) : Mixed M 2 (2 + r)) ∈ _ ↔ _
  rw [hW]
  simp only [Function.comp_apply, Equiv.symm_swap, Equiv.swap_apply_left, Equiv.swap_apply_right]
  exact and_comm

variable (D)

include h00 hc hκ hs hv in
theorem proj0_proper : ProperInvariant S (proj0 D).carrier :=
  vfDropLast_image_properInvariant (D.image_properInvariant h00 hc hκ hs hv)

include h00 hc hκ hs hv in
theorem proj1_proper : ProperInvariant S (proj1 D).carrier :=
  vfDropLast_image_properInvariant (reindexedVFSet_properInvariant _ _ (D.image_properInvariant h00 hc hκ hs hv))

theorem proj0_doublyBounded : VFDoublyBounded (proj0 D).carrier := by
  obtain ⟨δ, hδ⟩ := D.image_vfDoublyBounded
  refine ⟨δ, ?_⟩
  rintro q ⟨p, rfl⟩ i
  exact hδ p.val p.property i.castSucc

theorem proj1_doublyBounded : VFDoublyBounded (proj1 D).carrier := by
  obtain ⟨δ, hδ⟩ := reindexedVFSet_doublyBounded _ (Equiv.swap (0 : Fin 2) 1) D.image_vfDoublyBounded
  refine ⟨δ, ?_⟩
  rintro q ⟨p, rfl⟩ i
  exact hδ p.val p.property i.castSucc

variable {D} (H0 : StandardContractionStage (G := G) (proj0 D)) (H1 : StandardContractionStage (G := G) (proj1 D))
variable (hW : ImageProduct D)

/-- The first stage in the order `21` (`e = 1`, contracting `x₂` first). -/
def stageOneFirst : StandardContractionStage (G := G) (reindexedVFSet D.map.image 1) :=
  stageOn (firstStage hc hs hsmall (proj0 D) (proj1 D) (proj0_proper h00 hc hκ hs hv D) (proj0_doublyBounded D) H1)
    (prepared_one_eq hW)

/-- The second stage in the order `21`. -/
def stageOneSecond : StandardContractionStage (G := G) (stageOneFirst h00 hc hκ hs hv hsmall H1 hW).contracted :=
  secondStage hc hs hsmall (proj0 D) (proj1 D) (proj0_proper h00 hc hκ hs hv D) (proj0_doublyBounded D) H0 H1

/-- The first stage in the order `12` (`e = swap`, contracting `x₁` first). -/
def stageSwapFirst : StandardContractionStage (G := G) (reindexedVFSet D.map.image (Equiv.swap 0 1)) :=
  stageOn (firstStage hc hs hsmall (proj1 D) (proj0 D) (proj1_proper h00 hc hκ hs hv D) (proj1_doublyBounded D) H0)
    (prepared_swap_eq hW)

/-- The second stage in the order `12`. -/
def stageSwapSecond : StandardContractionStage (G := G) (stageSwapFirst h00 hc hκ hs hv hsmall H0 hW).contracted :=
  secondStage hc hs hsmall (proj1 D) (proj0 D) (proj1_proper h00 hc hκ hs hv D) (proj1_doublyBounded D) H1 H0

variable {ω : Map X (DefSet.univ (rawGammaPresentation (M := M)) S)}
variable (hω : ∀ p z : X, p.val.2 = z.val.2 → ω p = ω z)

/-- **The contraction in the order `21`.** -/
def contractionOne : NormalizedMeasuredContraction (G := G) X ω 1 :=
  twoStage h00 hc linear hκ hs hv hsmall hΓ D (stageOneFirst h00 hc hκ hs hv hsmall H1 hW)
    (stageOneSecond h00 hc hκ hs hv hsmall H0 H1 hW)
    (descForm h00 hω D 1 (twoStageProgram _ _))
    (fun p => descForm_factor h00 hω D 1 (twoStageProgram _ _) p)

/-- **The contraction in the order `12`.** -/
def contractionSwap : NormalizedMeasuredContraction (G := G) X ω (Equiv.swap 0 1) :=
  twoStage h00 hc linear hκ hs hv hsmall hΓ D (stageSwapFirst h00 hc hκ hs hv hsmall H0 hW)
    (stageSwapSecond h00 hc hκ hs hv hsmall H0 H1 hW)
    (descForm h00 hω D (Equiv.swap 0 1) (twoStageProgram _ _))
    (fun p => descForm_factor h00 hω D (Equiv.swap 0 1) (twoStageProgram _ _) p)

end Object

/-! ### The block swap -/

section Swap

/-- The permutation of label positions `(w, v, v') ↦ (w, v', v)`, read from the
target of the order `12` to that of the order `21`. -/
def blockSwap (m a b : ℕ) : Fin ((m + a) + b) ≃ Fin ((m + b) + a) :=
  finSumFinEquiv.symm.trans ((Equiv.sumCongr finSumFinEquiv.symm (Equiv.refl _)).trans
    ((Equiv.sumAssoc _ _ _).trans ((Equiv.sumCongr (Equiv.refl _) (Equiv.sumComm _ _)).trans
      ((Equiv.sumAssoc _ _ _).symm.trans ((Equiv.sumCongr finSumFinEquiv (Equiv.refl _)).trans finSumFinEquiv)))))

theorem blockSwap_old (m a b : ℕ) (i : Fin m) :
    blockSwap m a b (Fin.castAdd b (Fin.castAdd a i)) = Fin.castAdd a (Fin.castAdd b i) := by
  simp [blockSwap]

theorem blockSwap_left (m a b : ℕ) (j : Fin a) :
    blockSwap m a b (Fin.castAdd b (Fin.natAdd m j)) = Fin.natAdd (m + b) j := by
  simp [blockSwap]

theorem blockSwap_right (m a b : ℕ) (k : Fin b) :
    blockSwap m a b (Fin.natAdd (m + a) k) = Fin.castAdd a (Fin.natAdd m k) := by
  simp [blockSwap]

end Swap

/-! ### Lemma 7.21 for product cells -/

section Classes
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
variable (linear : GammaPiecewiseRationalAffineInput (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
variable (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
variable {T : LRV.Substructure M}
variable (hsmall : Cardinal.mk (T : Set M) < κ) (hΓ : NontrivialDefinableGamma (⟨(T : Set M), ∅⟩ : ParameterBase M))
variable {r : ℕ} {X : DefSet (rawMixedSpace (M := M) 2 r) (T : Set M)} {D : ZeroCenteredData X}
variable (H0 : StandardContractionStage (G := G) (proj0 D)) (H1 : StandardContractionStage (G := G) (proj1 D))
variable (hW : ImageProduct D)
variable {ω : Map X (DefSet.univ (rawGammaPresentation (M := M)) (T : Set M))}
variable (hω : ∀ p z : X, p.val.2 = z.val.2 → ω p = ω z)
open DiamondIntegral.Section7.TwoStageContractions DiamondIntegral.Section7.BoundedClasses
open DiamondIntegral.Section7.ChartOfMeasured DiamondIntegral.Section7.FirstStage
open DiamondIntegral.Section7.RelabelClasses

theorem volumeIndex_one (i : Fin 2) :
    (contractionOne h00 hc linear hκ hs hv hsmall hΓ H0 H1 hW hω).preparedContraction.data.program.volumeIndex i =
      Fin.lastCases (Fin.castAdd H0.arity (Fin.natAdd (2 + r) H1.leading))
        (fun _ => Fin.natAdd ((2 + r) + H1.arity) H0.leading) i :=
  twoStage_volumeIndex h00 hc linear hκ hs hv hsmall hΓ _ _ _ _ i

theorem volumeIndex_swap (i : Fin 2) :
    (contractionSwap h00 hc linear hκ hs hv hsmall hΓ H0 H1 hW hω).preparedContraction.data.program.volumeIndex i =
      Fin.lastCases (Fin.castAdd H1.arity (Fin.natAdd (2 + r) H0.leading))
        (fun _ => Fin.natAdd ((2 + r) + H0.arity) H1.leading) i :=
  twoStage_volumeIndex h00 hc linear hκ hs hv hsmall hΓ _ _ _ _ i

theorem prod_two_append {q : ℕ} (f : Fin q → Gamma M) (ν : Fin 2 → Fin q) (l : Fin 0 → Fin q) :
    ∏ i, f (Fin.append ν l i) = f (ν 0) * f (ν 1) := by
  rw [Fin.prod_univ_add (a := 2) (b := 0)]
  simp only [Fin.append_left, Finset.univ_eq_empty, Finset.prod_empty, mul_one, Fin.prod_univ_two]

theorem prod_two_append_comp {q q' : ℕ} (f : Fin q' → Gamma M) (τ : Fin q → Fin q') (ν : Fin 2 → Fin q)
    (l : Fin 0 → Fin q) : ∏ i, f (τ (Fin.append ν l i)) = f (τ (ν 0)) * f (τ (ν 1)) :=
  prod_two_append (fun j => f (τ j)) ν l

/-- **Lemma 7.21 for product cells.** When the normalized image of `X` is a
fibre product over its labels and the form depends only on the labels, the
contractions in the orders `21` and `12` built from the same unary stages have
the same head-start-`0` class. -/
theorem cls_product_orders
    (hFin₁ : ∀ a : Fin 2 → VF M, ∀ t : Fin 0 → RVInfinity M,
      {u : Fin r → RVInfinity M | (a, u) ∈ X.carrier ∧ u ∘ (Fin.elim0 : Fin 0 → Fin r) = t}.Finite)
    (hFin₂ : ∀ a : Fin 2 → VF M, ∀ t : Fin 0 → RVInfinity M,
      {u : Fin r → RVInfinity M | (a, u) ∈ X.carrier ∧ u ∘ (Fin.elim0 : Fin 0 → Fin r) = t}.Finite) :
    cls (objOf hc T ((contractionOne h00 hc linear hκ hs hv hsmall hΓ H0 H1 hW hω).headStartMeasuredObject
        h00 hc linear hκ hs hv hsmall hΓ 0 Fin.elim0 hFin₁)
        ((contractionOne h00 hc linear hκ hs hv hsmall hΓ H0 H1 hW hω).headStartObject_doublyBounded 0 Fin.elim0)) =
      cls (objOf hc T ((contractionSwap h00 hc linear hκ hs hv hsmall hΓ H0 H1 hW hω).headStartMeasuredObject
        h00 hc linear hκ hs hv hsmall hΓ 0 Fin.elim0 hFin₂)
        ((contractionSwap h00 hc linear hκ hs hv hsmall hΓ H0 H1 hW hω).headStartObject_doublyBounded 0 Fin.elim0)) := by
  have hP0 := proj0_proper h00 hc hκ hs hv D
  have hP1 := proj1_proper h00 hc hκ hs hv D
  have hU : ∀ u : Fin ((2 + r + H1.arity) + H0.arity) → RVInfinity M,
      ((Fin.elim0, u) : Mixed M 0 _) ∈
          (contractionOne h00 hc linear hκ hs hv hsmall hΓ H0 H1 hW hω).preparedContraction.data.rvTarget.carrier ↔
        ((Fin.elim0, u ∘ blockSwap (2 + r) H0.arity H1.arity) : Mixed M 0 _) ∈
          (contractionSwap h00 hc linear hκ hs hv hsmall hΓ H0 H1 hW hω).preparedContraction.data.rvTarget.carrier := by
    intro u
    refine (mem_productTarget hc hs hsmall (proj0 D) (proj1 D) hP0 (proj0_doublyBounded D) H0 H1 u).trans
      (Iff.trans ?_ (mem_productTarget hc hs hsmall (proj1 D) (proj0 D) hP1 (proj1_doublyBounded D) H1 H0
        (u ∘ blockSwap (2 + r) H0.arity H1.arity)).symm)
    simp only [Function.comp_apply, blockSwap_old, blockSwap_left, blockSwap_right]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨h3, h4, h1, h2⟩
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨h3, h4, h1, h2⟩
  have e1 : ((1 : Equiv.Perm (Fin 2)).symm 0) = Fin.castSucc 0 := rfl
  have e2 : ((1 : Equiv.Perm (Fin 2)).symm 1) = Fin.last 1 := rfl
  have e3 : ((Equiv.swap (0 : Fin 2) 1).symm 0) = Fin.last 1 := by
    rw [Equiv.symm_swap, Equiv.swap_apply_left]; rfl
  have e4 : ((Equiv.swap (0 : Fin 2) 1).symm 1) = Fin.castSucc 0 := by
    rw [Equiv.symm_swap, Equiv.swap_apply_right]; rfl
  have v0 : (contractionOne h00 hc linear hκ hs hv hsmall hΓ H0 H1 hW hω).preparedContraction.data.program.volumeIndex
      ((1 : Equiv.Perm (Fin 2)).symm 0) = blockSwap (2 + r) H0.arity H1.arity
        ((contractionSwap h00 hc linear hκ hs hv hsmall hΓ H0 H1 hW hω).preparedContraction.data.program.volumeIndex
          ((Equiv.swap (0 : Fin 2) 1).symm 0)) := by
    rw [e1, e3, volumeIndex_one, volumeIndex_swap, Fin.lastCases_castSucc, Fin.lastCases_last, blockSwap_left]
  have v1 : (contractionOne h00 hc linear hκ hs hv hsmall hΓ H0 H1 hW hω).preparedContraction.data.program.volumeIndex
      ((1 : Equiv.Perm (Fin 2)).symm 1) = blockSwap (2 + r) H0.arity H1.arity
        ((contractionSwap h00 hc linear hκ hs hv hsmall hΓ H0 H1 hW hω).preparedContraction.data.program.volumeIndex
          ((Equiv.swap (0 : Fin 2) 1).symm 1)) := by
    rw [e2, e4, volumeIndex_one, volumeIndex_swap, Fin.lastCases_last, Fin.lastCases_castSucc, blockSwap_right]
  have hprod : ∀ f : Fin ((2 + r + H1.arity) + H0.arity) → Gamma M,
      ∏ i, f (Fin.append (fun i => (contractionOne h00 hc linear hκ hs hv hsmall hΓ H0 H1 hW hω).preparedContraction.data.program.volumeIndex
          ((1 : Equiv.Perm (Fin 2)).symm i))
        ((contractionOne h00 hc linear hκ hs hv hsmall hΓ H0 H1 hW hω).oldIndex ∘ (Fin.elim0 : Fin 0 → Fin r)) i) =
      ∏ i, f (blockSwap (2 + r) H0.arity H1.arity (Fin.append (fun i =>
        (contractionSwap h00 hc linear hκ hs hv hsmall hΓ H0 H1 hW hω).preparedContraction.data.program.volumeIndex
          ((Equiv.swap (0 : Fin 2) 1).symm i))
        ((contractionSwap h00 hc linear hκ hs hv hsmall hΓ H0 H1 hW hω).oldIndex ∘ (Fin.elim0 : Fin 0 → Fin r)) i)) := by
    intro f
    rw [prod_two_append, prod_two_append_comp]
    exact congrArg₂ (· * ·) (congrArg f v0) (congrArg f v1)
  have hρ : ∀ (z : (contractionOne h00 hc linear hκ hs hv hsmall hΓ H0 H1 hW hω).preparedContraction.data.rvTarget)
      (z' : (contractionSwap h00 hc linear hκ hs hv hsmall hΓ H0 H1 hW hω).preparedContraction.data.rvTarget),
      z'.val.2 = z.val.2 ∘ blockSwap (2 + r) H0.arity H1.arity →
        ((contractionOne h00 hc linear hκ hs hv hsmall hΓ H0 H1 hW hω).preparedContraction.data.rvForm z).val =
          ((contractionSwap h00 hc linear hκ hs hv hsmall hΓ H0 H1 hW hω).preparedContraction.data.rvForm z').val := by
    intro z z' hz
    obtain ⟨y, rfl⟩ := (twoStageProgram (stageOneFirst h00 hc hκ hs hv hsmall H1 hW)
      (stageOneSecond h00 hc hκ hs hv hsmall H0 H1 hW)).surjective z
    obtain ⟨p, rfl⟩ := (prepOf_bijective h00 D 1).surjective y
    change (descForm h00 hω D 1 (twoStageProgram (stageOneFirst h00 hc hκ hs hv hsmall H1 hW)
      (stageOneSecond h00 hc hκ hs hv hsmall H0 H1 hW)) _).val =
      (descForm h00 hω D (Equiv.swap 0 1) (twoStageProgram (stageSwapFirst h00 hc hκ hs hv hsmall H0 hW)
        (stageSwapSecond h00 hc hκ hs hv hsmall H0 H1 hW)) z').val
    rw [descForm_factor]
    symm
    apply descForm_labels
    intro i
    rw [hz]
    change ((twoStageProgram (stageOneFirst h00 hc hκ hs hv hsmall H1 hW)
      (stageOneSecond h00 hc hκ hs hv hsmall H0 H1 hW)).toMap (prepOf D 1 p)).val.2
      (blockSwap (2 + r) H0.arity H1.arity (Fin.castAdd H1.arity (Fin.castAdd H0.arity (Fin.natAdd 2 i)))) =
        p.val.2 i
    rw [blockSwap_old]
    exact ((twoStageProgram (stageOneFirst h00 hc hκ hs hv hsmall H1 hW)
      (stageOneSecond h00 hc hκ hs hv hsmall H0 H1 hW)).retained (prepOf D 1 p) (Fin.natAdd 2 i)).trans
      (prepOf_labels D 1 p i)
  exact cls_labelObject_relabel hc rfl
    (contractionOne h00 hc linear hκ hs hv hsmall hΓ H0 H1 hW hω).preparedContraction.lift.originalTarget_recover
    (contractionSwap h00 hc linear hκ hs hv hsmall hΓ H0 H1 hW hω).preparedContraction.lift.originalTarget_recover
    _ _ (blockSwap (2 + r) H0.arity H1.arity) hU hprod
    (contractionOne h00 hc linear hκ hs hv hsmall hΓ H0 H1 hW hω).preparedContraction.data.rvForm
    (contractionSwap h00 hc linear hκ hs hv hsmall hΓ H0 H1 hW hω).preparedContraction.data.rvForm hρ _ _ _ _ _ _ _ _ _ _
    (fun p z hz => rvForm_read _ _ (fun _ => rfl) p z hz)
    (fun p z hz => rvForm_read _ _ (fun _ => rfl) p z hz) _ _

/-- **Lemma 7.21 for product cells, existence form.** Over a base with support
data, a family of product cells with form constant on label fibres has
standard contractions in the orders `21` and `12` with the same head-start-`0`
class. -/
theorem exists_product_orders (V : Set M) (hV : ∀ x ∈ V, iVF x) (hVT : V ⊆ (T : Set M))
    (hTV : (T : Set M) ⊆ algebraicClosureSet V) (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (hW : ImageProduct D) (hω : ∀ p z : X, p.val.2 = z.val.2 → ω p = ω z) :
    ∃ (G₁ : NormalizedMeasuredContraction (G := G) X ω 1)
      (G₂ : NormalizedMeasuredContraction (G := G) X ω (Equiv.swap 0 1)),
      ∀ hFin₁ hFin₂,
        cls (objOf hc T (G₁.headStartMeasuredObject h00 hc linear hκ hs hv hsmall hΓ 0 Fin.elim0 hFin₁)
          (G₁.headStartObject_doublyBounded 0 Fin.elim0)) =
        cls (objOf hc T (G₂.headStartMeasuredObject h00 hc linear hκ hs hv hsmall hΓ 0 Fin.elim0 hFin₂)
          (G₂.headStartObject_doublyBounded 0 Fin.elim0)) := by
  obtain ⟨U0⟩ := lemma_6_27_unary (G := G) h00 hc linear hκ hs hv V hsmall hΓ hV hVT hTV hnt (proj0 D)
    (proj0_proper h00 hc hκ hs hv D)
  obtain ⟨U1⟩ := lemma_6_27_unary (G := G) h00 hc linear hκ hs hv V hsmall hΓ hV hVT hTV hnt (proj1 D)
    (proj1_proper h00 hc hκ hs hv D)
  let H0 := U0.toStage h00 hc linear hκ hs hv hsmall hΓ
  let H1 := U1.toStage h00 hc linear hκ hs hv hsmall hΓ
  exact ⟨contractionOne h00 hc linear hκ hs hv hsmall hΓ H0 H1 hW hω,
    contractionSwap h00 hc linear hκ hs hv hsmall hΓ H0 H1 hW hω,
    fun hFin₁ hFin₂ => cls_product_orders h00 hc linear hκ hs hv hsmall hΓ H0 H1 hW hω hFin₁ hFin₂⟩

end Classes

end DiamondIntegral.Section7.ProductCells
