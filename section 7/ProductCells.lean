import «section 7».TwoStageContractions
import «section 7».PullbackStages
import «section 7».RelabelClasses
import «section 6».UnaryStandardContractionStages

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

end DiamondIntegral.Section7.ProductCells
