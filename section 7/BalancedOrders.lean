import «section 7».BalancedKinds
import «section 7».ProductCells

/-! The contraction of a family of balanced cells in one order (for
Lemma 7.21).

Let `X ⊆ VF² × RV^q` satisfy `BalancedShearStages.BalancedShearInput` with
positioning functions `ε(u, ·)` and paradigms `t(u)`, and let `S_A` be any unary
contraction stage of the base family `A₁ = pr(X) = {(x, u) : ∃ y, (x, y, u) ∈ X}`
(`baseFam`). The contraction contracting the fibre coordinate first:

1. the balanced translation `(x, y) ↦ (x, y − ε(u, x))`
   (`BalancedShearStages.translationStage`), with new labels `rv(x)`, `t(u)` and
   a tag; its contracted set is the fibre product of its labels with `A₁`
   (`transContracted_eq`);
2. `S_A`, pulled back to the contracted set (`secondStageB`).

**The final RV target** (`mem_finalB`) consists of the tuples
`(rv(x), t(u), tag, u, z)` with `z` in the contracted set of `S_A` retaining
`u`. Since `rv(x)` and `t(u)` are functions of `u`, which `z` retains, the
projection `(…, z) ↦ z` is a definable bijection onto the contracted set of `S_A`
(`finalProj`, `finalProj_bijective`). The two orders of a balanced cell are
compared through these bijections and the RV map ψ of Lemma 6.38. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section9
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.BalancedOrders
open DiamondIntegral.Section6 DiamondIntegral.Section2
open DiamondIntegral.Section7.BalancedShearStages DiamondIntegral.Section7.PullbackStages
open DiamondIntegral.Section7.ProductCells

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
variable (linear : GammaPiecewiseRationalAffineInput (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
variable (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
variable {S : Set M} (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S, ∅⟩ : ParameterBase M))
variable {q : ℕ} {X : DefSet (rawMixedSpace (M := M) 2 q) S}
variable {ε : (Fin q → RVInfinity M) → VF M → VF M} {t : (Fin q → RVInfinity M) → RV M}
variable {t₁ : (Fin q → RVInfinity M) → RVInfinity M}
variable (H : BalancedShearInput X ε t t₁) (R : TranslationRadii X ε)

omit [M ⊨ Axioms.ACVF] in
theorem mixed0_ext {k : ℕ} {p p' : Mixed M 0 k} (h : p.2 = p'.2) : p = p' :=
  Prod.ext (Subsingleton.elim (α := Fin 0 → VF M) _ _) h

omit [M ⊨ Axioms.ACVF] in
theorem mem_of_val {k : ℕ} {Z : DefSet (rawMixedSpace (M := M) 0 k) S} (z : Z) :
    ((Fin.elim0, z.val.2) : Mixed M 0 k) ∈ Z.carrier := by
  have h : ((Fin.elim0, z.val.2) : Mixed M 0 k) = z.val := mixed0_ext rfl
  rw [h]
  exact z.property

/-- The base family: the first coordinate with all labels. -/
abbrev baseFam (X : DefSet (rawMixedSpace (M := M) 2 q) S) : DefSet (rawMixedSpace (M := M) 1 q) S :=
  (vfDropLast X).image

omit [M ⊨ Axioms.ACVF] in
theorem mem_baseFam (y : Fin 1 → VF M) (u : Fin q → RVInfinity M) :
    ((y, u) : Mixed M 1 q) ∈ (baseFam X).carrier ↔ ∃ yy : VF M, (![y 0, yy], u) ∈ X.carrier := by
  constructor
  · rintro ⟨p, hp⟩
    have h1 : Fin.init p.val.1 = y := congrArg Prod.fst hp
    have h2 : p.val.2 = u := congrArg Prod.snd hp
    refine ⟨p.val.1 1, ?_⟩
    have he : ![y 0, p.val.1 1] = p.val.1 := by
      rw [← h1]
      exact vec_two p.val.1
    rw [he, ← h2]
    exact p.property
  · rintro ⟨yy, hyy⟩
    refine ⟨⟨(![y 0, yy], u), hyy⟩, ?_⟩
    change ((Fin.init ![y 0, yy], u) : Mixed M 1 q) = (y, u)
    refine Prod.ext (FibreRestriction.fin_one_ext rfl) rfl

/-- The translation stage. -/
abbrev transStage : StandardContractionStage (G := G) X :=
  translationStage (G := G) h00 hc linear hκ hs hv hsmall hΓ H R

/-- The labels of the contracted set of the translation. -/
abbrev transLabels : DefSet (rawMixedSpace (M := M) 0 (2 + (1 + q))) S :=
  (vfDropLast (transStage (G := G) h00 hc linear hκ hs hv hsmall hΓ H R).contracted).image

/-- The positions of the old labels after the translation. -/
def oldPos (q : ℕ) (i : Fin q) : Fin (2 + (1 + q)) := Fin.natAdd 2 (Fin.natAdd 1 i)

/-- The labels of the translation at a point with labels `u`. -/
def transLab (x : VF M) (tu : RV M) (u : Fin q → RVInfinity M) : Fin (2 + (1 + q)) → RVInfinity M :=
  Fin.append ![rv M x, tu.val] (Fin.append ![branchTag (M := M) false] u)

theorem transLab_old (x : VF M) (tu : RV M) (u : Fin q → RVInfinity M) (i : Fin q) :
    transLab x tu u (oldPos q i) = u i := by
  simp only [transLab, oldPos, Fin.append_right]

theorem mem_transLabels (w : Fin (2 + (1 + q)) → RVInfinity M) :
    ((Fin.elim0, w) : Mixed M 0 (2 + (1 + q))) ∈ (transLabels h00 hc linear hκ hs hv hsmall hΓ H R).carrier ↔
      ∃ (x : VF M) (u : Fin q → RVInfinity M) (y : VF M), (![x, y], u) ∈ X.carrier ∧ w = transLab x (t u) u := by
  constructor
  · rintro ⟨p, hp⟩
    have h2 : p.val.2 = w := congrArg Prod.snd hp
    obtain ⟨u, y, hxy, hw⟩ := (mem_translationStage_contracted h00 hc linear hκ hs hv hsmall hΓ H R
      p.val.1 p.val.2).mp p.property
    exact ⟨p.val.1 0, u, y, hxy, h2 ▸ hw⟩
  · rintro ⟨x, u, y, hxy, rfl⟩
    have hm := (mem_translationStage_contracted h00 hc linear hκ hs hv hsmall hΓ H R (fun _ => x)
      (transLab x (t u) u)).mpr ⟨u, y, hxy, rfl⟩
    refine ⟨⟨_, hm⟩, ?_⟩
    exact mixed0_ext rfl

theorem transLabels_rvBounded :
    RVSupportDoublyBounded (transLabels h00 hc linear hκ hs hv hsmall hΓ H R).carrier :=
  vfDropLast_image_rvBounded (transStage h00 hc linear hκ hs hv hsmall hΓ H R).contracted_proper.rvBounded

include H in
/-- Points of `X` with the same labels have the same leading term in the base
coordinate. -/
theorem rv_base_eq {x x' y y' : VF M} {u : Fin q → RVInfinity M} (h : (![x, y], u) ∈ X.carrier)
    (h' : (![x', y'], u) ∈ X.carrier) : rv M x = rv M x' := by
  have := congrFun (H.tagged _ h _ h' rfl) 0
  exact this

/-- The contracted set of the translation is the fibre product of its labels
with the base family. -/
theorem transContracted_eq :
    (pullbackProd (transLabels h00 hc linear hκ hs hv hsmall hΓ H R) (baseFam X) (oldPos q)).carrier =
      (transStage h00 hc linear hκ hs hv hsmall hΓ H R).contracted.carrier := by
  ext ⟨y, w⟩
  rw [mem_pullbackProd_zero, mem_transLabels, mem_baseFam, mem_translationStage_contracted]
  constructor
  · rintro ⟨⟨x, u, yy, hxy, rfl⟩, ⟨y₂, hy₂⟩⟩
    have hu : (fun i => transLab x (t u) u (oldPos q i)) = u := funext fun i => transLab_old x (t u) u i
    change (![y 0, y₂], (fun i => transLab x (t u) u (oldPos q i))) ∈ X.carrier at hy₂
    rw [hu] at hy₂
    refine ⟨u, y₂, hy₂, ?_⟩
    have hx := rv_base_eq H hxy hy₂
    simp only [transLab]
    rw [hx]
  · rintro ⟨u, y₂, hy₂, rfl⟩
    refine ⟨⟨y 0, u, y₂, hy₂, rfl⟩, ⟨y₂, ?_⟩⟩
    have hu : (fun i => transLab (y 0) (t u) u (oldPos q i)) = u := funext fun i => transLab_old _ (t u) u i
    change (![y 0, y₂], (fun i => transLab (y 0) (t u) u (oldPos q i))) ∈ X.carrier
    rw [hu]
    exact hy₂

variable (SA : StandardContractionStage (G := G) (baseFam X))

/-- The second stage: `S_A` pulled back to the contracted set of the
translation. -/
def secondStageB : StandardContractionStage (G := G) (transStage h00 hc linear hκ hs hv hsmall hΓ H R).contracted :=
  ProductCells.stageOn (pullbackStageZero (transLabels h00 hc linear hκ hs hv hsmall hΓ H R) (oldPos q) SA
    (transLabels_rvBounded h00 hc linear hκ hs hv hsmall hΓ H R) hc hs hsmall)
    (transContracted_eq h00 hc linear hκ hs hv hsmall hΓ H R).symm

theorem secondStageB_oldLabels :
    (secondStageB h00 hc linear hκ hs hv hsmall hΓ H R SA).oldLabels = Fin.castAdd SA.arity := rfl

theorem secondStageB_leading :
    (secondStageB h00 hc linear hκ hs hv hsmall hΓ H R SA).leading = Fin.natAdd (2 + (1 + q)) SA.leading := rfl

/-- **The final RV target.** -/
theorem mem_finalB (w : Fin ((2 + (1 + q)) + SA.arity) → RVInfinity M) :
    ((Fin.elim0, w) : Mixed M 0 _) ∈ (secondStageB h00 hc linear hκ hs hv hsmall hΓ H R SA).contracted.carrier ↔
      ((Fin.elim0, fun i => w (Fin.castAdd SA.arity i)) : Mixed M 0 _) ∈
          (transLabels h00 hc linear hκ hs hv hsmall hΓ H R).carrier ∧
        ((Fin.elim0, fun j => w (Fin.natAdd _ j)) : Mixed M 0 SA.arity) ∈ SA.contracted.carrier ∧
        ∀ i, w (Fin.natAdd _ (SA.oldLabels i)) = w (Fin.castAdd SA.arity (oldPos q i)) :=
  mem_pullbackStage_contracted (transLabels h00 hc linear hκ hs hv hsmall hΓ H R) (oldPos q) SA
    (properInvariant_zero (transLabels_rvBounded h00 hc linear hκ hs hv hsmall hΓ H R))
    (vfDoublyBounded_zero _) hc hs hsmall Fin.elim0 w

/-- The projection of the final target to the contracted set of `S_A`. -/
def finalProj : Map (secondStageB h00 hc linear hκ hs hv hsmall hΓ H R SA).contracted SA.contracted :=
  (reindexMap (secondStageB h00 hc linear hκ hs hv hsmall hΓ H R SA).contracted
    (fun p => ((Fin.elim0, fun j => p.2 (Fin.natAdd _ j)) : Mixed M 0 SA.arity))
    (Sum.elim Fin.elim0 (fun j => Sum.inr (Fin.natAdd _ j)))
    (fun p => by
      funext i
      cases i with
      | inl i => exact i.elim0
      | inr j => rfl)).corestrict (fun p => by
    have h := (mem_finalB h00 hc linear hκ hs hv hsmall hΓ H R SA p.val.2).mp (mem_of_val p)
    exact h.2.1)

theorem finalProj_val (p : (secondStageB h00 hc linear hκ hs hv hsmall hΓ H R SA).contracted) :
    (finalProj h00 hc linear hκ hs hv hsmall hΓ H R SA p).val.2 = fun j => p.val.2 (Fin.natAdd _ j) := rfl

/-- **The projection is a bijection.** -/
theorem finalProj_bijective : Function.Bijective (finalProj h00 hc linear hκ hs hv hsmall hΓ H R SA) := by
  constructor
  · intro p p' he
    have hz : ∀ j, p.val.2 (Fin.natAdd _ j) = p'.val.2 (Fin.natAdd _ j) := fun j =>
      congrFun (congrArg (fun z : SA.contracted => z.val.2) he) j
    obtain ⟨hl, -, hc₁⟩ := (mem_finalB h00 hc linear hκ hs hv hsmall hΓ H R SA p.val.2).mp (mem_of_val p)
    obtain ⟨hl', -, hc₁'⟩ := (mem_finalB h00 hc linear hκ hs hv hsmall hΓ H R SA p'.val.2).mp (mem_of_val p')
    obtain ⟨x, u, y, hxy, hw⟩ := (mem_transLabels h00 hc linear hκ hs hv hsmall hΓ H R _).mp hl
    obtain ⟨x', u', y', hxy', hw'⟩ := (mem_transLabels h00 hc linear hκ hs hv hsmall hΓ H R _).mp hl'
    have hu : ∀ i, u i = p.val.2 (Fin.natAdd _ (SA.oldLabels i)) := by
      intro i
      rw [hc₁ i]
      have e := congrFun hw (oldPos q i)
      rw [transLab_old] at e
      exact e.symm
    have hu' : ∀ i, u' i = p'.val.2 (Fin.natAdd _ (SA.oldLabels i)) := by
      intro i
      rw [hc₁' i]
      have e := congrFun hw' (oldPos q i)
      rw [transLab_old] at e
      exact e.symm
    have huu : u = u' := funext fun i => by rw [hu, hu']; exact hz (SA.oldLabels i)
    subst huu
    have hx : rv M x = rv M x' := rv_base_eq H hxy hxy'
    apply Subtype.ext
    apply mixed0_ext
    funext i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · have e1 : p.val.2 (Fin.castAdd SA.arity i) = transLab x (t u) u i := congrFun hw i
      have e2 : p'.val.2 (Fin.castAdd SA.arity i) = transLab x' (t u) u i := congrFun hw' i
      rw [e1, e2]
      simp only [transLab]
      rw [hx]
    · exact hz j
  · intro z
    obtain ⟨y, hy⟩ := ProductCells.exists_source_of_contracted SA (mem_of_val z)
    obtain ⟨yy, hyy⟩ := (mem_baseFam (y := y) (u := z.val.2 ∘ SA.oldLabels)).mp hy
    let u := z.val.2 ∘ SA.oldLabels
    let w : Fin ((2 + (1 + q)) + SA.arity) → RVInfinity M := Fin.append (transLab (y 0) (t u) u) z.val.2
    have hw : ((Fin.elim0, w) : Mixed M 0 _) ∈ (secondStageB h00 hc linear hκ hs hv hsmall hΓ H R SA).contracted.carrier := by
      refine (mem_finalB h00 hc linear hκ hs hv hsmall hΓ H R SA w).mpr ⟨?_, ?_, fun i => ?_⟩
      · refine (mem_transLabels h00 hc linear hκ hs hv hsmall hΓ H R _).mpr ⟨y 0, u, yy, hyy, ?_⟩
        funext i
        exact Fin.append_left _ _ i
      · have he : (fun j => w (Fin.natAdd _ j)) = z.val.2 := funext fun j => Fin.append_right _ _ j
        rw [he]
        exact mem_of_val z
      · have e1 : w (Fin.natAdd _ (SA.oldLabels i)) = z.val.2 (SA.oldLabels i) := Fin.append_right _ _ _
        have e2 : w (Fin.castAdd SA.arity (oldPos q i)) = transLab (y 0) (t u) u (oldPos q i) :=
          Fin.append_left _ _ _
        rw [e1, e2, transLab_old]
        rfl
    refine ⟨⟨_, hw⟩, Subtype.ext (mixed0_ext ?_)⟩
    funext j
    change w (Fin.natAdd _ j) = z.val.2 j
    exact Fin.append_right _ _ j

end DiamondIntegral.Section7.BalancedOrders
