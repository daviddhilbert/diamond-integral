import «section 5».DiagonalFinitePartitions
import «section 5».CharacterIdealRelations

/-! Character-line relations in the actual raw diagonal constructible
ring. Removing the fixed zero point gives the corresponding torus
relation, with no cancellation assumption on positive classes. -/
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section5.PuiseuxOriginal.DiagonalConstructible
open Classical FirstOrder FirstOrder.Language
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

def zeroSet (n : ℕ) : Set (Fin n → ℂ) := {x | ∀ i, x i = 0}

theorem zeroSet_definable (n : ℕ) : (Set.univ : Set ℂ).Definable Language.ring (zeroSet n) := by
  have hi (i : Fin n) : (Set.univ : Set ℂ).Definable Language.ring {x : Fin n → ℂ | x i = 0} :=
    (Set.DefinableFun.proj Language.ring (A := (Set.univ : Set ℂ)) (i := i)).ofPred_eq_const (Set.mem_univ _)
  change (Set.univ : Set ℂ).Definable Language.ring {x | ∀ i, x i = 0}
  rw [Set.ofPred_forall]
  exact Set.definable_iInter_of_finite hi

theorem zeroSet_invariant {n : ℕ} (q : Fin n → ℚ) : RationalInvariant q (zeroSet n) := by
  intro η x
  change (∀ i, (↑(compatibleRootCharacter η (Multiplicative.ofAdd (q i))) : ℂ) * x i = 0) ↔ ∀ i, x i = 0
  simp only [mul_eq_zero, Units.ne_zero, false_or]

def zeroObject {n : ℕ} (q : Fin n → ℚ) : Object :=
  ofSet q (zeroSet n) (zeroSet_definable n) (zeroSet_invariant q)

theorem zeroGraph {n : ℕ} :
    framedEquivGraph (zeroSet n) (zeroSet n) (_root_.Equiv.refl _) = zeroSet (n + n) := by
  ext z
  constructor
  · rintro ⟨x, hx, hy⟩
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · exact (congrFun hx j).trans (x.property j)
    · exact (congrFun hy j).trans (x.property j)
  · intro hz
    refine ⟨⟨fun _ => 0, fun _ => rfl⟩, ?_, ?_⟩
    · exact funext (fun i => hz (Fin.castAdd n i))
    · exact funext (fun i => hz (Fin.natAdd n i))

def zeroIso {n : ℕ} (q r : Fin n → ℚ) : Iso (zeroObject q) (zeroObject r) where
  equiv := _root_.Equiv.refl _
  graph_definable := by
    change (Set.univ : Set ℂ).Definable Language.ring (framedEquivGraph (zeroSet n) (zeroSet n) (_root_.Equiv.refl _))
    rw [zeroGraph]
    exact zeroSet_definable _
  graph_invariant := by
    change RationalInvariant (Fin.append q r) (framedEquivGraph (zeroSet n) (zeroSet n) (_root_.Equiv.refl _))
    rw [zeroGraph]
    exact zeroSet_invariant _

theorem zeroObject_class {n : ℕ} (q r : Fin n → ℚ) : objectClass (zeroObject q) = objectClass (zeroObject r) :=
  objectClass_iso (zeroIso q r)

def affineSpace {n : ℕ} (q : Fin n → ℚ) : Object :=
  ofSet q Set.univ Set.definable_univ (fun _ _ => Iff.rfl)

def affineLine (q : ℚ) : Object := affineSpace (fun _ : Fin 1 => q)

def puncturedLine (q : ℚ) : Object :=
  outside (affineLine q) (zeroSet 1) (zeroSet_definable 1) (zeroSet_invariant (fun _ => q))

theorem affineLine_class (q : ℚ) :
    objectClass (affineLine q) = objectClass (zeroObject (fun _ : Fin 1 => q)) + objectClass (puncturedLine q) := by
  have h := objectClass_scissor (affineLine q) (zeroSet 1) (zeroSet_definable 1) (zeroSet_invariant (fun _ => q))
  have he : (cut (affineLine q) (zeroSet 1) (zeroSet_definable 1) (zeroSet_invariant (fun _ => q))).domain = zeroSet 1 :=
    Set.univ_inter _
  have hc : objectClass (cut (affineLine q) (zeroSet 1) (zeroSet_definable 1) (zeroSet_invariant (fun _ => q))) =
      objectClass (zeroObject (fun _ : Fin 1 => q)) := setClass_congr (fun _ => q) _ _ _ _ _ _ he
  exact h.trans (congrArg (fun x => x + objectClass (puncturedLine q)) hc)

theorem line_difference_eq_torus_difference (q : ℚ) :
    objectClass (affineLine q) - objectClass (affineLine 0) =
      objectClass (puncturedLine q) - objectClass (puncturedLine 0) := by
  rw [affineLine_class q, affineLine_class 0, zeroObject_class (fun _ : Fin 1 => q) (fun _ => 0)]
  abel

def lineIdeal : Ideal Ring := characterLineIdeal (fun q : ℚ => objectClass (affineLine q)) (objectClass (affineLine 0))

def torusIdeal : Ideal Ring :=
  Ideal.span (Set.range (fun q : ℚ => objectClass (puncturedLine q) - objectClass (puncturedLine 0)))

def directSumLinearIdeal : Ideal Ring :=
  directSumCharacterIdeal (fun q : ℚ => objectClass (affineLine q)) (objectClass (affineLine 0))

theorem lineIdeal_eq_torusIdeal : lineIdeal = torusIdeal := by
  unfold lineIdeal characterLineIdeal torusIdeal
  simp_rw [line_difference_eq_torus_difference]

theorem directSumLinearIdeal_eq_lineIdeal : directSumLinearIdeal = lineIdeal :=
  directSumCharacterIdeal_eq_characterLineIdeal _ _

theorem arbitrary_product_linear_relation_mem (X : Object) (n : ℕ) (q : Fin n → ℚ) :
    objectClass X * ((∏ i, objectClass (affineLine (q i))) - objectClass (affineLine 0) ^ n) ∈ lineIdeal :=
  character_product_difference_multiple _ _ n q (objectClass X)

end DiamondIntegral.Section5.PuiseuxOriginal.DiagonalConstructible
