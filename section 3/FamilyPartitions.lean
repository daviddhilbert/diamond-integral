import «section 3».FamilyCoproductMaps
import Section4.FiniteGluing

/-! A piecewise disjoint partition is an actual definable bijection from
the coproduct of its two restricted families. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.DefinableGeometry
noncomputable section
namespace DiamondIntegral.Section3
variable {L : Language} {M : Type} [L.Structure M] {S : Set M} {P : Space L M}

theorem familyCarrier_ext (A : FiniteFamily P S) {a b : A.Carrier}
    (hi : a.1 = b.1) (hx : a.2.val = b.2.val) : a = b := by
  obtain ⟨i, a⟩ := a
  obtain ⟨j, b⟩ := b
  dsimp only at hi hx
  subst j
  exact congrArg (Sigma.mk i) (Subtype.ext hx)

theorem familyCoprod_cases (A B : FiniteFamily P S) (x : (A.coprod B).Carrier) :
    (∃ a, familyCoprodInl A B a = x) ∨ (∃ b, familyCoprodInr A B b = x) := by
  have h := familyCoprodEncode_decode A B x
  cases he : familyCoprodDecode A B x with
  | inl a => exact Or.inl ⟨a, by simpa only [he, familyCoprodEncode, Sum.elim_inl] using h⟩
  | inr b => exact Or.inr ⟨b, by simpa only [he, familyCoprodEncode, Sum.elim_inr] using h⟩

def FiniteFamily.withPieces (A : FiniteFamily P S) (X : Fin A.tags → DefSet P S) : FiniteFamily P S := ⟨A.tags, X⟩

def familyPartitionTag (N : ℕ) : Fin (N + N) → Fin N := Fin.addCases id id

theorem familyPartitionSubset (A : FiniteFamily P S) (X Y : Fin A.tags → DefSet P S)
    (hX : ∀ i, (X i).carrier ⊆ (A.piece i).carrier) (hY : ∀ i, (Y i).carrier ⊆ (A.piece i).carrier)
    (i : Fin (A.tags + A.tags)) :
    (((A.withPieces X).coprod (A.withPieces Y)).piece i).carrier ⊆
      (A.piece (familyPartitionTag A.tags i)).carrier := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa only [FiniteFamily.coprod, FiniteFamily.withPieces, familyPartitionTag, Fin.addCases_left, id_eq] using hX j
  · simpa only [FiniteFamily.coprod, FiniteFamily.withPieces, familyPartitionTag, Fin.addCases_right, id_eq] using hY j

def familyPartitionPieceMap (A : FiniteFamily P S) (X Y : Fin A.tags → DefSet P S)
    (hX : ∀ i, (X i).carrier ⊆ (A.piece i).carrier) (hY : ∀ i, (Y i).carrier ⊆ (A.piece i).carrier)
    (i : Fin (A.tags + A.tags)) :
    Map (((A.withPieces X).coprod (A.withPieces Y)).piece i) (A.piece (familyPartitionTag A.tags i)) :=
  Map.inclusion (familyPartitionSubset A X Y hX hY i)

def familyPartitionMap (A : FiniteFamily P S) (X Y : Fin A.tags → DefSet P S)
    (hX : ∀ i, (X i).carrier ⊆ (A.piece i).carrier) (hY : ∀ i, (Y i).carrier ⊆ (A.piece i).carrier) :
    ((A.withPieces X).coprod (A.withPieces Y)).Carrier → A.Carrier :=
  familyTaggedMap _ _ (familyPartitionTag A.tags) (familyPartitionPieceMap A X Y hX hY)

@[simp] theorem familyPartitionMap_inl (A : FiniteFamily P S) (X Y : Fin A.tags → DefSet P S)
    (hX : ∀ i, (X i).carrier ⊆ (A.piece i).carrier) (hY : ∀ i, (Y i).carrier ⊆ (A.piece i).carrier)
    (a : (A.withPieces X).Carrier) :
    familyPartitionMap A X Y hX hY (familyCoprodInl _ _ a) = ⟨a.1, Map.inclusion (hX a.1) a.2⟩ := by
  obtain ⟨i, a⟩ := a
  apply familyCarrier_ext A
  · change Fin.addCases id id (Fin.castAdd A.tags i) = i
    exact Fin.addCases_left i
  · rfl

@[simp] theorem familyPartitionMap_inr (A : FiniteFamily P S) (X Y : Fin A.tags → DefSet P S)
    (hX : ∀ i, (X i).carrier ⊆ (A.piece i).carrier) (hY : ∀ i, (Y i).carrier ⊆ (A.piece i).carrier)
    (b : (A.withPieces Y).Carrier) :
    familyPartitionMap A X Y hX hY (familyCoprodInr _ _ b) = ⟨b.1, Map.inclusion (hY b.1) b.2⟩ := by
  obtain ⟨i, b⟩ := b
  apply familyCarrier_ext A
  · change Fin.addCases id id (Fin.natAdd A.tags i) = i
    exact Fin.addCases_right i
  · rfl

theorem familyPartitionMap_bijective (A : FiniteFamily P S) (X Y : Fin A.tags → DefSet P S)
    (hX : ∀ i, (X i).carrier ⊆ (A.piece i).carrier) (hY : ∀ i, (Y i).carrier ⊆ (A.piece i).carrier)
    (hd : ∀ i, Disjoint (X i).carrier (Y i).carrier)
    (hu : ∀ i, ((X i).union (Y i)).carrier = (A.piece i).carrier) :
    Function.Bijective (familyPartitionMap A X Y hX hY) := by
  constructor
  · intro x y he
    rcases familyCoprod_cases (A.withPieces X) (A.withPieces Y) x with ⟨a, rfl⟩ | ⟨a, rfl⟩ <;>
      rcases familyCoprod_cases (A.withPieces X) (A.withPieces Y) y with ⟨b, rfl⟩ | ⟨b, rfl⟩
    · rw [familyPartitionMap_inl, familyPartitionMap_inl] at he
      apply congrArg (familyCoprodInl _ _)
      exact familyCarrier_ext _ (congrArg (fun p : A.Carrier => p.1) he) (congrArg (fun p : A.Carrier => p.2.val) he)
    · rw [familyPartitionMap_inl, familyPartitionMap_inr] at he
      have hi := congrArg Sigma.fst he
      obtain ⟨i, a⟩ := a
      obtain ⟨j, b⟩ := b
      dsimp only at hi
      subst j
      have hx : a.val = b.val := congrArg (fun p : A.Carrier => p.2.val) he
      exact False.elim (Set.disjoint_left.mp (hd i) a.property (hx.symm ▸ b.property))
    · rw [familyPartitionMap_inr, familyPartitionMap_inl] at he
      have hi := congrArg Sigma.fst he
      obtain ⟨i, a⟩ := a
      obtain ⟨j, b⟩ := b
      dsimp only at hi
      subst j
      have hx : a.val = b.val := congrArg (fun p : A.Carrier => p.2.val) he
      exact False.elim (Set.disjoint_left.mp (hd i) (hx ▸ b.property) a.property)
    · rw [familyPartitionMap_inr, familyPartitionMap_inr] at he
      apply congrArg (familyCoprodInr _ _)
      exact familyCarrier_ext _ (congrArg (fun p : A.Carrier => p.1) he) (congrArg (fun p : A.Carrier => p.2.val) he)
  · rintro ⟨i, a⟩
    rcases (hu i).ge a.property with ha | ha
    · refine ⟨familyCoprodInl _ _ ⟨i, ⟨a.val, ha⟩⟩, ?_⟩
      rw [familyPartitionMap_inl]
      rfl
    · refine ⟨familyCoprodInr _ _ ⟨i, ⟨a.val, ha⟩⟩, ?_⟩
      rw [familyPartitionMap_inr]
      rfl

def familyPartitionBijection (A : FiniteFamily P S) (X Y : Fin A.tags → DefSet P S)
    (hX : ∀ i, (X i).carrier ⊆ (A.piece i).carrier) (hY : ∀ i, (Y i).carrier ⊆ (A.piece i).carrier)
    (hd : ∀ i, Disjoint (X i).carrier (Y i).carrier)
    (hu : ∀ i, ((X i).union (Y i)).carrier = (A.piece i).carrier) :
    FamilyBijection ((A.withPieces X).coprod (A.withPieces Y)) A :=
  ⟨Equiv.ofBijective (familyPartitionMap A X Y hX hY) (familyPartitionMap_bijective A X Y hX hY hd hu),
    familyTaggedMap_definable _ _ _ _⟩

end DiamondIntegral.Section3
