import «section 3».GammaGroundFamilyCoproductMaps
/-! A piecewise disjoint partition is an actual definable bijection from
the coproduct of its two restricted families. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.DefinableGeometry
noncomputable section
namespace DiamondIntegral.Section3
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)}
variable {P : Space LRV M}

theorem gammaGroundFamilyCarrier_ext (A : GammaGroundFiniteFamily hc ground P) {a b : A.Carrier}
    (hi : a.1 = b.1) (hx : a.2.val = b.2.val) : a = b := by
  obtain ⟨i, a⟩ := a
  obtain ⟨j, b⟩ := b
  dsimp only at hi hx
  subst j
  exact congrArg (Sigma.mk i) (Subtype.ext hx)

theorem gammaGroundFamilyCoprod_cases (A B : GammaGroundFiniteFamily hc ground P) (x : (A.coprod B).Carrier) :
    (∃ a, gammaGroundFamilyCoprodInl A B a = x) ∨ (∃ b, gammaGroundFamilyCoprodInr A B b = x) := by
  have h := gammaGroundFamilyCoprodEncode_decode A B x
  cases he : gammaGroundFamilyCoprodDecode A B x with
  | inl a => exact Or.inl ⟨a, by simpa only [he, gammaGroundFamilyCoprodEncode, Sum.elim_inl] using h⟩
  | inr b => exact Or.inr ⟨b, by simpa only [he, gammaGroundFamilyCoprodEncode, Sum.elim_inr] using h⟩

def GammaGroundFiniteFamily.withPieces (A : GammaGroundFiniteFamily hc ground P) (X : Fin A.tags → GammaGroundDefSet hc ground P) : GammaGroundFiniteFamily hc ground P := ⟨A.tags, X⟩

def gammaGroundFamilyPartitionTag (N : ℕ) : Fin (N + N) → Fin N := Fin.addCases id id

theorem gammaGroundFamilyPartitionSubset (A : GammaGroundFiniteFamily hc ground P) (X Y : Fin A.tags → GammaGroundDefSet hc ground P)
    (hX : ∀ i, (X i).carrier ⊆ (A.piece i).carrier) (hY : ∀ i, (Y i).carrier ⊆ (A.piece i).carrier)
    (i : Fin (A.tags + A.tags)) :
    (((A.withPieces X).coprod (A.withPieces Y)).piece i).carrier ⊆
      (A.piece (gammaGroundFamilyPartitionTag A.tags i)).carrier := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa only [GammaGroundFiniteFamily.coprod, GammaGroundFiniteFamily.withPieces, gammaGroundFamilyPartitionTag, Fin.addCases_left, id_eq] using hX j
  · simpa only [GammaGroundFiniteFamily.coprod, GammaGroundFiniteFamily.withPieces, gammaGroundFamilyPartitionTag, Fin.addCases_right, id_eq] using hY j

def gammaGroundFamilyPartitionPieceMap (A : GammaGroundFiniteFamily hc ground P) (X Y : Fin A.tags → GammaGroundDefSet hc ground P)
    (hX : ∀ i, (X i).carrier ⊆ (A.piece i).carrier) (hY : ∀ i, (Y i).carrier ⊆ (A.piece i).carrier)
    (i : Fin (A.tags + A.tags)) :
    GammaGroundMap (((A.withPieces X).coprod (A.withPieces Y)).piece i) (A.piece (gammaGroundFamilyPartitionTag A.tags i)) :=
  GammaGroundMap.inclusion (gammaGroundFamilyPartitionSubset A X Y hX hY i)

def gammaGroundFamilyPartitionMap (A : GammaGroundFiniteFamily hc ground P) (X Y : Fin A.tags → GammaGroundDefSet hc ground P)
    (hX : ∀ i, (X i).carrier ⊆ (A.piece i).carrier) (hY : ∀ i, (Y i).carrier ⊆ (A.piece i).carrier) :
    ((A.withPieces X).coprod (A.withPieces Y)).Carrier → A.Carrier :=
  gammaGroundFamilyTaggedMap _ _ (gammaGroundFamilyPartitionTag A.tags) (gammaGroundFamilyPartitionPieceMap A X Y hX hY)

@[simp] theorem gammaGroundFamilyPartitionMap_inl (A : GammaGroundFiniteFamily hc ground P) (X Y : Fin A.tags → GammaGroundDefSet hc ground P)
    (hX : ∀ i, (X i).carrier ⊆ (A.piece i).carrier) (hY : ∀ i, (Y i).carrier ⊆ (A.piece i).carrier)
    (a : (A.withPieces X).Carrier) :
    gammaGroundFamilyPartitionMap A X Y hX hY (gammaGroundFamilyCoprodInl _ _ a) = ⟨a.1, GammaGroundMap.inclusion (hX a.1) a.2⟩ := by
  obtain ⟨i, a⟩ := a
  apply gammaGroundFamilyCarrier_ext A
  · change Fin.addCases id id (Fin.castAdd A.tags i) = i
    exact Fin.addCases_left i
  · rfl

@[simp] theorem gammaGroundFamilyPartitionMap_inr (A : GammaGroundFiniteFamily hc ground P) (X Y : Fin A.tags → GammaGroundDefSet hc ground P)
    (hX : ∀ i, (X i).carrier ⊆ (A.piece i).carrier) (hY : ∀ i, (Y i).carrier ⊆ (A.piece i).carrier)
    (b : (A.withPieces Y).Carrier) :
    gammaGroundFamilyPartitionMap A X Y hX hY (gammaGroundFamilyCoprodInr _ _ b) = ⟨b.1, GammaGroundMap.inclusion (hY b.1) b.2⟩ := by
  obtain ⟨i, b⟩ := b
  apply gammaGroundFamilyCarrier_ext A
  · change Fin.addCases id id (Fin.natAdd A.tags i) = i
    exact Fin.addCases_right i
  · rfl

theorem gammaGroundFamilyPartitionMap_bijective (A : GammaGroundFiniteFamily hc ground P) (X Y : Fin A.tags → GammaGroundDefSet hc ground P)
    (hX : ∀ i, (X i).carrier ⊆ (A.piece i).carrier) (hY : ∀ i, (Y i).carrier ⊆ (A.piece i).carrier)
    (hd : ∀ i, Disjoint (X i).carrier (Y i).carrier)
    (hu : ∀ i, ((X i).union (Y i)).carrier = (A.piece i).carrier) :
    Function.Bijective (gammaGroundFamilyPartitionMap A X Y hX hY) := by
  constructor
  · intro x y he
    rcases gammaGroundFamilyCoprod_cases (A.withPieces X) (A.withPieces Y) x with ⟨a, rfl⟩ | ⟨a, rfl⟩ <;>
      rcases gammaGroundFamilyCoprod_cases (A.withPieces X) (A.withPieces Y) y with ⟨b, rfl⟩ | ⟨b, rfl⟩
    · rw [gammaGroundFamilyPartitionMap_inl, gammaGroundFamilyPartitionMap_inl] at he
      apply congrArg (gammaGroundFamilyCoprodInl _ _)
      exact gammaGroundFamilyCarrier_ext _ (congrArg (fun p : A.Carrier => p.1) he) (congrArg (fun p : A.Carrier => p.2.val) he)
    · rw [gammaGroundFamilyPartitionMap_inl, gammaGroundFamilyPartitionMap_inr] at he
      have hi := congrArg Sigma.fst he
      obtain ⟨i, a⟩ := a
      obtain ⟨j, b⟩ := b
      dsimp only at hi
      subst j
      have hx : a.val = b.val := congrArg (fun p : A.Carrier => p.2.val) he
      exact False.elim (Set.disjoint_left.mp (hd i) a.property (hx.symm ▸ b.property))
    · rw [gammaGroundFamilyPartitionMap_inr, gammaGroundFamilyPartitionMap_inl] at he
      have hi := congrArg Sigma.fst he
      obtain ⟨i, a⟩ := a
      obtain ⟨j, b⟩ := b
      dsimp only at hi
      subst j
      have hx : a.val = b.val := congrArg (fun p : A.Carrier => p.2.val) he
      exact False.elim (Set.disjoint_left.mp (hd i) (hx ▸ b.property) a.property)
    · rw [gammaGroundFamilyPartitionMap_inr, gammaGroundFamilyPartitionMap_inr] at he
      apply congrArg (gammaGroundFamilyCoprodInr _ _)
      exact gammaGroundFamilyCarrier_ext _ (congrArg (fun p : A.Carrier => p.1) he) (congrArg (fun p : A.Carrier => p.2.val) he)
  · rintro ⟨i, a⟩
    rcases (hu i).ge a.property with ha | ha
    · refine ⟨gammaGroundFamilyCoprodInl _ _ ⟨i, ⟨a.val, ha⟩⟩, ?_⟩
      rw [gammaGroundFamilyPartitionMap_inl]
      rfl
    · refine ⟨gammaGroundFamilyCoprodInr _ _ ⟨i, ⟨a.val, ha⟩⟩, ?_⟩
      rw [gammaGroundFamilyPartitionMap_inr]
      rfl

def gammaGroundFamilyPartitionBijection (A : GammaGroundFiniteFamily hc ground P) (X Y : Fin A.tags → GammaGroundDefSet hc ground P)
    (hX : ∀ i, (X i).carrier ⊆ (A.piece i).carrier) (hY : ∀ i, (Y i).carrier ⊆ (A.piece i).carrier)
    (hd : ∀ i, Disjoint (X i).carrier (Y i).carrier)
    (hu : ∀ i, ((X i).union (Y i)).carrier = (A.piece i).carrier) :
    GammaGroundFamilyBijection ((A.withPieces X).coprod (A.withPieces Y)) A :=
  ⟨Equiv.ofBijective (gammaGroundFamilyPartitionMap A X Y hX hY) (gammaGroundFamilyPartitionMap_bijective A X Y hX hY hd hu),
    gammaGroundFamilyTaggedMap_definable _ _ _ _⟩

end DiamondIntegral.Section3
