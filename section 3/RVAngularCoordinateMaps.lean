import «section 3».RVAngularQuotient
import «section 3».RVUnitMonomialCodes
import «section 3».RVUnitSpace
import «section 3».DefinableBijections
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}
variable {A : Set (Fin n → (CanonicalRV.RVSort M)ˣ)}

def rvAngularCoordinateCode (E : RVAngularCell A) (K : Section2.ZeroFaceChart (Set.range E.active))
    (z : Fin n → M) : Fin K.zeroArity ⊕ Fin K.freeArity → M :=
  Sum.elim (fun i => rvIntegerMonomialRawMap (integerBasisMatrix E.basis) z (K.zeroIndex i))
    (fun i => rvIntegerMonomialRawMap (integerBasisMatrix E.basis) z (K.freeIndex i))

theorem rvAngularCoordinateCode_definable (E : RVAngularCell A) (K : Section2.ZeroFaceChart (Set.range E.active)) (S : Set M) :
    S.DefinableMap LRV (rvAngularCoordinateCode E K) := by
  intro i
  cases i with
  | inl i => exact rvIntegerMonomialRawMap_definable S (integerBasisMatrix E.basis) (K.zeroIndex i)
  | inr i => exact rvIntegerMonomialRawMap_definable S (integerBasisMatrix E.basis) (K.freeIndex i)

theorem rvAngularCoordinateCode_values (E : RVAngularCell A) (K : Section2.ZeroFaceChart (Set.range E.active))
    (x : Fin n → (CanonicalRV.RVSort M)ˣ) :
    rvAngularCoordinateCode E K (rvUnitValues x) =
      Sum.elim (rvUnitValues (E.coordinateEquiv K x).1) (rvUnitValues (E.coordinateEquiv K x).2) := by
  have hh := rvIntegerMonomialRawMap_unitValues (integerBasisMatrix E.basis) x
  funext i
  cases i with
  | inl i => exact congrFun hh (K.zeroIndex i)
  | inr i => exact congrFun hh (K.freeIndex i)

/-- The monomial basis and coordinate split are actual same-ground
maps on presented nonzero RV sets, with full graph definability. -/
def rvAngularCoordinateMap (X : DefSet (rawRVUnitSpace (M := M) n) S)
    (E : RVAngularCell X.carrier) (K : Section2.ZeroFaceChart (Set.range E.active)) :
    Map X (DefSet.univ ((rawRVUnitSpace K.zeroArity).prod (rawRVUnitSpace K.freeArity)) S) := by
  let F := rvAngularCoordinateCode E K
  let f := E.coordinateEquiv K
  have hCode (c : (rawRVUnitSpace (M := M) n).domain) : F c.val =
      Sum.elim (rvUnitValues (f ((rawRVUnitSpace n).decode c)).1) (rvUnitValues (f ((rawRVUnitSpace n).decode c)).2) := by
    have hh := rvAngularCoordinateCode_values E K ((rawRVUnitSpace n).decode c)
    rwa [rvUnitValues_decode] at hh
  have hdom (c : (rawRVUnitSpace (M := M) n).domain) : F c.val ∈
      ((rawRVUnitSpace (M := M) K.zeroArity).prod (rawRVUnitSpace K.freeArity)).domain := by
    change (F c.val ∘ Sum.inl ∈ (rawRVUnitSpace K.zeroArity).domain) ∧
      (F c.val ∘ Sum.inr ∈ (rawRVUnitSpace K.freeArity).domain)
    rw [hCode c]
    exact ⟨Set.mem_range_self _,Set.mem_range_self _⟩
  refine Map.ofCodes X f F (rvAngularCoordinateCode_definable E K S) hdom ?_
  intro c
  apply Prod.ext
  · apply rvUnitValues_injective
    exact (rvUnitValues_decode _).trans
      (congrArg (fun z : Fin K.zeroArity ⊕ Fin K.freeArity → M => z ∘ Sum.inl) (hCode c))
  · apply rvUnitValues_injective
    exact (rvUnitValues_decode _).trans
      (congrArg (fun z : Fin K.zeroArity ⊕ Fin K.freeArity → M => z ∘ Sum.inr) (hCode c))

theorem rvAngularCoordinateMap_injective (X : DefSet (rawRVUnitSpace (M := M) n) S)
    (E : RVAngularCell X.carrier) (K : Section2.ZeroFaceChart (Set.range E.active)) :
    Function.Injective (rvAngularCoordinateMap X E K) := by
  intro x y he
  apply Subtype.ext
  exact (E.coordinateEquiv K).injective (congrArg Subtype.val he)

def rvAngularCoordinateBijection (X : DefSet (rawRVUnitSpace (M := M) n) S)
    (E : RVAngularCell X.carrier) (K : Section2.ZeroFaceChart (Set.range E.active)) :
    DefinableBijection X (rvAngularCoordinateMap X E K).image where
  map := (rvAngularCoordinateMap X E K).toImage
  bijective := by
    constructor
    · intro x y he
      apply rvAngularCoordinateMap_injective X E K
      have hv : (rvAngularCoordinateMap X E K x).val = (rvAngularCoordinateMap X E K y).val :=
        congrArg (fun z : (rvAngularCoordinateMap X E K).image => z.val) he
      exact Subtype.ext hv
    · rintro ⟨y,x,hx⟩
      exact ⟨x,Subtype.ext hx⟩

theorem rvAngularCoordinateMap_image (X : DefSet (rawRVUnitSpace (M := M) n) S)
    (E : RVAngularCell X.carrier) (K : Section2.ZeroFaceChart (Set.range E.active)) :
    (rvAngularCoordinateMap X E K).image.carrier = E.coordinateImage K := by
  ext y
  exact ⟨fun ⟨x,hx⟩ => ⟨x.val,x.property,hx⟩,fun ⟨x,hx,he⟩ => ⟨⟨x,hx⟩,he⟩⟩
end DiamondIntegral.Section3
