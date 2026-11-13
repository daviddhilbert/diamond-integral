import «section 3».MeasuredRVMapCoproducts

/-! A definable disjoint partition, with inherited combined weight, is
also a coproduct in the genuine weight-preserving map category. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory CategoryTheory.Limits
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4

noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {S : Set M} {k : ℕ}

def MeasuredRVMapObject.restrict (U : MeasuredRVMapObject hc S k)
    (X : DefSet (rawRVSpace (M := M) U.obj.underlying.arity) S)
    (hX : X.carrier ⊆ U.obj.underlying.domain.carrier) : MeasuredRVMapObject hc S k := ⟨U.obj.restrict hc X hX⟩

def measuredRVUnionSubset (U : MeasuredRVMapObject hc S k)
    (A B : DefSet (rawRVSpace (M := M) U.obj.underlying.arity) S)
    (hA : A.carrier ⊆ U.obj.underlying.domain.carrier) (hB : B.carrier ⊆ U.obj.underlying.domain.carrier) :
    (A.union B).carrier ⊆ U.obj.underlying.domain.carrier := fun _ h => h.elim (fun h => hA h) (fun h => hB h)

def measuredRVUnionInl (U : MeasuredRVMapObject hc S k)
    (A B : DefSet (rawRVSpace (M := M) U.obj.underlying.arity) S)
    (hA : A.carrier ⊆ U.obj.underlying.domain.carrier) (hB : B.carrier ⊆ U.obj.underlying.domain.carrier) :
    U.restrict A hA ⟶ U.restrict (A.union B) (measuredRVUnionSubset U A B hA hB) :=
  ⟨Map.inclusion (fun _ h => Or.inl h), fun _ => rfl⟩

def measuredRVUnionInr (U : MeasuredRVMapObject hc S k)
    (A B : DefSet (rawRVSpace (M := M) U.obj.underlying.arity) S)
    (hA : A.carrier ⊆ U.obj.underlying.domain.carrier) (hB : B.carrier ⊆ U.obj.underlying.domain.carrier) :
    U.restrict B hB ⟶ U.restrict (A.union B) (measuredRVUnionSubset U A B hA hB) :=
  ⟨Map.inclusion (fun _ h => Or.inr h), fun _ => rfl⟩

def measuredRVUnionDesc (U : MeasuredRVMapObject hc S k)
    (A B : DefSet (rawRVSpace (M := M) U.obj.underlying.arity) S)
    (hA : A.carrier ⊆ U.obj.underlying.domain.carrier) (hB : B.carrier ⊆ U.obj.underlying.domain.carrier)
    {W : MeasuredRVMapObject hc S k} (f : U.restrict A hA ⟶ W) (g : U.restrict B hB ⟶ W) :
    U.restrict (A.union B) (measuredRVUnionSubset U A B hA hB) ⟶ W where
  map := f.map.union g.map
  preserves a := by
    by_cases ha : a.val ∈ A.carrier
    · have he : (f.map.union g.map) a = f.map ⟨a.val, ha⟩ := by simp [Map.union, MeasuredRVMapObject.restrict, MeasuredRVObject.restrict, RVObject.restrict, ha]
      rw [he]
      exact f.preserves ⟨a.val, ha⟩
    · have he : (f.map.union g.map) a = g.map ⟨a.val, a.property.resolve_left ha⟩ := by simp [Map.union, MeasuredRVMapObject.restrict, MeasuredRVObject.restrict, RVObject.restrict, ha]
      rw [he]
      exact g.preserves ⟨a.val, a.property.resolve_left ha⟩

theorem measuredRVUnion_inl_desc (U : MeasuredRVMapObject hc S k)
    (A B : DefSet (rawRVSpace (M := M) U.obj.underlying.arity) S)
    (hA : A.carrier ⊆ U.obj.underlying.domain.carrier) (hB : B.carrier ⊆ U.obj.underlying.domain.carrier)
    {W : MeasuredRVMapObject hc S k} (f : U.restrict A hA ⟶ W) (g : U.restrict B hB ⟶ W) :
    measuredRVUnionInl U A B hA hB ≫ measuredRVUnionDesc U A B hA hB f g = f := by
  apply MeasuredRVMap.ext
  apply Map.ext
  intro a
  exact Map.union_on_left f.map g.map a

theorem measuredRVUnion_inr_desc (U : MeasuredRVMapObject hc S k)
    (A B : DefSet (rawRVSpace (M := M) U.obj.underlying.arity) S)
    (hA : A.carrier ⊆ U.obj.underlying.domain.carrier) (hB : B.carrier ⊆ U.obj.underlying.domain.carrier)
    (hd : Disjoint A.carrier B.carrier)
    {W : MeasuredRVMapObject hc S k} (f : U.restrict A hA ⟶ W) (g : U.restrict B hB ⟶ W) :
    measuredRVUnionInr U A B hA hB ≫ measuredRVUnionDesc U A B hA hB f g = g := by
  apply MeasuredRVMap.ext
  apply Map.ext
  intro a
  exact Map.union_on_right f.map g.map hd a

theorem measuredRVUnion_hom_ext (U : MeasuredRVMapObject hc S k)
    (A B : DefSet (rawRVSpace (M := M) U.obj.underlying.arity) S)
    (hA : A.carrier ⊆ U.obj.underlying.domain.carrier) (hB : B.carrier ⊆ U.obj.underlying.domain.carrier)
    {W : MeasuredRVMapObject hc S k}
    {f g : U.restrict (A.union B) (measuredRVUnionSubset U A B hA hB) ⟶ W}
    (hl : measuredRVUnionInl U A B hA hB ≫ f = measuredRVUnionInl U A B hA hB ≫ g)
    (hr : measuredRVUnionInr U A B hA hB ≫ f = measuredRVUnionInr U A B hA hB ≫ g) : f = g := by
  apply MeasuredRVMap.ext
  apply Map.ext
  intro a
  rcases a.property with ha | ha
  · exact congrArg (fun h : U.restrict A hA ⟶ W => h.map ⟨a.val, ha⟩) hl
  · exact congrArg (fun h : U.restrict B hB ⟶ W => h.map ⟨a.val, ha⟩) hr

def measuredRVUnionIsColimit (U : MeasuredRVMapObject hc S k)
    (A B : DefSet (rawRVSpace (M := M) U.obj.underlying.arity) S)
    (hA : A.carrier ⊆ U.obj.underlying.domain.carrier) (hB : B.carrier ⊆ U.obj.underlying.domain.carrier)
    (hd : Disjoint A.carrier B.carrier) :
    IsColimit (BinaryCofan.mk (measuredRVUnionInl U A B hA hB) (measuredRVUnionInr U A B hA hB)) :=
  BinaryCofan.IsColimit.mk _ (fun f g => measuredRVUnionDesc U A B hA hB f g)
    (measuredRVUnion_inl_desc U A B hA hB) (measuredRVUnion_inr_desc U A B hA hB hd)
    (fun f g m hl hr => measuredRVUnion_hom_ext U A B hA hB
      (hl.trans (measuredRVUnion_inl_desc U A B hA hB f g).symm)
      (hr.trans (measuredRVUnion_inr_desc U A B hA hB hd f g).symm))

def measuredRVCoprodUnionIso (U : MeasuredRVMapObject hc S k)
    (A B : DefSet (rawRVSpace (M := M) U.obj.underlying.arity) S)
    (hA : A.carrier ⊆ U.obj.underlying.domain.carrier) (hB : B.carrier ⊆ U.obj.underlying.domain.carrier)
    (hd : Disjoint A.carrier B.carrier) :
    (U.restrict A hA).coprod (U.restrict B hB) ≅ U.restrict (A.union B) (measuredRVUnionSubset U A B hA hB) :=
  (measuredRVMapCoprodIsColimit (U.restrict A hA) (U.restrict B hB)).coconePointUniqueUpToIso
    (measuredRVUnionIsColimit U A B hA hB hd)

end DiamondIntegral.Section3
