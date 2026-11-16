import «section 6».ProperCovariance
import «section 6».MixedInteriorRadii

/-! Definability of a graph projection retaining the other endpoint's
RV tag. Only the fixed original tag is added to the real parameter base. -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n m r s : ℕ}

theorem mixed_definable_iff_values_image (S : Set M) (H : Set (Mixed M n r)) :
    (rawMixedSpace (M := M) n r).Definable S H ↔ S.Definable LRV (mixedValues '' H) := by
  have he : (rawMixedSpace (M := M) n r).preimage H = mixedValues '' H := by
    ext z
    constructor
    · rintro ⟨hz,hH⟩
      exact ⟨(rawMixedSpace n r).decode ⟨z,hz⟩,hH,mixedValues_decode _⟩
    · rintro ⟨a,ha,rfl⟩
      exact ⟨mixedValues_mem_domain a,by simpa only [decode_mixedValues] using ha⟩
  change S.Definable LRV _ ↔ _
  rw [he]

theorem mixed_tuple_image_definable (S : Set M) (H : Set (Mixed M n r))
    (hH : (rawMixedSpace (M := M) n r).Definable S H) :
    S.Definable LRV (mixedTuple '' H) := by
  let π : Fin (n+r) → Fin n ⊕ Fin r := Fin.addCases Sum.inl Sum.inr
  have hecode (a : Mixed M n r) : mixedValues a ∘ π = mixedTuple a := by
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp only [Function.comp_apply,π,Fin.addCases_left,mixedTuple,Fin.append_left]
      rfl
    · simp only [Function.comp_apply,π,Fin.addCases_right,mixedTuple,Fin.append_right]
      rfl
  have h := ((mixed_definable_iff_values_image S H).mp hH).image_comp π
  convert h using 1
  ext z
  constructor
  · rintro ⟨a,ha,rfl⟩
    exact ⟨mixedValues a,⟨a,ha,rfl⟩,hecode a⟩
  · rintro ⟨_,⟨a,ha,rfl⟩,he⟩
    exact ⟨a,ha,(hecode a).symm.trans he⟩

def taggedRelationProjection
    (R : Mixed M n r → Mixed M m s → Prop) (u : Fin r → RVInfinity M) :
    Set (Mixed M n s) := {a | ∃ b : Fin m → VF M, R (a.1,u) (b,a.2)}

theorem taggedRelationProjection_definable
    (S : Set M) (R : Mixed M n r → Mixed M m s → Prop)
    (hR : (rawMixedSpace (M := M) n r).RelationDefinable (rawMixedSpace m s) S R)
    (u : Fin r → RVInfinity M) :
    (rawMixedSpace (M := M) n s).Definable (S ∪ Set.range (rvValues u))
      (taggedRelationProjection R u) := by
  let T := S ∪ Set.range (rvValues u)
  let P := rawMixedSpace (M := M) n r
  let Q := rawMixedSpace (M := M) m s
  let φ (z : (Fin n ⊕ Fin s) ⊕ Fin m → M) : (Fin n ⊕ Fin r) ⊕ (Fin m ⊕ Fin s) → M :=
    Sum.elim (Sum.elim (fun i => z (.inl (.inl i))) (rvValues u))
      (Sum.elim (z ∘ Sum.inr) (fun i => z (.inl (.inr i))))
  have hφ : T.DefinableMap LRV φ := by
    rintro ((i | i) | (i | i))
    · exact Set.DefinableFun.proj LRV
    · exact LRV.definableFun_const _ (Or.inr (Set.mem_range_self i))
    · exact Set.DefinableFun.proj LRV
    · exact Set.DefinableFun.proj LRV
  have hraw : S.Definable LRV (P.relation Q R) := hR
  have h := ((hraw.mono Set.subset_union_left).preimage_map hφ).exists_of_finite
  apply (mixed_definable_iff_values_image T _).mpr
  convert h using 1
  ext z
  constructor
  · rintro ⟨a,⟨b,hRab⟩,rfl⟩
    refine ⟨vfValues b,?_⟩
    have hrel := P.relation_decode Q R
      ⟨mixedValues (a.1,u),mixedValues_mem_domain _⟩
      ⟨mixedValues (b,a.2),mixedValues_mem_domain _⟩
    have hc₁ : P.decode ⟨mixedValues (a.1,u),mixedValues_mem_domain _⟩ = (a.1,u) := decode_mixedValues _
    have hc₂ : Q.decode ⟨mixedValues (b,a.2),mixedValues_mem_domain _⟩ = (b,a.2) := decode_mixedValues _
    rw [hc₁,hc₂] at hrel
    exact hrel.mpr hRab
  · rintro ⟨b,hsrc,htgt,hRab⟩
    let x := P.decode ⟨φ (Sum.elim z b) ∘ Sum.inl,hsrc⟩
    let y := Q.decode ⟨φ (Sum.elim z b) ∘ Sum.inr,htgt⟩
    have hx : mixedValues x = φ (Sum.elim z b) ∘ Sum.inl := mixedValues_decode _
    have hy : mixedValues y = φ (Sum.elim z b) ∘ Sum.inr := mixedValues_decode _
    have hxu : x.2 = u := funext (fun i => Subtype.ext (congrFun hx (.inr i)))
    refine ⟨(x.1,y.2),⟨y.1,?_⟩,?_⟩
    · change R (x.1,u) (y.1,y.2)
      rw [← hxu]
      exact hRab
    · funext i
      cases i with
      | inl i => exact congrFun hx (.inl i)
      | inr i => exact congrFun hy (.inr i)

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem invariant_bounded_tagged_projection_isClopen
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (S : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (H : Set (Mixed M n r)) (hH : (rawMixedSpace (M := M) n r).Definable S H)
    (hgeometry : ProperInvariantGeometry H) : IsClopen (Prod.fst '' H) := by
  obtain ⟨δ,hδ⟩ := properInvariantGeometry_uniform_radius h00 hc linear hκ hs hv S hsmall hΓ H
    (mixed_tuple_image_definable S H hH) hgeometry
  have hinv : AlphaInvariant (fun _ => δ) (Prod.fst '' H) := by
    intro a b hab
    constructor
    · rintro ⟨⟨x,t⟩,hx,rfl⟩
      exact ⟨(b,t),(hδ t x b hab).mp hx,rfl⟩
    · rintro ⟨⟨x,t⟩,hx,rfl⟩
      exact ⟨(a,t),(hδ t x a hab.symm).mp hx,rfl⟩
  exact hinv.isClopen hv

end DiamondIntegral.Section6
