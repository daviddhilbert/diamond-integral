import «section 6».UnaryFiniteFieldImages
import Section4.MixedTagging

/-! Every zero-coordinate event in an ordinary unary chain pulls back
to one original-base definable set with finite VF projection. In
particular this controls all finite focus events without requiring
finite RV fibres at intermediate stages. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S R : Set M} {r s : ℕ}

def ordinaryChainZeroSources : {r s : ℕ} →
    {A : SpecialTransformations.Section5.DefSet (M := M) R 1 r} →
    {B : SpecialTransformations.Section5.DefSet (M := M) R 1 s} →
    SpecialTransformations.Section5.Chain R 1 A B → Set (Mixed M 1 r)
  | _,_,A,_,.nil _ => {p | p ∈ SpecialTransformations.Section5.carrier A ∧ p.1 0=0}
  | _,_,A,_,.cons p T => {q | q ∈ SpecialTransformations.Section5.carrier A ∧ q.1 0=0} ∪
      {q | ∃ a : A,a.val=q ∧ (p.toMap a).val ∈ ordinaryChainZeroSources T}

theorem unary_zero_projection_finite (A : Set (Mixed M 1 r)) :
    (Prod.fst '' {p : Mixed M 1 r | p ∈ A ∧ p.1 0=0}).Finite := by
  apply (Set.finite_singleton (0 : Fin 1 → VF M)).subset
  rintro x ⟨p,hp,rfl⟩
  apply Set.mem_singleton_iff.mpr
  funext i
  fin_cases i
  exact hp.2

theorem unary_zero_locus_gamma_definable (hc : CanonicalStructure.IsCanonical (M := M)) :
    SpecialTransformations.Section5.GammaSetDefinable (ordinaryNamedGammaBase S)
      {p : Mixed M 1 r | p.1 0=0} := by
  apply (SpecialTransformations.Section5.gammaLogicInput (ordinaryNamedGammaBase S)).real_set
  apply (ordinary_point_definable_iff hc _).mpr
  apply (mixed_definable_iff_values_image S _).mpr
  have hEq : S.Definable LRV {z : Fin 1 ⊕ Fin r → M | z (.inl 0)=iVFZero} :=
    (Set.DefinableFun.proj (L := LRV) (A := S) (i := (Sum.inl 0 : Fin 1 ⊕ Fin r))).ofPred_eq
      (vfZeroCode_definable S)
  have h : S.Definable LRV {z : Fin 1 ⊕ Fin r → M |
      z ∈ (rawMixedSpace (M := M) 1 r).domain ∧ z (.inl 0)=iVFZero} :=
    ((rawMixedSpace (M := M) 1 r).definable_domain S).inter hEq
  convert h using 1
  ext z
  constructor
  · rintro ⟨p,hp,rfl⟩
    exact ⟨mixedValues_mem_domain p,congrArg Subtype.val hp⟩
  · rintro ⟨hz,he⟩
    let p := (rawMixedSpace (M := M) 1 r).decode ⟨z,hz⟩
    refine ⟨p,?_,mixedValues_decode _⟩
    apply Subtype.ext
    exact (congrFun (mixedValues_decode (⟨z,hz⟩ : (rawMixedSpace (M := M) 1 r).domain)) (.inl 0)).trans he

theorem ordinaryChainZeroSources_gamma_definable
    (hc : CanonicalStructure.IsCanonical (M := M))
    {A : SpecialTransformations.Section5.DefSet (M := M) R 1 r}
    {B : SpecialTransformations.Section5.DefSet (M := M) R 1 s}
    (T : SpecialTransformations.Section5.Chain R 1 A B)
    (hT : SpecialTransformations.Section5.GammaChainDefinable (ordinaryNamedGammaBase S) T) :
    SpecialTransformations.Section5.GammaSetDefinable (ordinaryNamedGammaBase S) (ordinaryChainZeroSources T) := by
  let L := SpecialTransformations.Section5.gammaLogicInput (ordinaryNamedGammaBase S)
  induction T with
  | nil A => exact L.inter hT (unary_zero_locus_gamma_definable hc)
  | @cons a b c A B C p tail ih =>
    have hSource := SpecialTransformations.Section5.GammaChainDefinable.source
      (ordinaryNamedGammaBase S) (.cons p tail) hT
    have hPre := L.image_graph (L.restrict_graph (ih hT.2)
      (L.swap_graph (SpecialTransformations.Section5.GammaPrimitiveDefinable.graph L p hT.1)))
    apply L.union (L.inter hSource (unary_zero_locus_gamma_definable hc))
    convert hPre using 1
    ext q
    constructor
    · rintro ⟨a,rfl,ha⟩
      exact ⟨(p.toMap a).val,ha,a,rfl,rfl⟩
    · rintro ⟨z,hz,a,rfl,rfl⟩
      exact ⟨a,rfl,hz⟩

theorem ordinaryChainZeroSources_finite_vfProjection
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    {A : SpecialTransformations.Section5.DefSet (M := M) R 1 r}
    {B : SpecialTransformations.Section5.DefSet (M := M) R 1 s}
    (T : SpecialTransformations.Section5.Chain R 1 A B)
    (hT : SpecialTransformations.Section5.GammaChainDefinable (ordinaryNamedGammaBase S) T) :
    (Prod.fst '' ordinaryChainZeroSources T).Finite := by
  let L := SpecialTransformations.Section5.gammaLogicInput (ordinaryNamedGammaBase S)
  induction T with
  | nil A => exact unary_zero_projection_finite _
  | @cons a b c A B C p tail ih =>
    have hA := SpecialTransformations.Section5.GammaChainDefinable.source
      (ordinaryNamedGammaBase S) (.cons p tail) hT
    have hB := SpecialTransformations.Section5.GammaChainDefinable.source
      (ordinaryNamedGammaBase S) tail hT.2
    let f := originalBaseOrdinaryMap hc hA hB p.toMap
      (SpecialTransformations.Section5.GammaPrimitiveDefinable.graph L p hT.1)
    have hf : Function.Bijective f := p.bijective
    have hFin := unaryFieldImage_finite hc hκ hs hsmall (f.inverse hf) (ordinaryChainZeroSources tail) (ih hT.2)
    apply ((unary_zero_projection_finite (SpecialTransformations.Section5.carrier A)).union hFin).subset
    rintro x ⟨q,hq,rfl⟩
    rcases hq with hZero | ⟨a,rfl,ha⟩
    · exact Or.inl ⟨q,hZero,rfl⟩
    · apply Or.inr
      refine ⟨f a,ha,?_⟩
      rw [Map.inverse_apply]

end DiamondIntegral.Section6
