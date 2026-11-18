import «section 6».UnaryFinitaryLifting
import «section 6».MixedTupleDifferentiability
import «section 6».AffineTailDifferentiability
import «section 6».DiagonalRVLiftCalculus
import «section 6».GammaConstantMaps
import «section 6».NonzeroBranchTags
import «section 4».RVCoordinatePieceCover
import Section4.RVDimensionRank
import «section 6».UnaryLiftingFieldBase

/-! Lemma 6.30 (`RVlift`) in arbitrary tuple arity, with the strengthened
regularity used in Section 7: every branch of the lift is continuous and
(totally) differentiable at every point.

For sets `U ⊆ RV^N` (nonzero coordinates) and a definable finitary relation
`R ⊆ U × RV^m`, there is a definable center function `c(a, v) ∈ VF^m` with
`rv c(a, v) = v` whenever `R(rv a, v)`, whose branch `a ↦ c(a, v)` is
differentiable at every `a` with `R(rv a, v)`.

Proof (as in the manuscript, by induction on `dim_RV U`): cover `U` by
coordinate pieces on which a projection to at most `dim U` coordinates is
finite-to-one (`RVCoordinatePieceCover.exists_cover`); on each piece choose
centers over the selected VF coordinates with the RV labels as parameters
(`exists_parametric_rv_centers`); the labels where differentiability fails
form a set of smaller RV dimension
(`exists_small_rv_labels_for_tuple_differentiability`), over which the lift
is replaced by the inductively constructed one; everything is glued along
RV conditions, which are clopen on the lifted domain. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}

/-- A definable finitary relation `R ⊆ U × RV^m` with nonzero source tuples. -/
structure FinitaryRVRelation (S : Set M) (N m : ℕ) where
  rel : (Fin N → RVInfinity M) → (Fin m → RVInfinity M) → Prop
  definable : S.Definable LRV {z : Fin N ⊕ Fin m → M |
    ∃ t v, rel t v ∧ rvValues t = z ∘ Sum.inl ∧ rvValues v = z ∘ Sum.inr}
  finite : ∀ t, {v | rel t v}.Finite
  source : ∀ t v, rel t v → ∀ i, t i ≠ rvZero M

/-- The code of a VF input and an RV output. -/
def liftCode {N m : ℕ} (a : Fin N → VF M) (v : Fin m → RVInfinity M) : Fin N ⊕ Fin m → M :=
  Sum.elim (vfValues a) (rvValues v)

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

/-- A lift of a finitary relation (Lemma 6.30): definable centers in the
prescribed RV-polydiscs whose branches are differentiable everywhere. -/
structure TupleFinitaryLift {N m : ℕ} (R : FinitaryRVRelation S N m) where
  center : (Fin N ⊕ Fin m → M) → Fin m → VF M
  definable : ∀ j, S.DefinableFun LRV (fun z => (center z j).val)
  prescribed : ∀ (a : Fin N → VF M) v, R.rel (tupleRV a) v → ∀ j, rv M (center (liftCode a v) j) = v j
  differentiable : ∀ (a : Fin N → VF M) v, R.rel (tupleRV a) v →
    ∃ L, HasVFDerivativeAt (fun a' => center (liftCode a' v)) a L

namespace FinitaryRVRelation
variable {N m : ℕ} (R : FinitaryRVRelation S N m)

theorem codes_iff (z : Fin N ⊕ Fin m → M) (t : Fin N → RVInfinity M) (v : Fin m → RVInfinity M)
    (ht : rvValues t = z ∘ Sum.inl) (hv : rvValues v = z ∘ Sum.inr) :
    (∃ t' v', R.rel t' v' ∧ rvValues t' = z ∘ Sum.inl ∧ rvValues v' = z ∘ Sum.inr) ↔ R.rel t v := by
  constructor
  · rintro ⟨t',v',h,ht',hv'⟩
    have h1 : t' = t := rvValues_injective (ht'.trans ht.symm)
    have h2 : v' = v := rvValues_injective (hv'.trans hv.symm)
    rw [← h1,← h2]
    exact h
  · intro h
    exact ⟨t,v,h,ht,hv⟩

/-- The source domain `U = {t | ∃ v, R t v}`. -/
def domain : DefSet (rawRVSpace (M := M) N) S where
  carrier := {t | ∃ v, R.rel t v}
  definable := by
    change S.Definable LRV ((rawRVSpace (M := M) N).preimage {t | ∃ v, R.rel t v})
    have h := R.definable.exists_of_finite
    suffices he : (rawRVSpace (M := M) N).preimage {t | ∃ v, R.rel t v} =
        {x : Fin N → M | ∃ u : Fin m → M, Sum.elim x u ∈ {z : Fin N ⊕ Fin m → M |
          ∃ t v, R.rel t v ∧ rvValues t = z ∘ Sum.inl ∧ rvValues v = z ∘ Sum.inr}} by
      rw [he]
      exact h
    ext x
    constructor
    · rintro ⟨hx,v,hv⟩
      refine ⟨rvValues v,_,v,hv,?_,rfl⟩
      exact rvValues_decode ⟨x,hx⟩
    · rintro ⟨y,t,v,h,ht,hv⟩
      have ht' : rvValues t = x := ht
      refine ⟨⟨t,ht'⟩,v,?_⟩
      have he : (rawRVSpace (M := M) N).decode ⟨x,⟨t,ht'⟩⟩ = t := by
        subst ht'
        exact decode_rvValues t
      rw [he]
      exact h

end FinitaryRVRelation

section Piece
variable {N m e : ℕ} (σ : Fin e → Fin N) (R : FinitaryRVRelation S N m)

/-- The RV outputs in coordinate `j` over the selected inputs with codes `x`. -/
def pieceFamily (j : Fin m) (x : Fin e → M) : Set M :=
  {w | ∃ t v, R.rel t v ∧ rvValues (t ∘ σ) = (fun i => iRv (x i)) ∧ (v j).val = w}

/-- The selected projection is finite-to-one on the domain. -/
def SelectedFinite : Prop :=
  ∀ y : Fin e → RVInfinity M, {t | (∃ v, R.rel t v) ∧ t ∘ σ = y}.Finite

theorem pieceFamily_finite (hfib : SelectedFinite σ R) (j : Fin m) (x : Fin e → M) :
    (pieceFamily σ R j x).Finite := by
  by_cases hy : ∃ y : Fin e → RVInfinity M, rvValues y = fun i => iRv (x i)
  · obtain ⟨y,hy⟩ := hy
    apply ((hfib y).biUnion (fun t _ => (R.finite t).image (fun v => (v j).val))).subset
    rintro w ⟨t,v,h,ht,rfl⟩
    exact Set.mem_biUnion (x := t) ⟨⟨v,h⟩,rvValues_injective (ht.trans hy.symm)⟩ ⟨v,h,rfl⟩
  · apply Set.finite_empty.subset
    rintro w ⟨t,v,_,ht,_⟩
    exact hy ⟨t ∘ σ,ht⟩

theorem pieceFamily_rv (j : Fin m) (x : Fin e → M) : ∀ w ∈ pieceFamily σ R j x, iRV w := by
  rintro w ⟨t,v,_,_,rfl⟩
  exact (v j).property

theorem pieceFamily_definable (j : Fin m) :
    S.Definable LRV {z : Fin e ⊕ Fin 1 → M | z (.inr 0) ∈ pieceFamily σ R j (z ∘ Sum.inl)} := by
  let Q : Set ((Fin e ⊕ Fin 1) ⊕ (Fin N ⊕ Fin m) → M) :=
    {y | y ∘ Sum.inr ∈ {z : Fin N ⊕ Fin m → M |
        ∃ t v, R.rel t v ∧ rvValues t = z ∘ Sum.inl ∧ rvValues v = z ∘ Sum.inr}} ∩
      (⋂ i : Fin e, {y | y (.inr (.inl (σ i))) = iRv (y (.inl (.inl i)))}) ∩
      {y | y (.inr (.inr j)) = y (.inl (.inr 0))}
  have hQ : S.Definable LRV Q := by
    refine ((R.definable.preimage_comp Sum.inr).inter ?_).inter ?_
    · exact Set.definable_iInter_of_finite (fun i => (Set.DefinableFun.proj LRV).ofPred_eq
        (rv_scalarCode_definable (Set.DefinableFun.proj LRV)))
    · exact (Set.DefinableFun.proj LRV).ofPred_eq (Set.DefinableFun.proj LRV)
  have h := hQ.exists_of_finite
  suffices he : {z : Fin e ⊕ Fin 1 → M | z (.inr 0) ∈ pieceFamily σ R j (z ∘ Sum.inl)} =
      {z | ∃ u : Fin N ⊕ Fin m → M, Sum.elim z u ∈ Q} by
    rw [he]
    exact h
  ext z
  constructor
  · rintro ⟨t,v,hr,ht,hv⟩
    refine ⟨Sum.elim (rvValues t) (rvValues v),⟨⟨t,v,hr,rfl,rfl⟩,?_⟩,?_⟩
    · simp only [Set.mem_iInter,Set.mem_ofPred_eq]
      intro i
      exact congrFun ht i
    · exact hv
  · rintro ⟨u,⟨⟨t,v,hr,ht,hv⟩,hsel⟩,hj⟩
    simp only [Set.mem_iInter,Set.mem_ofPred_eq] at hsel
    refine ⟨t,v,hr,?_,?_⟩
    · funext i
      exact (congrFun ht (σ i)).trans (hsel i)
    · exact (congrFun hv j).trans hj

/-- Centers for the piece: definable functions of the selected VF inputs and
one RV output coordinate. -/
theorem exists_piece_centers
    (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hV : ∀ a ∈ V, iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (hsmall : Cardinal.mk S < κ) (hfib : SelectedFinite σ R) :
    ∃ c : Fin m → (Fin (e+1) → M) → VF M, (∀ j, S.DefinableFun LRV (fun z => (c j z).val)) ∧
      ∀ j (a : Fin e → VF M) w, w ∈ pieceFamily σ R j (vfValues a) →
        iRv (c j (Fin.snoc (vfValues a) w)).val = w := by
  have hA : S.Definable LRV (vfValues '' (Set.univ : Set (Fin e → VF M))) := by
    convert vfRawUniverse_definable S e using 1
    ext z
    exact ⟨by rintro ⟨a,_,rfl⟩ i; exact (a i).property,
      fun h => ⟨(fun i => ⟨z i,h i⟩),Set.mem_univ _,rfl⟩⟩
  have hj (j : Fin m) := exists_parametric_rv_centers hc h00 hs hv V S hV hVS hSV hnt hsmall
    Set.univ hA (pieceFamily σ R j) (pieceFamily_definable σ R j)
    (pieceFamily_finite σ R hfib j) (pieceFamily_rv σ R j)
  choose c hcd hcv using hj
  exact ⟨c,hcd,fun j a w hw => hcv j a (Set.mem_univ _) w hw⟩

/-- The piece center map on codes. -/
def pieceCenter (c : Fin m → (Fin (e+1) → M) → VF M) (z : Fin N ⊕ Fin m → M) : Fin m → VF M :=
  fun j => c j (Fin.snoc (fun i => z (.inl (σ i))) (z (.inr j)))

omit [M ⊨ Axioms.ACVF] in
theorem pieceCenter_definable (c : Fin m → (Fin (e+1) → M) → VF M)
    (hcd : ∀ j, S.DefinableFun LRV (fun z => (c j z).val)) (j : Fin m) :
    S.DefinableFun LRV (fun z => (pieceCenter σ c z j).val) := by
  have hg : S.DefinableMap LRV (fun z : Fin N ⊕ Fin m → M =>
      (Fin.snoc (fun i => z (.inl (σ i))) (z (.inr j)) : Fin (e+1) → M)) := by
    intro l
    refine Fin.lastCases ?_ (fun i => ?_) l
    · simpa only [Fin.snoc_last] using (Set.DefinableFun.proj LRV : S.DefinableFun LRV
        (fun z : Fin N ⊕ Fin m → M => z (.inr j)))
    · simpa only [Fin.snoc_castSucc] using (Set.DefinableFun.proj LRV : S.DefinableFun LRV
        (fun z : Fin N ⊕ Fin m → M => z (.inl (σ i))))
  exact (hcd j).comp hg

theorem pieceCenter_prescribed (c : Fin m → (Fin (e+1) → M) → VF M)
    (hcv : ∀ j (a : Fin e → VF M) w, w ∈ pieceFamily σ R j (vfValues a) →
      iRv (c j (Fin.snoc (vfValues a) w)).val = w)
    (a : Fin N → VF M) (v : Fin m → RVInfinity M) (h : R.rel (tupleRV a) v) (j : Fin m) :
    rv M (pieceCenter σ c (liftCode a v) j) = v j := by
  apply Subtype.ext
  exact hcv j (a ∘ σ) (v j).val ⟨tupleRV a,v,h,rfl,rfl⟩

omit [M ⊨ Axioms.ACVF] in
theorem pieceCenter_branch (c : Fin m → (Fin (e+1) → M) → VF M) (v : Fin m → RVInfinity M) :
    (fun a' : Fin N → VF M => pieceCenter σ c (liftCode a' v)) =
      fun a' => (fun x : Fin e → VF M => fun j => c j (Fin.snoc (vfValues x) (v j).val)) (a' ∘ σ) := rfl

/-- Composing with a coordinate selection preserves differentiability. -/
theorem vfDifferentiableAt_select_comp {F : (Fin e → VF M) → Fin m → VF M} {a : Fin N → VF M}
    (hF : VFDifferentiableAt F (a ∘ σ)) : VFDifferentiableAt (F ∘ (fun x : Fin N → VF M => x ∘ σ)) a := by
  obtain ⟨L,hL⟩ := hF
  obtain ⟨D,hD⟩ := vfdifferentiableAt_select σ a
  have h := @HasVFDerivativeAt.comp M _ _ N e m (fun x : Fin N → VF M => x ∘ σ) F a D L hL hD
  exact ⟨_,h⟩

end Piece

theorem vfDifferentiableAt_constFun {N m : ℕ} (K : Fin m → VF M) (a : Fin N → VF M) :
    VFDifferentiableAt (fun _ : Fin N → VF M => K) a := by
  have h := hasVFDerivativeAt_affine (M := M) (n := N) (m := m) 0 K a
  have he : (fun x : Fin N → VF M => (0 : (Fin N → VF M) →ₗ[VF M] (Fin m → VF M)) x + K) = fun _ => K := by
    funext x
    rw [LinearMap.zero_apply,zero_add]
  rw [he] at h
  exact ⟨_,h⟩

section Labels
variable {N m e : ℕ} (σ : Fin e → Fin N) (R : FinitaryRVRelation S N m)

/-- Labels: the pairs `(u, v)` of the relation, as RV tuples of length `N+m`. -/
def labelSet : DefSet (rawRVSpace (M := M) (N+m)) S where
  carrier := {t | R.rel (fun i => t (Fin.castAdd m i)) (fun j => t (Fin.natAdd N j))}
  definable := by
    change S.Definable LRV ((rawRVSpace (M := M) (N+m)).preimage
      {t | R.rel (fun i => t (Fin.castAdd m i)) (fun j => t (Fin.natAdd N j))})
    have h := R.definable.preimage_comp (Sum.elim (Fin.castAdd m) (Fin.natAdd N) : Fin N ⊕ Fin m → Fin (N+m))
    suffices he : (rawRVSpace (M := M) (N+m)).preimage
        {t | R.rel (fun i => t (Fin.castAdd m i)) (fun j => t (Fin.natAdd N j))} =
        {z : Fin (N+m) → M | z ∘ (Sum.elim (Fin.castAdd m) (Fin.natAdd N) : Fin N ⊕ Fin m → Fin (N+m)) ∈
          {z : Fin N ⊕ Fin m → M | ∃ t v, R.rel t v ∧ rvValues t = z ∘ Sum.inl ∧ rvValues v = z ∘ Sum.inr}} by
      rw [he]
      exact h
    ext z
    constructor
    · rintro ⟨hz,hr⟩
      refine ⟨_,_,hr,?_,?_⟩
      · funext i
        exact congrFun (rvValues_decode ⟨z,hz⟩) (Fin.castAdd m i)
      · funext j
        exact congrFun (rvValues_decode ⟨z,hz⟩) (Fin.natAdd N j)
    · rintro ⟨t,v,hr,ht,hv⟩
      have hz : rvValues (Fin.append t v) = z := by
        funext k
        refine Fin.addCases (fun i => ?_) (fun j => ?_) k
        · change ((Fin.append t v) (Fin.castAdd m i)).val = z (Fin.castAdd m i)
          rw [Fin.append_left]
          exact congrFun ht i
        · change ((Fin.append t v) (Fin.natAdd N j)).val = z (Fin.natAdd N j)
          rw [Fin.append_right]
          exact congrFun hv j
      refine ⟨⟨_,hz⟩,?_⟩
      have hd : (rawRVSpace (M := M) (N+m)).decode ⟨z,⟨_,hz⟩⟩ = Fin.append t v := by
        subst hz
        exact decode_rvValues _
      change R.rel (fun i => ((rawRVSpace (M := M) (N+m)).decode ⟨z,⟨_,hz⟩⟩) (Fin.castAdd m i))
        (fun j => ((rawRVSpace (M := M) (N+m)).decode ⟨z,⟨_,hz⟩⟩) (Fin.natAdd N j))
      rw [hd]
      simpa only [Fin.append_left,Fin.append_right] using hr

/-- The selected projection of a label. -/
def labelVolume : Map (labelSet R) (DefSet.univ (rawRVSpace (M := M) e) S) := by
  let F (z : Fin (N+m) → M) : Fin e → M := fun k => z (Fin.castAdd m (σ k))
  have hcode (c : (rawRVSpace (M := M) (N+m)).domain) :
      rvValues (fun k => (rawRVSpace (M := M) (N+m)).decode c (Fin.castAdd m (σ k))) = F c.val := by
    funext k
    exact congrFun (rvValues_decode c) (Fin.castAdd m (σ k))
  refine Map.ofCodes _ (fun t => fun k => t (Fin.castAdd m (σ k))) F
    (fun _ => Set.DefinableFun.proj LRV)
    (fun c => ⟨fun k => (rawRVSpace (M := M) (N+m)).decode c (Fin.castAdd m (σ k)),hcode c⟩) ?_
  intro c
  apply rvValues_injective
  exact (rvValues_decode _).trans (hcode c).symm

theorem labelVolume_finite (hfib : SelectedFinite σ R) : (labelVolume σ R).FiniteFibres := by
  intro b
  have hT := hfib b.val
  let P : Set ((Fin N → RVInfinity M) × (Fin m → RVInfinity M)) :=
    ⋃ t ∈ {t | (∃ v, R.rel t v) ∧ t ∘ σ = b.val}, {t} ×ˢ {v | R.rel t v}
  have hP : P.Finite := hT.biUnion (fun t _ => (Set.finite_singleton t).prod (R.finite t))
  have hI : ((fun p : (Fin N → RVInfinity M) × (Fin m → RVInfinity M) => Fin.append p.1 p.2) '' P).Finite :=
    hP.image _
  apply (hI.preimage Subtype.val_injective.injOn).subset
  intro a ha
  have hb : (fun k => a.val (Fin.castAdd m (σ k))) = b.val := congrArg Subtype.val ha
  refine ⟨((fun i => a.val (Fin.castAdd m i)),(fun j => a.val (Fin.natAdd N j))),?_,Fin.append_castAdd_natAdd⟩
  exact Set.mem_biUnion (x := fun i => a.val (Fin.castAdd m i)) ⟨⟨_,a.property⟩,hb⟩ ⟨rfl,a.property⟩

/-- The RV object of labels with the selected projection as volume. -/
def labelObject (hc : CanonicalStructure.IsCanonical (M := M)) (hfib : SelectedFinite σ R) :
    MeasuredRVObject (M := M) S e where
  object := ⟨N+m,labelSet R,labelVolume σ R⟩
  finiteVolume := labelVolume_finite σ R hfib
  nonzero u i := by
    have h := R.source _ _ u.property (σ i)
    exact fun he => h (Subtype.ext he)
  form := gammaOneMap hc (labelSet R)

/-- The piece centers on the lift of the label object. -/
def liftCenterMap (hc : CanonicalStructure.IsCanonical (M := M)) (hfib : SelectedFinite σ R)
    (c : Fin m → (Fin (e+1) → M) → VF M) (hcd : ∀ j, S.DefinableFun LRV (fun z => (c j z).val)) :
    Map (rvLift (labelObject σ R hc hfib).object) (DefSet.univ (rawVFSpace (M := M) m) S) := by
  let P := rawMixedSpace (M := M) e (N+m)
  let f (p : P.Carrier) : Fin m → VF M := fun j => c j (Fin.snoc (vfValues p.1) (p.2 (Fin.natAdd N j)).val)
  let F (z : Fin e ⊕ Fin (N+m) → M) : Fin m → M :=
    fun j => (c j (Fin.snoc (fun i => z (Sum.inl i)) (z (Sum.inr (Fin.natAdd N j))))).val
  have hF : S.DefinableMap LRV F := by
    intro j
    have hg : S.DefinableMap LRV (fun z : Fin e ⊕ Fin (N+m) → M =>
        (Fin.snoc (fun i => z (Sum.inl i)) (z (Sum.inr (Fin.natAdd N j))) : Fin (e+1) → M)) := by
      intro l
      refine Fin.lastCases ?_ (fun i => ?_) l
      · simpa only [Fin.snoc_last] using (Set.DefinableFun.proj LRV : S.DefinableFun LRV
          (fun z : Fin e ⊕ Fin (N+m) → M => z (Sum.inr (Fin.natAdd N j))))
      · simpa only [Fin.snoc_castSucc] using (Set.DefinableFun.proj LRV : S.DefinableFun LRV
          (fun z : Fin e ⊕ Fin (N+m) → M => z (Sum.inl i)))
    exact (hcd j).comp hg
  have hcode (z : P.domain) : vfValues (f (P.decode z)) = F z.val := by
    have hmv := mixedValues_decode z
    have h1 : vfValues (P.decode z).1 = fun i => z.val (Sum.inl i) := funext (fun i => congrFun hmv (Sum.inl i))
    have h2 (k : Fin (N+m)) : ((P.decode z).2 k).val = z.val (Sum.inr k) := congrFun hmv (Sum.inr k)
    funext j
    change (c j (Fin.snoc (vfValues (P.decode z).1) ((P.decode z).2 (Fin.natAdd N j)).val)).val = _
    rw [h1,h2]
    rfl
  exact Map.ofCodes _ f F hF (fun z => ⟨f (P.decode z),hcode z⟩)
    (fun z => vfValues_injective ((vfValues_decode _).trans (hcode z).symm))

theorem liftCenterMap_value (hc : CanonicalStructure.IsCanonical (M := M)) (hfib : SelectedFinite σ R)
    (c : Fin m → (Fin (e+1) → M) → VF M) (hcd : ∀ j, S.DefinableFun LRV (fun z => (c j z).val))
    (p : rvLift (labelObject σ R hc hfib).object) :
    (liftCenterMap σ R hc hfib c hcd p).val =
      fun j => c j (Fin.snoc (vfValues p.val.1) (p.val.2 (Fin.natAdd N j)).val) := rfl

end Labels

section Step
variable {N m : ℕ}

/-- Restrict a finitary relation to pairs whose label lies in a definable set. -/
def FinitaryRVRelation.restrictLabels (R : FinitaryRVRelation S N m)
    (X : DefSet (rawRVSpace (M := M) (N+m)) S) : FinitaryRVRelation S N m where
  rel t v := R.rel t v ∧ Fin.append t v ∈ X.carrier
  definable := by
    let τ : Fin (N+m) → Fin N ⊕ Fin m := Fin.append Sum.inl Sum.inr
    have hX := X.definable
    change S.Definable LRV ((rawRVSpace (M := M) (N+m)).preimage X.carrier) at hX
    have h := R.definable.inter (hX.preimage_comp τ)
    suffices he : {z : Fin N ⊕ Fin m → M | ∃ t v, (R.rel t v ∧ Fin.append t v ∈ X.carrier) ∧
        rvValues t = z ∘ Sum.inl ∧ rvValues v = z ∘ Sum.inr} =
        {z | ∃ t v, R.rel t v ∧ rvValues t = z ∘ Sum.inl ∧ rvValues v = z ∘ Sum.inr} ∩
          {z | z ∘ τ ∈ (rawRVSpace (M := M) (N+m)).preimage X.carrier} by
      rw [he]
      exact h
    have hcode (t : Fin N → RVInfinity M) (v : Fin m → RVInfinity M) (z : Fin N ⊕ Fin m → M)
        (ht : rvValues t = z ∘ Sum.inl) (hv : rvValues v = z ∘ Sum.inr) :
        rvValues (Fin.append t v) = z ∘ τ := by
      funext k
      refine Fin.addCases (fun i => ?_) (fun j => ?_) k
      · change ((Fin.append t v) (Fin.castAdd m i)).val = z (τ (Fin.castAdd m i))
        rw [Fin.append_left]
        change (t i).val = z (Fin.append Sum.inl Sum.inr (Fin.castAdd m i))
        rw [Fin.append_left]
        exact congrFun ht i
      · change ((Fin.append t v) (Fin.natAdd N j)).val = z (τ (Fin.natAdd N j))
        rw [Fin.append_right]
        change (v j).val = z (Fin.append Sum.inl Sum.inr (Fin.natAdd N j))
        rw [Fin.append_right]
        exact congrFun hv j
    ext z
    constructor
    · rintro ⟨t,v,⟨hr,hx⟩,ht,hv⟩
      refine ⟨⟨t,v,hr,ht,hv⟩,?_⟩
      have hmem : rvValues (Fin.append t v) ∈ (rawRVSpace (M := M) (N+m)).preimage X.carrier :=
        (Space.preimage_decode (rawRVSpace (M := M) (N+m)) X.carrier ⟨rvValues (Fin.append t v),⟨_,rfl⟩⟩).mpr (by rw [decode_rvValues]; exact hx)
      rw [hcode t v z ht hv] at hmem
      exact hmem
    · rintro ⟨⟨t,v,hr,ht,hv⟩,hx⟩
      refine ⟨t,v,⟨hr,?_⟩,ht,hv⟩
      have hx' : z ∘ τ ∈ (rawRVSpace (M := M) (N+m)).preimage X.carrier := hx
      rw [← hcode t v z ht hv] at hx'
      have h' := (Space.preimage_decode (rawRVSpace (M := M) (N+m)) X.carrier ⟨rvValues (Fin.append t v),⟨_,rfl⟩⟩).mp hx'
      rwa [decode_rvValues] at h'
  finite t := (R.finite t).subset (fun _ h => h.1)
  source t v h := R.source t v h.1

/-- The source domain of the restriction has dimension at most that of the
label set. -/
theorem restrictLabels_dim (hc : CanonicalStructure.IsCanonical (M := M)) (hex : RVExchangeInput (M := M))
    {κ : Cardinal} (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (R : FinitaryRVRelation S N m) (X : DefSet (rawRVSpace (M := M) (N+m)) S) {k : ℕ}
    (hX : rvDim X ≤ k) : rvDim (R.restrictLabels X).domain ≤ k := by
  apply (rvDim_le_iff_point_rank hc hex hs hsmall _ k).mpr
  rintro ⟨t,v,hr,hx⟩
  have h₁ : rvTupleRank hc hex S t ≤ rvTupleRank hc hex S (Fin.append t v) := by
    apply rvTupleRank_le_of_algebraic hc hex S (Fin.append t v) t
    intro i
    refine algebraicAt_of_mem (σ := .rv) ?_ (t i).property
    refine Or.inr ⟨Fin.castAdd m i,?_⟩
    change ((Fin.append t v) (Fin.castAdd m i)).val = (t i).val
    rw [Fin.append_left]
  have h₂ := rvTupleRank_le_rvDim hc hex X ⟨Fin.append t v,hx⟩
  exact h₁.trans (h₂.trans hX)

/-- The code condition recognizing the restricted relation. -/
def codeCondition (R' : FinitaryRVRelation S N m) (z : Fin N ⊕ Fin m → M) : Prop :=
  Sum.elim (fun i => iRv (z (Sum.inl i))) (z ∘ Sum.inr) ∈
    {z : Fin N ⊕ Fin m → M | ∃ t v, R'.rel t v ∧ rvValues t = z ∘ Sum.inl ∧ rvValues v = z ∘ Sum.inr}

theorem codeCondition_definable (R' : FinitaryRVRelation S N m) :
    S.Definable LRV (Set.ofPred (codeCondition R')) := by
  have hg : S.DefinableMap LRV (fun z : Fin N ⊕ Fin m → M =>
      (Sum.elim (fun i => iRv (z (Sum.inl i))) (z ∘ Sum.inr) : Fin N ⊕ Fin m → M)) := by
    rintro (i | j)
    · exact rv_scalarCode_definable (Set.DefinableFun.proj LRV)
    · exact Set.DefinableFun.proj LRV
  exact R'.definable.preimage_map hg

theorem codeCondition_liftCode (R' : FinitaryRVRelation S N m) (a : Fin N → VF M) (v : Fin m → RVInfinity M) :
    codeCondition R' (liftCode a v) ↔ R'.rel (tupleRV a) v :=
  R'.codes_iff _ (tupleRV a) v rfl rfl

end Step

section StepLift
variable {N m : ℕ}

/-- One piece (Lemma 6.30, inductive step): a relation on which a projection
to `e` coordinates is finite-to-one has a lift, given lifts for all
sub-relations of RV dimension `< e`. -/
theorem step_lift (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hV : ∀ a ∈ V, iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    {e : ℕ} (σ : Fin e → Fin N) (R : FinitaryRVRelation S N m) (hfib : SelectedFinite σ R)
    (ih : ∀ R' : FinitaryRVRelation S N m, rvDim R'.domain < e → Nonempty (TupleFinitaryLift R')) :
    Nonempty (TupleFinitaryLift R) := by
  obtain ⟨c,hcd,hcv⟩ := exists_piece_centers σ R hc h00 hs hv V hV hVS hSV hnt hsmall hfib
  rcases e with _ | n
  · refine ⟨⟨pieceCenter σ c,pieceCenter_definable σ c hcd,pieceCenter_prescribed σ R c hcv,fun a v _ => ?_⟩⟩
    have hconst : (fun a' : Fin N → VF M => pieceCenter σ c (liftCode a' v)) =
        fun _ => pieceCenter σ c (liftCode a v) := by
      funext a' j
      unfold pieceCenter
      congr 2
      funext i
      exact i.elim0
    rw [hconst]
    exact vfDifferentiableAt_constFun _ a
  · let O := labelObject σ R hc hfib
    let f0 := liftCenterMap σ R hc hfib c hcd
    obtain ⟨Dbad,_,hDdim,hGood⟩ := exists_small_rv_labels_for_tuple_differentiability (G := G)
      h00 hc hκ hs hsmall hΓ hv O (fun _ : Unit => m) (fun _ => f0)
    let hex := rvExchangeInput_of_earlier hκ hs h00
    let R' := R.restrictLabels Dbad
    have hR'dim : rvDim R'.domain < n+1 :=
      Nat.lt_succ_of_le (restrictLabels_dim hc hex hs hsmall R Dbad (Nat.le_of_lt_succ hDdim))
    obtain ⟨L'⟩ := ih R' hR'dim
    let center : (Fin N ⊕ Fin m → M) → Fin m → VF M :=
      fun z j => if codeCondition R' z then L'.center z j else pieceCenter σ c z j
    refine ⟨⟨center,fun j => ?_,fun a v h j => ?_,fun a v h => ?_⟩⟩
    · have he : (fun z => (center z j).val) =
          fun z => if codeCondition R' z then (L'.center z j).val else (pieceCenter σ c z j).val := by
        funext z
        by_cases hz : codeCondition R' z
        · simp only [center,hz,ite_true]
        · simp only [center,hz,ite_false]
      rw [he]
      exact Set.DefinableFun.ite (codeCondition_definable R') (L'.definable j) (pieceCenter_definable σ c hcd j)
    · by_cases h' : R'.rel (tupleRV a) v
      · have hz : codeCondition R' (liftCode a v) := (codeCondition_liftCode R' a v).mpr h'
        simp only [center,hz,ite_true]
        exact L'.prescribed a v h' j
      · have hz : ¬ codeCondition R' (liftCode a v) := fun hz => h' ((codeCondition_liftCode R' a v).mp hz)
        simp only [center,hz,ite_false]
        exact pieceCenter_prescribed σ R c hcv a v h j
    · have ha0 : ∀ i, a i ≠ 0 := fun i hi => R.source _ _ h i
        (by rw [show tupleRV a i = rv M (a i) from rfl,hi,rv_zero])
      obtain ⟨ρ,hρ⟩ := nonzero_tuple_rv_ball a ha0
      have hcondball : ∀ x ∈ vfBall a ρ, (codeCondition R' (liftCode x v) ↔ R'.rel (tupleRV a) v) :=
        fun x hx => by rw [codeCondition_liftCode,hρ x hx]
      by_cases h' : R'.rel (tupleRV a) v
      · obtain ⟨L,hL⟩ := L'.differentiable a v h'
        refine ⟨L,hL.congr_on_vfBall (ρ := ρ) (fun x hx => ?_)⟩
        have hz := (hcondball x hx).mpr h'
        funext j
        simp only [center,hz,ite_true]
      · have hlab : Fin.append (tupleRV a) v ∉ Dbad.carrier := fun hm => h' ⟨h,hm⟩
        have hpmem : (a ∘ σ,Fin.append (tupleRV a) v) ∈ (rvLift O.object).carrier := by
          refine ⟨⟨Fin.append (tupleRV a) v,?_⟩,rfl,?_⟩
          · change R.rel (fun i => Fin.append (tupleRV a) v (Fin.castAdd m i))
              (fun j => Fin.append (tupleRV a) v (Fin.natAdd N j))
            simpa only [Fin.append_left,Fin.append_right] using h
          · funext k
            change Fin.append (tupleRV a) v (Fin.castAdd m (σ k)) = tupleRV (a ∘ σ) k
            rw [Fin.append_left]
            rfl
        let p : rvLift O.object := ⟨_,hpmem⟩
        obtain ⟨L,F,⟨ρ',hρ'⟩,hF⟩ := hGood p hlab ()
        obtain ⟨L2,hL2⟩ := vfDifferentiableAt_select_comp σ (F := F) (a := a) ⟨L,hF⟩
        refine ⟨L2,hL2.congr_on_vfBall (ρ := max ρ ρ') (fun x hx => ?_)⟩
        have hxρ : x ∈ vfBall a ρ := vfBall_anti (le_max_left _ _) hx
        have hxρ' : x ∘ σ ∈ vfBall (a ∘ σ) ρ' := fun i => vfBall_anti (le_max_right _ _) hx (σ i)
        have hz : ¬ codeCondition R' (liftCode x v) := fun hz => h' ((hcondball x hxρ).mp hz)
        obtain ⟨hx',hval⟩ := hρ' (x ∘ σ) hxρ'
        change F (x ∘ σ) = center (liftCode x v)
        rw [← hval,liftCenterMap_value]
        funext j
        simp only [center,hz,ite_false]
        change c j (Fin.snoc (vfValues (x ∘ σ)) ((Fin.append (tupleRV a) v) (Fin.natAdd N j)).val) =
          c j (Fin.snoc (fun i => (x (σ i)).val) (v j).val)
        rw [Fin.append_right]
        rfl

end StepLift

section Cover
variable {N m : ℕ}

omit [M ⊨ Axioms.ACVF] in
theorem rvValues_mem_preimage_iff (X : DefSet (rawRVSpace (M := M) N) S) (t : Fin N → RVInfinity M) :
    rvValues t ∈ (rawRVSpace (M := M) N).preimage X.carrier ↔ t ∈ X.carrier := by
  have h := Space.preimage_decode (rawRVSpace (M := M) N) X.carrier ⟨rvValues t,⟨t,rfl⟩⟩
  rw [decode_rvValues] at h
  exact h

/-- Restrict a relation to sources in (`pos`) or outside (`¬ pos`) a definable set. -/
def FinitaryRVRelation.restrictSource (R : FinitaryRVRelation S N m)
    (X : DefSet (rawRVSpace (M := M) N) S) (pos : Bool) : FinitaryRVRelation S N m where
  rel t v := R.rel t v ∧ (t ∈ X.carrier ↔ pos = true)
  definable := by
    have hX := X.definable
    change S.Definable LRV ((rawRVSpace (M := M) N).preimage X.carrier) at hX
    let Y : Set (Fin N ⊕ Fin m → M) := {z | z ∘ Sum.inl ∈ (rawRVSpace (M := M) N).preimage X.carrier}
    have hY : S.Definable LRV Y := hX.preimage_comp Sum.inl
    have hW : S.Definable LRV (if pos then Y else Yᶜ) := by
      cases pos
      · exact hY.compl
      · exact hY
    have h := R.definable.inter hW
    suffices he : {z : Fin N ⊕ Fin m → M | ∃ t v, (R.rel t v ∧ (t ∈ X.carrier ↔ pos = true)) ∧
        rvValues t = z ∘ Sum.inl ∧ rvValues v = z ∘ Sum.inr} =
        {z | ∃ t v, R.rel t v ∧ rvValues t = z ∘ Sum.inl ∧ rvValues v = z ∘ Sum.inr} ∩
          (if pos then Y else Yᶜ) by
      rw [he]
      exact h
    ext z
    have key (t : Fin N → RVInfinity M) (ht : rvValues t = z ∘ Sum.inl) :
        (t ∈ X.carrier ↔ pos = true) ↔ z ∈ (if pos then Y else Yᶜ) := by
      have hy : z ∈ Y ↔ t ∈ X.carrier := by
        change z ∘ Sum.inl ∈ (rawRVSpace (M := M) N).preimage X.carrier ↔ t ∈ X.carrier
        rw [← ht]
        exact rvValues_mem_preimage_iff X t
      cases pos
      · simp only [Bool.false_eq_true,iff_false,ite_false,Set.mem_compl_iff]
        exact not_congr hy.symm
      · simp only [iff_true,ite_true]
        exact hy.symm
    constructor
    · rintro ⟨t,v,⟨hr,hx⟩,ht,hv⟩
      exact ⟨⟨t,v,hr,ht,hv⟩,(key t ht).mp hx⟩
    · rintro ⟨⟨t,v,hr,ht,hv⟩,hz⟩
      exact ⟨t,v,⟨hr,(key t ht).mpr hz⟩,ht,hv⟩
  finite t := (R.finite t).subset (fun _ h => h.1)
  source t v h := R.source t v h.1

/-- Glue lifts of the two restrictions along a definable RV condition. -/
theorem glue_lift (R : FinitaryRVRelation S N m) (X : DefSet (rawRVSpace (M := M) N) S)
    (L₁ : TupleFinitaryLift (R.restrictSource X true)) (L₂ : TupleFinitaryLift (R.restrictSource X false)) :
    Nonempty (TupleFinitaryLift R) := by
  let cond (z : Fin N ⊕ Fin m → M) : Prop :=
    (fun i => iRv (z (Sum.inl i))) ∈ (rawRVSpace (M := M) N).preimage X.carrier
  have hcond : S.Definable LRV (Set.ofPred cond) := by
    have hX := X.definable
    change S.Definable LRV ((rawRVSpace (M := M) N).preimage X.carrier) at hX
    exact hX.preimage_map (fun i => rv_scalarCode_definable (Set.DefinableFun.proj LRV))
  have hlift (a : Fin N → VF M) (v : Fin m → RVInfinity M) : cond (liftCode a v) ↔ tupleRV a ∈ X.carrier :=
    rvValues_mem_preimage_iff X (tupleRV a)
  let center : (Fin N ⊕ Fin m → M) → Fin m → VF M :=
    fun z j => if cond z then L₁.center z j else L₂.center z j
  refine ⟨⟨center,fun j => ?_,fun a v h j => ?_,fun a v h => ?_⟩⟩
  · have he : (fun z => (center z j).val) =
        fun z => if cond z then (L₁.center z j).val else (L₂.center z j).val := by
      funext z
      by_cases hz : cond z
      · simp only [center,hz,ite_true]
      · simp only [center,hz,ite_false]
    rw [he]
    exact Set.DefinableFun.ite hcond (L₁.definable j) (L₂.definable j)
  · by_cases hx : tupleRV a ∈ X.carrier
    · have hz : cond (liftCode a v) := (hlift a v).mpr hx
      simp only [center,hz,ite_true]
      exact L₁.prescribed a v ⟨h,by simpa only [iff_true] using hx⟩ j
    · have hz : ¬ cond (liftCode a v) := fun hz => hx ((hlift a v).mp hz)
      simp only [center,hz,ite_false]
      exact L₂.prescribed a v ⟨h,by simpa only [Bool.false_eq_true,iff_false] using hx⟩ j
  · have ha0 : ∀ i, a i ≠ 0 := fun i hi => R.source _ _ h i
      (by rw [show tupleRV a i = rv M (a i) from rfl,hi,rv_zero])
    obtain ⟨ρ,hρ⟩ := nonzero_tuple_rv_ball a ha0
    have hball : ∀ x ∈ vfBall a ρ, (cond (liftCode x v) ↔ tupleRV a ∈ X.carrier) :=
      fun x hx => by rw [hlift,hρ x hx]
    by_cases hx : tupleRV a ∈ X.carrier
    · obtain ⟨L,hL⟩ := L₁.differentiable a v ⟨h,by simpa only [iff_true] using hx⟩
      refine ⟨L,hL.congr_on_vfBall (ρ := ρ) (fun x hxb => ?_)⟩
      have hz := (hball x hxb).mpr hx
      funext j
      simp only [center,hz,ite_true]
    · obtain ⟨L,hL⟩ := L₂.differentiable a v ⟨h,by simpa only [Bool.false_eq_true,iff_false] using hx⟩
      refine ⟨L,hL.congr_on_vfBall (ρ := ρ) (fun x hxb => ?_)⟩
      have hz : ¬ cond (liftCode x v) := fun hz => hx ((hball x hxb).mp hz)
      funext j
      simp only [center,hz,ite_false]

open SpecialTransformations.Milestone0.Transfer in
/-- A relation with no pairs has a lift. -/
theorem empty_lift (R : FinitaryRVRelation S N m) (hR : ∀ t v, ¬ R.rel t v) : Nonempty (TupleFinitaryLift R) := by
  have hz : S.DefinableFun LRV (fun _ : Fin N ⊕ Fin m → M => iVFZero) :=
    SpecialTransformations.DefinableConstants.constant (SpecialTransformations.DefinableConstants.function_symbol
      (L := LRV) Fn.vfZero Fin.elim0 (fun i => i.elim0))
  exact ⟨⟨fun _ _ => 0,fun _ => hz,fun a v h => absurd h (hR _ _),fun a v h => absurd h (hR _ _)⟩⟩

/-- Lifts over a finite cover of the source by definable sets glue. -/
theorem cover_lift :
    ∀ (Xs : List (DefSet (rawRVSpace (M := M) N) S)) (R : FinitaryRVRelation S N m),
      (∀ t v, R.rel t v → ∃ X ∈ Xs, t ∈ X.carrier) →
      (∀ X ∈ Xs, ∀ R' : FinitaryRVRelation S N m, (∀ t v, R'.rel t v → t ∈ X.carrier) →
        Nonempty (TupleFinitaryLift R')) →
      Nonempty (TupleFinitaryLift R)
  | [],R,hcov,_ => empty_lift R (fun t v h => by obtain ⟨X,hX,_⟩ := hcov t v h; exact absurd hX (List.not_mem_nil))
  | X :: Xs,R,hcov,hpiece => by
    obtain ⟨L₁⟩ := hpiece X (List.mem_cons_self) (R.restrictSource X true)
      (fun t v h => by simpa only [iff_true] using h.2)
    obtain ⟨L₂⟩ := cover_lift Xs (R.restrictSource X false)
      (fun t v h => by
        obtain ⟨Y,hY,ht⟩ := hcov t v h.1
        rcases List.mem_cons.mp hY with rfl | hY
        · exact absurd ht (by simpa only [Bool.false_eq_true,iff_false] using h.2)
        · exact ⟨Y,hY,ht⟩)
      (fun Y hY => hpiece Y (List.mem_cons_of_mem X hY))
    exact glue_lift R X L₁ L₂

end Cover

section Main
variable {N m : ℕ}

/-- Lemma 6.30 by induction on the RV dimension of the source. -/
theorem lift_of_rvDim_le (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hV : ∀ a ∈ V, iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M)) :
    ∀ d (R : FinitaryRVRelation S N m), rvDim R.domain ≤ d → Nonempty (TupleFinitaryLift R) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro R hR
    have hex := rvExchangeInput_of_earlier hκ hs h00
    obtain ⟨p,D,hcov⟩ := DiamondIntegral.Section4.RVCoordinatePieceCover.exists_cover hc hex hs hsmall R.domain hR
    apply cover_lift (List.ofFn (fun i => (D i).source)) R
    · intro t v h
      obtain ⟨i,hi⟩ := hcov t ⟨v,h⟩
      exact ⟨(D i).source,(List.mem_ofFn' _ _).mpr ⟨i,rfl⟩,hi⟩
    · intro X hX R' hR'X
      obtain ⟨i,rfl⟩ := (List.mem_ofFn' _ _).mp hX
      have hfib : SelectedFinite (D i).select R' := by
        intro y
        obtain ⟨C,hC⟩ := DiamondIntegral.Section4.RVCoordinatePieceCover.uniform_bound hs hsmall (D i)
        apply (hC y).1.subset
        rintro t ⟨⟨v,hv⟩,hty⟩
        exact ⟨hR'X t v hv,hty⟩
      exact step_lift hc h00 hκ hs hv V hV hVS hSV hnt hsmall hΓ (D i).select R' hfib
        (fun R'' hR'' => ih (rvDim R''.domain) (lt_of_lt_of_le hR'' (D i).bound) R'' le_rfl)

/-- Lemma 6.30 (`RVlift`) in arbitrary tuple arity: every definable finitary
relation from RV-tuples (nonzero coordinates) to RV-tuples has a definable
lift whose branches are differentiable, hence continuous, at every point. -/
theorem lemma_6_30_tuple (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hV : ∀ a ∈ V, iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (R : FinitaryRVRelation S N m) : Nonempty (TupleFinitaryLift R) :=
  lift_of_rvDim_le hc h00 hκ hs hv V hV hVS hSV hnt hsmall hΓ (rvDim R.domain) R le_rfl

/-- Continuity of the branches (the strengthened form used in Section 7). -/
theorem TupleFinitaryLift.continuousAt {R : FinitaryRVRelation S N m} (L : TupleFinitaryLift R)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (a : Fin N → VF M) (v : Fin m → RVInfinity M) (h : R.rel (tupleRV a) v) :
    ContinuousAt (fun a' => L.center (liftCode a' v)) a := by
  obtain ⟨L',hL'⟩ := L.differentiable a v h
  exact HasDerivativeAt.continuousAt hv ((hasDerivativeAt_iff_companion _ _ _).mpr hL')

end Main

/-- Lemma 6.30 in tuple arity over a VF-generated base. -/
theorem lemma_6_30_tuple_vfGenerated (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (T : LRV.Substructure M) (B₀ : VFGeneratedFieldBase T)
    (hnt : ∃ x : B₀.field, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (hsmall : Cardinal.mk (T : Set M) < κ) (hΓ : NontrivialDefinableGamma (⟨(T : Set M),∅⟩ : ParameterBase M))
    {N m : ℕ} (R : FinitaryRVRelation (T : Set M) N m) : Nonempty (TupleFinitaryLift R) := by
  obtain ⟨hV,hVS,hSV,hnt'⟩ := vfGenerated_base_support T B₀ hnt
  exact lemma_6_30_tuple hc h00 hκ hs hv (vfFieldNames B₀.field) hV hVS hSV hnt' hsmall hΓ R

end DiamondIntegral.Section6
