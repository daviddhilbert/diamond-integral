import «section 6».UnaryCentripetalExistence

/-! Barycenters of complete finite root fibers give actual unary focus
maps over the original base. The graph, uniform finite bound, active
RV locus, and RV compatibility are all constructed from the root family. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {r : ℕ} {S : Set M}

structure UnaryRootFamily (A : DefSet (rawMixedSpace (M := M) 1 r) S) where
  roots : DefSet (rawMixedSpace (M := M) 1 r) S
  subset : roots.carrier ⊆ A.carrier
  finite : ∀ u : Fin r → RVInfinity M,
    {x : VF M | ((fun _ : Fin 1 => x),u) ∈ roots.carrier}.Finite

namespace UnaryRootFamily

variable {A : DefSet (rawMixedSpace (M := M) 1 r) S}

def fibre (R : UnaryRootFamily A) (u : Fin r → RVInfinity M) : Finset (VF M) := (R.finite u).toFinset

theorem mem_fibre (R : UnaryRootFamily A) (u : Fin r → RVInfinity M) (x : VF M) :
    x ∈ R.fibre u ↔ ((fun _ : Fin 1 => x),u) ∈ R.roots.carrier := (R.finite u).mem_toFinset

def rawFamily (R : UnaryRootFamily A) (t : Fin r → M) : Finset (VF M) :=
  if ht : ∀ i, iRV (t i) then R.fibre (fun i => ⟨t i,ht i⟩) else ∅

theorem rawFamily_labels (R : UnaryRootFamily A) (u : Fin r → RVInfinity M) :
    R.rawFamily (rvValues u) = R.fibre u := by
  unfold rawFamily
  rw [dite_eq_left (show ∀ i, iRV (rvValues u i) from fun i => (u i).property)]
  congr 1

theorem rawFamily_definable (R : UnaryRootFamily A) :
    RawClosure.Tuple.RelationDefinable S (Barycentre.finiteFibreRelation R.rawFamily) := by
  let π : Fin 1 ⊕ Fin r → Fin r ⊕ Fin 1 := Sum.elim (fun _ => .inr 0) Sum.inl
  have h := ((mixed_definable_iff_values_image S _).mp R.roots.definable).preimage_comp π
  change S.Definable LRV {z : Fin r ⊕ Fin 1 → M | ∃ x ∈ R.rawFamily (z ∘ Sum.inl), x.val = z (.inr 0)}
  convert h using 1
  ext z
  constructor
  · rintro ⟨x,hx,he⟩
    by_cases ht : ∀ i, iRV (z (.inl i))
    · have hx' : x ∈ R.fibre (fun i => ⟨z (.inl i),ht i⟩) := by
        simpa only [rawFamily,Function.comp_apply,dif_pos ht] using hx
      refine ⟨((fun _ : Fin 1 => x),fun i => ⟨z (.inl i),ht i⟩),(R.mem_fibre _ _).mp hx',?_⟩
      funext i
      cases i with
      | inl i => fin_cases i; exact he
      | inr i => rfl
    · have hh : R.rawFamily (z ∘ Sum.inl) = ∅ := dif_neg ht
      exact (Finset.notMem_empty _ (hh ▸ hx)).elim
  · rintro ⟨p,hp,he⟩
    have ht : ∀ i, iRV (z (.inl i)) := by
      intro i
      have hei : (p.2 i).val = z (.inl i) := congrFun he (.inr i)
      exact hei ▸ (p.2 i).property
    have hpu : p.2 = fun i => ⟨z (.inl i),ht i⟩ := funext fun i => Subtype.ext (congrFun he (.inr i))
    refine ⟨p.1 0,?_,congrFun he (.inl 0)⟩
    have hcode : rvValues p.2 = z ∘ Sum.inl := funext (fun i => congrFun he (.inr i))
    rw [← hcode,R.rawFamily_labels,R.mem_fibre]
    have hEta : (fun _ : Fin 1 => p.1 0) = p.1 := by funext i; fin_cases i; rfl
    simpa only [hEta] using hp

theorem exists_uniform_bound (R : UnaryRootFamily A)
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal} (hs : Saturated M κ)
    (hsmall : Cardinal.mk S < κ) : ∃ N : ℕ, ∀ t, (R.rawFamily t).card ≤ N := by
  have hsort (t : Fin r → M) (y : Fin 1 → M)
      (hy : (t,y 0) ∈ Barycentre.finiteFibreRelation R.rawFamily) :
      (∀ i, iRV (t i)) ∧ ∀ i, iVF (y i) := by
    obtain ⟨x,hx,he⟩ := hy
    have ht : ∀ i, iRV (t i) := by
      by_contra hn
      have hh : R.rawFamily t = ∅ := dif_neg hn
      exact Finset.notMem_empty _ (hh ▸ hx)
    refine ⟨ht,?_⟩
    intro i
    fin_cases i
    have he' : x.val = y 0 := he
    change iVF (y 0)
    rw [← he']
    exact x.property
  have hf (t : Fin r → M) :
      {y : Fin 1 → M | (t,y 0) ∈ Barycentre.finiteFibreRelation R.rawFamily}.Finite := by
    apply ((R.rawFamily t).finite_toSet.image (fun x => fun _ : Fin 1 => x.val)).subset
    rintro y ⟨x,hx,he⟩
    exact ⟨x,hx,by funext i; fin_cases i; exact he⟩
  have hfin := finite_rv_to_vf_tuple_relation_image hc hs S hsmall _ R.rawFamily_definable hsort hf
  have hi : Function.Injective (fun x : VF M => fun _ : Fin 1 => x.val) := by
    intro x y he
    exact Subtype.ext (congrFun he 0)
  let E := hfin.preimage hi.injOn
  refine ⟨E.toFinset.card,fun t => Finset.card_le_card ?_⟩
  intro x hx
  apply E.mem_toFinset.mpr
  exact ⟨t,x,hx,rfl⟩

def activeTags (R : UnaryRootFamily A) := locusTags A R.roots

theorem active_nonempty_fibre (R : UnaryRootFamily A) (u : Fin r → RVInfinity M)
    (hu : u ∈ R.activeTags.carrier) : (R.fibre u).Nonempty := by
  obtain ⟨p,⟨hpA,hpR⟩,hpu⟩ := hu
  refine ⟨p.1 0,(R.mem_fibre _ _).mpr ?_⟩
  have hEta : (fun _ : Fin 1 => p.1 0) = p.1 := by funext i; fin_cases i; rfl
  change ((fun _ : Fin 1 => p.1 0),u) ∈ R.roots.carrier
  rw [hEta,← hpu]
  exact hpR

def meanMap (R : UnaryRootFamily A) (h00 : M ⊨ Axioms.ACVF00)
    (N : ℕ) (hb : ∀ t, (R.rawFamily t).card ≤ N) :
    Map (focusActive A R.activeTags) (DefSet.univ (rawVFSpace (M := M) 1) S) := by
  let F (p : Mixed M 1 r) : Fin 1 → VF M := fun _ => Barycentre.mean (R.fibre p.2)
  let codes (z : Fin 1 ⊕ Fin r → M) : Fin 1 → M := fun _ => (Barycentre.mean (R.rawFamily (z ∘ Sum.inr))).val
  have hm : S.DefinableFun LRV (fun t => (Barycentre.mean (R.rawFamily t)).val) :=
    Barycentre.mean_definable h00 S R.rawFamily R.rawFamily_definable N hb
  have hd : S.DefinableMap LRV codes := by
    intro i
    exact @Set.DefinableFun.comp M LRV inferInstance (Fin r) (Fin 1 ⊕ Fin r) S _ inferInstance
      (fun z => z ∘ Sum.inr) (fun _ => Set.DefinableFun.proj LRV) hm
  have hdom (c : (rawMixedSpace (M := M) 1 r).domain) : codes c.val ∈ (rawVFSpace 1).domain :=
    ⟨fun _ => Barycentre.mean (R.rawFamily (c.val ∘ Sum.inr)),rfl⟩
  refine Map.ofCodes _ F codes hd hdom ?_
  intro c
  apply vfValues_injective
  have hp : mixedValues ((rawMixedSpace 1 r).decode c) = c.val := mixedValues_decode c
  have hRV : rvValues ((rawMixedSpace 1 r).decode c).2 = c.val ∘ Sum.inr :=
    funext fun i => congrFun hp (.inr i)
  refine (vfValues_decode _).trans ?_
  funext i
  change (Barycentre.mean (R.rawFamily (c.val ∘ Sum.inr))).val = _
  rw [← hRV,R.rawFamily_labels]
  rfl

def focusData (R : UnaryRootFamily A) (h00 : M ⊨ Axioms.ACVF00)
    (hA : ProperInvariant S A.carrier) (hD : VFDoublyBounded A.carrier)
    (htag : ∀ p ∈ A.carrier, ∀ q ∈ A.carrier, p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1)
    (N : ℕ) (hb : ∀ t, (R.rawFamily t).card ≤ N) : UnaryFocusData A where
  activeTags := R.activeTags
  focus := fun u => Barycentre.mean (R.fibre u)
  focusMap := R.meanMap h00 N hb
  focusMap_eq := fun _ => rfl
  sourceProper := hA
  sourceDoublyBounded := hD
  tagged := htag
  focusRV := by
    intro p hp hu
    apply SpecialTransformations.Section5.mean_sameRV h00 _ (R.active_nonempty_fibre p.2 hu)
    intro x hx
    exact congrFun (htag _ (R.subset ((R.mem_fibre _ _).mp hx)) p hp rfl) 0

theorem exists_focusData (R : UnaryRootFamily A)
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (hA : ProperInvariant S A.carrier) (hD : VFDoublyBounded A.carrier)
    (htag : ∀ p ∈ A.carrier, ∀ q ∈ A.carrier, p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1) :
    ∃ D : UnaryFocusData A, D.activeTags = R.activeTags ∧
      ∀ u, D.focus u = Barycentre.mean (R.fibre u) := by
  obtain ⟨N,hN⟩ := R.exists_uniform_bound hc hs hsmall
  exact ⟨R.focusData h00 hA hD htag N hN,rfl,fun _ => rfl⟩

end UnaryRootFamily
end DiamondIntegral.Section6
