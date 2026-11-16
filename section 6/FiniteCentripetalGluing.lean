import «section 6».FiniteGraphGluing

/-! Finite gluing of components with disjoint old-label loci, a common
changing coordinate and a common named coefficient. Full focus graphs,
continuity and covariance are assembled over the original base. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {I : Type} [Finite I] {A : DefSet (rawMixedSpace (M := M) n r) S}

def gluedFocus (D : I → CentripetalData (G := G) A)
    (x : Fin n → VF M) (u : Fin r → RVInfinity M) : VF M :=
  if h : ∃ i, u ∈ (D i).activeTags.carrier then (D h.choose).focus x u else 0

theorem gluedFocus_at (D : I → CentripetalData (G := G) A)
    (hsep : ∀ i j u, u ∈ (D i).activeTags.carrier → u ∈ (D j).activeTags.carrier → i = j)
    (i : I) (u : Fin r → RVInfinity M) (hu : u ∈ (D i).activeTags.carrier)
    (x : Fin n → VF M) : gluedFocus D x u = (D i).focus x u := by
  have h : ∃ j, u ∈ (D j).activeTags.carrier := ⟨i,hu⟩
  rw [gluedFocus,dite_eq_left h,hsep h.choose i u h.choose_spec hu]

theorem exists_finite_centripetal_gluing
    (D : I → CentripetalData (G := G) A)
    (hsep : ∀ i j u, u ∈ (D i).activeTags.carrier → u ∈ (D j).activeTags.carrier → i = j)
    (j : Fin n) (hj : ∀ i, (D i).coordinate = j)
    (c : VF M) (hc : ∀ i, (D i).coefficient = c)
    (hc0 : c ≠ 0) (hcpos : (1 : GammaInfinity M) ≤ vfValue c)
    (hcdef : S.Definable₁ LRV {c.val})
    (hA : ProperInvariant S A.carrier) (hAD : VFDoublyBounded A.carrier)
    (htag : ∀ p ∈ A.carrier, ∀ q ∈ A.carrier, p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1) :
    ∃ E : CentripetalData (G := G) A,
      E.coordinate = j ∧ E.coefficient = c ∧
      E.activeTags.carrier = ⋃ i, (D i).activeTags.carrier ∧
      (∀ i p, p ∈ A.carrier → p.2 ∈ (D i).activeTags.carrier → E.point p = (D i).point p) ∧
      (∀ p ∈ A.carrier, (∀ i, p.2 ∉ (D i).activeTags.carrier) → (E.point p).1 = p.1) := by
  let W : DefSet (rawRVSpace (M := M) r) S := ⟨⋃ i, (D i).activeTags.carrier,by
    apply (rv_definable_iff_values_image S _).mpr
    have hd (i) := (rv_definable_iff_values_image S _).mp (D i).activeTags.definable
    have he : rvValues '' (⋃ i, (D i).activeTags.carrier) = ⋃ i, rvValues '' (D i).activeTags.carrier :=
      Set.image_iUnion
    rw [he]
    exact Set.definable_iUnion_of_finite hd⟩
  let C (i : I) := focusActive A (D i).activeTags
  have hsub (i) : (C i).carrier ⊆ (focusActive A W).carrier :=
    fun p hp => ⟨hp.1,Set.mem_iUnion.mpr ⟨i,hp.2⟩⟩
  have hcover (p : focusActive A W) : ∃ i, p.val ∈ (C i).carrier := by
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp p.property.2
    exact ⟨i,p.property.1,hi⟩
  have hcompat (i k) (p : C i) (q : C k) (hpq : p.val = q.val) :
      ((D i).focusMap p).val = ((D k).focusMap q).val := by
    have hik : i = k := hsep i k p.val.2 p.property.2 ((congrArg Prod.snd hpq).symm ▸ q.property.2)
    subst k
    exact congrArg (fun a : C i => ((D i).focusMap a).val) (Subtype.ext hpq)
  obtain ⟨f,hf⟩ := exists_finite_glued_map (focusActive A W) (DefSet.univ (rawVFSpace 1) S) C
    (fun i => (D i).focusMap) hsub hcover hcompat
  have hF (u) (i) (hu : u ∈ (D i).activeTags.carrier) :
      (fun x : Fin n → VF M => gluedFocus D (Function.update x j 0) u) =
        (fun x => (D i).focus (Function.update x (D i).coordinate 0) u) := by
    funext x
    rw [gluedFocus_at D hsep i u hu,hj i]
  let E : CentripetalData (G := G) A := {
    coordinate := j
    activeTags := W
    focus := gluedFocus D
    focusMap := f
    focusMap_eq := fun p => by
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp p.property.2
      let q : C i := ⟨p.val,p.property.1,hi⟩
      have hpq : (⟨q.val,hsub i q.property⟩ : focusActive A W) = p := Subtype.ext rfl
      rw [← hpq]
      exact (congrFun (hf i q) 0).trans ((D i).focusMap_eq q |>.trans (by
        rw [gluedFocus_at D hsep i p.val.2 hi,hj i]))
    sourceProper := hA
    sourceDoublyBounded := hAD
    tagged := htag
    continuous := fun u hu => by
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hu
      rw [hF u i hi]
      exact (D i).continuous u hi
    focusRV := fun p hp hu => by
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hu
      rw [gluedFocus_at D hsep i p.2 hi,← hj i]
      exact (D i).focusRV p hp hi
    coefficient := c
    coefficient_nonzero := hc0
    coefficient_nonnegative := hcpos
    coefficient_definable := hcdef
    covariance := fun u hu => by
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hu
      obtain ⟨α,β,hα,hβ,hInv,hcov,hdom⟩ := (D i).covariance u hi
      refine ⟨α,β,hα,hβ,?_,?_,?_⟩
      · simpa only [hj i] using hInv
      · intro a ha b hb hab
        rw [gluedFocus_at D hsep i u hi,gluedFocus_at D hsep i u hi]
        have hh := hcov a ha b hb (by simpa only [hj i] using hab)
        simpa only [hj i] using hh
      · intro a ha
        rw [gluedFocus_at D hsep i u hi]
        simpa only [hj i,hc i] using hdom a ha }
  refine ⟨E,rfl,rfl,rfl,?_,?_⟩
  · intro i p hp hi
    have hEact : p.2 ∈ E.activeTags.carrier := Set.mem_iUnion.mpr ⟨i,hi⟩
    have hExt : E.extendedFocus p = (D i).extendedFocus p := by
      rw [E.extendedFocus_active hp hEact,(D i).extendedFocus_active hp hi]
      exact congrFun (hF p.2 i hi) p.1
    have hCore : E.core p = (D i).core p := by
      change decide _ = decide _
      rw [hExt,hc i,hj i]
    change E.point p = (D i).point p
    simp only [CentripetalData.point,hExt,hCore,hj i,hc i]
    rfl
  · intro p hp hi
    apply E.point_inactive
    change p.2 ∉ ⋃ i, (D i).activeTags.carrier
    intro h
    obtain ⟨i,hi'⟩ := Set.mem_iUnion.mp h
    exact hi i hi'

end DiamondIntegral.Section6
