import «section 6».DefinableSurjectiveDescent

/-! The actual original-base RV map induced by a bijection taking whole
old-tag fibers to whole old-tag fibers. The map, its complete graph,
commutative square and bijectivity are constructed. Disc preparation is
an explicit hypothesis and is not inferred from this quotient adapter. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n m r s : ℕ} {S : Set M}

def rvTagQuotient (A : DefSet (rawMixedSpace (M := M) n r) S) := (rvTagProjection A).image

def rvTagQuotientMap (A : DefSet (rawMixedSpace (M := M) n r) S) : Map A (rvTagQuotient A) :=
  (rvTagProjection A).toImage

theorem rvTagQuotientMap_surjective (A : DefSet (rawMixedSpace (M := M) n r) S) :
    Function.Surjective (rvTagQuotientMap A) := by
  rintro ⟨_,p,rfl⟩
  exact ⟨p,rfl⟩

theorem rvTagQuotientMap_eq_iff (A : DefSet (rawMixedSpace (M := M) n r) S) (p q : A) :
    rvTagQuotientMap A p = rvTagQuotientMap A q ↔ p.val.2 = q.val.2 := by
  constructor
  · intro h
    exact congrArg (fun z : rvTagQuotient A => z.val.2) h
  · intro h
    apply Subtype.ext
    exact Prod.ext rfl h

theorem rvTagQuotient_mem_iff (A : DefSet (rawMixedSpace (M := M) n r) S)
    (u : Fin r → RVInfinity M) :
    (Fin.elim0,u) ∈ (rvTagQuotient A).carrier ↔ ∃ p : A, p.val.2 = u := by
  constructor
  · rintro ⟨p,hp⟩
    exact ⟨p,congrArg Prod.snd hp⟩
  · rintro ⟨p,hp⟩
    exact ⟨p,Prod.ext rfl hp⟩

theorem rvTagQuotient_rvBounded (A : DefSet (rawMixedSpace (M := M) n r) S)
    (hA : RVSupportDoublyBounded A.carrier) : RVSupportDoublyBounded (rvTagQuotient A).carrier := by
  obtain ⟨δ,hδ⟩ := hA
  refine ⟨δ,?_⟩
  rintro _ ⟨p,rfl⟩ i
  exact hδ p.val p.property i

variable {A : DefSet (rawMixedSpace (M := M) n r) S}
variable {B : DefSet (rawMixedSpace (M := M) m s) S}

def MapsWholeTagFibres (f : Map A B) : Prop :=
  ∀ p : A, ∀ b : B, b.val.2 = (f p).val.2 ↔ ∃ a : A, a.val.2 = p.val.2 ∧ f a = b

theorem MapsWholeTagFibres.labels (f : Map A B) (h : MapsWholeTagFibres f)
    (p q : A) (hpq : p.val.2 = q.val.2) : (f p).val.2 = (f q).val.2 :=
  (h q (f p)).mpr ⟨p,hpq,rfl⟩

def rvTagMatchingMap (f : Map A B) (h : MapsWholeTagFibres f) :
    Map (rvTagQuotient A) (rvTagQuotient B) :=
  definableSurjectiveDescent (rvTagQuotientMap A) (rvTagQuotientMap_surjective A)
    ((rvTagQuotientMap B).comp f) (fun p q hpq =>
      (rvTagQuotientMap_eq_iff B (f p) (f q)).mpr
        (h.labels f p q ((rvTagQuotientMap_eq_iff A p q).mp hpq)))

theorem rvTagMatchingMap_commutes (f : Map A B) (h : MapsWholeTagFibres f) (p : A) :
    rvTagMatchingMap f h (rvTagQuotientMap A p) = rvTagQuotientMap B (f p) :=
  definableSurjectiveDescent_apply _ _ _ _ p

theorem rvTagMatchingMap_bijective (f : Map A B) (hf : Function.Bijective f) (h : MapsWholeTagFibres f) :
    Function.Bijective (rvTagMatchingMap f h) := by
  constructor
  · apply definableSurjectiveDescent_injective
    intro p q he
    have hLabel : (f q).val.2 = (f p).val.2 :=
      ((rvTagQuotientMap_eq_iff B (f p) (f q)).mp he).symm
    obtain ⟨a,ha,hfa⟩ := (h p (f q)).mp hLabel
    have haq : a = q := hf.injective hfa
    apply (rvTagQuotientMap_eq_iff A p q).mpr
    exact ha.symm.trans (congrArg (fun z : A => z.val.2) haq)
  · exact definableSurjectiveDescent_surjective _ _ _ _
      ((rvTagQuotientMap_surjective B).comp hf.surjective)

end DiamondIntegral.Section6
