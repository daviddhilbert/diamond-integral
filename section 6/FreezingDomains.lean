import «section 6».InitialPreparation

/-! The domain and continuity obligations of FMT. The product condition
is checked for the actual current domain before evaluating its function
at a frozen center. Uniform invariance supplies that condition on a disc. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open DiamondIntegral.Section2

namespace DiamondIntegral.Section6.FMT

variable {X Y Z : Type*}

def ProductDomain (A : Set (X × Y)) (D : Set X) (c : X) : Prop :=
  ∀ x ∈ D, ∀ y, (x,y) ∈ A ↔ (c,y) ∈ A

def freezePoint (D : Set X) (c : X) (p : X × Y) : X × Y := by
  classical
  exact if p.1 ∈ D then (c,p.2) else p

theorem freezePoint_mapsTo {A : Set (X × Y)} {D : Set X} {c : X}
    (hD : ProductDomain A D c) : Set.MapsTo (freezePoint D c) A A := by
  classical
  intro p hp
  by_cases hd : p.1 ∈ D
  · simpa only [freezePoint,hd,ite_true] using (hD p.1 hd p.2).mp hp
  · simpa only [freezePoint,hd,ite_false] using hp

def freezeFunction {A : Set (X × Y)} {D : Set X} {c : X}
    (hD : ProductDomain A D c) (f : A → Z) (p : A) : Z :=
  f ⟨freezePoint D c p.val,freezePoint_mapsTo hD p.property⟩

theorem freezeFunction_inside {A : Set (X × Y)} {D : Set X} {c : X}
    (hD : ProductDomain A D c) (f : A → Z) (p : A) (hp : p.val.1 ∈ D) :
    freezeFunction hD f p = f ⟨(c,p.val.2),(hD p.val.1 hp p.val.2).mp p.property⟩ := by
  simp only [freezeFunction,freezePoint,hp,ite_true]

theorem freezeFunction_outside {A : Set (X × Y)} {D : Set X} {c : X}
    (hD : ProductDomain A D c) (f : A → Z) (p : A) (hp : p.val.1 ∉ D) : freezeFunction hD f p = f p := by
  simp only [freezeFunction,freezePoint,hp,ite_false,Subtype.coe_eta]

theorem productDomain_iff_set_equality (A : Set (X × Y)) (D : Set X) (c : X) :
    ProductDomain A D c ↔ A ∩ (D ×ˢ Set.univ) = D ×ˢ {y | (c,y) ∈ A} := by
  constructor
  · intro h
    ext p
    exact ⟨fun hp => ⟨hp.2.1,(h p.1 hp.2.1 p.2).mp hp.1⟩,
      fun hp => ⟨(h p.1 hp.1 p.2).mpr hp.2,hp.1,Set.mem_univ _⟩⟩
  · intro h x hx y
    have he := Set.ext_iff.mp h (x,y)
    simpa only [Set.mem_inter_iff,Set.mem_prod,Set.mem_univ,true_and,and_true,Set.mem_setOf_eq,hx] using he

variable [TopologicalSpace X] [TopologicalSpace Y]

theorem freezePoint_continuous {D : Set X} (hD : IsClopen D) (c : X) : Continuous (freezePoint D c : X × Y → X × Y) := by
  classical
  have hE : IsClopen (Prod.fst ⁻¹' D : Set (X × Y)) := hD.preimage continuous_fst
  have hG : Continuous (fun p : X × Y => (c,p.2)) := continuous_const.prodMk continuous_snd
  apply hG.if _ continuous_id
  intro p hp
  change p ∈ frontier (Prod.fst ⁻¹' D) at hp
  rw [hE.frontier_eq] at hp
  exact False.elim hp

variable [TopologicalSpace Z]

theorem freezeFunction_continuous {A : Set (X × Y)} {D : Set X} {c : X}
    (hD : ProductDomain A D c) (hcl : IsClopen D) (f : A → Z) (hf : Continuous f) :
    Continuous (freezeFunction hD f) :=
  hf.comp (((freezePoint_continuous hcl c).comp continuous_subtype_val).subtype_mk
    (fun p : A => freezePoint_mapsTo hD p.property))

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def ScalarDisc (a : VF M) (δ : Gamma M) : Set (VF M) := {x | δ.val < vfValue (x-a)}

omit [TopologicalSpace X] in
theorem productDomain_of_invariant {A : Set (VF M × X)} (a c : VF M) (δ : Gamma M)
    (hc : c ∈ ScalarDisc a δ)
    (hA : ∀ x y : VF M, ∀ z : X, δ.val < vfValue (x-y) → ((x,z) ∈ A ↔ (y,z) ∈ A)) :
    ProductDomain A (ScalarDisc a δ) c := by
  intro x hx z
  apply hA x c z
  have h := vfValue_min_le_sub (x-a) (c-a)
  rw [show (x-a)-(c-a) = x-c by abel] at h
  exact (lt_min hx hc).trans_le h

end DiamondIntegral.Section6.FMT
