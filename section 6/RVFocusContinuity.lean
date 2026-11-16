import «section 6».UniformRVFibrewiseContinuity
import «section 6».ScalarCodeExtension
import «section 6».InvarianceTopology

/-! Uniform continuity exceptions for actual partial focus maps. Zero
extension is definable over the original base; clopen current domains
make its tail fibers continuous, without an extension hypothesis. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open Classical FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}
variable {C : DefSet (rawMixedSpace (M := M) n r) S}
variable {B : DefSet (rawVFSpace (M := M) 1) S}

def totalFocusFibre (f : Map C B) (u : Fin r → RVInfinity M)
    (x : Fin n → VF M) : Fin 1 → VF M :=
  fun _ => ⟨scalarCodeExtension f (mixedValues (x,u)),scalarCodeExtension_isVF f _⟩

theorem totalFocusFibre_at (f : Map C B) (u : Fin r → RVInfinity M)
    (x : Fin n → VF M) (hx : (x,u) ∈ C.carrier) :
    totalFocusFibre f u x = (f ⟨(x,u),hx⟩).val := by
  funext i
  fin_cases i
  exact Subtype.ext (scalarCodeExtension_at f ⟨(x,u),hx⟩)

theorem totalFocusFibre_off (f : Map C B) (u : Fin r → RVInfinity M)
    (x : Fin n → VF M) (hx : (x,u) ∉ C.carrier) : totalFocusFibre f u x = 0 := by
  have hno : mixedValues (x,u) ∉ (rawMixedSpace n r).preimage C.carrier := by
    rintro ⟨hz,hzC⟩
    apply hx
    simpa only [decode_mixedValues] using hzC
  funext i
  apply Subtype.ext
  change scalarCodeExtension f (mixedValues (x,u)) = iVFZero
  rw [scalarCodeExtension,dite_eq_right hno]

def totalFocusFamilyCode (f : Map C B) (z : Fin r ⊕ Fin n → M) : M :=
  scalarCodeExtension f (z ∘ Sum.swap)

theorem totalFocusFamilyCode_definable (f : Map C B) :
    S.DefinableFun LRV (totalFocusFamilyCode f) := by
  change S.DefinableFun LRV (fun z : Fin r ⊕ Fin n → M => scalarCodeExtension f (z ∘ Sum.swap))
  exact (scalarCodeExtension_definable f).comp
    (show S.DefinableMap LRV (fun z : Fin r ⊕ Fin n → M => z ∘ Sum.swap) from
      fun _ => Set.DefinableFun.proj LRV)

theorem totalFocusFamilyCode_at (f : Map C B) (u : Fin r → RVInfinity M)
    (x : Fin n → VF M) :
    totalFocusFamilyCode f (Sum.elim (rvValues u) (vfValues x)) = (totalFocusFibre f u x 0).val := rfl

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem continuous_of_clopen_zero_complement
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [Zero Y]
    (D : Set X) (hD : IsClopen D) (g : X → Y) (hg : ContinuousOn g D)
    (hz : ∀ x ∉ D, g x = 0) : Continuous g := by
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x ∈ D
  · exact hg.continuousAt (hD.isOpen.mem_nhds hx)
  · apply (continuousAt_const : ContinuousAt (fun _ : X => (0 : Y)) x).congr
    filter_upwards [hD.isClosed.isOpen_compl.mem_nhds hx] with y hy
    exact (hz y hy).symm

def focusTailDomain (C : DefSet (rawMixedSpace (M := M) (n+1) r) S)
    (u : Fin r → RVInfinity M) (a : VF M) : Set (Fin n → VF M) :=
  {b | (Fin.cons a b,u) ∈ C.carrier}

def focusTailMap {C : DefSet (rawMixedSpace (M := M) (n+1) r) S}
    (f : Map C B) (u : Fin r → RVInfinity M) (a : VF M)
    (b : focusTailDomain C u a) : Fin 1 → VF M :=
  (f ⟨(Fin.cons a b.val,u),b.property⟩).val

theorem totalFocusFibre_tail_continuous
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {C : DefSet (rawMixedSpace (M := M) (n+1) r) S}
    (hC : ∀ u, IsClopen (vfFibre C.carrier u)) (f : Map C B)
    (u : Fin r → RVInfinity M) (a : VF M) (hf : Continuous (focusTailMap f u a)) :
    Continuous (fun b : Fin n → VF M => totalFocusFibre f u (Fin.cons a b)) := by
  have hcons : Continuous (fun b : Fin n → VF M => (Fin.cons a b : Fin (n+1) → VF M)) := by
    apply continuous_pi
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact continuous_const
    · exact continuous_apply j
  have hD : IsClopen (focusTailDomain C u a) := (hC u).preimage hcons
  apply continuous_of_clopen_zero_complement (focusTailDomain C u a) hD
  · apply continuousOn_iff_continuous_restrict.mpr
    convert hf using 1
    funext b
    exact totalFocusFibre_at f u (Fin.cons a b.val) b.property
  · intro b hb
    exact totalFocusFibre_off f u (Fin.cons a b) hb

theorem exists_uniform_focus_continuity_exception
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {C : DefSet (rawMixedSpace (M := M) (n+1) r) S}
    (hC : ∀ u, IsClopen (vfFibre C.carrier u)) (f : Map C B)
    (hf : ∀ u a, Continuous (focusTailMap f u a)) :
    ∃ E : Set (Fin 1 → VF M), E.Finite ∧ S.Definable LRV (vfValues '' E) ∧
      ∀ u, ContinuousOn (totalFocusFibre f u) {x | (fun _ : Fin 1 => x 0) ∉ E} :=
  exists_uniform_rv_fibrewise_continuity_exception h00 hc hκ hs hsmall hv
    (totalFocusFamilyCode f) (totalFocusFamilyCode_definable f) (totalFocusFibre f)
    (totalFocusFamilyCode_at f)
    (fun u a => totalFocusFibre_tail_continuous hv hC f u a (hf u a))

end DiamondIntegral.Section6
