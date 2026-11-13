import «section 4».RVDefinableGraphExtension
import «section 4».RESOrdinaryRing

/-! Adjoining a proper RV function of constant value preserves finite RES
value patterns, its degree and its measured/ordinary RES classes. This
allows a definable function on a coefficient object to be used as an
actual retained coordinate without changing that coefficient class. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVDefinableGraphRES
open RVMeasuredCharts RVRealProducts FiniteTupleBlocks FiniteTupleGraphProduct RVDefinableGraphExtension
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem codeValue_vrv (t : M) (ht : NonzeroRV t) :
    (codeValue t).val = Values.vrv ⟨t, ht.1⟩ := by
  rw [codeValue, dite_eq_left ht]
  rfl

theorem last_eq {B : Base (M := M)} {k : ℕ} (r : Chart B k) (f : (Fin r.arity → M) → M)
    (u : Fin (1 + r.arity) → M) (hu : u ∈ domain r f) :
    u (tailIndex 1 r.arity 0) = f (u ∘ headIndex 1 r.arity) := (congrFun hu.2 0).symm

theorem finite_patterns {B : Base (M := M)} {k : ℕ} (r : RESChart B k)
    (f : (Fin r.arity → M) → M)
    (hf : DefinableOverBase B (fun _ : Fin (1 + r.arity) => .rv) (domain r.toChart f))
    (hp : ∀ x ∈ r.domain, NonzeroRV (f x)) (δ : Values.Gamma (M := M))
    (hv : ∀ x ∈ r.domain, codeValue (f x) = δ) :
    (Set.range (chart r.toChart f hf).valuePattern).Finite := by
  have hfin := r.finite_values.image (fun p => join 1 r.arity p ![δ.val])
  apply hfin.subset
  rintro p ⟨u, rfl⟩
  let x : r.domain := ⟨u.val ∘ headIndex 1 r.arity, u.property.1⟩
  refine ⟨r.toChart.valuePattern x, ⟨x, rfl⟩, ?_⟩
  apply block_ext 1 r.arity
  · funext i
    change join 1 r.arity (r.toChart.valuePattern x) ![δ.val] (headIndex 1 r.arity i) =
      (chart r.toChart f hf).valuePattern u (headIndex 1 r.arity i)
    rw [join_head]
    rfl
  · funext i
    fin_cases i
    change join 1 r.arity (r.toChart.valuePattern x) ![δ.val] (tailIndex 1 r.arity 0) =
      (chart r.toChart f hf).valuePattern u (tailIndex 1 r.arity 0)
    rw [join_tail]
    change δ.val = Values.vrv ⟨u.val (tailIndex 1 r.arity 0), _⟩
    have he := last_eq r.toChart f u.val u.property
    have hp' : NonzeroRV (u.val (tailIndex 1 r.arity 0)) := he.symm ▸ hp x.val x.property
    have hv' : codeValue (u.val (tailIndex 1 r.arity 0)) = δ := by
      rw [he]
      exact hv x.val x.property
    exact (congrArg Subtype.val hv').symm.trans (codeValue_vrv _ hp')

def resChart {B : Base (M := M)} {k : ℕ} (r : RESChart B k) (f : (Fin r.arity → M) → M)
    (hf : DefinableOverBase B (fun _ : Fin (1 + r.arity) => .rv) (domain r.toChart f))
    (hp : ∀ x ∈ r.domain, NonzeroRV (f x)) (δ : Values.Gamma (M := M))
    (hv : ∀ x ∈ r.domain, codeValue (f x) = δ) : RESChart B k :=
  ⟨chart r.toChart f hf, finite_patterns r f hf hp δ hv⟩

theorem measured_class {B : Base (M := M)} {k : ℕ} (r : RESChart B k) (f : (Fin r.arity → M) → M)
    (hf : DefinableOverBase B (fun _ : Fin (1 + r.arity) => .rv) (domain r.toChart f))
    (hp : ∀ x ∈ r.domain, NonzeroRV (f x)) (δ : Values.Gamma (M := M))
    (hv : ∀ x ∈ r.domain, codeValue (f x) = δ) :
    RESChartRing.objectClass (resChart r f hf hp δ hv) = RESChartRing.objectClass r :=
  RESChartRing.objectClass_iso (a := resChart r f hf hp δ hv) (b := r) (iso r.toChart f hf)

theorem ordinary_class {B : Base (M := M)} {k : ℕ} (r : RESChart B k) (f : (Fin r.arity → M) → M)
    (hf : DefinableOverBase B (fun _ : Fin (1 + r.arity) => .rv) (domain r.toChart f))
    (hp : ∀ x ∈ r.domain, NonzeroRV (f x)) (δ : Values.Gamma (M := M))
    (hv : ∀ x ∈ r.domain, codeValue (f x) = δ) :
    RESOrdinaryRing.objectClass (resChart r f hf hp δ hv) = RESOrdinaryRing.objectClass r :=
  RESOrdinaryRing.objectClass_iso (a := resChart r f hf hp δ hv) (b := r)
    (RVForgetScissors.ofMeasured (iso r.toChart f hf))

end DiamondIntegral.Section4.RVDefinableGraphRES
