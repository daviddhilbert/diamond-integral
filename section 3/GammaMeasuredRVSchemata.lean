import «section 3».GammaVolumeCodeEquivalence
import IntegrationSection6.GammaFiniteObjectSchemata

/-! Finite-volume RV families with genuine Gamma densities. Their density
rows are complete equivalence classes of RV representatives, so validity
and every comparison predicate remain first-order over the original base. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open IntegrationInACVF.Section6
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

structure GammaMeasuredRVSchema (hc : CanonicalStructure.IsCanonical (M := M))
    (B : Base (M := M)) (p a k : ℕ) (sp : Fin p → SortTag := fun _ => .rv) where
  object : GammaFiniteRVSchema B p a k sp
  density : Set (Fin ((p+a)+1) → M)
  density_definable : DefinableOverBase B (Fin.append (Fin.append sp (fun _ : Fin a => .rv)) (fun _ : Fin 1 => .rv)) density
  density_code : ∀ w ∈ density, w ∘ Fin.natAdd (p+a) ∈ (volumeGammaSpace hc).domain

variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {p a k : ℕ} {sp : Fin p → SortTag}

def GammaMeasuredRVSchema.valid (F : GammaMeasuredRVSchema hc B p a k sp) (z : Fin p → M) : Prop :=
  F.object.valid z ∧ gammaQuotientFunctionRowValid sp (fun _ : Fin a => .rv) (fun _ : Fin 1 => .rv)
    F.object.domain F.density (gammaVolumeCodeEq (hc := hc)) z

theorem GammaMeasuredRVSchema.valid_definable (F : GammaMeasuredRVSchema hc B p a k sp) :
    DefinableOverBase B sp {z | F.valid z} :=
  F.object.valid_definable.inter (gamma_quotient_function_row_validity_definable sp
    (fun _ : Fin a => .rv) (fun _ : Fin 1 => .rv) F.object.domain_definable F.density_definable gammaVolumeCodeEq_definable)

def GammaMeasuredRVSchema.rowDensity (F : GammaMeasuredRVSchema hc B p a k sp) (z : Fin p → M)
    (x : Fin a → CanonicalRV.RVSort M) (c : (volumeGammaSpace hc).domain) : Prop :=
  Fin.append (Fin.append z (rvValues x)) c.val ∈ F.density

theorem GammaMeasuredRVSchema.rowDensity_exists (F : GammaMeasuredRVSchema hc B p a k sp)
    (z : Fin p → M) (hz : F.valid z) (x : F.object.rowDomain z) :
    ∃ c : (volumeGammaSpace hc).domain, F.rowDensity z x.val c := by
  obtain ⟨y,hy⟩ := hz.2.2.1 (rvValues x.val) x.property
  have hCode : y ∈ (volumeGammaSpace hc).domain := by
    simpa only [Function.comp_def,Fin.append_right] using F.density_code _ hy
  exact ⟨⟨y,hCode⟩,hy⟩

theorem GammaMeasuredRVSchema.rowDensity_same_value (F : GammaMeasuredRVSchema hc B p a k sp)
    (z : Fin p → M) (hz : F.valid z) (x : F.object.rowDomain z)
    (c : (volumeGammaSpace hc).domain) (hDensity : F.rowDensity z x.val c)
    (d : (volumeGammaSpace hc).domain) :
    F.rowDensity z x.val d ↔ (volumeGammaSpace hc).decode c = (volumeGammaSpace hc).decode d := by
  have hQ := hz.2.2.2.2 (rvValues x.val) (fun j => (x.val j).property)
  have hd : ∀ j, sortEval (SortTag.rv) (d.val j) := by
    intro j
    change Fin 1 at j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact d.property.1
  exact (hQ.2 c.val hDensity d.val hd).trans (gammaVolumeCodeEq_append c d)

theorem GammaMeasuredRVSchema.rowDensity_value_unique (F : GammaMeasuredRVSchema hc B p a k sp)
    (z : Fin p → M) (hz : F.valid z) (x : F.object.rowDomain z) :
    ∃! γ : (volumeGammaSpace hc).Carrier,
      ∃ c : (volumeGammaSpace hc).domain, F.rowDensity z x.val c ∧ (volumeGammaSpace hc).decode c = γ := by
  obtain ⟨c,hDensity⟩ := F.rowDensity_exists z hz x
  refine ⟨(volumeGammaSpace hc).decode c,⟨c,hDensity,rfl⟩,?_⟩
  rintro γ ⟨d,hd,hγ⟩
  exact hγ.symm.trans ((F.rowDensity_same_value z hz x c hDensity d).mp hd).symm

def GammaMeasuredRVSchema.rowGammaValue (F : GammaMeasuredRVSchema hc B p a k sp)
    (z : Fin p → M) (hz : F.valid z) (x : F.object.rowDomain z) : (volumeGammaSpace hc).Carrier :=
  (F.rowDensity_value_unique z hz x).choose

theorem GammaMeasuredRVSchema.rowGammaValue_graph (F : GammaMeasuredRVSchema hc B p a k sp)
    (z : Fin p → M) (hz : F.valid z) (x : F.object.rowDomain z) (d : (volumeGammaSpace hc).domain) :
    F.rowDensity z x.val d ↔ (volumeGammaSpace hc).decode d = F.rowGammaValue z hz x := by
  constructor
  · intro hd
    exact (F.rowDensity_value_unique z hz x).choose_spec.2 _ ⟨d,hd,rfl⟩
  · intro hd
    obtain ⟨c,hDensity,hγ⟩ := (F.rowDensity_value_unique z hz x).choose_spec.1
    exact (F.rowDensity_same_value z hz x c hDensity d).mpr (hγ.trans hd.symm)

theorem GammaMeasuredRVSchema.rowDensity_support (F : GammaMeasuredRVSchema hc B p a k sp)
    (z : Fin p → M) (hz : F.valid z) (x : Fin a → CanonicalRV.RVSort M)
    (d : (volumeGammaSpace hc).domain) (hd : F.rowDensity z x d) : x ∈ F.object.rowDomain z :=
  hz.2.2.2.1 (rvValues x) d.val hd

end DiamondIntegral.Section3
