import «section 5».NativeMixedMapGraphs
import «section 5».NativeMixedSortedRealization

/-! Actual fibres of arbitrary native mixed maps have full original-base
row formulas and native presentations over exactly the displayed raw
parameter tuple, with no enlargement of the Gamma ground. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
open DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n r p q : ℕ}

def nativeMixedBlockSwap (a b : ℕ) : Fin (b+a) → Fin (a+b) :=
  Fin.addCases (Fin.natAdd a) (Fin.castAdd b)

theorem nativeMixedBlockSwap_append {α : Type*} {a b : ℕ} (x : Fin a → α) (y : Fin b → α) :
    Fin.append x y ∘ nativeMixedBlockSwap a b = Fin.append y x := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp only [nativeMixedBlockSwap,Function.comp_apply,Fin.addCases_left,Fin.addCases_right,
      Fin.append_left,Fin.append_right]

def nativeMixedMapFibreFormula
    {A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)}
    {C : GammaGroundDefSet hc B (rawMixedSpace (M := M) p q)} (f : GammaGroundMap A C) :
    {D : Set (Fin ((p+q)+(n+r)) → M) // DefinableOverBase B
      (Fin.append (Fin.append (fun _ : Fin p => .vf) (fun _ : Fin q => .rv))
        (Fin.append (fun _ : Fin n => .vf) (fun _ : Fin r => .rv))) D} :=
  ⟨{w | ∃ a : A,w = Fin.append (nativeMixedCode (f a).val) (nativeMixedCode a.val)},by
    have h := (nativeMixedMapGraph_definable f).image_real (nativeMixedBlockSwap (n+r) (p+q))
    rw [nativeMixedBlockSwap_append] at h
    convert h using 1
    ext w
    constructor
    · rintro ⟨a,rfl⟩
      exact ⟨Fin.append (nativeMixedCode a.val) (nativeMixedCode (f a).val),⟨a,rfl⟩,
        nativeMixedBlockSwap_append _ _⟩
    · rintro ⟨_,⟨a,rfl⟩,hw⟩
      exact ⟨a,hw.symm.trans (nativeMixedBlockSwap_append _ _)⟩⟩

theorem nativeMixedMapFibreFormula_row
    {A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)}
    {C : GammaGroundDefSet hc B (rawMixedSpace (M := M) p q)} (f : GammaGroundMap A C)
    (z : Fin (p+q) → M) (x : Fin (n+r) → M) :
    Fin.append z x ∈ (nativeMixedMapFibreFormula f).val ↔
      ∃ a : A,nativeMixedCode (f a).val = z ∧ nativeMixedCode a.val = x := by
  constructor
  · rintro ⟨a,ha⟩
    refine ⟨a,funext (fun i => ?_),funext (fun i => ?_)⟩
    · have hi := congrFun ha (Fin.castAdd (n+r) i)
      simpa only [Fin.append_left] using hi.symm
    · have hi := congrFun ha (Fin.natAdd (p+q) i)
      simpa only [Fin.append_right] using hi.symm
  · rintro ⟨a,hz,hx⟩
    exact ⟨a,(congrArg₂ Fin.append hz hx).symm⟩

def nativeMixedMapFibreAt
    {A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)}
    {C : GammaGroundDefSet hc B (rawMixedSpace (M := M) p q)} (f : GammaGroundMap A C)
    (z : Fin (p+q) → M) :
    GammaGroundDefSet hc ⟨B.real ∪ Set.range z,B.gamma⟩ (rawMixedSpace (M := M) n r) :=
  nativeMixedOfRaw {x | Fin.append z x ∈ (nativeMixedMapFibreFormula f).val}
    (gamma_tuple_parameter_specialize _ _ z (nativeMixedMapFibreFormula f).property)

theorem nativeMixedMapFibreAt_domain
    {A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)}
    {C : GammaGroundDefSet hc B (rawMixedSpace (M := M) p q)} (f : GammaGroundMap A C)
    (z : Fin (p+q) → M) : nativeMixedDomain (nativeMixedMapFibreAt f z) =
      {x | Fin.append z x ∈ (nativeMixedMapFibreFormula f).val} := nativeMixedDomain_ofRaw _ _

theorem nativeMixedMapFibreAt_mem
    {A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)}
    {C : GammaGroundDefSet hc B (rawMixedSpace (M := M) p q)} (f : GammaGroundMap A C)
    (z : Fin (p+q) → M) (x : Section2.Mixed M n r) :
    x ∈ (nativeMixedMapFibreAt f z).carrier ↔ ∃ a : A,a.val = x ∧ nativeMixedCode (f a).val = z := by
  change Fin.append z (nativeMixedCode x) ∈ (nativeMixedMapFibreFormula f).val ↔ _
  rw [nativeMixedMapFibreFormula_row]
  exact ⟨fun ⟨a,hz,hx⟩ => ⟨a,nativeMixedCode_injective hx,hz⟩,
    fun ⟨a,hx,hz⟩ => ⟨a,hz,congrArg nativeMixedCode hx⟩⟩

theorem nativeMixedMapFibreAt_finite
    {A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)}
    {C : GammaGroundDefSet hc B (rawMixedSpace (M := M) p q)} (f : GammaGroundMap A C)
    (hf : ∀ x : Fin n → Section2.VF M,{t | (x,t) ∈ A.carrier}.Finite) (z : Fin (p+q) → M) :
    ∀ x : Fin n → Section2.VF M,{t | (x,t) ∈ (nativeMixedMapFibreAt f z).carrier}.Finite := by
  intro x
  apply (hf x).subset
  intro t ht
  obtain ⟨a,ha,_⟩ := (nativeMixedMapFibreAt_mem f z (x,t)).mp ht
  change (x,t) ∈ A.carrier
  exact ha ▸ a.property

end DiamondIntegral.Section5
