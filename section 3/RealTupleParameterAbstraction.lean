import «section 3».GammaGroundRawDescent
import Section4.MapProduct
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.DefinableGeometry
noncomputable section
namespace DiamondIntegral.Section3
variable {L : Language} {M : Type} [L.Structure M]
variable {α β : Type} {S : Set M}

/-- Replace a named finite real tuple by free variables in an actual
first-order formula, retaining every original real parameter. -/
theorem rawDefinable_realTuple_abstraction (r : β → M) {A : Set (α → M)}
    (hA : (S ∪ Set.range r).Definable L A) :
    ∃ R : Set (β ⊕ α → M), S.Definable L R ∧
      ∀ x : α → M, Sum.elim r x ∈ R ↔ x ∈ A := by
  obtain ⟨φ,hφ⟩ := Set.definable_iff_exists_formula_sum.mp hA
  let pick (p : ↥(S ∪ Set.range r)) (hp : p.val ∉ S) : β :=
    Classical.choose (p.property.resolve_left hp)
  have hpick (p : ↥(S ∪ Set.range r)) (hp : p.val ∉ S) : r (pick p hp) = p.val :=
    Classical.choose_spec (p.property.resolve_left hp)
  let f : ↥(S ∪ Set.range r) ⊕ α → S ⊕ (β ⊕ α) :=
    Sum.elim (fun p => if hp : p.val ∈ S then Sum.inl ⟨p.val,hp⟩
      else Sum.inr (Sum.inl (pick p hp))) (fun a => Sum.inr (Sum.inr a))
  let R : Set (β ⊕ α → M) := {z | (φ.relabel f).Realize (Sum.elim Subtype.val z)}
  refine ⟨R,Set.definable_iff_exists_formula_sum.mpr ⟨φ.relabel f,rfl⟩,?_⟩
  intro x
  have he : (Sum.elim Subtype.val (Sum.elim r x)) ∘ f = Sum.elim Subtype.val x := by
    funext i
    cases i with
    | inl p =>
      by_cases hp : p.val ∈ S
      · simp only [f,Function.comp_apply,Sum.elim_inl,dite_eq_left hp]
      · simp only [f,Function.comp_apply,Sum.elim_inl,dite_eq_right hp,Sum.elim_inr]
        exact hpick p hp
    | inr a => rfl
  change (φ.relabel f).Realize (Sum.elim Subtype.val (Sum.elim r x)) ↔ _
  rw [Formula.realize_relabel,he]
  exact (Set.ext_iff.mp hφ x).symm

/-- Real-parameter abstraction on an interpreted presentation is obtained
by retaining all its code representatives and taking their definable image. -/
theorem presentedDefinable_realTuple_abstraction [Finite β] (Q : Space L M)
    (r : β → M) {A : Set Q.Carrier} (hA : Q.Definable (S ∪ Set.range r) A) :
    ∃ R : Set ((rawTupleSpace L M β).prod Q).Carrier,
      ((rawTupleSpace L M β).prod Q).Definable S R ∧
      ∀ x : Q.Carrier, (r,x) ∈ R ↔ x ∈ A := by
  obtain ⟨H,hH,hHx⟩ := rawDefinable_realTuple_abstraction r hA
  let P := rawTupleSpace L M β
  let D : DefSet (P.prod (realCodeSpace Q)) S := {
    carrier := {z | Sum.elim z.1 z.2.val ∈ H}
    definable := by
      have hd := ((P.prod (realCodeSpace Q)).definable_domain S).inter hH
      change S.Definable L ((P.prod (realCodeSpace Q)).preimage {z | Sum.elim z.1 z.2.val ∈ H})
      convert hd using 1
      ext z
      change (∃ hz : z ∈ (P.prod (realCodeSpace Q)).domain,
        Sum.elim (z ∘ Sum.inl) (z ∘ Sum.inr) ∈ H) ↔
          (z ∈ (P.prod (realCodeSpace Q)).domain ∧ z ∈ H)
      rw [Sum.elim_comp_inl_inr]
      exact exists_prop }
  let F := (Map.prodMap (Map.id (DefSet.univ P S)) (realCodeDecodeMap Q S)).restrict
    (show D.carrier ⊆ ((DefSet.univ P S).prod (DefSet.univ (realCodeSpace Q) S)).carrier from
      fun _ _ => ⟨Set.mem_univ _,Set.mem_univ _⟩)
  refine ⟨F.image.carrier,F.image.definable,?_⟩
  intro x
  constructor
  · rintro ⟨a,ha⟩
    have hr : a.val.1 = r := congrArg Prod.fst ha
    have hx : Q.decode a.val.2 = x := congrArg Prod.snd ha
    have hh : Sum.elim r a.val.2.val ∈ H := hr ▸ a.property
    exact hx ▸ (Q.preimage_decode A a.val.2).mp ((hHx a.val.2.val).mp hh)
  · intro hx
    obtain ⟨c,hc⟩ := Q.onto x
    have hh : Sum.elim r c.val ∈ H :=
      (hHx c.val).mpr ((Q.preimage_decode A c).mpr (hc.symm ▸ hx))
    exact ⟨⟨(r,c),hh⟩,Prod.ext rfl hc⟩

/-- Abstract real names while retaining a separately named imaginary tuple. -/
theorem imaginaryDefinable_realTuple_abstraction [Finite β]
    (P Q : Space L M) (p : P.Carrier) (r : β → M) {A : Set Q.Carrier}
    (hA : ImaginaryDefinable P p Q (S ∪ Set.range r) A) :
    ∃ R : Set ((rawTupleSpace L M β).prod Q).Carrier,
      ImaginaryDefinable P p ((rawTupleSpace L M β).prod Q) S R ∧
      ∀ x : Q.Carrier, (r,x) ∈ R ↔ x ∈ A := by
  obtain ⟨T,hT,hTx⟩ := hA
  obtain ⟨D,hD,hDx⟩ := presentedDefinable_realTuple_abstraction (P.prod Q) r hT
  let U := rawTupleSpace L M β
  let F : Map (DefSet.univ (P.prod (U.prod Q)) S)
      (DefSet.univ (U.prod (P.prod Q)) S) :=
    Map.ofCodes _ (fun z => (z.2.1,(z.1,z.2.2)))
      (fun z => Sum.elim (fun i => z (.inr (.inl i)))
        (Sum.elim (fun i => z (.inl i)) (fun i => z (.inr (.inr i)))))
      (fun i => by cases i with
        | inl i => exact Set.DefinableFun.proj L
        | inr i => cases i <;> exact Set.DefinableFun.proj L)
      (fun c => ⟨c.property.2.1,c.property.1,c.property.2.2⟩)
      (fun _ => rfl)
  let E : Set (P.prod (U.prod Q)).Carrier := {z | (F ⟨z,Set.mem_univ _⟩).val ∈ D}
  have hE : (P.prod (U.prod Q)).Definable S E := by
    have hh := F.definable_preimage hD
    have he : E = {z | ∃ a : DefSet.univ (P.prod (U.prod Q)) S,
        a.val = z ∧ (F a).val ∈ D} := by
      ext z
      constructor
      · intro hz
        exact ⟨⟨z,Set.mem_univ _⟩,rfl,hz⟩
      · rintro ⟨a,rfl,ha⟩
        exact ha
    rw [he]
    exact hh
  let R : Set (U.prod Q).Carrier := {z | (p,z) ∈ E}
  refine ⟨R,⟨E,hE,fun _ => Iff.rfl⟩,?_⟩
  intro x
  exact (hDx (p,x)).trans (hTx x).symm

end DiamondIntegral.Section3

open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)}
variable {B : GammaParameters.Base (M := M)} {β : Type} [Finite β]

/-- A finite real tuple can be made variable over the original mixed
real/Gamma base. No code of an old Gamma parameter is adjoined. -/
theorem gammaGroundDefinable_realTuple_abstraction (Q : Space LRV M)
    (r : β → M) {A : Set Q.Carrier}
    (hA : GammaGroundDefinable hc ⟨B.real ∪ Set.range r,B.gamma⟩ Q A) :
    ∃ R : Set ((rawTupleSpace LRV M β).prod Q).Carrier,
      GammaGroundDefinable hc B ((rawTupleSpace LRV M β).prod Q) R ∧
      ∀ x : Q.Carrier, (r,x) ∈ R ↔ x ∈ A := by
  obtain ⟨k,γ,hγ,hA⟩ := hA
  obtain ⟨R,hR,hRx⟩ := imaginaryDefinable_realTuple_abstraction
    ((volumeGammaSpace hc).power (Fin k)) Q γ r hA
  exact ⟨R,⟨k,γ,hγ,hR⟩,hRx⟩
end DiamondIntegral.Section3
