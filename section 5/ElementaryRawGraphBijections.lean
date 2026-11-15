import «section 5».ElementaryRawGraphMaps

/-! Actual definable bijections and their inverse graphs restrict to
actual bijections over the unchanged named parameters. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
variable {L : Language} {M N P : Type} [L.Structure M] [L.Structure N]
variable {c : P → M} {n m : ℕ}

def rawTupleSwap (n m : ℕ) : Fin (n+m) → Fin (m+n) :=
  Fin.addCases (Fin.natAdd m) (Fin.castAdd n)

theorem rawTupleSwap_append {Q : Type} (x : Fin n → Q) (y : Fin m → Q) :
    Fin.append y x ∘ rawTupleSwap n m = Fin.append x y := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp [rawTupleSwap,Function.comp_def]

theorem rawTupleSwap_twice (w : Fin (n+m) → M) :
    (w ∘ rawTupleSwap m n) ∘ rawTupleSwap n m = w := by
  have hw := Fin.append_castAdd_natAdd (f := w)
  rw [←hw,rawTupleSwap_append,rawTupleSwap_append]

def RawDefinableGraphMap.inverse
    {A : L.DefinableSet (Set.range c) (Fin n)} {B : L.DefinableSet (Set.range c) (Fin m)}
    (f : RawDefinableGraphMap c A B) (hf : Function.Bijective f.toFun) :
    RawDefinableGraphMap c B A where
  toFun := (_root_.Equiv.ofBijective f.toFun hf).symm
  graph_definable := by
    have hd := f.graph_definable.preimage_comp (rawTupleSwap n m)
    suffices he : {w : Fin (m+n) → M | w ∘ rawTupleSwap n m ∈ f.graph.val} =
        {w | ∃ b : B.val,w = Fin.append b.val ((_root_.Equiv.ofBijective f.toFun hf).symm b).val} by
      exact he ▸ hd
    ext w
    constructor
    · rintro ⟨a,ha⟩
      refine ⟨f.toFun a,?_⟩
      have h := congrArg (fun t : Fin (n+m) → M => t ∘ rawTupleSwap m n) ha
      rw [rawTupleSwap_twice,rawTupleSwap_append] at h
      have hi : ((_root_.Equiv.ofBijective f.toFun hf).symm (f.toFun a)).val = a.val :=
        congrArg Subtype.val ((_root_.Equiv.ofBijective f.toFun hf).symm_apply_apply a)
      exact h.trans (congrArg (Fin.append (f.toFun a).val) hi.symm)
    · rintro ⟨b,rfl⟩
      refine ⟨(_root_.Equiv.ofBijective f.toFun hf).symm b,?_⟩
      rw [rawTupleSwap_append]
      exact congrArg (Fin.append _) (congrArg Subtype.val ((_root_.Equiv.ofBijective f.toFun hf).apply_symm_apply b)).symm

variable (e : M ↪ₑ[L] N) (c : P → M)
variable {A : L.DefinableSet (Set.range (e ∘ c)) (Fin n)}
variable {B : L.DefinableSet (Set.range (e ∘ c)) (Fin m)}

theorem RawDefinableGraphMap.restrict_injective
    (f : RawDefinableGraphMap (e ∘ c) A B) (hf : Function.Injective f.toFun) :
    Function.Injective (f.restrict e c) := by
  intro x y he
  have h := congrArg (fun z : (elementaryActualDefinableEquiv e c B).val => e ∘ z.val) he
  rw [f.restrict_commutes,f.restrict_commutes] at h
  have ha := hf (Subtype.ext h)
  apply Subtype.ext
  funext i
  exact e.injective (congrFun (congrArg Subtype.val ha) i)

theorem RawDefinableGraphMap.restrict_bijective
    (f : RawDefinableGraphMap (e ∘ c) A B) (hf : Function.Bijective f.toFun) :
    Function.Bijective (f.restrict e c) := by
  refine ⟨f.restrict_injective e c hf.1,?_⟩
  intro y
  let g := f.inverse hf
  let x := g.restrict e c y
  refine ⟨x,?_⟩
  apply Subtype.ext
  funext i
  apply e.injective
  have h := f.restrict_commutes e c x
  have hg := g.restrict_commutes e c y
  have hx : (⟨e ∘ x.val,x.property⟩ : A.val) = g.toFun ⟨e ∘ y.val,y.property⟩ := Subtype.ext hg
  have he : f.toFun (g.toFun ⟨e ∘ y.val,y.property⟩) = ⟨e ∘ y.val,y.property⟩ :=
    (_root_.Equiv.ofBijective f.toFun hf).apply_symm_apply _
  exact congrFun (h.trans ((congrArg (fun a : A.val => (f.toFun a).val) hx).trans (congrArg Subtype.val he))) i

end DiamondIntegral.Section5
