# Local measured tensor proof route

This note records proof development, not an accepted mathematical input.
No HK result is a premise. The unmeasured positive tensor map and its
group-completed map now have local surjectivity proofs. Their injectivity
and the measured comparison remain open.

For a Gamma-valued definable form on a nonzero RV tuple, the checked
`rv_tuple_gamma_algebraic_depends_on_values` removes all angular RV names
once the input Gamma values are named. Thus each form value is Gamma-
definable over the original base and that value tuple. This applies to the
combined weight used in the measured category, not merely to a separately
chosen volume function.

Abstract a finite tuple of named Gamma parameters to free Gamma variables,
using the full imaginary code syntax. A raw relation obtained by abstracting
a parameter need not be invariant in its other Gamma codes away from the
original parameter. Define the abstracted predicate universally over every
proper RV code tuple of those Gamma values. This restores full invariance
and specializes to the original predicate. Functionalize the output graph
by requiring uniqueness; at the original value tuple it remains the named
singleton. The result is an original-ground definable partial Gamma function
through the given input/output value pair, with no representative retained.

Saturation over the small common-name set gives finitely many such partial
Gamma functions covering the full graph of the form. Their full Gamma
code graphs define old-ground predicates on the RV source. Refine the
source into finitely many disjoint cells according to the first function
whose graph contains its form value. Each cell has its form determined by
a Gamma function of its original coordinate-value tuple.

Apply the checked original-ground RV product normal form to each cell.
The original input values are integral monomials of the residue-coordinate
values and the free Gamma coordinates. Partition the residue factor by its
finite tuple of Gamma values; those finite values must be individually
Gamma-definable over the original ground. On each resulting product, the
combined weight depends only on the free Gamma factor. Set the residue
combined weight to one and assign the remaining Gamma combined weight to
the Gamma factor. Convert combined weights back to the actual volume forms
using the proved equations. Retain degree-zero and finite Gamma forms.
The checked rank argument supplies the true RES[k-m] label degree.

Measured injectivity still requires invariance of the resulting balanced
tensor expression under actual measured RV isomorphisms, together with the
local unmeasured injectivity argument. No uniqueness of a product normal
form, cancellation in a positive semiring, definable Gamma section, or
unproved generic torus rigidity may be substituted for that proof.

The finite actual volume-map partition is now individually checked in
`RVGammaFormValuePartition.lean`. Each source cell has one original-ground
Gamma function of its coordinate values. The 641-module full build and audit pass for these additions
(2014 public theorem types; 3984 audited heads). Later drafts must retain the monomial
Gamma-value reconstruction data of each product chart: the existing
unmeasured product-piece record only stores its bijection, so it does not
by itself state the contraction formula needed to substitute the form.
Keep this additional formula explicit instead of treating an arbitrary
bijection as value-contracting. The basis and its integral inverse already
supply the formula; the next adapters expose it and partition residue
factors by their individually original-ground definable finite value tuples.


### Local measured product geometry — 655-module checkpoint

The full build and principle audit pass: 2034 public theorem types,
1819 printed definitions, 151 named instances and 8 selected reused
heads (4012 audited heads). Only the standard logical principles occur.
`GammaGroundRV_form_normal_form` now proves finite disjoint product
charts for every actual original-ground definable Gamma-valued weight
on a full RV tuple domain, including zeros. The charts retain an explicit
original-ground Gamma function giving the weight on the Gamma factor.
The proof reconstructs original values by the integral inverse monomial
matrix and splits the finite residue-value support into individually
original-ground definable Gamma tuples. It adds no RV representatives
to the ground and uses no HK input.

This is the measured geometric decomposition, not the measured tensor
comparison: the actual RES label degree, volume-form allocation and
positive scissors assembly still need to be joined to these charts.
The coefficient monomorphisms and tensor injectivity remain open.


### Concrete measured tensor surjectivity — 663-module checkpoint

The full build and audit pass: 2052 public theorem types,
1829 definitions, 151 named instances and
8 selected reused heads (4040 audited heads), using only the
standard logical principles. `MeasuredTensorSurjectivity` proves actual
object preimages and surjectivity of both `gammaGroundMeasuredTensorMap`
and `gammaGroundMeasuredGroupTensorMap`. It uses the locally proved
form-product charts, actual RES[k-m] degree transport, prescribed combined
weights converted to genuine same-ground volume forms, and finite positive
scissors assembly. Finite and degree-zero Gamma forms are retained.
No HK premise is used. Both unmeasured tensor surjectivity results remain
checked. Tensor injectivity and the Gamma-to-RV coefficient monomorphisms
remain open; Proposition 3.18 is not yet complete.
