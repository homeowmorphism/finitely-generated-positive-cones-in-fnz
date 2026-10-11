> Historical development and source notes. Proof plans, old namespaces, and
> checkpoint statuses below describe their recorded snapshots. For the current
> submission and verification commands, see [README.md](README.md) and
> [REVIEW_START_HERE.md](REVIEW_START_HERE.md). Commit hashes and removed development files refer to the
> private development repository, not to this public snapshot.

# Finitely generated positive cones in free-group × cyclic-group products
## A correctness-first Lean/mathlib blueprint for arXiv:2608.31103v1

**Source:** Hang Lu Su, *Finitely generated positive cones in Fₙ × ℤ*, version 1, 31 August 2026.  
**Blueprint scope:** all numbered mathematical results of the paper, with explicit dependency boundaries for cited results; two algebraic replacement proofs make the subgroup identifications more suitable for Lean.  
**Implementation status (2026-09-21):** M00 and M01 are proved with their exact unconditional statements at the original pin; the optional generator bound is also proved. M01 uses the FG-specific cofinality, finite-domain and invariant-gap-coordinate proof described after §18. The stronger original O00/O01 isolated-order obligations are also proved, without finite-generation hypotheses. See [PROGRESS.md](PROGRESS.md), [EXTERNAL_OBLIGATIONS.md](EXTERNAL_OBLIGATIONS.md), and [CLASSIFICATION_REVIEW.md](CLASSIFICATION_REVIEW.md). The numbered sections retain the original proof plan; the implementation record identifies substantive replacements.

This rewrite preserves the main mathematical statements while changing the proof architecture. In particular, it avoids using a commutative cone API for noncommutative groups, does not confuse subgroup generation with semigroup generation, and does not infer a free rank from an unranked freeness instance.

### Contents

1. [Deliverables and trust boundary](#1-deliverables-and-trust-boundary)
2. [Target propositions and conventions](#2-target-propositions-and-conventions)
3. [Mathlib reuse map](#3-mathlib-reuse-map)
4. [Elementary cone infrastructure](#4-elementary-cone-infrastructure)
5. [Positive Schreier rewriting](#5-positive-schreier-rewriting)
6. [A reusable weighted-action construction](#6-a-reusable-weighted-action-construction)
7. [The presented group and positive-word calculations](#7-the-presented-group-and-positive-word-calculations)
8. [The index-six subgroup and its generators](#8-the-index-six-subgroup-and-its-generators)
9. [A finite certificate for the marked product isomorphism](#9-a-finite-certificate-for-the-marked-product-isomorphism)
10. [The cone on the index-six subgroup](#10-the-cone-on-the-index-six-subgroup)
11. [The cover in modular coordinates](#11-the-cover-in-modular-coordinates)
12. [An explicit free basis, including the rank proof](#12-an-explicit-free-basis-including-the-rank-proof)
13. [The second subgroup and its power transversal](#13-the-second-subgroup-and-its-power-transversal)
14. [The final positive generating set](#14-the-final-positive-generating-set)
15. [Isolation and the odd-rank obstruction](#15-isolation-and-the-odd-rank-obstruction)
16. [External theorem obligations](#16-external-theorem-obligations)
17. [Implementation order and acceptance tests](#17-implementation-order-and-acceptance-tests)
18. [Correspondence with the source](#18-correspondence-with-the-source)
19. [Sources and versioning](#19-sources-and-versioning)

## 1. Deliverables and trust boundary

`tasks.json` is the machine-readable dependency graph. Every task has a stable identifier, a proposed declaration name, a contract, a proof plan, dependencies, and a target module. These identifiers also appear below. Names proposed for new declarations are **not claims that those declarations already exist in mathlib**.

`FnZPositiveCones/Interfaces.lean` defines `IsPositiveCone`, finite-generation predicates, the presented group, and the final goal propositions. It deliberately contains no proof placeholders or external axioms. `ApiAudit.lean` contains `#check` commands for names inspected in documentation/source. Its purpose is to catch signature and version discrepancies at the start of implementation. Both files were elaborated at the pinned mathlib/toolchain on 2026-09-20 (`lake build`, `lake env lean ApiAudit.lean`; record in `build_logs/`); the single discrepancy found, an unused `deriving Fintype` clause that the current derive handler rejects under the default `backward.isDefEq.respectTransparency`, has been removed.

The implemented library uses the `FnZPositiveCones` namespace and module prefix. Import `FnZPositiveCones.Main` for both main theorems, or `FnZPositiveCones` for the complete library. `Main.lean` contains the two endpoint declarations; their supporting proofs remain in the construction and classification modules.

The proposed dependency pin is mathlib commit

```text
dec5b2b780537b6eaf7f5e5f000c12f7387fb24d
```

whose `lean-toolchain` specifies `leanprover/lean4:v4.35.0-rc2`. The package records this pair; `lake build` and `lake env lean ApiAudit.lean` were run against it on 2026-09-20 and passed. Some API inspection used the live documentation site; therefore the first implementation task is to run the audit against the pinned checkout, not to assume that a documentation lookup is a compilation test.

There are three different kinds of mathematical obligation:

- **Mathlib reuse:** existing definitions and theorems, with their actual hypotheses.
- **Local proof tasks:** the new lemmas described in detail in this document, including the two explicit isomorphism constructions.
- **External proof projects:** the Dubrovina–Dubrovin/Navas (DD/Navas) theorem about the specified positive cone, and the MMRT obstruction used only for the classification. A literature citation does not discharge a Lean goal.

The local existence proof can first be developed as a theorem taking `BaseConeGoal` as a hypothesis. The final unconditional theorem is obtained only after that hypothesis is supplied by a checked proof. Likewise, the odd-rank classification has a separate, explicit upstream dependency. Do not replace either dependency by an untracked `axiom`.

## 2. Target propositions and conventions

### 2.1 Strict positive cones [C00]

For any group, not necessarily commutative, use a `Subsemigroup` and the following predicate:

```lean
def IsPositiveCone {G : Type u} [Group G] (P : Subsemigroup G) : Prop :=
  (1 : G) ∉ P ∧ ∀ g : G, g = 1 ∨ g ∈ P ∨ g⁻¹ ∈ P

def SemigroupFG {G : Type u} [Group G] (P : Subsemigroup G) : Prop :=
  ∃ S : Finset G, Subsemigroup.closure (S : Set G) = P

def HasFGPositiveCone (G : Type u) [Group G] : Prop :=
  ∃ S : Finset G, IsPositiveCone (Subsemigroup.closure (S : Set G))

abbrev FnZ (n : ℕ) := FreeGroup (Fin n) × Multiplicative ℤ
```

Multiplicative closure and exclusion of one imply that an element and its inverse cannot both be positive. Thus the displayed predicate expresses the required disjoint trichotomy without adding redundant fields.

`Subsemigroup.closure S` means closure under **nonempty** finite products. It does not add the identity automatically. Do not replace it by `Submonoid.closure S`, `Subgroup.closure S`, or the predicate that the ambient group is finitely generated.

The use of `Multiplicative ℤ` matters: the direct product is a product of multiplicative groups. The integer `1` viewed additively corresponds to the distinguished central generator, whereas the multiplicative identity of this factor corresponds to additive `0`.

### 2.2 Main goals [M00, M01, M02 optional]

The existence target is

```lean
∀ n : ℕ, 2 ≤ n → Even n → HasFGPositiveCone (FnZ n)
```

and the classification target is

```lean
∀ n : ℕ, 2 ≤ n → (HasFGPositiveCone (FnZ n) ↔ Even n)
```

An optional quantitative refinement constructed below, `BoundedEvenRankGoal` [M02], is

```lean
∀ n : ℕ, 2 ≤ n → Even n →
  ∃ S : Finset (FnZ n), S.card ≤ 6 * (n - 1) + 1 ∧
    IsPositiveCone (Subsemigroup.closure (S : Set (FnZ n)))
```

For `n ≥ 2`, the bound is `6*n - 5`. This is an upper bound deduced from this blueprint's generating set, not a minimality result and not an additional theorem attributed to the paper.

### 2.3 Conventions that must remain fixed

**Right cosets:** a transversal represents cosets `K g`. The representative `rep g` must satisfy `g * (rep g)⁻¹ ∈ K`. This is the orientation needed for the Schreier factor `t*s*(rep(t*s))⁻¹`.

**Right actions:** if `L : G →* Equiv.Perm V` is a usual permutation homomorphism, define

\[
v\mathbin{\cdot}g=L(g^{-1})(v).
\]

Then `(v · g) · h = v · (g*h)`. Applying `L(g)` directly would reverse this convention.

**Exponents:** use natural powers for finite repetition and integer powers when subtraction occurs. For example, the exponent in `b^(6*k-s)` is the integer `6*(k:ℤ)-(s:ℤ)`, never truncated natural subtraction.

**Subgroup types:** `H : Subgroup Gamma2` has an associated group type `↥H`. The second subgroup will be `K : Subgroup H`, not silently a subgroup of `Gamma2`. Ambient calculations are transported through subgroup inclusions using subtype extensionality.

**The small case:** put `d = n-1` and retain the hypothesis `0 < d`. For `n=2`, `d=1` and the vertex set is a singleton. Use a bijective orbit enumeration rather than an `IsCycle` statement which may exclude the identity permutation.

## 3. Mathlib reuse map

The following are actual names inspected in documentation/source, not newly proposed declarations. See the source catalogue in §19 and the executable `#check` audit. Exact elaboration at the chosen pin remains the first build task.

| Mathematical need | Existing mathlib entry points | What they do not supply |
|---|---|---|
| Nonempty multiplicative closure | `Subsemigroup.closure`, `subset_closure`, `closure_le`, `closure_mono`, `closure_induction` | Positivity and exclusion of one |
| Restrict/transport a semigroup | `Subsemigroup.comap`, `Subsemigroup.map`, `MulHom.map_mclosure` | Arbitrary homomorphic images/preimages need not preserve positive cones |
| A finitely presented group | `PresentedGroup`, `PresentedGroup.of`, `one_of_mem`, `toGroup`, `toGroup.of`, `closure_range_of`, `ext` | No automatic solution of the word problem |
| A right transversal | `Subgroup.IsComplement`, `Subgroup.IsComplement.toRightFun`, `mul_inv_toRightFun_mem`, `rightQuotientEquiv` | The particular transversals must be proved valid |
| Ordinary Schreier generation | `Subgroup.closure_mul_image_eq`, `closure_mul_image_eq_top`, `closure_mul_image_eq_top'` | These give **subgroup**, not positive-semigroup, generation |
| Free universal properties | `FreeGroup.lift`, `lift_apply_of`, `ext_hom`, `freeGroupCongr` | Injectivity of a map defined by generators |
| A marked free basis | `FreeGroupBasis`, `ofRepr`, `reindex`, `map`, `ext_hom` | The desired basis and its cardinality |
| Freeness of a subgroup | `subgroupIsFreeOfIsFree` | The output alone does not identify its rank |
| Orbit/stabilizer equivalence | `MulAction.orbitEquivQuotientStabilizer` | Match its left-action/left-coset conventions explicitly |
| Subgroup index | `Subgroup.index`, `index_ker`, `index_comap_of_surjective` | Never use a finite-group cardinal formula with an infinite free group |
| Modular arithmetic | `ZMod.isUnit_iff_coprime`, `unitOfCoprime`, `natCast_zmod_val` | Nonzero is not the same as invertible for composite moduli |

Two important negative API findings govern this design.

First, `GroupCone G` in `Mathlib.Algebra.Order.Group.Cone` assumes `[CommGroup G]` and extends `Submonoid G`. It is a nonnegative-cone API. It is not the representation for the strict positive cones in this paper. Adding a false commutativity instance or changing the theorem to use a monoid closure would invalidate the project.

Second, the inspected Nielsen–Schreier API provides `IsFreeGroup` for a subgroup. The theorem `Subgroup.rank_le_index_mul_rank` is only a bound. Neither is the statement that an index-`d` subgroup of `F₂` has a specified basis indexed by `Fin (d+1)`. Section 12 supplies that basis instead of relying on an unverified exact-rank theorem name. Another implementation may reuse a richer spanning-tree theorem, but only after exposing its basis and proving the cardinality correspondence.

For semigroup maps, the actual argument order is **map first, semigroup second**:

```lean
Subsemigroup.comap (f : M →ₙ* N) (S : Subsemigroup N)
Subsemigroup.map   (f : M →ₙ* N) (S : Subsemigroup M)
```

A `MonoidHom` is accepted either through the registered coercion to `M →ₙ* N` or explicitly via `.toMulHom`; the blueprint writes `.toMulHom` for readability. Pick one form and use it consistently so that `map_mclosure` and `comap` lemmas rewrite without unfolding.

## 4. Elementary cone infrastructure

### 4.1 Disjointness and rigidity [C01]

**Contracts.** For a positive cone `P`:

1. `g ∈ P → g ≠ 1`.
2. `g ∈ P → g⁻¹ ∉ P`.
3. If `P` and `Q` are positive cones and `P ≤ Q`, then `P = Q`.

**Proof of (2).** If both memberships hold, `P.mul_mem` puts `g*g⁻¹ = 1` in `P`.

**Proof of (3).** For `q ∈ Q`, the trichotomy for `P` gives `q=1`, `q∈P`, or `q⁻¹∈P`. The first contradicts positivity of `Q`; the third, together with `P≤Q`, puts both `q` and `q⁻¹` in `Q`. Hence `q∈P`. Finish with subsemigroup extensionality or antisymmetry.

These lemmas need no ordered-group instance. Keep them in the algebraic cone module.

### 4.2 Restriction to a subgroup [C02]

For `K : Subgroup G`, define

```lean
Subsemigroup.comap K.subtype.toMulHom P
```

as a subsemigroup of the group type `K`. It is a positive cone when `P` is. Exclusion of one follows under the inclusion; totality follows by applying ambient totality to the underlying element. If the ambient element is one, use subtype extensionality to conclude that the subgroup element is one.

**Boundary:** this is restriction along an injective homomorphism. Pullback along an arbitrary homomorphism is not enough: a nonidentity element in its kernel would have neither itself nor its inverse in the pulled-back strict cone.

### 4.3 Transport through a multiplicative equivalence [C03]

Given `e : G ≃* G'`, define the transported semigroup as

```lean
Subsemigroup.map e.toMonoidHom.toMulHom P
```

Prove it is a positive cone by using injectivity for exclusion of one and surjectivity for totality. To transport finite generation, use `MulHom.map_mclosure` and the finite image of a generating set. This also transports a cardinal upper bound.

Do not use arbitrary quotient maps here. A positive element may be killed by a quotient.

### 4.4 Finite determination [C04]

Define

```lean
def FinitelyDetermined {G : Type u} [Group G] (P : Subsemigroup G) : Prop :=
  ∃ S : Finset G, (S : Set G) ⊆ (P : Set G) ∧
    ∀ Q : Subsemigroup G, IsPositiveCone Q →
      (S : Set G) ⊆ (Q : Set G) → Q = P
```

If `P = closure S` and `S ⊆ Q`, the universal property of closure gives `P≤Q`; C01 gives equality. This establishes finite determination from semigroup finite generation. The topology adapter is postponed until §15, so it is not a dependency of the even-rank construction.

## 5. Positive Schreier rewriting

This is a new reusable theorem, not an invocation of ordinary subgroup Schreier generation.

### 5.1 Transversal interface [T00, T01]

Fix `K : Subgroup G`, `T : Set G`,

```lean
hT : Subgroup.IsComplement (K : Set G) T
hT1 : (1 : G) ∈ T
```

Let `rep g` be the underlying group element of `hT.toRightFun g`. The implementation should first expose the following local helper lemmas:

\[
\begin{aligned}
&\operatorname{rep}(g)\in T,\qquad g\operatorname{rep}(g)^{-1}\in K,\\
&t\in T\Longrightarrow\operatorname{rep}(t)=t,\\
&\operatorname{rep}(1)=1,\qquad g\in K\Longrightarrow\operatorname{rep}(g)=1,\\
&\operatorname{rep}(g)=\operatorname{rep}(h)
 \Longleftrightarrow gh^{-1}\in K,\\
&\operatorname{rep}(\operatorname{rep}(g)h)=\operatorname{rep}(gh).
\end{aligned}
\]

The last identity follows because `g = k * rep g` for some `k∈K`. It requires no normality assumption. Prove these from unique right-coset representatives rather than mixing left-quotient APIs into the argument.

For any `t,p : G`, define the subgroup-valued element

\[
\Delta(t,p)=\left\langle tp\operatorname{rep}(tp)^{-1},\;\text{membership in }K\right\rangle.
\]

The membership proof exists for every `t,p`; only later will positivity require `t∈T`.

### 5.2 Exact equality theorem [T02]

**Inputs:** a positive cone `P`, a set `S⊆G` with `P=Subsemigroup.closure S`, the transversal data above, and

\[
\forall t\in T\ \forall s\in S,
\quad \Delta(t,s)=1\ \lor\ (\Delta(t,s):G)\in P.
\]

Define a set of elements of the **subgroup type** `K` by

\[
A=\{\Delta(t,s):t\in T,\ s\in S,\ \Delta(t,s)\ne1\}.
\]

**Output:**

\[
\operatorname{comap}(K\hookrightarrow G)(P)
       =\operatorname{Subsemigroup.closure}(A).
\tag{PS}
\]

No finiteness assumption is needed for this equality. Finiteness is a separate corollary. No prefix-closed transversal and no normal subgroup are required.

### 5.3 Closure-induction proof

Let `Q = Subsemigroup.closure A` inside `K`. Temporarily adjoin the identity:

\[
M=\{k\in K:k=1\ \lor\ k\in Q\}.
\]

This is a **temporary submonoid**, proved closed by the four cases for the two disjunctions. It is not the positive cone. Using it avoids extracting nonempty lists and deleting identity factors.

Prove, by `Subsemigroup.closure_induction` on `p∈closure S`, the strengthened invariant

\[
\forall t\in T,\quad \Delta(t,p)\in M.
\tag{I}
\]

For a generator `s`, either the Schreier element is one, or it belongs to `A` and hence to `Q`.

For a product `p*q`, put `u = rep(t*p)`. The representative identities give

\[
\Delta(t,pq)=\Delta(t,p)\,\Delta(u,q).
\tag{F}
\]

To verify this, multiply out in the ambient group:

\[
(tp u^{-1})(u q\operatorname{rep}(u q)^{-1})
   = tpq\operatorname{rep}(tpq)^{-1}.
\]

Use `u∈T` to invoke the second induction hypothesis. Both factors lie in `M`, so their product does too. Lift the ambient equality to the subgroup by subtype extensionality.

Now take an element `p` of the restricted cone. Set `t=1` in (I). Since `p∈K`, `rep p=1`, so `p∈M`. The alternative `p=1` contradicts `1∉P`; therefore `p∈Q`.

For the reverse inclusion, every generator in `A` is positive by the Schreier positivity hypothesis and its nonidentity condition. The restricted semigroup is closed, so the closure universal property gives `Q≤P|K`.

**Important implementation detail:** the induction statement quantifies over **all** `t∈T`. An invariant only about `Δ(1,p)` is too weak for the product step.

### 5.4 Finite specialization [T03]

If `T` and `S` are finite, then `A` is finite: take the image of the finite product of their indexing types and remove one. Use `Set.Finite.toFinset` or an explicitly indexed `Finset.image`, locally under `classical` as necessary.

Conclude `SemigroupFG (P|K)`. Both applications in this project provide explicit finite transversals, so no general finite-index-to-finite-transversal theorem is needed on the critical path.

**Forbidden shortcut:** `Subgroup.fg_of_index_ne_zero` proves finite generation of the group `K`; it does not prove (PS).

## 6. A reusable weighted-action construction

The same small construction will establish injectivity in two different free-group identifications. It is worth implementing once.

### 6.1 Weighted permutations [W00]

Let `Q` be a state type, `D` a group, `δ : Equiv.Perm Q`, and `ω : Q → D`. Define

\[
T_{\delta,\omega}(q,h)=(\delta(q),\;h\,\omega(q)).
\]

Its inverse is explicitly

\[
T_{\delta,\omega}^{-1}(q,h)
 =\bigl(\delta^{-1}(q),\;h\,\omega(\delta^{-1}(q))^{-1}\bigr).
\]

Package these maps as an `Equiv.Perm (Q × D)` and prove both inverse laws by simplification and cancellation. In particular, no word problem, choice of normal form, or group presentation is involved here.

Every such permutation commutes with **left** multiplication in the second coordinate:

\[
T(q,c h)=(\delta(q),c(h\omega(q))).
\tag{L}
\]

Associativity suffices; `D` need not be commutative. A finite-order state permutation does not force its weighted lift to have that finite order.

### 6.2 From generators to a right action [W01]

For a free group, assign each free generator to the **inverse** of its desired weighted right transition and apply `FreeGroup.lift`. For a presented group, apply `PresentedGroup.toGroup` after proving the relator identities among those permutations.

If the resulting homomorphism is `L : G →* Equiv.Perm (Q×D)`, define the right action by `L(g⁻¹)`. Prove the multiplication law once. Prove property (L) for all group elements by the universal property/generator induction, including inverses.

Keep two actions conceptually distinct: the state action on `Q`, and the weighted action on `Q×D`. Prove that projection to the first coordinate intertwines them.

### 6.3 The stabilizer weight homomorphism [W02]

Fix `q₀ : Q`, and let `K` be its stabilizer for the state action. For `k∈K`, write

\[
(q_0,1)\mathbin{\cdot}k=(q_0,w(k)).
\]

Then `w : K →* D` is a group homomorphism. Indeed,

\[
(q_0,1)\cdot(k_1k_2)
=((q_0,1)\cdot k_1)\cdot k_2
=(q_0,w(k_1))\cdot k_2
=(q_0,w(k_1)w(k_2)),
\]

where the final equality is (L). The state is `q₀` because both elements are in the stabilizer. This is the key reason the accumulated weight is a homomorphism rather than merely a cocycle.

Package the homomorphism at the subgroup type, or at a subgroup provably equal to the stabilizer. Do not define it by selecting a word for an element and asserting independence of the selection.

## 7. The presented group and positive-word calculations

### 7.1 Presentation [G00]

Use a two-element generator type with constructors `a` and `b`. In the free group on this type, let

\[
r=b a^2 b a^{-1},\qquad
\Gamma=\operatorname{PresentedGroup}(\{r\}).
\]

Use the images of the generators as the elements `a,b : Γ`. The interface file spells out this definition. Obtain

\[
b a^2 b=a
\tag{R}
\]

from `PresentedGroup.one_of_mem`, simplification of the generator images, and group cancellation. Also record that `a,b` generate `Γ` as a subgroup, using `PresentedGroup.closure_range_of` and enumeration of the two generators.

There is no need to identify this presentation with a separately defined braid group. The external cone theorem will use this exact presentation and marking.

### 7.2 Elementary identities [G01, G02]

From (R), prove

\[
b^{-1}a=a^2b,\qquad ab^{-1}=ba^2.
\tag{7.1}
\]

Next, for natural numbers `s,t`, prove by induction

\[
b^{-s}a=a(ab)^s,\qquad ab^{-t}=(ba)^t a.
\tag{7.2}
\]

For `s,t≥1`, prove

\[
b^{-s}ab^{-t}=a(ab)^{s-1}(ba)^{t-1}a.
\tag{7.3}
\]

A convenient derivation of (7.3) isolates one inverse power on each side:

\[
b^{-s}ab^{-t}
=b^{-(s-1)}(b^{-1}ab^{-1})b^{-(t-1)}
=b^{-(s-1)}a^2b^{-(t-1)},
\]

and then uses (7.2). This avoids a separate two-dimensional induction. Encode the positive integer assumptions so that `s-1` and `t-1` in natural powers are justified, or parameterize (7.3) by `s+1,t+1` from the start.

Suggested tactics: use named rewrites for (R) and (7.1), `pow_succ`/integer-power lemmas, and `group` for pure group normalization **after** inserting the presentation-specific rewrites. `group` does not know (R) automatically.

### 7.3 Positivity membership without the external cone theorem [G03]

Let

\[
P_2=\operatorname{Subsemigroup.closure}\{a,b\}.
\]

Prove the following two membership statements using only the presentation:

\[
\forall p,q\in\mathbb Z,\quad b^pab^q\in P_2,
\tag{7.4}
\]

and

\[
\forall k\in\mathbb N,\quad 1\le k\Longrightarrow b^k\in P_2.
\tag{7.5}
\]

Split (7.4) into the four sign cases for `p,q`. When both are negative, use (7.3); when exactly one is negative, use (7.2); when neither is negative, the expression is already a positive word with an `a` in it.

**Zero-power pitfall:** `1` is not automatically in a subsemigroup. Do not prove membership of `(ab)^0` or `b^0` in `P₂`. Instead, prove anchored closure statements such as

\[
u,v\in P\Longrightarrow u v^m\in P\quad(m\in\mathbb N),
\]

by induction starting with `u`. Apply them to expressions that already contain a known positive letter. Prove (7.5) by induction on `k-1` starting with `b`.

These membership results do not assert that the displayed words are nonidentity. That conclusion uses exclusion of one from the external base-cone theorem.

### 7.4 The external base-cone theorem [E00, E01, E02]

The DD/Navas input is exactly

\[
1\notin P_2,
\qquad
\forall g\in\Gamma,\quad g=1\ \lor\ g\in P_2\ \lor\ g^{-1}\in P_2.
\]

Treat these as two independently tracked proof obligations, joined into `IsPositiveCone P₂`. The source theorem is Theorem 3.1 of [Su], attributed there to Dubrovina–Dubrovin [DD, Theorem 5] (stated for `B₃` with `a = σ₁σ₂`, `b = σ₂⁻¹`) and to Navas [Navas, Main Theorem]. Navas's theorem at parameter `n = 2` reads `Γ₂ = ⟨a,b⟩⁺ ⊔ ⟨a⁻¹,b⁻¹⟩⁺ ⊔ {1}` for the presentation `⟨a,b | ba²b=a⟩`, which is exactly [E00] and [E01] for `Subsemigroup.closure {a,b}`. Section 16 specifies the dependency boundary. None of the finite certificate checks below proves this theorem.

## 8. The index-six subgroup and its generators

### 8.1 The quotient map [G04]

Construct

\[
\phi:\Gamma\longrightarrow\operatorname{Multiplicative}(\operatorname{ZMod}6)
\]

by sending `a` to additive residue `4` and `b` to additive residue `1`, wrapped with `Multiplicative.ofAdd`. Use `PresentedGroup.toGroup (f := φ₀) h`, where `φ₀ : GammaLetter → Multiplicative (ZMod 6)` is the generator assignment and `h` the relator check (`f` is an implicit argument of `toGroup`). The relator calculation is

\[
1+2\cdot4+1-4=6=0\quad\text{in }\mathbb Z/6.
\]

This is a finite arithmetic obligation in `ZMod 6`; after unfolding the multiplicative wrapper (`ofAdd_add`, `ofAdd_eq_one`) close it with `decide` or `reduce_mod_char` (`norm_num` alone stops at `(6 : ZMod 6) = 0`). Surjectivity follows from the image of powers of `b`: every residue has a natural representative less than six. Set `H = phi.ker`.

The subgroup index is six. This is a useful recorded result, but the later proof uses an explicit transversal, not only the number `6`.

### 8.2 The first transversal [G05]

For `s : Fin 6`, set

\[
t_s=b^{-s}.
\]

The images `phi(t_s)=-s` are the six distinct residues; here and below, an additive expression in `phi(g)` means `Multiplicative.toAdd (phi g)`. Consequently these elements form a right transversal for `H`. To construct `Subgroup.IsComplement`, prove existence and uniqueness of a decomposition `g=h*t_s`: choose `s` from `-phi(g)` and put `h=g*t_s⁻¹`. Equality of two representatives follows by applying `phi`.

Here `H` is normal because it is a kernel. This fact is available for this step only; the generic positive Schreier lemma and the second subgroup must not inherit an accidental normality hypothesis.

### 8.3 The Schreier table [G06]

Put

\[
r_s=(s+2)\bmod6,
\qquad A_s=b^{-s}ab^{r_s},
\qquad C=b^6.
\]

All these elements are in `H`; introduce subgroup-valued versions immediately. The table is

| `s` | `r_s` | Schreier factor for `a` | Schreier factor for `b` |
|---:|---:|---|---|
| 0 | 2 | `A₀ = a b²` | `C = b⁶` |
| 1 | 3 | `A₁ = b⁻¹ a b³` | `1` |
| 2 | 4 | `A₂ = b⁻² a b⁴` | `1` |
| 3 | 5 | `A₃ = b⁻³ a b⁵` | `1` |
| 4 | 0 | `A₄ = b⁻⁴ a` | `1` |
| 5 | 1 | `A₅ = b⁻⁵ a b` | `1` |

For the `a` column, the state changes from `s` to `s+2` because `phi(a)=4`. For the `b` column it changes to `s-1`.

Prove representative identification first, then simplify the Schreier expression. Do not ask a simplifier to discover coset representatives from scratch. Since the state type has six elements, `fin_cases` followed by arithmetic and group normalization is an appropriate proof strategy.

### 8.4 Ordinary group generation, independent of positivity [G07]

Let `Y` denote the seven-element indexed family `A₀,…,A₅,C`. Invoke `Subgroup.closure_mul_image_eq_top` with the first transversal and ambient generating set `{a,b}`. Simplify the table; adding or removing the identity does not affect **subgroup** closure. Conclude

\[
\operatorname{Subgroup.closure}(\{A_0,\ldots,A_5,C\})=\top
\quad\text{inside }H.
\tag{8.1}
\]

This does not depend on E00–E02. It will establish surjectivity of the product map in §9.

## 9. A finite certificate for the marked product isomorphism

The desired result is not merely an abstract isomorphism. Its marking must identify the image of `C`, because that image determines the second transversal.

This section is a replacement proof designed for formalization. It avoids the paper's sketched passage through the central quotient, `PSL₂(ℤ)`, and ping-pong. It does not require a generic Reidemeister–Schreier presentation theorem or a GAP certificate.

### 9.1 Three marked elements and centrality [G08]

Inside `H`, define

\[
X=ab^2,\qquad Y_0=a^2b^2a^2,\qquad Z=a^3.
\]

Membership in `H` follows from the quotient-map calculation. Prove that `Z` commutes with `a` and `b`. The nontrivial calculation is

\[
ba^3=(ba^2)a=(ab^{-1})a=a(a^2b)=a^3b.
\]

Extend commutation to all of `Γ`, or at least to the subgroup generated by `X,Y₀`, using generator induction. This is the only centrality fact needed. There is no need to identify the entire center or establish the infinite order of `Z` separately.

### 9.2 Relations among the seven subgroup generators [G09]

Let `B₀=C`, and let `B_s=1` for `s=1,…,5`. Rewrite the equation `ba²b=a` starting at state `s` in the first transversal. The result is

\[
A_s=B_s A_{s-1} A_{s+1} B_{s+3},
\tag{9.1}
\]

with all subscripts modulo six. Explicitly,

\[
\begin{array}{lll}
A_0=C A_5 A_1,& A_1=A_0 A_2,& A_2=A_1 A_3,\\
A_3=A_2 A_4 C,& A_4=A_3 A_5,& A_5=A_4 A_0.
\end{array}
\tag{9.2}
\]

These are identities in `Γ`, proved directly by multiplying the defining Schreier expressions and using (R). They are not being assumed to be a complete presentation of `H`.

Direct telescoping also gives

\[
X=A_0,\qquad Z=A_0 A_2 A_4,
\qquad Y_0=A_0 A_2^2 A_4.
\tag{9.3}
\]

From these identities derive, in the indicated order,

\[
\begin{aligned}
A_2&=X^{-1}Y_0Z^{-1}X, & A_1&=X A_2,\\
A_4&=A_2^{-1}X^{-1}Z, & A_5&=A_4X,\\
A_3&=A_1^{-1}A_2, & C&=(A_2A_4)^{-1}A_3.
\end{aligned}
\tag{9.4}
\]

These express every member of the generating family as a group word in `X,Y₀,Z`; no commutation is needed for this. Centrality of `Z` is used only in §9.5, to make `E` multiplicative.

### 9.3 The target table [G10]

Let

\[
D=F(x,y)\times\langle z\rangle
  =\operatorname{FreeGroup}(\operatorname{Fin}2)\times\operatorname{Multiplicative}\mathbb Z.
\]

Here `x=(of 0,1)`, `y=(of 1,1)`, and `z=(1,ofAdd 1)`. Define the following elements of this **already existing** product group:

| Symbol | Element of `D` |
|---|---|
| `α₀` | `x` |
| `α₁` | `y x z⁻¹` |
| `α₂` | `x⁻¹ y x z⁻¹` |
| `α₃` | `x⁻¹ y⁻¹ x⁻¹ y x` |
| `α₄` | `x⁻¹ y⁻¹ z²` |
| `α₅` | `x⁻¹ y⁻¹ x z²` |
| `c` | `y⁻¹ x⁻¹ y x z⁻¹` |

Let `β₀=c` and `β_s=1` for the remaining states. Prove the six finite identities

\[
\alpha_s=\beta_s\alpha_{s-1}\alpha_{s+1}\beta_{s+3}.
\tag{9.5}
\]

Also prove

\[
\alpha_0\alpha_2\alpha_4=z,
\qquad
\alpha_0\alpha_2^2\alpha_4=y.
\tag{9.6}
\]

Use product extensionality: the first coordinate is a free-group cancellation identity and the second is integer addition. This is preferable to a large tactic call in the product group which obscures where commutativity is actually available.

The accompanying Python program checks all six identities by exact reduced-word calculations. A Lean proof must still reproduce these finite calculations in the kernel.

### 9.4 Constructing the inverse map from the six-state action [G11, G12]

Use states `s∈ZMod 6`, converting to `Fin 6` when indexing the table. The desired weighted right transitions on `(s,h)∈ZMod 6×D` are

\[
T_a(s,h)=(s+2,h\alpha_s),
\qquad
T_b(s,h)=(s-1,h\beta_s).
\tag{9.7}
\]

The paths `b,a,a,b` and `a` finish at the same state `s+2`; their weights agree by (9.5). Therefore the corresponding weighted permutations satisfy the defining relation.

Apply W01 with generator images `T_a⁻¹,T_b⁻¹` to get a homomorphism from `Γ` to permutations. Its associated right action has first coordinate

\[
s\mathbin{\cdot}\gamma=s-\operatorname{toAdd}(\phi(\gamma)).
\tag{9.8}
\]

This is proved on generators and then on the group. Consequently the stabilizer of state zero is exactly `H`. W02 supplies a homomorphism

\[
\psi_0:H\longrightarrow D.
\]

Evaluate the three marked words starting at zero:

\[
\psi_0(X)=x,\qquad
\psi_0(Y_0)=\alpha_0\alpha_2^2\alpha_4=y,
\qquad
\psi_0(Z)=\alpha_0\alpha_2\alpha_4=z.
\tag{9.9}
\]

The paths for `ab²`, `a²b²a²`, and `a³` return to zero. Their intervening `b` steps have trivial weights in these particular evaluations. The path `b⁶` has weight `c`.

### 9.5 The forward homomorphism and the isomorphism [G13, G14]

Construct a homomorphism

\[
E:D\longrightarrow H,
\qquad x\mapsto X,\quad y\mapsto Y_0,\quad z\mapsto Z.
\]

Use `FreeGroup.lift` for the first factor and integer powers of `Z` for the second. Define `E(w,m)=f(w) Z^m`. Prove it preserves multiplication by commutation of `Z` with the image of `f`. Either reuse a product-hom constructor with commuting ranges after auditing its exact type, or prove this multiplication law directly. Do not use a coproduct constructor whose hypotheses require the target group to be commutative.

By (9.9), `ψ₀ ∘ E` is the identity on the free generators and on the cyclic generator. The free universal property and integer-power induction imply

\[
\psi_0\circ E=\operatorname{id}_D.
\]

Thus `E` is injective. Equations (9.4) imply that every `A_s` and `C` belongs to its range; ordinary group generation (8.1) implies that `E` is surjective.

Obtain a multiplicative equivalence from this bijective homomorphism and invert it to get

\[
\psi:H\simeq D
\]

with exactly the marking (9.9). Since `ψ₀ ∘ E = id_D` and `E` is bijective, `ψ = ψ₀` as functions: for `h ∈ H`, `h = E(ψ h)` (`MulEquiv.apply_symm_apply`), so `ψ₀ h = ψ₀ (E (ψ h)) = ψ h`. Record this as a named lemma; it transfers every table evaluation of §9.4 to `ψ`. This proof does not assume that the six relations (9.2) present `H`: they are used for surjectivity, while the separately constructed left inverse proves injectivity.

### 9.6 The marked image of `b⁶` [G15]

By the identification `ψ = ψ₀` of §9.5 and the weight `c` of the path `b⁶` computed in §9.4 (equivalently, by pushing `C = (A₂A₄)⁻¹A₃` from (9.4) through `ψ` with the marking (9.9)), the table gives

\[
\psi(C)=y^{-1}x^{-1}yxz^{-1}.
\tag{9.10}
\]

Let `ρ:D→F(x,y)` be projection onto the first factor, and define

\[
g=y^{-1}x^{-1}yx.
\]

Then `ρ(ψ(C))=g`. Preserve this statement as a named simplification lemma. An abstract equivalence `H ≃* FnZ 2` without this marking is insufficient for the later power-transversal proof.

## 10. The cone on the index-six subgroup

### 10.1 Restriction and membership [H00]

Assuming E02, define

\[
P_H=\operatorname{comap}(H\hookrightarrow\Gamma)(P_2).
\]

C02 proves that it is a positive cone on the group type `H`. By (7.4) and (7.5), each of `A₀,…,A₅,C` belongs to `P_H`. Therefore none is one. This is where the base-cone theorem converts positive-word membership into a nonidentity assertion.

### 10.2 Finite semigroup generation [H01]

Apply T02 and T03 using the table of §8.3. The nonidentity Schreier factors are exactly the indexed family

\[
Y=\{A_0,A_1,A_2,A_3,A_4,A_5,C\}.
\]

Conclude

\[
P_H=\operatorname{Subsemigroup.closure}(Y).
\tag{10.1}
\]

Here `Y` is a finite set in `H`. One need not prove that all seven displayed entries are pairwise distinct: a finite image suffices for finite generation and the later upper bound.

Keep (8.1) and (10.1) as separate declarations. The former is subgroup generation and does not use E02; the latter is semigroup generation and does.

## 11. The cover in modular coordinates

The main proof can be implemented for every natural `d>0`, and only later specialized to `d=n-1`.

### 11.1 Reflection action [D00]

Let `V_d = ZMod d`. Retain a local instance `[NeZero d]` supplied from `0<d`. This is essential: `ZMod 0` is the integers, not a finite vertex type.

Define involutions

\[
R_x(j)=-j,\qquad R_y(j)=-j-1.
\tag{11.1}
\]

Package them as permutations. Use `FreeGroup.lift` to construct

\[
L:F(x,y)\to\operatorname{Perm}(V_d),\quad
L(x)=R_x,\quad L(y)=R_y.
\]

Define the right action using `L(w⁻¹)`. Since the two generator permutations are involutions, both a generator and its inverse act by the same reflection. This involutivity does not mean that general words act by their own inverses.

### 11.2 Two explicit word actions [D01]

Put `u=yx`. Reading right-action words from left to right gives

\[
j\cdot u=R_x(R_y(j))=j+1,
\tag{11.2}
\]

and

\[
j\cdot g
=R_x(R_y(R_x(R_y(j))))=j+2.
\tag{11.3}
\]

By induction, `j·u^k=j+k` and `j·g^k=j+2k` for natural `k`. Also record the equivalence `j·w = j' ↔ j = j'·w⁻¹` (each group element acts by a bijection of the state set); §13.3 uses it to convert `0·h = 2k` into `h·(C^k)⁻¹ ∈ K`. Integer-power versions `j·g^m = j+2m` for `m : ℤ` are an acceptable alternative.

These identities replace the original case split across the endpoints of the staggered cover.

### 11.3 Stabilizer and index [D02]

Let

\[
K_d=\{w\in F(x,y):0\cdot w=0\}.
\]

This is a subgroup. It is also the usual left stabilizer of zero for `L`, because `L(w⁻¹)(0)=0` iff `L(w)(0)=0`. Either use `MulAction.stabilizer` and prove this equivalence, or define the subgroup directly and later connect it to the action API.

The `u` powers visit every residue, so the action is transitive. The map

\[
K_d\backslash F(x,y)\longrightarrow V_d,
\qquad K_d w\longmapsto0\cdot w
\tag{11.4}
\]

is a bijection. The orientation check is

\[
0\cdot w=0\cdot v
\Longleftrightarrow0\cdot(wv^{-1})=0
\Longleftrightarrow wv^{-1}\in K_d.
\]

Conclude `[F₂:K_d]=d`. If using `MulAction.orbitEquivQuotientStabilizer`, account explicitly for its conventional left action and left cosets, using inversion as appropriate. Alternatively, prove the right-transversal statement directly and obtain the index from it.

Do not apply a cardinal formula for a finite group: `F₂` and `K_d` are infinite. The finite object being counted is the quotient/orbit.

### 11.4 Parity as invertibility of two [D03]

By (11.3), the orbit of zero under powers of `g` is the image of multiplication by two in `ZMod d`.

If `d` is odd, `2` is a unit. One proof uses `ZMod.isUnit_iff_coprime` and `Nat.Coprime 2 d`. Another gives the explicit inverse

\[
q=\frac{d+1}{2}\in\mathbb N,
\quad 2q=d+1,
\quad (2:ZMod d)(q:ZMod d)=1.
\]

Here `(d+1)/2` is exact natural division under the oddness hypothesis, not a field division operation. Therefore

\[
\operatorname{Fin}d\longrightarrow V_d,\qquad k\longmapsto2k
\tag{11.5}
\]

is bijective. This is the precise orbit-enumeration theorem needed later.

If `d` is even, then `d≥2`. Reduction modulo two distinguishes the two orbits: translation by two preserves parity, and the even and odd residue classes are each one orbit. Thus the action of `g` is transitive exactly when `d` is odd.

For `d=1`, (11.5) is the unique bijection between singleton types. No `IsCycle` claim is required. For composite odd `d`, invertibility follows from coprimality, not merely from `2≠0`.

The nontransitivity for even `d` only says that this particular power transversal fails. It is not a proof of the odd-rank nonexistence theorem.

### 11.5 Matching the paper's vertex labels [D04, optional]

To establish literal correspondence with the staggered swaps on vertices `v₀,…,v_{d-1}`, use the relabelling

\[
e(j)=
\begin{cases}
2j,&2j<d,\\
2(d-j)-1,&2j\ge d,
\end{cases}
\qquad0\le j<d.
\tag{11.6}
\]

This enumerates the even indices in increasing order, then the odd indices in decreasing order. Prove that `e : Fin d ≃ Fin d` is a bijection. Let `σ_x` swap `(2j-1, 2j)` for `1 ≤ j ≤ ⌊(d-1)/2⌋` (so `2j ≤ d-1`) and `σ_y` swap `(2j-2, 2j-1)` for `1 ≤ j ≤ ⌊d/2⌋` (so `2j-1 ≤ d-1`), all other vertices fixed; these are the paper's staggered swaps with `n = d+1`. In particular the terminal vertex `d-1` is fixed by `σ_x` when `d` is even and by `σ_y` when `d` is odd, matching the fixed points `d/2` of `R_x` and `(d-1)/2` of `R_y` under `e`. Then

\[
e\circ R_x=\sigma_x\circ e,
\qquad e\circ R_y=\sigma_y\circ e.
\]

The proof is a finite-index arithmetic split, with bounds discharged by `omega` once the modular representatives are exposed. This node certifies that the modular model is the paper's cover in different coordinates; the main theorem can use the modular model directly without depending on this relabelling proof.

The paper's alternating-word description of individual vertices can likewise be proved by induction on the word length [D05, optional]. It is explanatory, not a dependency of the power transversal.

## 12. An explicit free basis, including the rank proof

The index calculation alone does not provide the required `K_d ≃* FreeGroup (Fin (d+1))` term. This section constructs such a term and proves injectivity rather than assuming a rank formula.

### 12.1 Change of ambient free generators [B00]

The pair `x,u=yx` is another free generating pair of `F(x,y)`. An explicit equivalence is obtained from the homomorphisms

\[
F(X,U)\to F(x,y):\quad X\mapsto x,\ U\mapsto yx,
\]

and

\[
F(x,y)\to F(X,U):\quad x\mapsto X,\ y\mapsto UX^{-1}.
\]

Their compositions are identities on the two generators. Use `FreeGroup.ext_hom`, then cancellation. In particular, `{x,u}` generates the ambient group as a subgroup.

The state actions in this basis are especially simple:

\[
j\cdot x=-j,\qquad j\cdot u=j+1.
\]

### 12.2 A different transversal, used only for the basis proof [B01]

For `j : Fin d`, let `t_j=u^j`. These are right-coset representatives for `K_d` because `0·u^j=j` enumerates the vertex set bijectively. This transversal must not be confused with the later positive transversal consisting of powers of `C`.

Let

\[
r_j=\operatorname{val}(-j:ZMod d),\quad 0\le r_j<d,
\]

and define subgroup elements

\[
a_j=u^j x u^{-r_j}\quad(j<d),
\qquad c_d=u^d.
\tag{12.1}
\]

The state calculations prove membership in `K_d`. The ordinary Schreier factors for the generating set `{x,u}` are

\[
\gamma(t_j,x)=a_j,
\qquad
\gamma(t_j,u)=
\begin{cases}
1,&j<d-1,\\
c_d,&j=d-1.
\end{cases}
\tag{12.2}
\]

No assertion about positivity is being made here.

### 12.3 Generation of the stabilizer [B02]

Invoke the existing ordinary Schreier theorem with the transversal `u^j` and ambient generators `{x,u}`. Equation (12.2) gives

\[
\operatorname{Subgroup.closure}
 \bigl(\{a_j:j<d\}\cup\{c_d\}\bigr)=\top
\quad\text{in }K_d.
\tag{12.3}
\]

There are `d+1` indexed candidates, but this fact alone does not prove that they are a free basis. The next two steps prove independence.

### 12.4 The labelled action for the inverse homomorphism [B03]

Let

\[
I_d=\operatorname{Fin}d\mathbin{\oplus}\operatorname{Unit},
\qquad E_d=\operatorname{FreeGroup}(I_d).
\]

Write `e_j` for the generator corresponding to `Sum.inl j`, and `e_*` for the generator corresponding to `Sum.inr ()`.

Construct weighted right transitions on `ZMod d × E_d`:

\[
T_x(j,h)=(-j,h e_j),
\tag{12.4}
\]

and

\[
T_u(j,h)=
\begin{cases}
(j+1,h),&\operatorname{val}(j)<d-1,\\
(0,h e_*),&\operatorname{val}(j)=d-1.
\end{cases}
\tag{12.5}
\]

In (12.4), use the canonical `Fin d` representative of the residue to index `e_j`. These are weighted permutations by W00. The state reflection is involutive, but its weighted lift need not be; imposing `T_x²=1` would destroy this free-basis proof. Since `x,u` are free generators, W01 defines an action without any relator checks. The first-coordinate action is the state action of §11.

A shorter implementation can avoid transporting an action across the basis equivalence: apply `FreeGroup.lift` on the original generators with permutation images

\[
L'(x)=T_x^{-1},\qquad L'(y)=T_u^{-1}T_x.
\]

Then `L'(yx)=T_u⁻¹`, so the associated right transitions for `x,u` are exactly (12.4)–(12.5). This formula also fixes the multiplication-order convention explicitly.

By W02, restriction to the stabilizer gives a homomorphism

\[
\lambda_d:K_d\to E_d.
\]

### 12.5 Evaluation on the candidate basis [B04]

Prove

\[
\lambda_d(a_j)=e_j,\qquad\lambda_d(c_d)=e_*.
\tag{12.6}
\]

For the first equality, the initial path `u^j` goes from zero to `j` without wrapping because `j<d`; its weight is one. The `x` step contributes `e_j` and moves to residue `-j`, whose chosen representative is `r_j`. The final path `u^{-r_j}` goes from `r_j` down to zero without crossing the wrap edge in reverse, so its weight is also one.

Make the “no wrapping” claims actual induction lemmas with bounds:

- For `0≤m<d`, the path of `m` positive `u` steps starting at zero has final state `m` and weight one.
- For `0≤m<d`, the path of `m` negative `u` steps starting at residue `m` has final state zero and weight one.
- The path of `d` positive `u` steps starting at zero wraps exactly once and has weight `e_*`.

The last lemma proves the second equality in (12.6). These are universal proofs in `d`, not finite enumeration over a sample of degrees.

**Small-case check:** when `d=1`, there is no nontrivial tree path. The `x` loop has label `e₀`, and the single `u` step is the wrap loop with label `e_*`. Thus the construction still gives two free generators.

### 12.6 The basis equivalence [B05, B06]

Define

\[
\eta_d:E_d\to K_d
\]

using `FreeGroup.lift`, sending `e_j↦a_j` and `e_*↦c_d`. Equation (12.6) and `FreeGroup.ext_hom` imply

\[
\lambda_d\circ\eta_d=\operatorname{id}_{E_d}.
\]

Therefore `η_d` is injective. Equation (12.3) implies that it is surjective. Convert it to `MulEquiv.ofBijective η_d ⟨inj, surj⟩ : E_d ≃* K_d`, take `.symm`, and package the inverse `K_d ≃* E_d` as `FreeGroupBasis.ofRepr (…).symm` (the argument of `ofRepr` has type `K_d ≃* FreeGroup I_d`, so `ofRepr` does not avoid the inversion), obtaining

\[
\operatorname{FreeGroupBasis}(I_d)(K_d).
\]

The finite type `I_d` has cardinality `d+1`. Construct an equivalence `I_d ≃ Fin (d+1)` using the standard finite-type cardinality API, reindex the basis with `FreeGroupBasis.reindex`, and take its `repr`. The resulting output is an actual marked equivalence

\[
K_d\simeq F_{d+1}.
\tag{12.7}
\]

This closes the rank obligation. There is no reliance on an unspecified choice of free generators from `IsFreeGroup`, nor on an unproved formula for their number.

## 13. The second subgroup and its power transversal

### 13.1 Definition with subgroup types [K00]

Fix `d>0`. Let `f = ρ ∘ ψ : H →* F₂`, and define

\[
K=K_d.\operatorname{comap}(f):\operatorname{Subgroup}(H).
\tag{13.1}
\]

The state action of `H` is pulled back through `f`. By definition, `K` is its stabilizer at zero. The underlying element of `K` first coerces to `H` and only then to `Γ`.

The index `[H:K]=d` follows from surjectivity of `f` and the corresponding index of `K_d`, using `Subgroup.index_comap_of_surjective`, or from the explicit orbit correspondence. It is not necessary to show that `K_d` or `K` is normal.

### 13.2 Product equivalence [K01]

Construct directly

\[
K\simeq K_d\times\operatorname{Multiplicative}\mathbb Z
\]

by

\[
h\longmapsto\left(\left\langle(\psi h)_1,
\ \text{membership in }K_d\right\rangle,(\psi h)_2\right).
\]

The inverse sends `(w,m)` to `ψ⁻¹(w,m)` with the defining membership proof. Verify both inverse laws by subtype and product extensionality. Compose with (12.7) on the first factor to get

\[
K\simeq F_{d+1}\times\mathbb Z.
\tag{13.2}
\]

For the final theorem choose `d=n-1`; `n≥2` gives `d>0` and `d+1=n`. In Lean `n - 1 + 1 = n` is only propositional (`Nat.sub_add_cancel`), so `FnZ (n-1+1)` and `FnZ n` are different types: state the construction for every `d` with target `FnZ (d+1)`, and in the final theorem destructure `n` first (`obtain ⟨d, rfl⟩ : ∃ d, n = d + 1 := ⟨n - 1, by omega⟩`, then `0 < d` and `Odd d` from `2 ≤ d+1` and `Even (d+1)`), or finish with `rw [Nat.sub_add_cancel]`. No further equivalence transport is needed, and the bound `6*(d+1-1)+1 = 6*d+1` is definitional after destructuring.

### 13.3 The positive power transversal [K02]

Assume `d` odd. Write `C` for the element `b⁶` of the subgroup type `H`. Equation (9.10) gives `f(C)=g`, so

\[
0\cdot C^k=2k\quad\text{in }ZMod d.
\]

The orbit bijection (11.5) proves that

\[
T_C=\{C^k:0\le k<d\}
\tag{13.3}
\]

is a right transversal for `K` in `H`. In particular, for odd `d` the representatives are distinct (injectivity of `k ↦ 2k`) and reach every coset (surjectivity), and the one indexed by zero is the group identity.

To prove the complement property directly, given `h∈H`, choose the unique `k<d` with `0·h=2k`. Then `h(C^k)⁻¹∈K` by the bijection equivalence recorded in §11.2 (`0·h = 0·C^k` iff `0·(h(C^k)⁻¹) = 0`), hence `h=(h(C^k)⁻¹)C^k`. Uniqueness follows by comparing orbit states. This proves the correct `K h` orientation without relying on implicit quotient conventions.

For every `d>0`, even without oddness, `C^d∈K`, because its state action sends zero to `2d=0`. Oddness is required both for the `C^k` (`k<d`) to lie in distinct cosets and for them to reach **all** cosets (for even `d`, `C^{d/2} ∈ K` already collides with `C^0`, and the odd states are missed); it is not needed for this membership statement.

## 14. The final positive generating set

### 14.1 The six families containing `a` [K03]

Use `P_H` from (10.1), `K` from (13.1), and `T_C` from (13.3). For `k<d` and `s<6`, the chosen representative of `C^k A_s` is `C^{k'}` for some unique `k'<d`.

The corresponding Schreier element, viewed in `Γ`, is

\[
\begin{aligned}
\gamma(C^k,A_s)
 &= C^k A_s C^{-k'}\\
 &= b^{6k-s}\,a\,b^{r_s-6k'}.
\end{aligned}
\tag{14.1}
\]

The two exponents in the last line are integers. Equation (7.4) proves that this ambient element is in `P₂`. The Schreier construction gives membership in the subgroup type `K`; therefore its image in `H` lies in `P_H`.

No explicit formula for `k'` is necessary. Its bounds and representative property suffice. This avoids a second set of six-by-parity coset calculations.

In Lean, first prove the ambient group identity, then lift the positive membership through the two inclusions. Do not mix subgroup elements from `K≤H` and `H≤Γ` in one untyped expression.

### 14.2 The factors arising from `C` [K04]

For `k<d-1`, `C^k C = C^{k+1}` is itself a representative. Hence

\[
\gamma(C^k,C)=1.
\]

For `k=d-1`, the product is `C^d∈K`, so its representative is one and

\[
\gamma(C^{d-1},C)=C^d.
\tag{14.2}
\]

This lies in `P_H`: it is the positive natural power of `C∈P_H`, with exponent `d≥1`. This argument also works for `d=1`, when the second case is the only case.

### 14.3 Apply positive Schreier a second time [K05, K07, M00]

Equations (14.1)–(14.2) verify every positivity hypothesis of T02. Since the two indexing sets are finite, T03 gives a finitely generated positive cone

\[
P_K=\operatorname{comap}(K\hookrightarrow H)(P_H).
\]

Transport it along (13.2) using C03. This yields a finitely generated positive cone on `F_{d+1}×ℤ` whenever `d>0` is odd. For `n≥2` even, set `d=n-1` (destructuring `n = d+1` as in §13.2); this proves the intended even-rank goal. State it first as the conditional theorem `BaseConeGoal → EvenRankGoal` [K07], with the base cone as an explicit hypothesis threaded through H00–K06; the unconditional `EvenRankGoal` [M00] is obtained by applying it to E02, the DD/Navas base-cone proof, which is the only external input to this branch.

### 14.4 An explicit cardinal bound [K06, M02, optional]

The nonidentity Schreier generating set may be taken to be

\[
S_K=\{\gamma(C^k,A_s):k<d,\ s<6\}\cup\{C^d\}.
\tag{14.3}
\]

Every displayed element is positive, so none is the identity. The `C`-column contributes only its one wrap factor; its other factors are one and are discarded.

The finite-image bound gives

\[
|S_K|\le6d+1.
\]

Transporting by an equivalence preserves this upper bound. Thus for even `n≥2` one can obtain at most `6n-5` generators. No pairwise-distinctness proof is needed for the six-by-`d` family, and no claim of optimality follows.

This finite set is an explicit mathematical witness. Use of `classical` or chosen representatives in an implementation does not, by itself, give an executable algorithm producing reduced words in the final free basis; that would be a separate computational refinement.

## 15. Isolation and the odd-rank obstruction

### 15.1 Cone-to-order correspondence [C05]

For a positive cone define

\[
g<h\Longleftrightarrow g^{-1}h\in P,
\qquad
 g\le h\Longleftrightarrow g=h\ \lor\ g^{-1}h\in P.
\]

Irreflexivity follows from `1∉P`. Transitivity follows from

\[
(g^{-1}h)(h^{-1}k)=g^{-1}k.
\]

Trichotomy follows from the cone trichotomy for `g⁻¹h`. Left invariance follows from

\[
(cg)^{-1}(ch)=g^{-1}h.
\]

Package a `LinearOrder` and a proof of monotonicity of each **left** translation. Do not impose right-translation monotonicity or a bi-order: neither follows from these hypotheses. For a left-invariant total order, the set `{g | 1<g}` is the inverse construction. Verify the two constructions are inverse.

### 15.2 Topology of cone sign functions

Let `LO(G)` be the subtype of `Subsemigroup G` satisfying `IsPositiveCone`. Map a cone to its characteristic function in `G → Bool`, with **discrete** topology on `Bool`, and give `LO(G)` the induced topology. This prevents accidental use of an unsuitable topology on `Prop`.

The set of cones containing a fixed finite subset `S` is open: it is a finite intersection of coordinate-positive cylinders. For a finitely determined cone, this cylinder is its singleton, proving that the cone is isolated.

For the converse needed to compare interfaces, start from a finite cylinder isolating a cone. Positive constraints are kept. A negative constraint at `g≠1` is equivalent, for positive cones, to a positive constraint at `g⁻¹`; a constraint excluding one is automatically satisfied by every cone and can be removed. Thus an isolated cone is finitely determined in the sense of C04.

Finally show that this topology corresponds under the cone/order bijection to finite inequalities between group elements: `g<h` is the sign of `g⁻¹h`. This is the explicit adapter to a theorem stated in terms of isolated left orders.

This proves the paper's Lemma 2.1 with ordinary product/subspace topology infrastructure. None of this topological construction is required for the existence theorem.

### 15.3 The external odd-rank statement [O00, O01]

The needed consequence of MMRT is:

\[
 n\ge2,\ n\text{ odd}
 \Longrightarrow F_n\times\mathbb Z
 \text{ has no isolated left order}.
\tag{15.1}
\]

Through C05, convert it to the precise topology-free interface

```lean
∀ n : ℕ, 2 ≤ n → Odd n →
  ∀ P : Subsemigroup (FnZ n), IsPositiveCone P → ¬ FinitelyDetermined P
```

This is `OddRankObstructionGoal` in the interface file. It is an explicit external-theorem adapter, not a claim that mathlib already contains (15.1).

### 15.4 Classification [O02, O03, M01]

For odd `n≥2`, a finitely generated cone would be finitely determined by C04, contradicting the odd-rank obstruction (`OddRankObstructionGoal`, taken as an explicit hypothesis in O02 and supplied by O01 only in M01). Hence no such cone exists. For the forward direction of the equivalence with `Even n`, split natural-number parity: failure of `Even n` gives `Odd n`, which is impossible. The reverse direction is the even-rank construction K07. State the classification first as `ConditionalClassificationGoal` [O03], with both external statements as hypotheses; M01 applies it to E02 and O01.

The failed `C`-power transversal for even `d` has no logical role in this contradiction. Distinguish “this construction cannot use that transversal” from “no finitely generated positive cone exists.”

## 16. External theorem obligations

### 16.1 DD/Navas: the exact cone, not merely left-orderability

[E00] is `1∉Subsemigroup.closure {a,b}` for the specified presentation. [E01] is the trichotomy for the same closure. An abstract theorem that `Γ` is left-orderable is too weak: it need not make both marked generators positive, and it need not identify the cone with their semigroup closure.

The Main Theorem of Navas [Navas], specialized to parameter two, supplies precisely this decomposition. Its proof separates a reduction argument for totality from the exclusion-of-one argument. A separate upstream formalization can follow its word-reduction and dynamics proof, or import another **checked** theorem with the exact marking and semigroup conclusion. This blueprint does not claim to have formalized those arguments.

If an available theorem is stated for `B₃ = ⟨σ₁,σ₂ | σ₁σ₂σ₁ = σ₂σ₁σ₂⟩`, prove the marked equivalence sending `a ↦ σ₁σ₂` (first generator times second, the marking of [Su], [DD] and [Navas]; the relation holds since `σ₂⁻¹(σ₁σ₂)²σ₂⁻¹ = σ₂⁻¹σ₁σ₂σ₁ = σ₁σ₂`) and `b ↦ σ₂⁻¹`, transport the cone along it, and identify the transported closure with `Subsemigroup.closure {a,b}` via `MulHom.map_mclosure`. (`a ↦ σ₂σ₁` is also a valid marking, and its closure is the same cone via `σ₂σ₁ = (σ₁σ₂)²σ₂⁻²` and `σ₁σ₂ = σ₂⁻²(σ₂σ₁)²`, but use `σ₁σ₂` so that the imported generating set matches literally.) If the imported statement is Dubrovina–Dubrovin's original, note that it is phrased for right orders and for a cone finitely generated as a monoid: `IsPositiveCone` sees only the set, which is the same for the induced left order, so no inversion is applied, but `1 ∉` the semigroup closure must be separated from the monoid statement. Avoid this detour when a theorem is available directly for the presentation.

### 16.2 MMRT: needed only for the reverse implication

Theorem 1.1 of [MMRT] gives the parity classification for isolated linear/left orders on `Fₙ×ℤ`. Only its odd-rank nonexistence direction is needed. Importing it requires a checked theorem and a verified equivalence between its model of free groups, cyclic factor, order structures, and topology and those used here. The odd-rank direction of [MMRT, Theorem 1.1] (stated there for linear, i.e. left, orders on `Fₙ×ℤ`) is proved on p. 14 of [MMRT] from three inputs that a from-scratch formalization of O00 must also cover: Theorem 1.3 of [MMRT] (`Fₙ` has no isolated circular order for odd `n`); continuity and local injectivity of the map `π*` from left orders with cofinal center to circular orders, taken from the proof of [Mann–Rivas, Proposition 5.4]; and Proposition 4.12 of [MMRT] (a non-cofinal center forces non-isolation), which imports Lemmas 4.3, 4.5 and 4.11 from Deroin–Navas–Rivas, Alonso–Brum–Rivas and Matsumoto. None of this changes the statement of O00 or O01.

**Implementation correction to the cofinal transfer.** Continuity and local injectivity alone do not imply that an isolated point has isolated image. [Mann–Rivas, Proposition 5.4](https://aif.centre-mersenne.org/item/10.5802/aif.3191.pdf) proves the converse isolation direction. The implementation now proves the needed direction: `External/CircularTopology.lean` constructs a continuous injective lift with fixed generator heights, and `External/CofinalCocycle.lean` proves it passes through each original cofinal order. Taking the preimage of the isolated cone proves `isOpen_singleton_cofinalProductCircularGroupOrder`. This fills the gap in the proposed dependency description without assuming quotient openness or changing the parity theorem.

Keep this project outside the dependency chain of M00. A completed even-rank formalization should not wait for the much larger dynamical classification project.

### 16.3 Permitted intermediate deliverables

A theorem of type `BaseConeGoal → EvenRankGoal` (`ConditionalEvenRankGoal`, manifest node K07) is a meaningful completed **conditional** result. A theorem of type

```lean
BaseConeGoal → OddRankObstructionGoal → ClassificationGoal
```

is another meaningful conditional result (`ConditionalClassificationGoal`, manifest node O03). The manifest therefore threads `BaseConeGoal` as an explicit hypothesis through H00–K07 and `OddRankObstructionGoal` through O02–O03; only M00, M01 and M02 depend on the external nodes E02 and O01. Report these types literally while the external proofs remain outstanding. Do not report either as the unconditional theorem, and do not hide hypotheses using globally postulated constants.

## 17. Implementation order and acceptance tests

### 17.1 Module layout

The task manifest uses this proposed layout:

```text
FnZPositiveCones/
  Interfaces.lean                -- C00, supplied goal definitions; audit nodes A00, A01
  Cone/Basic.lean                 -- C01–C04
  Cone/Topology.lean              -- C05
  Schreier/Positive.lean          -- T00–T03
  Actions/Weighted.lean           -- W00–W02
  Gamma/Basic.lean                -- G00–G04, G08
  Gamma/Schreier.lean             -- G05–G07
  Gamma/MarkedProduct.lean        -- G09–G15
  External/BaseCone.lean          -- E00–E02, only checked proofs/imports
  Gamma/PositiveCone.lean         -- H00–H01
  Cover/Modular.lean              -- D00–D03
  Cover/SourceCoordinates.lean    -- D04–D05, optional
  Cover/ExplicitBasis.lean        -- B00–B06
  Construction.lean              -- K00–K07, M02: existence helpers
  External/OddRank.lean           -- O00–O01, only checked proofs/imports
  Classification.lean            -- O02, O03: converse and classification helpers
  Main.lean                      -- M00, M01: the two main theorem declarations
```

Only the interface file is supplied as Lean source in this package; the other paths are proposed destinations for implementation tasks. The mathematical proofs in §§4–15 specify their contents.

### 17.2 Recommended development sequence

Start with the pinned API audit [A00]. Implement cone basics, the positive Schreier theorem, and the weighted-action utility independently. Next develop the algebraic subgroup certificate and the modular-cover/basis branch in parallel. Neither branch needs the external cone proof until the actual positive cones are assembled.

After the marked isomorphism and explicit free basis are available, implement the subgroup tower, power transversal, Schreier positivity, and transport. First close the conditional even-rank theorem. The isolation/topology branch and the odd-rank external adapter can then be developed independently of it.

The full dependency graph is in `tasks.json`; its topological order is machine validated. Task IDs, not informal section order, determine prerequisite relationships.

### 17.3 Local tactic guidance

Use `ext` or `Subtype.ext` before simplifying equalities in subgroup/product types. Normalize integer exponents with the appropriate `zpow` lemmas, never by silently changing them to natural powers. Use `fin_cases` for the fixed six-state table, and induction plus modular arithmetic for the parameterized cover.

Use `group` for noncommutative cancellation after substituting the named relation identities. Use `ring`/`norm_num` only in the additive modular/integer coordinates, not in the free group. Use `omega` for natural bounds and parity bookkeeping after exposing casts and divisions; it is not a replacement for the modular-unit argument.

For finite certificates, a proof by reduction or `decide` is acceptable only when the object is genuinely decidable and the resulting proof is checked. A Python boolean or a CAS output must not be inserted as an axiom. A computation in `FreeGroup` also does not automatically prove a corresponding identity in the presented group: those require the presentation-specific derivations of §9.2.

### 17.4 Regression checks already run [A01]

The package's standard-library Python program performed **48 exact assertions** for the fixed six-state certificate. These cover the six table relations (9.5), the two product identities (9.6), the relator action at every state, the checker's inverse-letter rule at every state (24 of the 48), evaluation of all six `A_s`, and the marked `X,Y₀,Z,C` evaluations.

It also performed **78,976 regression assertions** for `1≤d≤128`, checking the modular-to-staggered relabelling, the actions of `u` and `g`, the parity orbit size, the proposed inverse of two for odd `d`, and the candidate free-basis weight evaluations. These parameterized tests do **not** prove the universal statements for all `d`.

Both sets of checks passed. The exact report is `certificate_checks.json`; the fixed table is also supplied as signed-word data in `certificate_data.json`. The report explicitly excludes Lean compilation, the external theorems, uniform proofs in `d`, and derivations inside the presented group.

### 17.5 Release acceptance [A02]

Before calling the development an unconditional formalization, inspect the final theorem types and `#print axioms` output. No `sorryAx`, unproved project axioms, or hidden additional orderability assumptions may occur. Ordinary Lean foundations such as choice are not to be confused with an unproved mathematical theorem; disclose any additional computational trust mechanism separately.

Check all of the following semantic points during review: strict semigroup closure; no false commutativity assumption; exact subgroup subtype coercions; correct right-action convention; the marked image of `C`; a proved inverse for both claimed isomorphisms; the case `d=1`; a coprimality rather than field argument for composite odd `d`; and a checked odd-rank obstruction for nonexistence. The implementation retains both the direct FG proof and the full isolated-order theorem.

Also check the final target really uses `FreeGroup (Fin n) × Multiplicative ℤ` and natural rank `n≥2`, not an unspecified free group, a finite cyclic group, or a proposition strengthened with an accidental normality hypothesis.

## 18. Correspondence with the source

| Source item | Blueprint tasks/sections | Treatment |
|---|---|---|
| Definition of a positive cone and finite semigroup generation | C00, §2 | Exact semantics, represented by `Subsemigroup` |
| Lemma 2.1: isolation | C01, C04, C05, §§4 and 15 | Algebraic finite determination, then an explicit topology adapter |
| Lemma 2.2: positive Schreier criterion | T00–T03, §5 | Same mathematical statement, strengthened to arbitrary sets before the finite corollary; closure-induction proof |
| Theorem 3.1: Dubrovina–Dubrovin positive cone | E00–E02, §§7.4 and 16 | Explicit external proof project with exact marking |
| Lemma 3.2: two-sided positive sandwich | G01–G03, §7 | Four sign cases and nonempty-product-safe induction |
| Proposition 3.3: marked subgroup isomorphism | G04–G15, §§8–9 | Explicit algebraic certificate and a constructed inverse replace the sketch |
| Proposition 3.3: positive cone on `H` | H00–H01, §10 | First positive Schreier application |
| Identity for `b⁶` before §4's cover construction | G15, §9.6 | Recorded as a marked-image lemma |
| Proposition 4.1(1)–(2): word action and full cycle | D00–D03, §11 | Translation by one/two; singleton-safe orbit enumeration |
| Proposition 4.1(3): index and free rank | D02, B00–B06, §§11–12 | Orbit index plus an explicitly proved free basis |
| Proposition 4.1(4): parity | D03, §11.4 | Invertibility of two modulo `d` |
| Figure and Remark 4.2 | D04–D05, §11.5 | Proved optional coordinate and alternating-path identifications in `Cover.SourceCoordinates` |
| Remark 4.3: limitation of the transversal | D03, O00–O02 | Preserved logical distinction between construction failure and nonexistence |
| Theorem 1.1 / §5 | K00–K05, M00, §§13–14 | Second positive Schreier application and equivalence transport |
| Corollary 1.2 | M01, F00–F03; O00–O03, S00, I00–I01 | Exact unconditional classification; direct FG proof and the full isolated-order obstruction are both checked |
| Cited MMRT Theorem 1.1, odd direction | O00–O01, S00, I00–I01 | `mmrt_no_isolated_order_odd` and `oddRankObstruction` in `External/OddRankComplete.lean`; no FG hypothesis |
| Additional generator bound | K06, M02, §§2.2 and 14.4 | New derived upper bound, explicitly not an optimality claim |

Contextual historical assertions about regular languages, other braid-group orders, and the origin of the cover are not prerequisites of the proof and are not turned into unnecessary formalization tasks. The direct proof also makes the full-center calculation, the identification with `PSL₂(ℤ)`, and the separate ping-pong proof of the marked subgroup unnecessary for the local isomorphism branch.

### Implementation record and substantive replacements

The source correspondence above now has checked proofs for C01–C05, T00–T03, W00–W02, G00–G15, E00–E02, H00–H01, D00–D05, B00–B06, and the even-rank construction. `FnZPositiveCones.evenRank_hasFGPositiveCone` in `Main.lean` has the exact M00 statement. The manifest records each actual declaration and module. Root imports cover the implementation, not only `Interfaces.lean`.

The two replacements proposed in §§9 and 12 are implemented: the product isomorphism has a weight homomorphism as its checked inverse, and the modular cover has an explicit free basis. The fixed certificate occupies `Gamma/Certificate.lean`; presentation-specific identities occupy `Gamma/MarkedProduct.lean`; action and inverse construction occupy `Gamma/Weighted.lean` and `Gamma/Isomorphism.lean`. This separates file ownership without changing the mathematics.

For E00, an explicit piecewise linear action on ℝ replaces Navas's projective ping-pong proof. Its marked generators satisfy the exact relation and preserve a strict movement predicate that excludes the identity. E01 implements central positive fractions, finite-word normalization, and a positive complement for each reduced word. `External/BaseCone.lean` proves both exact supplied goals without assuming orderability or injectivity of the action. The temporary identity-adjoined monoid is used only inside totality; the endpoint remains the strict semigroup closure.

O00 and O01 are now proved in `External/OddRankComplete.lean`. The exact declarations are `mmrt_no_isolated_order_odd : LeftOrderOddRankObstructionGoal` and `oddRankObstruction : OddRankObstructionGoal`. Their two dynamical inputs are theorems, not hypotheses: `NoncofinalEndpointAction.center_cofinal_of_isolated` and `circularOddRankObstruction` in `CircularIsolatedComplete`. The cofinal quotient, integer cocycle, free-group splitting, continuous lift and exact recovery prove both required isolation transfers. `STRONG_OBSTRUCTION_REVIEW.md` records an independent review of the actual theorem types and axiom dependencies.

The noncofinal replacement takes an actual finite endpoint of the central orbit. Its orbit is weakly monotone for the given order, and resolving ties by that order recovers it. Two free-group actions preserve arbitrary finite endpoint tests while moving a common conjugate in opposite directions. Extending by a trivial central action yields distinct nearby product orders. This proves MMRT Proposition 4.12's needed conclusion without the earlier changing-primitive protection-bound step.

The circular branch first derives a successor from isolation. Last-letter accumulation sets are nonempty, closed and invariant. Isolation of the actual lifted order makes complementary-component stabilizers cyclic; cyclic accumulation is fixed, and the tight realization's genuine orbit-gap endpoints exclude such accumulation inside a component. This proves the required last-letter density without a minimal-set or no-finite-orbit assumption. `CircularSuffixSeparation` uses shortest last-letter insertion to avoid closed proper-suffix endpoint collisions (the repair corresponding to Matsumoto Lemma 7.2). `CircularIsolatedSeparation` then proves first-letter closure separation by protected crossing perturbations. Generic finite normalized domains and the endpoint parity proof finish MMRT Theorem 1.3's odd-rank direction.

The FG-specific route proves central cofinality directly from finite positive generation (`NoncofinalPrecone`) and first-letter closure separation from a finite positive-path cutset (`CircularFGSeparation`, `CircularFGDomains`). It constructs actual finite normalized circle domains (`CircularFGPingPong`). The endpoint modules extract their connected components, prove strict separation within each color, sort their cyclic order, and derive the generator/inverse adjacency equation from oriented endpoint images (`CircularComponentConfiguration`). This endpoint calculation corresponds to MMRT Proposition 2.8.

`CircularNormalizedOrbit` proves that each entire first-letter orbit closure lies inside its open normalized domain. Every finite domain endpoint therefore avoids the marked orbit closure. Except for the unique finite complementary interval containing the basepoint, the closed complementary intervals lie inside actual successor gaps. `CircularGapCoordinate` transports points to the identity gap and assigns their real coordinate there. The coordinate is invariant under every group element and increases strictly across each nonbase complementary interval. The endpoint action equations then give a finite permutation whose coordinate increases except at one distinguished interval. `PingPongGapPotential` proves that permutation is one cycle, and `CircularGapConnectivity` derives even rank using the checked boundary parity theorem.

This replaces MMRT §3.1's minimal-set gap argument and applies to either the FG or the isolated-order input once actual finite domains and a successor are supplied. It assumes neither essential domain components nor an unproved bijection between finite complementary intervals and orbit gaps. `FnZPositiveCones.hasFGPositiveCone_iff_even` in `Main.lean` combines this obstruction with M00. The manifest adds F00–F03, S00 and I00–I01 for the actual replacement dependencies while preserving the original O00/O01 contracts and conditional O03. S00 is the generic domain constructor: F02 depends on it rather than on the FG-specific F01. The stronger isolated-order theorem is proved independently of M01.

## 19. Sources and versioning

### Mathematical sources

**[Su]** Hang Lu Su, *Finitely generated positive cones in Fₙ × ℤ*, arXiv:2608.31103v1, 31 August 2026. The source result numbering in this document refers to this version.  
PDF: <https://arxiv.org/pdf/2608.31103v1>  
HTML: <https://arxiv.org/html/2608.31103v1>

**[DD]** T. V. Dubrovina and N. I. Dubrovin, *On braid groups*, Sbornik: Mathematics 192 (2001), no. 5, 693–703 (translation of Mat. Sb. 192 (2001), no. 5, 53–64), DOI 10.1070/SM2001v192n05ABEH000564. Cited by [Su, Theorem 3.1] as Theorem 5, specialised to `B₃` with `a = σ₁σ₂`, `b = σ₂⁻¹`.

**[Navas]** Andrés Navas, *A remarkable family of left-ordered groups: central extensions of Hecke groups*, arXiv:0909.4994v3; published in *Journal of Algebra* 328 (2011), no. 1, 31–42, DOI 10.1016/j.jalgebra.2010.10.020. Use the Main Theorem with parameter `n = 2`, i.e. the relation `ba²b=a`.  
<https://arxiv.org/pdf/0909.4994>

**[MMRT]** Dominique Malicet, Kathryn Mann, Cristóbal Rivas, Michele Triestino, *Ping-pong configurations and circular orders on free groups*, arXiv:1709.02348; *Groups, Geometry, and Dynamics* 13 (2019), 1195–1218. Use Theorem 1.1 and only its odd-rank obstruction.  
<https://arxiv.org/pdf/1709.02348>

### Mathlib sources inspected

The live documentation links below establish names and hypotheses that were inspected. They are not evidence of a successful build of this package.

- Strict-closure infrastructure: <https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Group/Subsemigroup/Basic.html>
- Semigroup maps: <https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Group/Subsemigroup/Operations.html>
- Commutative cone API, inspected to avoid inappropriate reuse: <https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Order/Group/Cone.html>
- Presentations: <https://leanprover-community.github.io/mathlib4_docs/Mathlib/GroupTheory/PresentedGroup.html>
- Complements/transversals: <https://leanprover-community.github.io/mathlib4_docs/Mathlib/GroupTheory/Complement.html>
- Ordinary Schreier theorem: <https://leanprover-community.github.io/mathlib4_docs/Mathlib/GroupTheory/Schreier.html>
- Free bases: <https://leanprover-community.github.io/mathlib4_docs/Mathlib/GroupTheory/FreeGroup/IsFreeGroup.html>
- Nielsen–Schreier: <https://leanprover-community.github.io/mathlib4_docs/Mathlib/GroupTheory/FreeGroup/NielsenSchreier.html>
- Cosets: <https://leanprover-community.github.io/mathlib4_docs/Mathlib/GroupTheory/Coset/Basic.html>
- Group actions and quotients: <https://leanprover-community.github.io/mathlib4_docs/Mathlib/GroupTheory/GroupAction/Quotient.html>
- Indices: <https://leanprover-community.github.io/mathlib4_docs/Mathlib/GroupTheory/Index.html>
- Modular arithmetic: <https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/ZMod/Basic.html>

Pinned source tree: <https://github.com/leanprover-community/mathlib4/tree/dec5b2b780537b6eaf7f5e5f000c12f7387fb24d>  
Pinned toolchain file: <https://raw.githubusercontent.com/leanprover-community/mathlib4/dec5b2b780537b6eaf7f5e5f000c12f7387fb24d/lean-toolchain>

The finite weighted certificates, the closure-induction presentation of positive Schreier rewriting, the modular relabelling formula, and the explicit basis proof above are supplied as derivations for this blueprint. Their universal correctness still needs the local Lean proofs listed in the manifest; they are not attributed to an existing mathlib theorem.
