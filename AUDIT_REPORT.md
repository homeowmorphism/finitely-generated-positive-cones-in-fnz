> Historical AI review of the snapshot identified below. This report is not
> a verification report for the current submission commit. Old namespaces,
> toolchains, and checkpoint statuses are preserved as written. Commit hashes and removed development files refer to the
> private development repository, not to this public snapshot.
> See [README.md](README.md) for current checks and
> [formalization.yaml](formalization.yaml) for review disclosure.

# Adversarial audit of the Lean 4 formalization of arXiv:2608.31103v1

Repository `/Users/hanglu/Github/Lean4/positive_cones_in_fnz`, branch `main`, commit `6881f5d`.
Toolchain `leanprover/lean4:v4.35.0-rc2`; Mathlib pinned at `dec5b2b780537b6eaf7f5e5f000c12f7387fb24d`.
Paper TeX: `/Users/hanglu/Github/Lean4/fnz-positive-cones/references/fnz-positive-cones.tex` (576 lines), cited by line.

Read-only audit. `git diff --stat HEAD` is empty; the only untracked additions are `AI_AUDIT_PROMPT.md` (pre-existing) and `audit_scratch/`. Mathlib remains at the pinned commit with a clean working tree.

---

## 1. Verdict

**Do the two endpoints faithfully state Theorem 1.1 and Corollary 1.2? YES.**

**Does the kernel accept them from `propext`, `Classical.choice` and `Quot.sound` only? YES.**

```
$ cd /Users/hanglu/Github/Lean4/positive_cones_in_fnz && lake env lean audit_scratch/L1_Prints.lean
evenRank_hasFGPositiveCone : ∀ (n : ℕ), 2 ≤ n → Even n → HasFGPositiveCone (FreeGroup (Fin n) × Multiplicative ℤ)
hasFGPositiveCone_iff_even : ∀ (n : ℕ), 2 ≤ n → (HasFGPositiveCone (FreeGroup (Fin n) × Multiplicative ℤ) ↔ Even n)
'FnZPositiveCones.evenRank_hasFGPositiveCone' depends on axioms: [propext, Classical.choice, Quot.sound]
'FnZPositiveCones.hasFGPositiveCone_iff_even' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The printed types are literal: no `abbrev`, notation, auto-bound implicit or instance argument hides a hypothesis. `Even` is Mathlib's `∃ r, n = r + r` and `Odd` is Mathlib's, both resolving to Mathlib modules (§2, L1). Against TeX 76 ("For every even integer n ≥ 2, the group Fₙ × ℤ has a positive cone which is finitely generated as a semigroup") and TeX 82 ("For n ≥ 2, the group Fₙ × ℤ has a finitely generated positive cone if and only if n is even"), the hypothesis shapes `2 ≤ n`, `Even n` and the `↔` match exactly.

`Main.lean:26-27` spells the command `#printaxioms`. It does parse as `#print axioms` — Lean's maximal-munch tokenizer splits `#print` from the identifier `axioms` — and the messages appear during elaboration:

```
$ lake build
info: FnZPositiveCones/Main.lean:26:0: 'FnZPositiveCones.evenRank_hasFGPositiveCone' depends on axioms: [propext, Classical.choice, Quot.sound]
info: FnZPositiveCones/Main.lean:27:0: 'FnZPositiveCones.hasFGPositiveCone_iff_even' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (9103 jobs).
```

**The trust-chain result is backed by a positive control**, without which a clean scan proves nothing. Planting one sorried theorem and one axiom in the project's own namespace and running the brief's scan over them:

```
$ lake env lean audit_scratch/L1_PositiveControl.lean
CONTROL: declarations flagged for nonstandard axioms: [(FnZPositiveCones.audit_control_axiom, [FnZPositiveCones.audit_control_axiom]),
 (FnZPositiveCones.audit_control_uses_axiom, [FnZPositiveCones.audit_control_axiom]),
 (FnZPositiveCones.audit_control_sorried, [sorryAx])]
CONTROL: project axioms detected: [FnZPositiveCones.audit_control_axiom]
CONTROL PASSED: the scan detects both a sorry and a project axiom.
```

**No BLOCKER. One MAJOR, which is a broken repository check and a false documentation claim, not a mathematical defect. No mathematical defect was found**, and the sharpest degeneracy route on the even-rank side is closed by proof (finding N1 below).

---

## 2. Trust chain (L1), in detail

### 2.1 Whole-library scan

The brief's script, run verbatim:

```
$ lake env lean audit_scratch/FullAxiomScan.lean
scanned 3430 project declarations
OK: every project declaration uses only [propext, Classical.choice, Quot.sound]
FreeGroup is declared in Mathlib.GroupTheory.FreeGroup.Basic
Multiplicative is declared in Mathlib.Algebra.Group.TypeTags.Basic
Even is declared in Mathlib.Algebra.Group.Even
Odd is declared in Mathlib.Algebra.Ring.Parity
Subsemigroup is declared in Mathlib.Algebra.Group.Subsemigroup.Defs
Subsemigroup.closure is declared in Mathlib.Algebra.Group.Subsemigroup.Basic
Finset is declared in Mathlib.Data.Finset.Defs
Fin is declared in Init.Prelude
IsOpen is declared in Mathlib.Topology.Defs.Basic
LinearOrder is declared in Mathlib.Order.Defs.LinearOrder
CircularOrder is declared in Mathlib.Order.Circular
PresentedGroup is declared in Mathlib.GroupTheory.PresentedGroup
MulEquiv is declared in Mathlib.Algebra.Group.Equiv.Defs
Subgroup.index is declared in Mathlib.GroupTheory.Index
```

No shadow was reported for any of the fourteen core names.

### 2.2 A stronger scan, closing a gap in the brief's script

The brief's script filters by **name prefix**, so a declaration parked in a project module but outside the `FnZPositiveCones` namespace would escape it. I replaced the filter with the **defining module**:

```
$ lake env lean audit_scratch/L1_ModuleScan.lean
constants declared in project modules: 3531
project-module declarations OUTSIDE the FnZPositiveCones namespace: 97
project axioms: 0; opaque: 0; unsafe: 0; partial: 4
  PROJECT PARTIAL: [FnZPositiveCones.NoncofinalFreeSubgroup.vertices._unsafe_rec,
   FnZPositiveCones.CircularDynamics.evalWord._unsafe_rec,
   FnZPositiveCones.CircularDynamics.wordTrace._unsafe_rec,
   FnZPositiveCones.sourceAlternatingWord._unsafe_rec]
OK: every project-module declaration uses only [propext, Classical.choice, Quot.sound]
total axioms visible anywhere in the environment: 12
they are: [(Classical.choice, Init.Prelude), (lcVoid, Init.Prelude), (lcCast, Init.Prelude),
 (lcErased, Init.Prelude), (lcProof, Init.Prelude), (sorryAx, Init.Prelude), (Quot.sound, Init.Prelude),
 (propext, Init.Core), (lcUnreachable, Init.Prelude), (Quot.lcInv, Init.Prelude),
 (isScalarObj, Init.Prelude), (lcAny, Init.Prelude)]
```

The four `partial` constants are the compiler's own `._unsafe_rec` auxiliaries for well-founded recursion, which the brief's script skips by name. The twelve axioms visible anywhere are Lean core's; `sorryAx` is present in the environment, as it always is, but is used by nothing.

Of the 97 out-of-namespace declarations, 93 are `_private.FnZPositiveCones.*` private auxiliaries. The remaining four are auto-generated equation and congruence lemmas for **Mathlib** definitions, forced into existence when a project file first simp-normalizes them:

```
$ lake env lean audit_scratch/L1_Stray.lean
Equiv.sigmaSubtype.eq_1 :: kind=thm      parent declared in Mathlib.Logic.Equiv.Basic
FreeGroup.norm.congr_simp :: kind=thm    parent declared in Mathlib.GroupTheory.FreeGroup.Reduce
ZMod.finEquiv.congr_simp :: kind=thm     parent declared in Mathlib.Data.ZMod.Basic
Equiv.permCongrHom.eq_1 :: kind=thm      parent declared in Mathlib.Algebra.Group.End
```

None redefines a Mathlib declaration; each is an equation lemma *about* one.

### 2.3 What the endpoints actually rest on

`#print axioms` reports axioms but says nothing about `unsafe`, `partial` or `opaque` constants. I traced the endpoints' proof-term closures directly.

**A methodology trap worth recording**, because I fell into it first: at this toolchain `ConstantInfo.value?` with its **default** `allowOpaque := false` returns `none` for imported theorems, so a naive traversal silently visits nothing and reports a vacuous "clean". Either `ci.value? true` or matching `.thmInfo tv => tv.value` works. The repository's own `FinalContractAudit.lean:119` uses `ci.value? true` and is therefore **sound**; I verified the two accessors agree:

```
$ lake env lean audit_scratch/L1_AuditToolCheck.lean
project theorems: 2801; value? true returns some for 2801; .thmInfo field works for 2801
FinalContractAudit-style closure (value?):   1412 project constants
corrected closure (.thmInfo field):          1412 project constants
```

With the correct accessor:

```
$ lake env lean audit_scratch/L1_EndpointReach.lean
--- FnZPositiveCones.evenRank_hasFGPositiveCone
    proof-term closure: 12344 constants, 559 of them from project modules
--- FnZPositiveCones.hasFGPositiveCone_iff_even
    proof-term closure: 26827 constants, 1500 of them from project modules
--- FnZPositiveCones.mmrt_no_isolated_order_odd
    proof-term closure: 27389 constants, 1425 of them from project modules
```

Every `opaque` constant reached belongs to Mathlib or Lean core: `Real.wrapped*` (`Mathlib.Basic.Real.Basic`), `wrapped*` (`Mathlib.Topology.Defs.Filter`), `IsFreeGroup.wrapped*`, `String.Internal.append`, `Lean.opaqueId`. **No project `opaque`, no `unsafe`, no `partial`, and no nonstandard axiom is reachable from either endpoint.**

### 2.4 Keyword grep, every hit explained

Zero hits, in the package sources (not `.lake/`), for: `native_decide`, `implemented_by`, `@[extern]`, `unsafe`, `opaque`, `set_option`, `nolint`, `notation`, `macro`, `elab`, `syntax`, `macro_rules`, `declare_syntax`, `#eval`, `#reduce`.

| Token | Hits under `FnZPositiveCones/` | Explanation |
|---|---|---|
| `sorry` / `admit` | 2 | Both inside prose: `Interfaces.lean:7` ("contains no `sorry`, no `axiom`") and `FreeGroupOrbitPerturbation.lean:246` (the English word "admit"). |
| `axiom` | 2 | Both prose: `Interfaces.lean:7` and `NoncofinalDynamics.lean:227` ("without a dynamical axiom"). |
| `partial` | 3 | All prose, in docstrings about *partial actions* and *partial overlap*. |
| `decide` | 25 lines | All kernel-checked. |

The brief's estimate of "about forty" `decide` occurrences resolves as 25 in the library plus 13 in the seven root audit files, i.e. 38. Exactly one is not a bare `decide`:

```
$ grep -rn 'native_decide\|decide +' FnZPositiveCones/
FnZPositiveCones/Gamma/Weighted.lean:144:  decide +revert
```

`+revert` reverts dependent hypotheses before deciding; it is **not** `+native` and not `+kernel`. Nothing in the package uses `native_decide`.

### 2.5 Mathlib untampered; no shadowing

```
$ cd .lake/packages/mathlib && git rev-parse HEAD && git status --porcelain | wc -l
dec5b2b780537b6eaf7f5e5f000c12f7387fb24d
       0
```

No directory named `Mathlib`, `Lean`, `Init`, `Std` or `Batteries` exists inside the package. Comparing 165 project module names against 8,543 Mathlib module names gives **zero collisions**, and no project module sits under a reserved root. `lakefile.lean` contains one `require` (Mathlib at the pin) and no `moreLeanArgs`, `moreServerArgs` or `precompileModules`.

### 2.6 `autoImplicit`

`autoImplicit` and `relaxedAutoImplicit` are both **true** here, because `lakefile.lean` declares no `leanOptions` and Mathlib's own setting does not propagate downstream. The hazard is real — a typo silently becomes a variable:

```
$ lake env lean audit_scratch/L1_AutoImplicit.lean
@audit_autoimplicit_demo : {HasFGPostiveCone : Sort u_1} → ℕ → HasFGPostiveCone → HasFGPostiveCone
```

But it provably never fires in this project. A verifier established this definitively by elaborating **all 165 library source files under `-DautoImplicit=false -DrelaxedAutoImplicit=false`, with zero errors** — a stronger test than a binder-name heuristic, since it also covers private declarations, non-`Sort` binder domains and short names. Recorded as **N8**, not a finding.

---

## 3. Findings

### F1 — MAJOR. The repository's own documented validation command fails at HEAD.

**Files:** `scratch_axioms_twin.lean:24,27`; `validate_package.py:53-60`; claims at `README.md:50`, `PROGRESS.md:23`, `tasks.json:130`, `package_checks.json:7`.

`validate_package.py:53-60` scans every non-`.lake` `*.lean` file under the repository root for `\b(axiom|sorry|admit)\b` after stripping comments. The git-tracked root file `scratch_axioms_twin.lean`, added in commit `6881f5d` itself, contains:

```
24:theorem twin_sorried : 1 = 2 := sorry
27:axiom twin_axiom : 1 = 2
```

so the validator aborts.

**Reproduction.** Run in a clean worktree at the audited commit. This matters: my own `audit_scratch/` files also contain those tokens, so an in-tree run is confounded.

```
$ git worktree add --detach /tmp/audit_clean_head 6881f5d
$ cd /tmp/audit_clean_head && python3 validate_package.py; echo "EXIT=$?"
ValueError: Unexpected proof placeholder/postulate in scratch_axioms_twin.lean
EXIT=1
```

**Sole-cause control**, same clean worktree, that one file removed:

```
$ rm -f scratch_axioms_twin.lean && python3 validate_package.py; echo "EXIT=$?"
{ "package_structure": "passed", "task_count": 72, "dependency_edges": 150,
  "acyclic_dependency_graph": true, "certificate_data_matches_checker": true,
  "no_supplied_Lean_postulates_or_placeholders": true, "Lean_compilation_performed": true }
EXIT=0
```

**Four documented claims are falsified:**

1. `README.md:50` — "all seven audits, **package validation**, certificate checks and independent endpoint review passed again." The command is prescribed at `README.md:60` and `REVIEW_START_HERE.md:62`.
2. `PROGRESS.md:23` — "**repository validation** and certificate checks passed", in a sentence whose own command set names `python3 validate_package.py`.
3. `tasks.json:130` — "No supplied Lean file postulates an axiom." The word "supplied" does not narrow the scope away from a root file: `validate_package.py:51-52` describes its own check as covering "the supplied implementation/specification files (dependency sources under `.lake/` are not part of the package)", and emits the key `no_supplied_Lean_postulates_or_placeholders`.
4. `package_checks.json:7` — `"no_supplied_Lean_postulates_or_placeholders": true`, a git-tracked recorded output that is not reproducible at HEAD.

**Explicitly NOT falsified, and I decline to report it as such:** `README.md:50` "No project axioms or proof placeholders are admitted." Its own supporting clause is "`ProofAudit.lean`, `ReviewAudit.lean`, and `DynamicsAudit.lean` inspect exact types and kernel dependencies", which scopes "admitted" to kernel dependencies — and those are clean. That sub-claim is contestable at worst.

**This is not a soundness problem.** `lakefile.lean` declares only `@[default_target] lean_lib FnZPositiveCones`, so the file is outside the library, `lake build` never compiles it, and nothing references `twin_axiom` or `twin_sorried`. Its own header describes it as a "Worked twin" and a "contrast case", so this is a stray artifact, not misrepresentation. But nothing outside the file discloses it: `grep -rn scratch_axioms_twin` over all `.md`, `.json`, `.py`, `.lean` and `.log` outside `.lake` returns no hits, and `.gitignore` covers only `.lake/`, `__pycache__/`, `*.olean`, `*.ilean`.

**Suggested fix.** One line: delete the file, rename it out of `*.lean`, move it under `audit_scratch/`, or add it to `.gitignore`; then regenerate `package_checks.json`.

### F2 — MINOR. A docstring asserts uniqueness its theorem does not state.

**File:** `FnZPositiveCones/External/CircularGapConnectivity.lean:89-90`.

```lean
/-- There is exactly one finite complementary interval containing the base. -/
theorem exists_base_gap : ∃ b, (0 : StandardCircle) ∈ Q.componentFamily.gap b
```

The type is bare existence; no `∃!` or `ExistsUnique` appears in the file. Uniqueness is true and follows in two lines from `CircularIntervalGaps.lean:120 gap_disjoint`, which the same file already uses at line 110, but it is never stated. A reader citing this lemma by its docstring would cite the wrong statement.

Two independent verifiers checked five candidate docstring defects and **refuted four of them**; only this one survives. In particular `CircularGapConnectivity.lean:99-100` states its type verbatim after the colon, and `PingPongCombinatorics.lean:411-420` and `OddRankObstruction.lean:4-9` describe their modules rather than overclaiming their declarations.

**Suggested fix.** "There is a finite complementary interval containing the base; `gap_disjoint` makes it unique."

### F3 — MINOR. Four stale documentation facts.

| Sub-item | Claim | Reality |
|---|---|---|
| (a) | `blueprint.md:1312` "Only the interface file is supplied as Lean source in this package; the other paths are proposed destinations for implementation tasks." | All 17 paths in the §17.1 layout block exist as implemented Lean source, and `blueprint.md:1372` in the same document says the opposite. Partly mitigated by the dated banner at `blueprint.md:6` and by `blueprint.md:1289` calling the block a "proposed layout". |
| (b) | `README.md:11` "Approximately 8,900 words" for `blueprint.md` | `wc -w blueprint.md` → `10774`. Accurate at the initial commit (8,909); never updated. |
| (c) | `PROGRESS.md:57` "Nothing has been committed or pushed." | False on both halves: four commits exist, HEAD is `6881f5d`. No staleness qualifier; the file's own heading is dated the same day as HEAD. |
| (d) | `FINAL_CONTRACT_REVIEW.md:113`, `REVIEW_DEPENDENCIES.md:189` certify no HEAD diff in `lakefile.toml` | That file has never existed in any commit; the repo uses `lakefile.lean`. |

### F4 — MINOR. `REVIEW_DEPENDENCIES.md` states proved obligations as open, with no staleness banner.

`REVIEW_DEPENDENCIES.md:42` ("O00 and unconditional O01 remain unproved") and `:183` ("M01/A02 remain pending") are contradicted by `External/OddRankComplete.lean:15,24` and `Main.lean:20`. Unlike `EXTERNAL_OBLIGATIONS.md`, that file carries no staleness banner, and `PROGRESS.md:61` lists it among the current independent reports.

The analogous sentences in `EXTERNAL_OBLIGATIONS.md` are **downgraded to N3** below: `:36` falls inside the banner at `:16`, and `:288`/`:302-303`, although outside it, sit in a paragraph headed "Completed FG classification, checkpoint 8" that still cites a 9,072-job build against today's 9,103, and end with "These unfinished stronger assertions are not used by the proved M01 classification."

### F5 — MINOR. Documentation names that do not resolve as Lean identifiers.

Three `tasks.json` `declaration` fields are `kind: "validation"` pseudo-names with no Lean counterpart: `FnZPositiveCones.api_audit`, `FnZPositiveCones.independent_certificate_checks`, `FnZPositiveCones.release_audit`. `validate_package.py:32` treats the field as a declaration-name namespace, so the schema does not distinguish them from real names.

Four review references use **module**-qualified paths rather than namespace-qualified names, so pasting them into `#check` errors:

| Document | Written | Actual |
|---|---|---|
| `CLASSIFICATION_REVIEW.md:51` | `CircularNormalizedOrbit.closure_letterOrbit_subset_domain` | `FiniteNormalizedDomains.closure_letterOrbit_subset_domain` (`CircularNormalizedOrbit.lean:34`) |
| `CLASSIFICATION_REVIEW.md:69` | `CircularGapConnectivity.gap_connected` | `NormalizedIntervalData.gap_connected` (`CircularGapConnectivity.lean:150`) |
| `CLASSIFICATION_REVIEW.md:75` | `PingPongGapPotential.isCycleOn_of_increase_off_one` | `PingPong.isCycleOn_of_increase_off_one` (`PingPongGapPotential.lean:10`) |
| `EXTERNAL_OBLIGATIONS.md:229` | `CircularFGDomains.colorClosures_disjoint_of_semigroupFG` | `CircularFGSeparation.colorClosures_disjoint_of_semigroupFG` (`CircularFGDomains.lean:18`) |

Separately, 20 `tasks.json` `declaration` fields name superseded contract names, each resolved by that node's `implementation_declaration`. `tasks.json` documents this convention via `original_target_module` / `original_contract`, so it is by design, not a defect. **All 51 `implementation_declaration` values resolve and live in exactly their recorded `target_module`.**

### F6 — MINOR. Pre-rename identifiers, a stale hash, and stale module counts in dated reviews.

`CLASSIFICATION_REVIEW.md:12,18,97` and `FINAL_ENDPOINT_REVIEW.md:12,16,29` use the old `PositiveConesBlueprint.` prefix; `PROGRESS.md:71,77` say `PositiveCones/Main.lean` and package `positive-cones`. `REVIEW_START_HERE.md:48-50` already warns that dated reports retain former names, which covers the namespace part. Two items are **not** covered by that warning:

```
$ shasum -a 256 FnZPositiveCones/Interfaces.lean
5d15fb7bd5d59df06fd6b0001e95ae1a7d555cf43f2878db5e7208ec4ed6d178
```

against `FINAL_ENDPOINT_REVIEW.md:31`, which pins `4c6d4306…`; and `FINAL_CONTRACT_REVIEW.md:109` (163 modules) and `REVIEW_DEPENDENCIES.md:204` (39 modules) against the current 164.

### F7 — MINOR, cosmetic. `#printaxioms` written without a space.

`FnZPositiveCones/Main.lean:26-27`. It parses and emits the expected output (§1), so this is presentation only. Worth spelling `#print axioms` so no reader suspects a custom command.

### Candidate findings I investigated and dropped

Reported because "no findings" is only credible with the negative results attached.

- **"Seven generators" docstring** (`Gamma/PositiveCone.lean:41`). Two verifiers independently returned DROP. The phrase describes `Set.range gammaA ∪ {gammaC}` with `gammaA : Fin 6 → gammaH`; it asserts no cardinality, `blueprint.md:540` uses the same phrase, and the numeral 7 appears in no declaration's type or proof term anywhere in the library.
- **Four of the five candidate docstring overclaims** (see F2).
- **`README.md:50` "No project axioms or proof placeholders are admitted"** (see F1).
- **`FinalContractAudit.lean`'s traversal being vacuous.** I suspected this after hitting the `value?` trap myself. It is **not** vacuous: the file uses `value? true`, and its closure agrees with mine at 1,412 project constants (§2.3).
- **`autoImplicit` having bitten somewhere** (see §2.6 and N8).

---

## 4. Correspondence table (L4)

Rows marked **(verified directly)** I checked myself against the TeX; the rest were established by a dedicated sub-auditor and spot-checked.

| Paper item | TeX | Lean (file:line) | Verdict |
|---|---|---|---|
| Positive cone `G = P ⊔ P⁻¹ ⊔ {1}`; `⟨S⟩⁺` = non-empty products; FG | 57-64 | `IsPositiveCone` (`Interfaces.lean:16`), `SemigroupFG` (:20), `HasFGPositiveCone` (:24) | **MATCH** (verified directly). `Subsemigroup.closure` is `sInf {S \| s ⊆ S}`; its induction principle has only `mem` and `mul` cases and **no `one` case**, and `(⊥ : Subsemigroup G)` is literally `∅` (checked by `rfl`). Disjointness is derived, not assumed: `positiveCone_inv_not_mem` (`Cone/Basic.lean:18`). |
| Lemma 2.1, FG cone is isolated | 107-117 | `finiteGenerationImpliesFiniteDetermination` (`Cone/Basic.lean:95`), `finiteDetermination_iff_isolated` (`Cone/Topology.lean:40`), `semigroupFG_isolated` (:92) | **MATCH**. Proof follows the paper: cylinder open plus maximality (`positiveCone_rigidity`). |
| Lemma 2.2, positive Schreier criterion | 125-146 | `schreierDelta` (`Schreier/Positive.lean:66`), `positiveSchreierSet` (:85), `positiveSchreier_closure_eq` (:114), `positiveSchreier_finiteGeneration` (:160) | **MATCH** (verified directly). `schreierDelta hT t p = ⟨t*p*(rightRep hT (t*p))⁻¹, _⟩` is γ(t,p)=tp·(t̄p)⁻¹ (TeX 129); `positiveSchreierSet hT S = {k \| ∃ t ∈ T, ∃ s ∈ S, schreierDelta hT t s = k ∧ k ≠ 1}` is S_K = {γ(t,s)}∖{1} (TeX 142). `Subgroup.IsComplement ↑K T` is the **right** transversal G = ⊔ Kt, matching the orientation of γ. Finiteness is required only for the "in particular". |
| Γ₂ = ⟨a,b ∣ ba²b=a⟩ | 182-187 | `gammaRelator` (`Interfaces.lean:47`), `Gamma2` (:53), `gamma_relation` (`Gamma/Basic.lean:6`) | **MATCH**. Relator is `ba²ba⁻¹`. |
| Theorem 3.1, Dubrovina–Dubrovin cone | 189-191 | `baseCone` (`External/BaseCone.lean:510`) | **MATCH, stronger.** The paper cites; Lean proves. See N4. |
| Lemma 3.2, `bᵖabᵠ ∈ P₂`, `bᵏ ∈ P₂` | 202-221 | `gamma_sandwich_mem` (`Gamma/Basic.lean:100`), `gamma_positive_power_mem` (:129) | **MATCH**, integer exponents both sides. |
| φ : Γ₂ → ℤ/6, H = ker φ, index 6 | 223-232 | `gamma_phi` (`Gamma/Basic.lean:148`), `gammaH` (:165), `gammaH_index` (:167) | **MATCH**. Index 6 is a theorem, not a comment. |
| Prop 3.3, ψ : H ≅ F₂×ℤ with ψ(ab²)=x, ψ(a²b²a²)=y, ψ(a³)=z | 234-246 | `H_marked_product_equiv` (`Gamma/Isomorphism.lean:43`), `_X/_Y/_Z` (:56,:59,:62) | **MATCH**. The three marked images are `@[simp] theorem`s, not definitions. See N5. |
| Prop 3.3, generating set Y of P_H | 247-256 | `gammaGenerators` (`Gamma/Schreier.lean:107`), `gammaH_positive_generators` (`Gamma/PositiveCone.lean:42`) | **MATCH**. The six `gammaA s` are `b⁰ab², b⁻¹ab³, b⁻²ab⁴, b⁻³ab⁵, b⁻⁴ab⁰, b⁻⁵ab¹` and `gammaC = b⁶`, verified by `rfl`. |
| ψ(b⁶) = y⁻¹x⁻¹yxz⁻¹ | 316-324 | `psi_C` (`Gamma/Isomorphism.lean:66`), `markedProjection_C` (:74), `coverG` (`Cover/Modular.lean:14`) | **MATCH**, character for character. |
| Prop 4.1 (1)-(4): cover, index n−1, rank n, parity | 395-441 | `coverSubgroup` (`Cover/Modular.lean:102`), `cover_stabilizer_index` (:150), `coverRankEquiv` (`Cover/ExplicitBasis.lean:59`), `doubling_orbit_parity` (`Modular.lean:176`), `two_isUnit_of_odd` (:159) | **MATCH / DEVIATION (equivalent).** d = n−1 gives index n−1 and rank d+1 = n. `IsCycle` is never invoked; θ is *identified* as j ↦ j+1 on `ZMod d`, which is stronger. See N6. |
| Remarks after Prop 4.1 | 443-450 | `sourceRelabel` (`Cover/SourceCoordinates.lean:39`), `sourceRelabel_conjugates_x/_y` (:164,:172), `staggeredX/Y_fixed_iff` (:124,:131), `sourceAlternatingWord_state` (:210) | **DEVIATION, bridge proved.** See N6. |
| §5 proof: K, transversal {b⁶ᵏ}, positivity of Schreier elements | 457-528 | `secondSubgroup` (`Construction/Subgroup.lean:11`), `C_power_transversal` (:47), `secondSchreier_positive` (:120), `secondSubgroupFnZEquiv` (`Construction/Product.lean:35`), `conditionalEvenRank` (`Construction.lean:12`) | **MATCH**. `C_A_sandwich` is TeX 508 character for character. |
| Bound `6(n−1)+1` (beyond the paper) | 247-255, 457-528 | `evenRank_generator_bound` (`Construction.lean:39`) | **MATCH** (verified directly). See N7. |

### Specific checks (a)–(e)

**(a) `External/BaseCone.lean` — clean; no monoid/semigroup confusion.** `BaseConeAction.representation : Gamma2 →* (ℝ ≃o ℝ)` is `PresentedGroup.toGroup` applied to `generator_relations` (:175), so the relator `ba²ba⁻¹` is genuinely respected. The invariant `Moves` is closed under `*` (`moves_mul`, :196) and `¬ Moves 1` (:212); `positive_moves` (:216) uses `Subsemigroup.closure_induction`, whose only cases are `mem` and `mul` — non-empty products exactly. `baseTotal` concludes about the strict semigroup: `BaseTotalGoal = (∀ g : Gamma2, g = 1 ∨ g ∈ Subsemigroup.closure {aGamma, bGamma} ∨ g⁻¹ ∈ …)` by `rfl`. The identity-adjoined `Submonoid` appears only inside the normal-form proof.

**(b) Six-state weighted action — homomorphism on H; inverse two-sided.** `gamma_weighted_action` is `presentedWeightedLift` applied to a kernel-checked table identity (`Certificate.lean:21`), and `gamma_weighted_stabilizer` (`Weighted.lean:105`) proves the state-0 stabilizer is exactly `H`. `H_marked_product_equiv` is `(MulEquiv.ofBijective markedProduct_to_H ⟨inj, surj⟩).symm`, with injectivity from the weighted certificate and surjectivity from `gammaH_generators` — two independent proofs, not a fabricated inverse.

**(c) `coverRankEquiv` is an explicit basis.** `coverExplicitBasis d : FreeGroupBasis (Fin d ⊕ Unit) ↥(coverSubgroup d)` with basis elements the explicit words `u^j·x·(u^{-j})⁻¹` and `u^d`. `IsFreeGroup` is never used.

**(d) No special-casing.** No `d`-dependent case split on the even-rank path. `n = 2` (d = 1, `ZMod 1`) and composite odd d (9 = 3², 15 = 3·5) go through the same code; all instantiate.

**(e) Off-by-one correct.** `conditionalEvenRank` sets d = n−1, derives `0 < d` from `2 ≤ n` and `Odd d` from `Even n`, and transports to `FnZ (d+1)` = rank n. At n = 2: d = 1, `Odd 1` ✓, `NeZero 1` ✓. The bound lands at `6*((d+1)−1)+1 = 6d+1` ✓. `evenRank_hasFGPositiveCone` is definitionally `conditionalEvenRank baseCone`, with nothing further — confirmed by `#print`, not by `rfl` (proof irrelevance would make an `rfl` check vacuous).

---

## 5. Odd-direction reconstruction (L5)

The paper cites MMRT Theorem 1.1 for odd n; the repository proves it, in roughly 130 files under `External/`.

**Statement.** `mmrt_no_isolated_order_odd : LeftOrderOddRankObstructionGoal` (`External/OddRankComplete.lean:15`) unfolds (`External/OddRank.lean:12-14`) to

```
∀ (n : ℕ), 2 ≤ n → Odd n → ∀ (O : LeftGroupOrder (FnZ n)), ¬ IsOpen {O}
```

It quantifies over **all** left orders — no finite-generation, cofinality or orientation hypothesis — and "isolated" is literally `IsOpen ({O} : Set (LeftGroupOrder (FnZ n)))`, as the brief requires.

**Two routes, sharing a tail.** The route `Main.lean` actually uses is *not* the one through Lemma 2.1. Confirmed directly:

```
$ lake env lean audit_scratch/L5_RouteCheck.lean
closure of hasFGPositiveCone_iff_even: 26827 constants
  inEndpointClosure=false :: FnZPositiveCones.mmrt_no_isolated_order_odd
  inEndpointClosure=false :: FnZPositiveCones.oddRankObstruction
  inEndpointClosure=false :: FnZPositiveCones.finiteGenerationImpliesFiniteDetermination
  inEndpointClosure=false :: FnZPositiveCones.FinitelyDetermined
  inEndpointClosure=true  :: FnZPositiveCones.even_of_hasFGPositiveCone
  inEndpointClosure=true  :: FnZPositiveCones.hasFGPositiveCone_exists_finiteNormalizedDomains
  inEndpointClosure=true  :: FnZPositiveCones.NormalizedIntervalData.even_card
```

The classification's negative half runs `HasFGPositiveCone → ∃ finite normalized domains → Even n`, bypassing the topology entirely. The isolated-order theorem is proved separately and is strictly stronger. See N2.

**The shared tail** (both routes) is the citable core:

1. **Finite normalized ping-pong domains.** `FiniteNormalizedDomains R` (`CircularFGPingPong.lean:14`) bundles an open, regular, nonempty family `domain : ι × Bool → Set StandardCircle` with finitely many components, pairwise-disjoint closures, `0 ∉ closure`, and the **exact** normalization identity `letterPerm ρ s '' (closure (domain (inverseLetter s)))ᶜ = domain s` — an equality, strictly stronger than ping-pong `MapsTo`.
2. **Component/endpoint combinatorics.** `NormalizedIntervalData D` (`CircularComponentConfiguration.lean:32`) chooses real endpoints in the chart (0,1) for every component, strictly separated. It is **unconditionally inhabited** from `D` alone, so `FiniteNormalizedDomains.intervalData` is total. The exact image identity yields bijections `forward i : Pos i ≃ Neg i` and `backward i`, and MMRT Prop 2.8's local equation `backward i (forward i c) = positiveNext i c` becomes a theorem (:110).
3. **Connectivity via an invariant potential** — the genuinely new step. `gapCoordinate a` (`CircularGapCoordinate.lean:12`) transports a point of its successor-gap back to the identity gap and reads the chart coordinate; well defined off the orbit closure because gaps are disjoint under `IsSuccessor`, and invariant (:28). Exactly one finite gap contains the base (`exists_base_gap`); every other closed finite gap misses the orbit closure, hence lies in a single tight orbit gap, so the coordinate strictly increases across it; polygon edges preserve it. A finite permutation with such a potential has one cycle (`PingPongGapPotential`), giving GapStep-connectivity (`gap_connected`, :150).
4. **Parity.** `even_card_of_gap_connected` → `PingPong.even_of_connected_component_configuration` → `MMRTParity.even_of_one_boundary`: one base disc plus one polygon disc per generator, `discRotation` with |I|+1 cycles, a fixed-point-free gluing involution, connectivity forcing a single boundary cycle, then permutation signs give `Even (Fintype.card I)`.

**Correction to the brief's premise.** `NormalizedIntervalData.even_card` does *not* conclude with no extra hypothesis. Its actual type:

```
$ lake env lean audit_scratch/L1_Verify5.lean
@NormalizedIntervalData.even_card : ∀ {ι} {C : CircularGroupOrder (FreeGroup ι)} {R : CircularRealization C}
  {D : FiniteNormalizedDomains R} (Q : NormalizedIntervalData D) [Fintype ι] [Nonempty ι] {a : FreeGroup ι},
  C.IsSuccessor a → Even (Fintype.card ι)
```

It carries `[Fintype ι]`, `[Nonempty ι]` and a **successor hypothesis**. Both are discharged by the callers (`Classification.lean:40-41`), and `Fintype.card_fin` converts to `Even n` (:42), so the route is sound; but the summary should read "given a successor".

**Definitional honesty.** A dedicated sub-auditor printed and read every definition in the odd-rank spine — `CircularGroupOrder`, `TightRealization`, `CircularRealization`, `IsSuccessor`, `FiniteNormalizedDomains`, `NormalizedIntervalData`, `CircleIntervalFamily`, `gapCoordinate` — and found **no definition that encodes something weaker than its name or docstring claims**. The one wording defect is F3 in that lens's numbering, recorded here as N9: `FiniteNormalizedDomains`' docstring calls `finite_components` and `image_domain` "conclusions of the construction" when they are *fields*, i.e. obligations on any future constructor. Two verifiers judged this defensible as module-level prose; it is worth a one-line edit anyway.

**Source mapping** (`EXTERNAL_OBLIGATIONS.md`). MMRT Theorem 1.1 odd direction, MMRT Theorem 1.3 / the ping-pong branch, MMRT §4.2's isolation transfer, and Mann–Rivas Prop 4.7 all correspond, and none is weaker than the cited result; the §4.2 entry is explicit that continuity plus local injectivity gives only the other direction, the needed one coming from a continuous injective cocycle lift. **Matsumoto Lemma 7.2 is unverifiable from the Lean side**: `grep -rn "Matsumoto" --include='*.lean'` returns zero hits. What `CircularSuffixSeparation.lean:99` proves (`exists_closed_suffix_avoiding_pair`) is at least the right shape. Recommend adding the citation to that module's docstring or dropping the claim.

---

## 6. Claims ledger (L6), summary

A full ledger of roughly 70 claims was compiled. Everything substantive is **BACKED** except the items in §3. Highlights:

| Claim | Status |
|---|---|
| Both endpoint types, `README.md:31-33,43,47` | BACKED, exact |
| "The marked image of b⁶ is y⁻¹x⁻¹yxz⁻¹" (`README.md:45`) | BACKED — `psi_C` (`Gamma/Isomorphism.lean:66`) |
| "index n−1" and "rank n" (`README.md:45`, `PROGRESS.md:36`) | BACKED — `cover_stabilizer_index`, `coverRankEquiv` |
| Bound `6*(n-1)+1`, "a derived bound, not a minimality claim" | BACKED — `evenRank_generator_bound`; minimality consistently disclaimed at `Interfaces.lean:27`, `Construction.lean:38`, `blueprint.md:103,1189,1366`, `README.md:35` |
| "72 tasks including the original 65" | BACKED — 72 nodes, 72 topological entries, 150 edges, 0 duplicates; the 7 extras are F00–F03, S00, I00, I01 |
| All 51 `implementation_declaration` fields resolve, in their recorded `target_module` | BACKED, 51/51 |
| `blueprint.md:1349-1365` correspondence table | BACKED — all 44 task IDs resolve; row 1365's declarations exist with the stated types |
| Build: 9,103 jobs; seven audits exit 0; `verify_certificates.py --max-d 128` exit 0 | BACKED, reproduced |
| `certificate_checks.json` equals live checker output | BACKED, byte-identical after JSON normalization |
| Mathlib pin and toolchain | BACKED |
| "package validation … passed again" and three companions | **OVERCLAIM — F1** |
| `blueprint.md:1312`, `README.md:11`, `PROGRESS.md:57`, `lakefile.toml` | **STALE — F3** |
| `REVIEW_DEPENDENCIES.md:42,183` | **STALE — F4** |

---

## 7. Notes: deliberate deviations and structural observations

**N1 — Anti-vacuity of the even-rank chain, proved.** The sharpest way `baseCone` could be useless is a collapsed presentation: in a *trivial* group the empty subsemigroup satisfies `IsPositiveCone` vacuously. That degeneracy is real (`IsPositiveCone (⊥ : Subsemigroup PUnit)` elaborates), so ruling it out is not idle. It is ruled out:

```
$ lake env lean audit_scratch/L3_AntiVacuity.lean
'audit_Gamma2_nontrivial' depends on axioms: [propext, Classical.choice, Quot.sound]
'audit_baseCone_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`Nontrivial Gamma2` follows from the marked isomorphism `gammaH ≃* F₂ × ℤ`, and hence `∃ g : Gamma2, g ∈ basePositiveClosure`.

**N2 — Non-vacuity of the odd-rank statements is NOT certified by the library.** `mmrt_no_isolated_order_odd` at odd n is a ∀ over `LeftGroupOrder (FnZ n)`. At **even** n the library inhabits that type, via its own construction:

```
$ lake env lean audit_scratch/L3_OddNonVacuity.lean
'audit_leftOrder_inhabited_even' depends on axioms: [propext, Classical.choice, Quot.sound]
'audit_positiveCone_inhabited_even' depends on axioms: [propext, Classical.choice, Quot.sound]
```

At **odd** n nothing does: every declaration producing a `LeftGroupOrder` or `PositiveCone` takes one as input, and Mathlib at the pin proves no free-group orderability. Mathematically the type is inhabited (Fₙ × ℤ is left-orderable), so the theorem is not vacuous in truth — but a reader cannot verify that from inside the library. **This does not affect the endpoints**: `¬ HasFGPositiveCone (FnZ 3)` quantifies over `Finset (FnZ 3)`, which is inhabited, so the classification has real content at odd n regardless. Suggested addition: a witness `Nonempty (LeftGroupOrder (FnZ n))`, which would make the odd-rank theorems self-certifying.

**N3 — The endpoints bypass the advertised MMRT contracts.** Established in §5. The brief lists this as deliberate. `README.md:49` and `EXTERNAL_OBLIGATIONS.md:8` advertise `mmrt_no_isolated_order_odd` and `oddRankObstruction` as the locally-proved contracts without saying that `hasFGPositiveCone_iff_even` does not rest on them. Worth one clarifying sentence.

**N4 — MMRT Prop 4.12 is replaced, not transcribed, and this is disclosed.** Four modules transcribing MMRT's argument are **dead code** relative to the endpoint:

```
$ lake env lean audit_scratch/L1_Verify5.lean
exists=true  inClosure=false  :: FnZPositiveCones.NoncofinalCrossings.orbitIntervals_laminar
exists=true  inClosure=false  :: FnZPositiveCones.NoncofinalPrimitiveEntry.exists_primitive_entry
exists=true  inClosure=false  :: FnZPositiveCones.NoncofinalFreeSubgroup.index_ne_zero_of_fg_normal
exists=true  inClosure=false  :: FnZPositiveCones.NoncofinalConvexJump.normal_of_maximal_convex_noCrossings
exists=true  inClosure=true   :: FnZPositiveCones.NoncofinalEndpointAction.not_isolated_of_not_cofinal
exists=true  inClosure=true   :: FnZPositiveCones.FreeGroupOrbitPerturbation.exists_finite_trace_opposite_motions
```

Cofinality is instead discharged by `NoncofinalEndpointAction.center_cofinal_of_isolated`, which is **stronger** than the interface (every countable nonabelian free basis, no parity, no orientation). Two verifiers confirmed this is disclosed, not misrepresented: `EXTERNAL_OBLIGATIONS.md:8` says the argument "bypasses the changing-primitive trajectory-bound issue … that issue is no longer a required obligation", and `tasks.json` node I00 records the source as "Replacement for MMRT Proposition 4.12; bypasses the changing-primitive protection-bound step". I originally graded this MAJOR and **downgraded it to a note** on that evidence. If you cite this work, cite `center_cofinal_of_isolated` on its own terms, not as a formalization of MMRT Prop 4.12.

**N5 — Theorem 3.1 proved locally.** An explicit piecewise-linear action on ℝ (`a = x+1/3`, `h` a conjugated half-translation, `b = a·h⁻¹`) plus a word normalizer, rather than Dubrovina–Dubrovin or Navas. Verified sound in §4(a). This strengthens the formalization: the paper's only external input on this branch is discharged.

**N6 — Prop 3.3 by six-state weighted certificate.** Verified sound in §4(b). A sub-auditor independently recomputed all seven ψ-images by hand and in Lean and found them to agree term for term with the hard-coded table, so the certificate is forced by the relations rather than an unchecked oracle.

**N7 — Cover coordinates, and the scope of the relabelling.** `ZMod d` with reflections j ↦ −j and j ↦ −j−1, so `coverG` acts as j ↦ j+2 and transitivity is `IsUnit (2 : ZMod d)`, i.e. d odd. The bridge to the paper's vertices **is proved**: generator-level conjugations (`sourceRelabel_conjugates_x/_y`), the exact swap-pair and fixed-point lemmas matching TeX 331-341, and word-level alternating-path lemmas (`sourceAlternatingWord_vertex`, `sourceAlternatingWord_state`) matching TeX 444. It stops short of packaging `staggeredX/Y` as a `FreeGroup (Fin 2) →* Equiv.Perm (Fin d)`, so there is no intertwining lemma for arbitrary words and no named `Stab(v₀) = coverSubgroup d`. Two verifiers graded this a scope note rather than a defect: the main theorem uses the modular model directly, and `blueprint.md:891` discloses exactly this. A sub-auditor also checked the relabelling reproduces the paper's explicit cycles at n = 3,4,5,6.

**N8 — The bound is what the paper's construction yields.** Y has seven elements (TeX 249-255); T = {b⁶ᵏ : 0 ≤ k ≤ n−2} has n−1 elements. Of the seven, the six containing `a` give a nontrivial Schreier element for each of the n−1 cosets (TeX 505-510), and `w = b⁶` gives γ = 1 for k < n−2 and the single element b^{6(n−1)} at k = n−2 (TeX 512-518). Total 6(n−1)+1, exactly the Lean bound. No document claims minimality.

**N9 — `autoImplicit` is on but provably never fires** (§2.6). Latent risk for future edits only. Setting `leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]` in `lakefile.lean` would close it at no cost, since all 165 files already elaborate under those flags.

**N10 — `FiniteNormalizedDomains`' docstring** calls two of its own fields "conclusions of the construction" (`CircularFGPingPong.lean:11-14`). True of the one constructor at :32, misleading for anyone building the structure another way.

---

## 8. What was not checked, and why

1. **No cold build.** Every Lean result rests on the warm `.lake` (9,103 jobs replayed). The brief forbids editing `.lake/`, and a from-scratch Mathlib rebuild is hours of work. Consequence: I verified that the *stored* oleans are internally consistent and axiom-clean, not that they were produced by the pinned sources. Mitigation: Mathlib's working tree is clean at the pinned commit, and `lake build` reports no out-of-date targets.
2. **Mathlib itself is trusted.** The endpoints reach Mathlib and Lean-core `opaque` constants (§2.3). Auditing Mathlib is out of scope.
3. **The cited papers were not read.** I do not have MMRT, Mann–Rivas, Matsumoto, Dubrovina–Dubrovin or Hermiller–Šunić. Source mappings in §5 are judged on internal coherence between the Lean statement and the repository's own description, never against the sources. The Matsumoto Lemma 7.2 mapping is therefore **unverified**, not confirmed.
4. **Proof *strategies* under `External/` were read at docstring and top-level-statement granularity**, with dives only where a docstring and a type disagreed. The kernel has accepted these proofs, so correctness is settled; what a breadth pass can miss is a definition that means less than its name, and that is what was targeted.
5. **`verify_certificates.py` is not kernel evidence**, as its own output says: `"method": "integer arithmetic and reduced free-group words; not kernel checked"`, `"uniform_proof": false`. It passed (exit 0, 48 exact assertions, 78,976 regression assertions for 1 ≤ d ≤ 128) and its stored output matches, but the Lean proofs are what carry the theorems.
6. **`PROGRESS_HISTORY.md` (34,792 bytes) and the `build_logs/` contents were not line-audited**, being historical records rather than claims about current state.
7. **I did not attempt to prove the library inconsistent.** Given a clean axiom scan validated by a positive control, any false theorem would require unsoundness in Lean or Mathlib, which is outside this audit.

---

## Appendix: reproducing this audit

All scratch files are under `audit_scratch/` and run with `cd /Users/hanglu/Github/Lean4/positive_cones_in_fnz && lake env lean audit_scratch/<file>`.

| File | Purpose |
|---|---|
| `FullAxiomScan.lean` | the brief's whole-library scan |
| `L1_ModuleScan.lean` | stronger module-based scan (§2.2) |
| `L1_PositiveControl.lean` | **positive control**: proves the scan detects a planted `sorry` and axiom |
| `L1_EndpointReach.lean` | endpoint proof-term closures, correct accessor |
| `L1_AuditToolCheck.lean` | shows `FinalContractAudit.lean`'s traversal is sound |
| `L1_Prints.lean`, `L1_Hygiene.lean`, `L1_Stray.lean` | endpoint and definition prints; shadowing; stray declarations |
| `L2_Subbasis.lean` | the paper's one-sided subbasis generates the Lean topology |
| `L3_Vacuity.lean`, `L3_AntiVacuity.lean`, `L3_OddNonVacuity.lean` | degeneracy probes; N1; N2 |
| `L5_RouteCheck.lean`, `L1_Verify5.lean` | which declarations carry the endpoints; N4 |
| `L4_Schreier.lean`, `L4_SchreierBody.lean` | Lemma 2.2 against TeX 125-146 |

One note on the topology, proved rather than asserted (`L2_Subbasis.lean`): the paper lists the **one-sided** subbasis {P : g ∈ P} (TeX 103) while the Lean topology is induced from the full product of discrete `Bool`, whose subbasis is two-sided. They agree because for g ≠ 1 the complementary sign set is itself a positive-sign set, at g⁻¹, and at g = 1 both sign sets are trivial.
