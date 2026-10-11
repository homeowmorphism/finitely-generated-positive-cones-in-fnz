> Historical AI review of the snapshot identified below. This report is not
> a verification report for the current submission commit. Old namespaces,
> toolchains, and checkpoint statuses are preserved as written. Commit hashes and removed development files refer to the
> private development repository, not to this public snapshot.
> See [README.md](README.md) for current checks and
> [formalization.yaml](formalization.yaml) for review disclosure.

# Strong odd-rank obstruction review

Independent reviewer: cones worker. Implementation owners: coordinator, gamma worker, and classification-review worker. This review changed no implementation files.

The original O00 and O01 contracts are proved. The final artifact audit accepted these explicit types:

```lean
mmrt_no_isolated_order_odd :
  ∀ n : ℕ, 2 ≤ n → Odd n →
    ∀ O : LeftGroupOrder (FreeGroup (Fin n) × Multiplicative ℤ),
      ¬ IsOpen ({O} : Set (LeftGroupOrder (FreeGroup (Fin n) × Multiplicative ℤ)))

oddRankObstruction :
  ∀ n : ℕ, 2 ≤ n → Odd n →
    ∀ P : Subsemigroup (FreeGroup (Fin n) × Multiplicative ℤ),
      IsPositiveCone P → ¬ FinitelyDetermined P
```

Neither declaration assumes finite semigroup generation. The cone target remains the supplied strict `Subsemigroup` cone in the noncommutative product group.

The review covered `CircularLastLetterDensity.lean`, `CircularIsolatedSeparation.lean`, `CircularIsolatedComplete.lean`, and `OddRankComplete.lean`, with inspection of their critical adapters:

- Density uses the actual last-letter orbit sets. Their accumulation sets are nonempty, closed, invariant, and avoid the marked basepoint. Reverse isolation transfer gives finite determination of the lifted left order. Convexity and injectivity of the actual component stabilizer's free projection then give cyclicity, using the checked free-group nonisolation theorem. The separately reviewed tightness argument and covering-map transfer place every orbit accumulation point in each last-letter accumulation set. No minimal-set or finite-orbit exclusion theorem is assumed.
- Separation applies the successor word-length bound only after proving that an interval contains no full-orbit point. It does not turn finite-trace adjacency into full-orbit adjacency. The prescribed-last-letter argument produces a closed interval avoiding every proper suffix of both endpoints. This includes endpoint coincidences. The resulting supported crossing preserves the protected finite traces and contradicts isolation.
- `CircularIsolatedComplete` supplies both density and successor inputs. The actual normalized-domain and connected-endpoint calculation then proves `circularOddRankObstruction`, with no remaining geometric premise.
- `OddRankComplete` combines that circular obstruction with `NoncofinalEndpointAction.isolatedOddRankCenterCofinal`. The cofinal quotient adapter uses the checked lift through the given order. Opposite cones handle the negative orientation of the marked center. The exact cone/order topology equivalence produces O00 and O01.

The dependency check found no import cycle in the 134 project modules reachable from `OddRankComplete`. This closure contains no final classification or FG-obstruction module. At declaration level, O00 invokes the independently proved conditional circular/cofinal adapter, with both inputs supplied. It does not invoke the final O01 declaration. O01 then applies the existing cone adapter to O00.

Source correspondence: O00 proves the required odd-rank direction of [MMRT, Theorem 1.1](https://arxiv.org/pdf/1709.02348). Its circular input proves the odd-rank direction of MMRT Theorem 1.3. The separation/domain construction corresponds to [Mann–Rivas, Proposition 4.7 and Theorem 1.5](https://arxiv.org/pdf/1607.00054). Closed suffix avoidance uses the last-letter insertion method of [Matsumoto, Lemma 7.2, printed page 1430](https://ems.press/content/serial-article-files/30075), adapted and checked for free-group words. The invariant-component argument replaces the minimal-set route. The explicit quotient/lift topology proofs supply the isolation implications rather than relying on continuity and local injectivity alone.

Validation: the coordinator reported the completed `External.OddRankComplete` build with 9071 jobs. Independent command `lake env lean /private/tmp/StrongObstructionArtifactAudit.lean` passed with exit code 0. Its explicit examples check O00, O01, circular nonisolation, last-letter density, and first-letter separation against the built artifacts. Axiom audits of both final endpoints and four critical helpers report only `propext`, `Classical.choice`, and `Quot.sound`.

No proof or statement gap was found in this review. Earlier prose calling O00/O01 open needs updating by the coordinator; it does not represent an unresolved mathematical obligation in these final declarations.
