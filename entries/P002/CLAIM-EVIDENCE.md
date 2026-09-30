# P002: claim-to-evidence correspondence

## Selected declaration

`HordijkSteelThreshold.palomar_critical_window_variable_intensity`
(the only name in `comparator.json`).

Exact formal content, read from the Challenge:

```
∃ L : {lambda : ℝ // 0 < lambda} → ℝ,
  Continuous L ∧ Monotone L ∧
  ∀ lambda, 0 < L lambda ∧ L lambda ≤ 1 - Real.exp (-36 * lambda.val) ∧ L lambda < 1 ∧
    ∀ f : ℕ → ℝ, Tendsto (fun n => f n / n) atTop (𝓝 lambda.val) →
      Tendsto (fun n => rafProbability n (f n / n)) atTop (𝓝 (L lambda))
```

- Quantifiers and direction. One function `L` on the positive reals is asserted
  to exist. For each `lambda > 0` it satisfies the three inequalities, and the
  convergence holds for every real sequence `f` with `f(n)/n → lambda`. So the
  limit depends only on `lambda`, not on the particular sequence. There are no
  other hypotheses.
- Model (all definitions visible in the Challenge). Molecules `Molecule n` are
  the nonempty binary words of length at most `n`. Reactions `Reaction n` are
  pairs (product word of length at least two, split position), so
  `|Reaction n| = (n-2)2^(n+1) + 4`. `binaryPolymerCRS n 2` is the reversible
  ligation/cleavage system `u + v ⇌ uv`, and its food set is every word of length
  at most two. `IsRevRAF` requires a nonempty reaction set `S`. Both sides of
  every reaction in `S` must lie in a finite stage of the reversible closure of
  food under `S`, and every reaction in `S` needs a catalyst in that closure.
  `HasRAFEvent n` is the event that such an `S` exists.
- Randomness and normalization. `rafProbability n v` is the probability of
  `HasRAFEvent n` under independent Bernoulli catalysis coordinates, one for each
  (molecule, reaction) pair. The same coordinate serves both directions of a
  reaction. The parameter is `catalysisP n v = clamp(v·n/|Reaction n|)`, with
  `clamp(x) = min 1 (max 0 x)`. Evaluated at `v = f(n)/n`, the unclamped value is
  `f(n)/|Reaction n|` for `n > 0` (`rawCatalysisP_ratio` in the proof sources).
  So `f(n)` is the mean number of reactions catalyzed by one molecule, as in the
  manuscript's `f_n = p_n R_n`. The coordinates are sampled as two `setBernoulli`
  families (reactions that can fire from food, and all other reactions) with the
  same parameter. Their product is the same i.i.d. law on all coordinates.
- Limiting probability. The statement gives `0 < L(lambda) < 1` for every
  `lambda > 0`, so the limit lies strictly between zero and one. It also gives
  the gateway ceiling `L(lambda) ≤ 1 - e^(-36 lambda)`, together with continuity
  and monotonicity of `L`. The ceiling implies `L(lambda) → 0` as `lambda ↓ 0`.
  The limit `L(lambda) → 1` as `lambda → ∞` is not stated.

Informal claim supported: in the fixed-food, uniform, reversible binary-polymer
model with split-position reaction identities, if `f(n)/n → lambda ∈ (0, ∞)`
then the RAF probability converges to a limit that lies strictly between zero
and one. The limit is continuous and nondecreasing in `lambda` and is at most
`1 - e^(-36 lambda)`.

Manuscript correspondence: Theorem 2.2 (critical-window law), without the
identification `Θ(lambda) = S(1 - e^(-lambda))`. The theorem's eventual identity
`p_n = f_n/R_n` and its endpoint limit at infinity are also omitted. Corollary 2.3
(no finite step threshold) follows directly from the selected statement: take
`f(n) = lambda·n`, so that `rafProbability n lambda → L(lambda) ∈ (0,1)`.

Solution route: `Registry/P002/Solution.lean` imports
`proofs.HordijkSteelThreshold.PublicationResolution`. It sets
`L(x) = transitionLimit x` (defined in the proofs as the real value of the
infinite reversible survival probability at openness `1 - e^(-x)`). It then
applies `continuous_transitionLimit`, `transitionLimit_mono`,
`corrected_transition` (positivity, ceiling, `< 1`) and
`variable_intensity_transition`. The proof sources define `rafProbability`,
`catalysisP`, `uniformCatalysisMeasure`, `catalysisOf`, `HasRAFEvent`,
`binaryPolymerCRS` and `IsRevRAF` with matching definitions in the Challenge.

## Literature correspondence

Primary reference: W. Hordijk and M. Steel, "Autocatalytic sets in polymer
networks with variable catalysis distributions", *Journal of Mathematical
Chemistry* 54(10) (2016) 1997–2021, doi:10.1007/s10910-016-0666-z,
arXiv:1605.03919v1. The source describes uniform independent catalysis and bidirectional reactions.
Section 7 (Future work), Eq. (21), states the conjecture: for
`f_n ~ lambda·n` there should
be a finite `gamma > 0` such that the RAF probability tends to 0 for
`lambda < gamma` and to 1 for `lambda > gamma`.

Within the formalized model, the entry settles that no such `gamma` exists. At
every finite `lambda > 0` the limit exists and lies strictly between 0 and 1, so
both branches of the conjectured step fail. The resolution is specific to the
model conventions listed above: food `X_2`, uniform independent catalysis,
split-position identities, and one coordinate for both directions.

Relation to P036. P036 treats the same literature question in a different
convention. There, split descriptions `(u,v)` and `(v,u)` with `uv = vu` become
one channel, and the normalization is `p_n = f_n/|J_n|` over the quotient
channels. The two random models are not identical. The P036 manuscript
(Lemma 3.1, Example 3.2) shows that quotienting does not carry homogeneous
split-position Bernoulli catalysis to homogeneous quotient catalysis. P002's statement is
about the split-position model only and says nothing about the quotient model.
P036's selected statement asserts a positive monotone limit but not a limit
below one.

## Evidence boundary

- Not formalized in the selected statement: the identification of `L` with
  `S(1 - e^(-lambda))`, the infinite reversible closure process, the eventual
  exactness of the clamp, `L(lambda) → 1` as `lambda → ∞`, the outer
  sublinear/superlinear regimes (Corollary 2.4), and any convergence rate. The
  manuscript proves several of these in other declarations. They are not
  submitted here.
- The finite-`n` clamp is part of the definition of `rafProbability` and is
  explicit in the Challenge. For negative or very large `f(n)` it changes the
  parameter, but it does not affect the limit statement.
- No conditional premises, external axioms or unproved assumptions enter the
  statement. A text scan of the 153 local modules in the Solution import
  closure found no `sorry`, `admit`, `axiom` declaration, `native_decide`,
  `implemented_by` or `extern`. This scan is not an axiom-closure check.
