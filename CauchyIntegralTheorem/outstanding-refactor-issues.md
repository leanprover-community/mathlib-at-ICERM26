# Outstanding Refactor Issues

This refactor moved the existing declarations into the proposed module layout. The following items
are intentionally left for later passes because they are semantic changes, require mathlib
archaeology, or would broaden the proof-maintenance surface.

## Definition Shape

- `Path.IsPiecewiseC1` is still an abbreviation rather than a structure.
  Changing it to a structure may improve projection names and extensibility, but it would touch
  almost every proof using `rcases hγ with ⟨S, ...⟩`. I recommend doing this only after the file
  layout settles.

- `Path.IsPiecewiseLinear` is still the existing interpolation-based abbreviation.
  A lighter predicate mirroring the local affine-on-cells statement might be useful, especially for
  avoiding heavy equality-to-interpolation arguments. This should be designed together with the
  piecewise-`C¹` bridge, not introduced mechanically.

## Generalizations

- `complexCurveIntegral_sum_equalGrid_subpath` is still an equal-grid statement.
  The natural next theorem is the same additivity result over an arbitrary ordered subdivision.
  Once available, the local Cauchy ladder proof should use that theorem instead of choosing an
  equal mesh.

- I did not add a new `complexCurveIntegral_eq_sub_of_hasPrimitiveOn'` with integrability inferred
  automatically.
  Inferring integrability without smuggling in stronger holomorphic regularity facts is delicate.
  The current exact-on-open theorem,
  `complexCurveIntegral_eq_sub_of_isExactOn_piecewiseC1`, is the safer high-level API.

## Mathlib Checks

- `IntervalIntegral/Reparameterization.lean` is built from mathlib's
  `intervalIntegral.integral_deriv_smul_comp'` and
  `intervalIntegral.sum_integral_adjacent_intervals`. I did not find a single mathlib theorem with
  the same piecewise-`C¹` API, so the local packaging lemmas remain useful.

## Cleanup

- Two declarations still use `sorry`, as before this refactor:
  `Complex.AnalyticOnNhd.isExactOn_of_isSimplyConnected` and
  `complexCurveIntegral_eq_sum_meromorphic_residue_kernel_integrals`.
