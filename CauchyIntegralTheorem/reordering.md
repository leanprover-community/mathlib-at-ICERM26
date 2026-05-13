
Complex/CauchyIntegralTheorem.lean

``The following theorem is a proof of Cauchy's integral theorem for a complex domain $U\subset C$ in the sense that, for any two C^1 piecewise paths \gamma, \gamma^\prime: [0,1] \rightarrow U with same start and end points and every holomorphic function $f: U \rightarrow C$, the respective complex curve integrals \int \gamma f and \int \gamma^\prime f agree.
20 theorem complexCurveIntegral_eq_of_homotopic_piecewiseC1

``A corollary of complexCurveIntegral_eq_of_homotopic_piecewiseC1: All complex curve integrals over nullhomotopic C^1 piecewise paths are zero.''
105 **corollary** complexCurveIntegral_eq_zero_of_nullhomotopic_piecewiseC1

``A further corollary: All complex curve integrals over C^1 piecewise loops in simply connected domains are zero.''
125 **corollary** complexCurveIntegral_eq_zero_of_isSimplyConnected_piecewiseC1

Complex/HasPrimitives.lean

20 theorem AnalyticOnNhd.isExactOn_of_isSimplyConnected
31 **lemma** exists_primitive_of_analyticOnNhd_isSimplyConnected
42 theorem DifferentiableOn.isExactOn_of_isSimplyConnected
60 **lemma** exists_analyticOnNhd_pathIntegralPrimitiveOn_ball
116 **lemma** analyticOnNhd_pathIntegral_of_pathFamilyOn_ball

Complex/ResidueTheorem.lean

29 **lemma** fdzForm_meromorphicRemainder
43 **lemma** complexCurveIntegral_eq_principalPartSum_of_remainder_integral_eq_zero
65 **lemma** complexCurveIntegral_eq_principalPartSum_of_holomorphic_remainder
86 **lemma** complexCurveIntegral_sub_zpow_neg_eq_zero_of_two_le
150 **lemma** analyticOnNhd_of_meromorphicNFOn_nonneg_divisor
164 **lemma** analyticOnNhd_meromorphicRemainder_of_nonneg_divisor
174 **lemma** differentiableOn_meromorphicRemainder_of_nonneg_divisor

''This should be a reasonable version of the residue theorem''
200 theorem complexCurveIntegral_eq_sum_meromorphic_residue_kernel_integrals

CurveIntegral/Primitive.lean

24 lemma fdzForm_apply --> PUT INTO NEW ComplexCurveIntegral/Basic.lean
32 lemma complexCurveIntegral_def --> PUT INTO NEW ComplexCurveIntegral/Basic.lean
36 lemma complexCurveIntegral_eq_intervalIntegral_deriv --> PUT INTO NEW ComplexCurveIntegral/Basic.lean
Also this lemma should probably use the abbrev complexCurveIntegrand introduced below in the file.

43 **lemma** complexCurveIntegral_eq_sub_of_hasDerivAt_comp

``For a holomorphic function f having a primitive F, the complex curve integral for any path from a to b is just the difference F b - F a.'' 
60 **proposition** complexCurveIntegral_eq_sub_of_hasPrimitiveOn
NOTE THERE SHOULD BE A VERSION OF THIS PROPOSITION WITHOUT INTEGRALITY, INDUCE IT AS
propositiion complexCurveIntegral_eq_sub_of_hasPrimitiveOn'
Indeed, f is holomorphic being a derivative of a holomorphic function, hence there should be some integraility. I think this is Path.IsPiecewiseC1.intervalIntegrable_complexCurveIntegrand below.
I still think it should not generally dropped to avoid logical shortcuts. (That holomorphic functions are smooth is mostly a consequence of Cauchy Integral Formula, which follows from Cauchy Integral Theorem, which is precisely what we prove here.)

77 lemma sum_range_sub_consecutive --> Check that it is not already covered by mathlib. If it is not, put it in a separate file according to the most likely conventions used in mathlib.

90 lemma complexCurveIntegrand_apply

``Note: This is just an auxiliary version with integrality as an explicit requirement. The proposition you probably want to use is complexCurveIntegral_eq_sub_of_hasPrimitiveOn_open_piecewiseC1 below.''
93 **lemma** complexCurveIntegral_eq_sub_of_hasPrimitiveOn_piecewiseC1

200 lemma Path.IsPiecewiseC1.intervalIntegrable_complexCurveIntegrand

260 lemma Path.IsPiecewiseC1.curveIntegrable_fdzForm

279 **proposition** complexCurveIntegral_eq_sub_of_hasPrimitiveOn_open_piecewiseC1 --> RENAME THIS complexCurveIntegral_eq_sub_of_isExactOn_piecewiseC1 (or similar, if you find a more standard notation, but openness is not as important as exactness -- and is actually contain in isExactOn, I suppose)

public abbrev Path.UniformClose --> Should be in a separate file. Name that file according to where you would find such a thing in mathlib.

CurveIntegral/PathReparam.lean --> Rename intervalIntegral/Reparameterization.lean  ; COULD YOU CHECK FOR EACH OF THESE LEMMAS WHETHER IT IS ALREADY IN MATHLIB
37 lemma intervalIntegral_reparam_C1
58 lemma intervalIntegral_reparam_piecewise_C1_sum
124 lemma intervalIntegral_reparam_piecewise_C1
173 lemma intervalIntegral_reparam_piecewise_C1_zero_one

CurveIntegral/Local.lean

18 **lemma** exists_isPiecewiseLinear_mapsInto_of_isOpen_isConnected --> PUT INTO PiecewiseLinear/Open.lean
40 **proposition** eq_complexCurveIntegral_of_mapsInto_ball_piecewiseC1 --> PUT INTO Complex/CauchyIntegralTheoremAux.lean
81 **lemma** complexCurveIntegral_trans_piecewiseC1 --> PUT INTO ComplexCurveIntegral/PathAdditivity.lean
95 **lemma** complexCurveIntegral_subpath_split_two --> PUT INTO ComplexCurveIntegral/PathAdditivity.lean
164 **lemma** complexCurveIntegral_subpath_zero_one_split --> PUT INTO ComplexCurveIntegral/PathAdditivity.lean
310 **lemma** complexCurveIntegral_subpath_eq_intervalIntegral --> PUT INTO ComplexCurveIntegral/PathAdditivity.lean
387 **proposition** complexCurveIntegral_subpath_split  --> PUT INTO ComplexCurveIntegral/PathAdditivity.lean
''This is the main proposition we need, but it has room for improvement as a general fact on ComplexCurveIntegrals. There should be no equal grid requirement.''
414 **proposition** complexCurveIntegral_sum_equalGrid_subpath --> PUT INTO ComplexCurveIntegral/PathAdditivity.lean

479 theorem complexCurveIntegral_segment_same --> PUT INTO ComplexCurveIntegral/Basic.lean
490 **lemma** complexCurveIntegral_eq_of_uniformClose_piecewiseC1_of_thickening --> This seems a straightforward consequence of eq_complexCurveIntegral_of_mapsInto_ball_piecewiseC1''; put it for now into Complex/CauchyIntegralTheoremAux.lean as well. Add a comment in that file that it contains preliminary versions of the CauchyIntegralTheorem that are needed in the full proof.

777 **proposition** exists_eps_eq_complexCurveIntegral_of_uniformClose_piecewiseC1' --> PUT into Complex/CauchyIntegralTheoremAux.lean as well.

PiecewiseLinear/Basic.lean

``This is a standard and very useful result from topology that I could not find in mathlib. A function on $U$ is continuous if U is a finite union of closed subsets and the restriction of f to each of these closed subsets is continuous.``
24 lemma ContinuousOn.finset_iUnion_of_isClosed --> PUT into Topology/Union.lean

207 **proposition** piecewiseLinearInterpolation_apply_of_mem_Icc
``This is an equal grid version of piecewiseLinearInterpolation_apply_of_mem_Icc.``
288 **corollary** piecewiseLinearInterpolation_apply_equalGrid

349 **lemma** piecewiseLinearInterpolation_isPiecewiseLinear

``In a normed space E, every path [0,1]->E can be approximated by a piecewise linear one.``
357 **proposition** exists_isPiecewiseLinear_forall_dist_lt --> MOVE to PiecewiseLinear/Approximation.lean

``The following is a curiosity and the idea of considering a homotopy [0,1]^2 -> E as [0,1] -> [0,1] \times E may be useful for some inductive arguments. It is however not used in the proof of Cauchy's integral theorem.``
500 theorem exists_isPiecewiseLinear_homotopy --> MOVE to PiecewiseLinear/Approximation.lean

--> Could it be useful to implement a predicate ``isPiecewiseLinear`` on a path that mirrors the rhs of piecewiseLinearInterpolation_apply_of_mem_Icc? If so, make changes in the implementation elsewhere.
The current abbreviation IsPiecewiseLinear seems very heavy.

PiecewiseLinear/PiecewiseC1.lean --> THIS WHOLE FILE SHOULD BE RENAMED PiecewiseC1/Basic.lean

I think IsPiecewiseC1 should be implemented as a structure on paths? Contradict me if this would be unwise. If not make the changes.

74 **lemma** isPiecewiseC1_of_contDiffOn_extend
82 **lemma** IsPiecewiseC1.cast
156 lemma exists_subpath_partition --> MOVE To Bin/Subpath.lean if it is really not used anymore.
438 **lemma** IsPiecewiseC1.subpath 
580 **lemma** segment_isPiecewiseC1
593 **lemma** IsPiecewiseC1.trans
710 **lemma** IsPiecewiseC1.lineMap --> Move this, together with its preceeding abbreivation into PiecewiseC1/Homotopy.lean

PiecewiseLinear/PiecewiseC1_Adapter.lean

Add the comment that this file adds some infrastructure to move from our definition of PiecewiseC1: To use some interval integral statements from mathlib, it is more convenient to work with an ordered ``list'' of breakpoints than with just a finite set. It is also needed in one direction for connecting piecewise linear with piecewise C1.

24 lemma exists_mem_subdivision
63 **lemma** IsPiecewiseC1.exists_subdivision
155 **lemma** isPiecewiseC1_of_subdivision
215 **lemma** IsPiecewiseLinear.isPiecewiseC1 --> Put this into separate file PiecewiseC1/OfPiecewiseLinear.lean

PiecewiseLinear/Homotopy.lean --> Should move to PiecewiseC1/Homotopy

``Given a homotopy H : [0,1] \times [0,1] -> E, we can obtain a sequence of paths H i/N that are uniformly close to each other.``
24 **lemma** exists_uniform_grid_homotopy_slices_close

``In preparation of the proof of the main proposition exists_piecewiseC1_homotopy_of_homotopy in this file, we pick a sequence of piecewise C1-paths \Gamma i each of which approximates the path H i/N from the homotopy H.``
61 **lemma** exists_piecewiseC1_chain_of_homotopy

``This is the main proposition: In a normed space E, two paths that are topologically homotopic also admit a homotopy H of piecewise C1 paths.``
206 **proposition** exists_piecewiseC1_homotopy_of_homotopy